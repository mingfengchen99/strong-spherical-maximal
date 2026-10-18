import EllipsoidGraph
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Set.Finite.List

/-!
# Uniform bounds for the actual ellipsoid amplitude

The radius parameter is written as exp(p). Smoothness at s=0 follows from
vanishing of chi on a neighborhood of the normal equator. Uniform bounds
come from compactness of the parameter box, for the actual mixed derivatives.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff Topology

namespace StrongSpherical.EllipsoidAmplitude
open ProductOscillation QuadraticGraph AmplitudeBounds EllipsoidGraph
variable {n m : ℕ}

/-- Taking an input derivative preserves joint smoothness in the parameter. -/
theorem contDiff_family_partial {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (a : P → Space n → ℂ) (ha : ContDiff ℝ ∞ (Function.uncurry a)) (i : Fin n) :
    ContDiff ℝ ∞ (Function.uncurry (fun p => coordinateDerivative i (a p))) := by
  have h : ContDiff ℝ ∞ (fun y : (P × Space n) × Space n => a y.1.1 y.2) :=
    ha.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact (h.fderiv contDiff_snd (by simp)).clm_apply contDiff_const

theorem contDiff_family_mixed {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (a : P → Space n → ℂ) (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (l : List (Fin n)) :
    ContDiff ℝ ∞ (Function.uncurry (fun p => mixedDerivative l (a p))) := by
  induction l generalizing a with
  | nil => exact ha
  | cons i l ih => exact ih _ (contDiff_family_partial a ha i)

/-- Compact parameter and support sets give one bound for every ordered
coordinate derivative through any prescribed finite order. -/
theorem exists_uniform_inputDerivativeBound {P : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (a : P → Space n → ℂ) (ha : ContDiff ℝ ∞ (Function.uncurry a))
    (K : Set P) (hK : IsCompact K) (B : Set (Space n)) (hB : IsCompact B)
    (hs : ∀ p ∈ K, Function.support (a p) ⊆ B) (k : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ K, InputDerivativeBound k M (a p) := by
  classical
  have hl : ∀ l : List (Fin n), ∃ M : ℝ,
      ∀ p ∈ K, ∀ v ∈ B, ‖mixedDerivative l (a p) v‖ ≤ M := by
    intro l
    obtain ⟨M, hM⟩ := (hK.prod hB).bddAbove_image
      (contDiff_family_mixed a ha l).continuous.norm.continuousOn
    exact ⟨M, fun p hp v hv => hM ⟨(p, v), ⟨hp, hv⟩, rfl⟩⟩
  choose M hM using hl
  obtain ⟨M0, hM0⟩ := ((List.finite_length_le (α := Fin n) (n := k)).image M).bddAbove
  refine ⟨max 0 M0, le_max_left _ _, ?_⟩
  intro p hp l hl v
  by_cases hv : v ∈ B
  · exact (hM l p hp v hv).trans ((hM0 ⟨l, hl, rfl⟩).trans (le_max_right _ _))
  · have hts : tsupport (a p) ⊆ B := closure_minimal (hs p hp) hB.isClosed
    have hz : mixedDerivative l (a p) v = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hh => hv (hts (tsupport_mixedDerivative_subset l (a p) hh)))
    simpa only [hz, norm_zero] using le_max_left (0 : ℝ) M0

/-- Input translation preserves all the coordinate derivatives, without
requiring any differentiability of a parameter chosen at the output. -/
theorem mixedDerivative_translate (l : List (Fin n)) (a : Space n → ℂ) (z : Space n) :
    mixedDerivative l (fun v => a (v + z)) = fun v => mixedDerivative l a (v + z) := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
    have heq : coordinateDerivative i (fun v => a (v + z)) =
        fun v => coordinateDerivative i a (v + z) := by
      funext v
      exact congrArg (fun L : Space n →L[ℝ] ℂ => L (coordinateVector i)) (fderiv_comp_add_right z)
    simp only [mixedDerivative, heq]
    exact ih _

theorem inputDerivativeBound_translate (k : ℕ) (M : ℝ) (a : Space n → ℂ)
    (ha : InputDerivativeBound k M a) (z : Space n) :
    InputDerivativeBound k M (fun v => a (v + z)) := by
  intro l hl v
  rw [mixedDerivative_translate]
  exact ha l hl _

/-- Exponential coordinates avoid a boundary in the positive radius space. -/
def exponentialRadii (p : Fin n → ℝ) : Radii n :=
  ⟨fun i => Real.exp (p i), fun _ => Real.exp_pos _⟩

def amplitudeArgument (p : Fin (m + 1) → ℝ) (w : Space (m + 1)) : Space (m + 1) :=
  inverseDilation (exponentialRadii p) (patchOffset 0 w)

@[simp] theorem amplitudeArgument_last (p : Fin (m + 1) → ℝ) (w : Space (m + 1)) :
    amplitudeArgument p w (Fin.last m) = (Real.exp (p (Fin.last m)))⁻¹ * (-Real.sqrt (normalInput w)) := by
  simp [amplitudeArgument, inverseDilation, diagonalDilation, exponentialRadii, patchOffset]

@[simp] theorem amplitudeArgument_castSucc (p : Fin (m + 1) → ℝ) (w : Space (m + 1)) (i : Fin m) :
    amplitudeArgument p w i.castSucc = (Real.exp (p i.castSucc))⁻¹ * (0 - w i.castSucc) := by
  simp [amplitudeArgument, inverseDilation, diagonalDilation, exponentialRadii, patchOffset, spatialInput]

def parameterAmplitude (chi : Space (m + 1) → ℂ)
    (p : Fin (m + 1) → ℝ) (w : Space (m + 1)) : ℂ :=
  graphAmplitude chi (fun _ => exponentialRadii p) 0 w

theorem continuous_amplitudeArgument :
    Continuous (fun y : (Fin (m + 1) → ℝ) × Space (m + 1) => amplitudeArgument y.1 y.2) := by
  have hcoord : ∀ j, Continuous (fun y : (Fin (m + 1) → ℝ) × Space (m + 1) => amplitudeArgument y.1 y.2 j) := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [amplitudeArgument_last]
      unfold normalInput
      exact ((Real.continuous_exp.comp ((continuous_apply (Fin.last m)).comp continuous_fst)).inv₀ (fun _ => Real.exp_ne_zero _)).mul (by fun_prop)
    · simp only [amplitudeArgument_castSucc]
      exact ((Real.continuous_exp.comp ((continuous_apply i.castSucc).comp continuous_fst)).inv₀ (fun _ => Real.exp_ne_zero _)).mul (by fun_prop)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin (m + 1) => ℝ)).comp (continuous_pi hcoord)

/-- Smoothness of the zero extension is derived from the normal patch support. -/
theorem contDiff_parameterAmplitude (chi : Space (m + 1) → ℂ) (hchi : ContDiff ℝ ∞ chi)
    (c : ℝ) (hc : 0 < c)
    (hpatch : Function.support chi ⊆ {u | u (Fin.last m) ≤ -c}) :
    ContDiff ℝ ∞ (Function.uncurry (parameterAmplitude chi)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hs : 0 < normalInput y.2
  · have hsmooth : ContDiffAt ℝ ∞
        (fun z : (Fin (m + 1) → ℝ) × Space (m + 1) =>
          (((Real.exp (z.1 (Fin.last m))) ^ 2 : ℝ) : ℂ) *
            ((2 * Real.sqrt (normalInput z.2) : ℝ) : ℂ)⁻¹ *
            ((∏ i, Real.exp (z.1 i) : ℝ) : ℂ)⁻¹ * chi (amplitudeArgument z.1 z.2)) y := by
      have hroot : ContDiffAt ℝ ∞ (fun z : (Fin (m + 1) → ℝ) × Space (m + 1) =>
          Real.sqrt (normalInput z.2)) y := by
        have hh : ContDiffAt ℝ ∞ (fun z : (Fin (m + 1) → ℝ) × Space (m + 1) => normalInput z.2) y := by
          unfold normalInput
          fun_prop
        exact hh.sqrt hs.ne'
      have harg : ContDiffAt ℝ ∞
          (fun z : (Fin (m + 1) → ℝ) × Space (m + 1) => amplitudeArgument z.1 z.2) y := by
        apply (contDiffAt_piLp 2).2
        intro j
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simp only [amplitudeArgument_last]
          change ContDiffAt ℝ ∞ (fun z => (Real.exp (z.1 (Fin.last m)))⁻¹ * (-Real.sqrt (normalInput z.2))) y
          have hh : ContDiffAt ℝ ∞ (fun z : (Fin (m + 1) → ℝ) × Space (m + 1) => z.1 (Fin.last m)) y := by fun_prop
          exact (hh.exp.inv (Real.exp_ne_zero _)).mul hroot.neg
        · simp only [amplitudeArgument_castSucc]
          change ContDiffAt ℝ ∞ (fun z => (Real.exp (z.1 i.castSucc))⁻¹ * (0 - z.2 i.castSucc)) y
          have hh : ContDiffAt ℝ ∞ (fun z : (Fin (m + 1) → ℝ) × Space (m + 1) => z.1 i.castSucc) y := by fun_prop
          exact (hh.exp.inv (Real.exp_ne_zero _)).mul (by fun_prop)
      have hch := hchi.contDiffAt.comp y harg
      have hprod : ContDiffAt ℝ ∞ (fun z : (Fin (m + 1) → ℝ) × Space (m + 1) =>
          (∏ i, Real.exp (z.1 i) : ℝ)) y := by fun_prop
      have hprod0 : (∏ i : Fin (m + 1), Real.exp (y.1 i)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i _ => Real.exp_ne_zero _)
      have hroot0 : (2 * Real.sqrt (normalInput y.2) : ℝ) ≠ 0 := by positivity
      exact (((Complex.ofRealCLM.contDiff.contDiffAt.comp y (by fun_prop : ContDiffAt ℝ ∞
        (fun z : (Fin (m + 1) → ℝ) × Space (m + 1) => (Real.exp (z.1 (Fin.last m))) ^ 2) y)).mul
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp y (contDiffAt_const.mul hroot)).inv
          (Complex.ofReal_ne_zero.mpr hroot0))).mul
        ((Complex.ofRealCLM.contDiff.contDiffAt.comp y hprod).inv
          (Complex.ofReal_ne_zero.mpr hprod0))).mul hch
    apply hsmooth.congr_of_eventuallyEq
    have he : ∀ᶠ z : (Fin (m + 1) → ℝ) × Space (m + 1) in 𝓝 y, 0 < normalInput z.2 :=
      (isOpen_lt continuous_const (by unfold normalInput; fun_prop : Continuous (fun z : (Fin (m + 1) → ℝ) × Space (m + 1) => normalInput z.2))).mem_nhds hs
    filter_upwards [he] with z hz
    simp [Function.uncurry, parameterAmplitude, graphAmplitude, hz, sqrtJacobian, dilationJacobian, exponentialRadii, amplitudeArgument]
  · have heq : amplitudeArgument y.1 y.2 (Fin.last m) = 0 := by
      rw [amplitudeArgument_last]
      change (Real.exp (y.1 (Fin.last m)))⁻¹ * (-Real.sqrt (normalInput y.2)) = 0
      rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_gt hs), neg_zero, mul_zero]
    have he : ∀ᶠ z : (Fin (m + 1) → ℝ) × Space (m + 1) in 𝓝 y,
        -c < amplitudeArgument z.1 z.2 (Fin.last m) := by
      apply (isOpen_lt continuous_const
        ((PiLp.continuous_apply 2 (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).comp continuous_amplitudeArgument)).mem_nhds
      change -c < amplitudeArgument y.1 y.2 (Fin.last m)
      rw [heq]
      linarith
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : (Fin (m + 1) → ℝ) × Space (m + 1) => (0 : ℂ)) y).congr_of_eventuallyEq
    filter_upwards [he] with z hz
    have hzero : chi (amplitudeArgument z.1 z.2) = 0 := by
      by_contra hne
      exact (not_le_of_gt hz) (hpatch hne)
    simp only [Function.uncurry, parameterAmplitude, graphAmplitude]
    split_ifs with ht
    · change _ * chi (amplitudeArgument z.1 z.2) = 0
      rw [hzero, mul_zero]
    · rfl

end StrongSpherical.EllipsoidAmplitude

namespace StrongSpherical.EllipsoidAmplitude
open ProductOscillation QuadraticGraph AmplitudeBounds EllipsoidGraph
variable {m : ℕ}

/-- The real amplitude support gives the fixed input box used by Lemma 3.2. -/
theorem graphAmplitude_support (chi : Space (m + 1) → ℂ)
    (hchi : Function.support chi ⊆ {u | ‖u‖ ≤ 2})
    (r : Space m → Radii (m + 1)) (hr : ∀ x, r x ∈ localRadii (m + 1)) (x : Space m) :
    Function.support (graphAmplitude chi r x) ⊆ inputSupport 16 x := by
  intro v hv
  have hs : 0 < normalInput v := by
    by_contra hn
    exact hv (by simp only [graphAmplitude, if_neg hn])
  have hne : chi (inverseDilation (r x) (patchOffset x v)) ≠ 0 := by
    intro hh
    apply hv
    simp only [graphAmplitude, if_pos hs, hh, mul_zero]
  have hnorm := hchi hne
  have hcoord : ∀ j, |inverseDilation (r x) (patchOffset x v) j| ≤ 2 := by
    intro j
    have hh : |inverseDilation (r x) (patchOffset x v) j| ≤ ‖inverseDilation (r x) (patchOffset x v)‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (inverseDilation (r x) (patchOffset x v)) j
    exact hh.trans hnorm
  have hnormal : Real.sqrt (normalInput v) ≤ 4 := by
    have hh := hcoord (Fin.last m)
    simp only [inverseDilation, diagonalDilation_apply, patchOffset, slicePoint_last] at hh
    rw [abs_mul, abs_inv, abs_of_pos ((r x).2 _), abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)] at hh
    have hm := mul_le_mul_of_nonneg_left hh ((r x).2 (Fin.last m)).le
    have he : (r x).1 (Fin.last m) * (((r x).1 (Fin.last m))⁻¹ * Real.sqrt (normalInput v)) = Real.sqrt (normalInput v) := by
      field_simp [ne_of_gt ((r x).2 _)]
    rw [he] at hm
    linarith [(hr x (Fin.last m)).2]
  constructor
  · intro i
    have hh := hcoord i.castSucc
    simp only [inverseDilation, diagonalDilation_apply, patchOffset, slicePoint_castSucc, PiLp.sub_apply] at hh
    rw [abs_mul, abs_inv, abs_of_pos ((r x).2 _)] at hh
    have hm := mul_le_mul_of_nonneg_left hh ((r x).2 i.castSucc).le
    have he : (r x).1 i.castSucc * (((r x).1 i.castSucc)⁻¹ * |x i - spatialInput v i|) = |x i - spatialInput v i| := by
      field_simp [ne_of_gt ((r x).2 _)]
    rw [he] at hm
    rw [abs_sub_comm]
    change |x i - spatialInput v i| ≤ 16
    linarith [(hr x i.castSucc).2]
  · rw [abs_of_pos hs]
    nlinarith [Real.sq_sqrt hs.le, Real.sqrt_nonneg (normalInput v)]

/-- The support is uniformly separated from the normal boundary s=0. -/
theorem graphAmplitude_support_normal_lower (chi : Space (m + 1) → ℂ)
    (c : ℝ) (hc : 0 < c)
    (hpatch : Function.support chi ⊆ {u | u (Fin.last m) ≤ -c})
    (r : Space m → Radii (m + 1)) (hr : ∀ x, r x ∈ localRadii (m + 1))
    (x : Space m) (v : Space (m + 1)) (hv : graphAmplitude chi r x v ≠ 0) :
    c ^ 2 ≤ normalInput v := by
  have hs : 0 < normalInput v := by
    by_contra hn
    exact hv (by simp only [graphAmplitude, if_neg hn])
  have hne : chi (inverseDilation (r x) (patchOffset x v)) ≠ 0 := by
    intro hh
    apply hv
    simp only [graphAmplitude, if_pos hs, hh, mul_zero]
  have hh := hpatch hne
  change inverseDilation (r x) (patchOffset x v) (Fin.last m) ≤ -c at hh
  simp only [inverseDilation, diagonalDilation_apply, patchOffset, slicePoint_last] at hh
  have hm := mul_le_mul_of_nonneg_left hh ((r x).2 (Fin.last m)).le
  have he : (r x).1 (Fin.last m) * (((r x).1 (Fin.last m))⁻¹ * (-Real.sqrt (normalInput v))) = -Real.sqrt (normalInput v) := by
    field_simp [ne_of_gt ((r x).2 _)]
  rw [he] at hm
  have hlo : c ≤ Real.sqrt (normalInput v) := by
    nlinarith [mul_nonneg hc.le (sub_nonneg.mpr (hr x (Fin.last m)).1)]
  nlinarith [Real.sq_sqrt hs.le]

end StrongSpherical.EllipsoidAmplitude

namespace StrongSpherical.EllipsoidAmplitude
open ProductOscillation QuadraticGraph AmplitudeBounds EllipsoidGraph
variable {m : ℕ}

/-- Compact logarithmic coordinates for all local radii. -/
def radiusParameterBox (n : ℕ) : Set (Fin n → ℝ) :=
  Set.pi univ (fun _ => Icc 0 (Real.log 2))

theorem isCompact_radiusParameterBox (n : ℕ) : IsCompact (radiusParameterBox n) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

theorem exponentialRadii_mem_local {p : Fin (m + 1) → ℝ}
    (hp : p ∈ radiusParameterBox (m + 1)) : exponentialRadii p ∈ localRadii (m + 1) := by
  intro j
  have hj := hp j (mem_univ j)
  constructor
  · change 1 ≤ Real.exp (p j)
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hj.1
  · change Real.exp (p j) ≤ 2
    simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using Real.exp_le_exp.mpr hj.2

theorem log_radii_mem_box (r : Radii (m + 1)) (hr : r ∈ localRadii (m + 1)) :
    (fun j => Real.log (r.1 j)) ∈ radiusParameterBox (m + 1) := by
  intro j _
  exact ⟨Real.log_nonneg (hr j).1, Real.log_le_log (r.2 j) (hr j).2⟩

theorem exponentialRadii_log (r : Radii (m + 1)) :
    exponentialRadii (fun j => Real.log (r.1 j)) = r := by
  apply Subtype.ext
  funext j
  exact Real.exp_log (r.2 j)

theorem graphAmplitude_eq_parameter_translate (chi : Space (m + 1) → ℂ)
    (r : Space m → Radii (m + 1)) (x : Space m) (v : Space (m + 1)) :
    graphAmplitude chi r x v =
      parameterAmplitude chi (fun j => Real.log ((r x).1 j)) (v + -slicePoint x 0) := by
  have hn : normalInput (v + -slicePoint x 0) = normalInput v := by
    simp [normalInput]
  have ha : patchOffset 0 (v + -slicePoint x 0) = patchOffset x v := by
    ext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp [patchOffset, hn]
    · simp [patchOffset, spatialInput, sub_eq_add_neg]
  simp only [parameterAmplitude, graphAmplitude, exponentialRadii_log, hn, sqrtJacobian, ha]

/-- All amplitude hypotheses of Lemma 3.2 now follow from the original smooth
cutoff and its patch support. The constant is uniform over all local radii. -/
theorem exists_graphAmplitude_bounds (chi : Space (m + 1) → ℂ)
    (hchi : ContDiff ℝ ∞ chi) (c : ℝ) (hc : 0 < c)
    (hpatch : Function.support chi ⊆ {u | u (Fin.last m) ≤ -c})
    (hsupport : Function.support chi ⊆ {u | ‖u‖ ≤ 2}) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ r : Space m → Radii (m + 1),
      (∀ x, r x ∈ localRadii (m + 1)) → ∀ x,
        ContDiff ℝ (m + 4 : ℕ) (graphAmplitude chi r x) ∧
        InputDerivativeBound (m + 4) M (graphAmplitude chi r x) ∧
        Function.support (graphAmplitude chi r x) ⊆ inputSupport 16 x := by
  have ha := contDiff_parameterAmplitude chi hchi c hc hpatch
  obtain ⟨M, hM, hbound⟩ := exists_uniform_inputDerivativeBound (parameterAmplitude chi) ha
    (radiusParameterBox (m + 1)) (isCompact_radiusParameterBox _) (inputSupport 16 (0 : Space m))
    (isCompact_inputSupport _ _) (fun p hp =>
      graphAmplitude_support chi hsupport (fun _ => exponentialRadii p)
        (fun _ => exponentialRadii_mem_local hp) 0) (m + 4)
  refine ⟨M, hM, ?_⟩
  intro r hr x
  have heq : graphAmplitude chi r x =
      fun v => parameterAmplitude chi (fun j => Real.log ((r x).1 j)) (v + -slicePoint x 0) :=
    funext (graphAmplitude_eq_parameter_translate chi r x)
  refine ⟨?_, ?_, graphAmplitude_support chi hsupport r hr x⟩
  · rw [heq]
    exact (ha.comp (contDiff_const.prodMk (contDiff_id.add contDiff_const))).of_le (WithTop.coe_le_coe.mpr (show (m + 4 : ℕ∞) ≤ ⊤ from le_top))
  · rw [heq]
    exact inputDerivativeBound_translate _ _ _
      (hbound _ (log_radii_mem_box (r x) (hr x))) _

end StrongSpherical.EllipsoidAmplitude

namespace StrongSpherical.EllipsoidAmplitude
open ProductOscillation QuadraticGraph AmplitudeBounds EllipsoidGraph
variable {m : ℕ}

theorem measurable_graphAmplitude_output (chi : Space (m + 1) → ℂ)
    (hchi : ContDiff ℝ ∞ chi) (c : ℝ) (hc : 0 < c)
    (hpatch : Function.support chi ⊆ {u | u (Fin.last m) ≤ -c})
    (r : Space m → Radii (m + 1)) (hr : ∀ j, Measurable (fun x => (r x).1 j))
    (v : Space (m + 1)) : Measurable (fun x => graphAmplitude chi r x v) := by
  have ha := (contDiff_parameterAmplitude chi hchi c hc hpatch).continuous.measurable
  have hp : Measurable (fun x : Space m => (fun j => Real.log ((r x).1 j))) :=
    measurable_pi_iff.mpr (fun j => (hr j).log)
  have hv : Measurable (fun x : Space m => v + -slicePoint x 0) := by
    unfold slicePoint
    fun_prop
  have h := ha.comp (hp.prodMk hv)
  simpa only [Function.comp_def, Function.uncurry, ← graphAmplitude_eq_parameter_translate] using h

/-- The complete graph slice estimate for the actual amplitude, with every
regularity, support and derivative hypothesis discharged. -/
theorem exists_actual_slice_bound (m : ℕ) (chi : Space (m + 1) → ℂ)
    (hchi : ContDiff ℝ ∞ chi) (c : ℝ) (hc : 0 < c)
    (hpatch : Function.support chi ⊆ {u | u (Fin.last m) ≤ -c})
    (hsupport : Function.support chi ⊆ {u | ‖u‖ ≤ 2})
    (beta : ℝ → ℂ) (hbeta : Measurable beta) (B : ℝ) (hB : ∀ t, ‖beta t‖ ≤ B)
    (hbetaSupport : Function.support beta ⊆ {t | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ lambda : ℝ, 1 ≤ lambda →
      ∀ (r : Space m → Radii (m + 1)) (hr : ∀ j, Measurable (fun x => (r x).1 j)),
        (∀ x, r x ∈ localRadii (m + 1)) →
        ∀ g : Space (m + 1) → ℂ, MemLp g 2 volume →
          MemLp (graphOperator (coefficients r hr) (graphAmplitude chi r)
            (frequencyAmplitude r beta lambda) g) 2 volume ∧
          eLpNorm (graphOperator (coefficients r hr) (graphAmplitude chi r)
            (frequencyAmplitude r beta lambda) g) 2 volume ≤
            ENNReal.ofReal (C * lambda ^ (1 / 2 - (m : ℝ) / 4)) * eLpNorm g 2 volume := by
  obtain ⟨M, hM, hAmp⟩ := exists_graphAmplitude_bounds chi hchi c hc hpatch hsupport
  obtain ⟨C, hC, hSlice⟩ := exists_uniform_slice_bound m 16 M B (by norm_num) hM
    beta hbeta hB hbetaSupport
  refine ⟨C, hC, ?_⟩
  intro lambda hlambda r hr hlocal g hg
  exact hSlice lambda hlambda r hr hlocal (graphAmplitude chi r)
    (fun x => (hAmp r hlocal x).1) (fun x => (hAmp r hlocal x).2.1)
    (fun x => (hAmp r hlocal x).2.2)
    (measurable_graphAmplitude_output chi hchi c hc hpatch r hr) g hg

end StrongSpherical.EllipsoidAmplitude
