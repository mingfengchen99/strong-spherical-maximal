import JointOscillation
import Mathlib.Analysis.Calculus.FDeriv.Star
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Uniform input-amplitude bounds

Leibniz estimates for the actual ordered coordinate derivatives, volume bounds
for the input support box, and uniform control of the paired-amplitude seminorm
in JointOscillation. This supplies the amplitude constant in the joint input
integral form of (3.19) in arXiv:2609.32421v2.

The final theorem quantifies a single positive constant before the amplitude
family and all varying phase parameters. Gram-kernel frequency integration
and the Schur/TT* operator argument remain subsequent steps.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace StrongSpherical.AmplitudeBounds

open ProductOscillation QuadraticGraph JointOscillation
variable {n m k : ℕ}

/-- Uniform bounds for every ordered input coordinate derivative through order `k`,
including the empty list, which is the amplitude itself. -/
def InputDerivativeBound (k : ℕ) (M : ℝ) (a : Space n → ℂ) : Prop :=
  ∀ l : List (Fin n), l.length ≤ k → ∀ v, ‖mixedDerivative l a v‖ ≤ M

theorem inputDerivativeBound_mono {j : ℕ} {M : ℝ} {a : Space n → ℂ}
    (hjk : j ≤ k) (ha : InputDerivativeBound k M a) : InputDerivativeBound j M a :=
  fun l hl v => ha l (hl.trans hjk) v

theorem inputDerivativeBound_partial (i : Fin n) {M : ℝ} {a : Space n → ℂ}
    (ha : InputDerivativeBound (k + 1) M a) :
    InputDerivativeBound k M (coordinateDerivative i a) := by
  intro l hl v
  exact ha (i :: l) (by simpa only [List.length_cons] using Nat.add_le_add_right hl 1) v

theorem mixedDerivative_append (l r : List (Fin n)) (a : Space n → ℂ) :
    mixedDerivative (l ++ r) a = mixedDerivative r (mixedDerivative l a) := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih => exact ih (coordinateDerivative i a)

/-- Real coordinate differentiation commutes with complex conjugation, including
at points where the Fréchet derivative is defined to be zero. -/
theorem coordinateDerivative_conj (i : Fin n) (a : Space n → ℂ) :
    coordinateDerivative i (fun v => conj (a v)) = fun v => conj (coordinateDerivative i a v) := by
  ext v
  unfold coordinateDerivative
  change fderiv ℝ (fun v => star (a v)) v (coordinateVector i) = star _
  rw [fderiv_star]
  rfl

theorem mixedDerivative_conj (l : List (Fin n)) (a : Space n → ℂ) :
    mixedDerivative l (fun v => conj (a v)) = fun v => conj (mixedDerivative l a v) := by
  induction l generalizing a with
  | nil => rfl
  | cons i l ih =>
    simp only [mixedDerivative, coordinateDerivative_conj]
    exact ih (coordinateDerivative i a)

theorem inputDerivativeBound_conj {M : ℝ} {a : Space n → ℂ}
    (ha : InputDerivativeBound k M a) : InputDerivativeBound k M (fun v => conj (a v)) := by
  intro l hl v
  simpa only [mixedDerivative_conj, Complex.norm_conj] using ha l hl v

theorem coordinateDerivative_add (i : Fin n) {a b : Space n → ℂ}
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    coordinateDerivative i (fun v => a v + b v) =
      fun v => coordinateDerivative i a v + coordinateDerivative i b v := by
  ext v
  unfold coordinateDerivative
  rw [fderiv_fun_add (ha v) (hb v)]
  rfl

theorem coordinateDerivative_mul (i : Fin n) {a b : Space n → ℂ}
    (ha : Differentiable ℝ a) (hb : Differentiable ℝ b) :
    coordinateDerivative i (fun v => a v * b v) =
      fun v => coordinateDerivative i a v * b v + a v * coordinateDerivative i b v := by
  ext v
  unfold coordinateDerivative
  rw [fderiv_fun_mul (ha v) (hb v)]
  change a v * fderiv ℝ b v (coordinateVector i) + b v * fderiv ℝ a v (coordinateVector i) = _
  ring

theorem mixedDerivative_add (l : List (Fin n)) {a b : Space n → ℂ}
    (ha : ContDiff ℝ l.length a) (hb : ContDiff ℝ l.length b) :
    mixedDerivative l (fun v => a v + b v) =
      fun v => mixedDerivative l a v + mixedDerivative l b v := by
  induction l generalizing a b with
  | nil => rfl
  | cons i l ih =>
    rw [mixedDerivative, coordinateDerivative_add i
      (ha.differentiable (by simp)) (hb.differentiable (by simp))]
    exact ih (contDiff_partial i ha) (contDiff_partial i hb)

/-- Each derivative splits between the two factors, costing a factor of two. -/
theorem norm_mixedDerivative_mul_le (l : List (Fin n)) (M N : ℝ) (hM : 0 ≤ M)
    {a b : Space n → ℂ} (ha : ContDiff ℝ l.length a) (hb : ContDiff ℝ l.length b)
    (hDa : InputDerivativeBound l.length M a) (hDb : InputDerivativeBound l.length N b)
    (v : Space n) :
    ‖mixedDerivative l (fun u => a u * b u) v‖ ≤ (2 : ℝ) ^ l.length * M * N := by
  induction l generalizing a b with
  | nil =>
    simp only [mixedDerivative, List.length_nil, pow_zero, one_mul, norm_mul]
    exact mul_le_mul (hDa [] (by simp) v) (hDb [] (by simp) v) (norm_nonneg _) hM
  | cons i l ih =>
    have ha0 : ContDiff ℝ l.length a := ha.of_le (by norm_cast; simp)
    have hb0 : ContDiff ℝ l.length b := hb.of_le (by norm_cast; simp)
    have ha1 : ContDiff ℝ l.length (coordinateDerivative i a) := contDiff_partial i ha
    have hb1 : ContDiff ℝ l.length (coordinateDerivative i b) := contDiff_partial i hb
    have hDa0 := inputDerivativeBound_mono (Nat.le_succ l.length) hDa
    have hDb0 := inputDerivativeBound_mono (Nat.le_succ l.length) hDb
    have hDa1 := inputDerivativeBound_partial i hDa
    have hDb1 := inputDerivativeBound_partial i hDb
    have h1 := ih ha1 hb0 hDa1 hDb0
    have h2 := ih ha0 hb1 hDa0 hDb1
    rw [mixedDerivative, coordinateDerivative_mul i
      (ha.differentiable (by simp)) (hb.differentiable (by simp)),
      mixedDerivative_add l (ha1.mul hb0) (ha0.mul hb1)]
    calc
      _ ≤ ‖mixedDerivative l (fun u => coordinateDerivative i a u * b u) v‖ +
          ‖mixedDerivative l (fun u => a u * coordinateDerivative i b u) v‖ := norm_add_le _ _
      _ ≤ (2 : ℝ) ^ l.length * M * N + (2 : ℝ) ^ l.length * M * N := add_le_add h1 h2
      _ = _ := by simp only [List.length_cons, pow_succ]; ring

/-- A uniform derivative bound for a product through the full stated order. -/
theorem inputDerivativeBound_mul (M N : ℝ) (hM : 0 ≤ M) (hN : 0 ≤ N)
    {a b : Space n → ℂ} (ha : ContDiff ℝ k a) (hb : ContDiff ℝ k b)
    (hDa : InputDerivativeBound k M a) (hDb : InputDerivativeBound k N b) :
    InputDerivativeBound k ((2 : ℝ) ^ k * M * N) (fun v => a v * b v) := by
  intro l hl v
  calc
    _ ≤ (2 : ℝ) ^ l.length * M * N := norm_mixedDerivative_mul_le l M N hM
      (ha.of_le (by exact_mod_cast hl)) (hb.of_le (by exact_mod_cast hl))
      (inputDerivativeBound_mono hl hDa) (inputDerivativeBound_mono hl hDb) v
    _ ≤ _ := by gcongr; norm_num

end StrongSpherical.AmplitudeBounds

namespace StrongSpherical.AmplitudeBounds
open ProductOscillation QuadraticGraph JointOscillation
variable {m : ℕ}

/-- Center of the input box, with last coordinate zero. -/
def inputCenter (z : Space m) : Fin (m + 1) → ℝ := Fin.snoc (fun i => z i) 0

/-- The corresponding coordinate box before applying `WithLp.toLp`. -/
def inputCube (R : ℝ) (z : Space m) : Set (Fin (m + 1) → ℝ) :=
  Set.pi univ (fun j => Icc (inputCenter z j - R) (inputCenter z j + R))

theorem inputSupport_eq_preimage_cube (R : ℝ) (z : Space m) :
    inputSupport R z = (@WithLp.ofLp 2 (Fin (m + 1) → ℝ)) ⁻¹' inputCube R z := by
  ext v
  constructor
  · intro hv j _
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa only [inputCenter, Fin.snoc_last, zero_sub, zero_add, normalInput, mem_Icc] using abs_le.mp hv.2
    · have h := abs_le.mp (hv.1 i)
      simp only [inputCenter, Fin.snoc_castSucc, mem_Icc]
      constructor <;> linarith [h.1, h.2]
  · intro hv
    constructor
    · intro i
      have h := hv i.castSucc (mem_univ _)
      simp only [inputCenter, Fin.snoc_castSucc, mem_Icc] at h
      apply abs_le.mpr
      constructor <;> linarith [h.1, h.2]
    · have h := hv (Fin.last m) (mem_univ _)
      simp only [inputCenter, Fin.snoc_last, zero_sub, zero_add, mem_Icc] at h
      exact abs_le.mpr h

theorem isCompact_inputCube (R : ℝ) (z : Space m) : IsCompact (inputCube R z) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem measurableSet_inputCube (R : ℝ) (z : Space m) : MeasurableSet (inputCube R z) :=
  (isCompact_inputCube R z).isClosed.measurableSet

theorem volume_inputSupport (R : ℝ) (z : Space m) :
    volume (inputSupport R z) = (ENNReal.ofReal (2 * R)) ^ (m + 1) := by
  rw [inputSupport_eq_preimage_cube]
  rw [(PiLp.volume_preserving_ofLp (Fin (m + 1))).measure_preimage (measurableSet_inputCube R z).nullMeasurableSet]
  change Measure.pi (fun _ : Fin (m + 1) => (volume : Measure ℝ)) (inputCube R z) = _
  rw [inputCube, Measure.pi_pi]
  simp only [Real.volume_Icc]
  have heq : ∀ j : Fin (m + 1), inputCenter z j + R - (inputCenter z j - R) = 2 * R := by
    intro j
    ring
  simp_rw [heq]
  simp

theorem volume_inputSupport_lt_top (R : ℝ) (z : Space m) :
    volume (inputSupport R z) < ⊤ := by
  rw [volume_inputSupport]
  finiteness

theorem real_volume_inputSupport (R : ℝ) (z : Space m) (hR : 0 ≤ R) :
    volume.real (inputSupport R z) = (2 * R) ^ (m + 1) := by
  rw [Measure.real, volume_inputSupport, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]

theorem isCompact_inputSupport (R : ℝ) (z : Space m) : IsCompact (inputSupport R z) := by
  rw [inputSupport_eq_preimage_cube]
  exact (PiLp.homeomorph 2 (fun _ : Fin (m + 1) => ℝ)).isCompact_preimage.2 (isCompact_inputCube R z)

theorem measurableSet_inputSupport (R : ℝ) (z : Space m) : MeasurableSet (inputSupport R z) :=
  (isCompact_inputSupport R z).isClosed.measurableSet

/-- A pointwise amplitude bound and the fixed support box give a uniform `L¹` bound. -/
theorem integral_norm_le_boxVolume (R M : ℝ) (z : Space m) (hR : 0 ≤ R)
    {f : Space (m + 1) → ℂ} (hsupport : tsupport f ⊆ inputSupport R z)
    (hM : ∀ v, ‖f v‖ ≤ M) :
    (∫ v, ‖f v‖) ≤ M * (2 * R) ^ (m + 1) := by
  have heq : (∫ v, ‖f v‖) = ∫ v in inputSupport R z, ‖f v‖ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    rw [image_eq_zero_of_notMem_tsupport (fun hf => hv (hsupport hf)), norm_zero]
  rw [heq]
  have h := norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (Space (m + 1))))
    (s := inputSupport R z) (f := fun v => ‖f v‖) (C := M)
    (volume_inputSupport_lt_top R z) (fun v _ => by simpa using hM v)
  rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _),
    real_volume_inputSupport R z hR] at h
  exact h

end StrongSpherical.AmplitudeBounds


namespace StrongSpherical.AmplitudeBounds

open ProductOscillation QuadraticGraph JointOscillation
variable {m k : ℕ}

/-- Closedness of the fixed box upgrades the paper's support condition to topological support. -/
theorem tsupport_subset_inputSupport (R : ℝ) (z : Space m) {a : Space (m + 1) → ℂ}
    (hsupport : Function.support a ⊆ inputSupport R z) : tsupport a ⊆ inputSupport R z :=
  closure_minimal hsupport (isCompact_inputSupport R z).isClosed

theorem hasCompactSupport_of_inputSupport (R : ℝ) (z : Space m) {a : Space (m + 1) → ℂ}
    (hsupport : tsupport a ⊆ inputSupport R z) : HasCompactSupport a :=
  (isCompact_inputSupport R z).of_isClosed_subset (isClosed_tsupport _) hsupport

/-- Leibniz and conjugation estimates for the actual amplitude product in the Gram kernel. -/
theorem inputDerivativeBound_pairAmplitude (M : ℝ) (hM : 0 ≤ M)
    (a : Space m → Space (m + 1) → ℂ) (x z : Space m)
    (hax : ContDiff ℝ k (a x)) (haz : ContDiff ℝ k (a z))
    (hDax : InputDerivativeBound k M (a x)) (hDaz : InputDerivativeBound k M (a z)) :
    InputDerivativeBound k ((2 : ℝ) ^ k * M ^ 2) (pairAmplitude a x z) := by
  have hc : ContDiff ℝ k (fun v => conj (a z v)) := Complex.conjCLE.contDiff.comp haz
  change InputDerivativeBound k ((2 : ℝ) ^ k * M ^ 2) (fun v => a x v * conj (a z v))
  simpa only [pow_two, mul_assoc] using inputDerivativeBound_mul M M hM hM
    hax hc hDax (inputDerivativeBound_conj hDaz)

/-- An explicit constant depending only on the dimension, support radius and input derivative bound. -/
def pairSeminormConstant (m : ℕ) (R M : ℝ) : ℝ :=
  2 * (2 * R) ^ (m + 1) * (2 : ℝ) ^ (m + 2) * M ^ 2

theorem pairSeminormConstant_nonneg (m : ℕ) (R M : ℝ) (hR : 0 ≤ R) :
    0 ≤ pairSeminormConstant m R M := by
  unfold pairSeminormConstant
  positivity

/-- The amplitude seminorm left explicit in JointOscillation is uniformly controlled
from pointwise input derivative bounds and the fixed support box. -/
theorem amplitudeSeminorm_pair_le (R M : ℝ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (a : Space m → Space (m + 1) → ℂ) (x z : Space m)
    (hax : ContDiff ℝ (m + 2 : ℕ) (a x)) (haz : ContDiff ℝ (m + 2 : ℕ) (a z))
    (hDax : InputDerivativeBound (m + 2) M (a x))
    (hDaz : InputDerivativeBound (m + 2) M (a z))
    (hsupport : Function.support (a z) ⊆ inputSupport R z) :
    amplitudeSeminorm (pairAmplitude a x z) ≤ pairSeminormConstant m R M := by
  let C := (2 : ℝ) ^ (m + 2) * M ^ 2
  have hpair := inputDerivativeBound_pairAmplitude M hM a x z hax haz hDax hDaz
  have htsz := tsupport_subset_inputSupport R z hsupport
  have hts : tsupport (pairAmplitude a x z) ⊆ inputSupport R z :=
    (tsupport_pairAmplitude_subset_right a x z).trans htsz
  have hts0 : tsupport (spatialDerivatives (pairAmplitude a x z)) ⊆ inputSupport R z :=
    (tsupport_mixedDerivative_subset _ (pairAmplitude a x z)).trans hts
  have hts2 : tsupport (coordinateDerivative (Fin.last m)
      (coordinateDerivative (Fin.last m) (spatialDerivatives (pairAmplitude a x z)))) ⊆
        inputSupport R z :=
    (tsupport_partial_subset _ _).trans ((tsupport_partial_subset _ _).trans hts0)
  have h0 : (∫ v, ‖spatialDerivatives (pairAmplitude a x z) v‖) ≤ C * (2 * R) ^ (m + 1) :=
    integral_norm_le_boxVolume R C z hR hts0
      (fun v => hpair (spatialDerivativeList m) (by simp) v)
  have h2 : (∫ v, ‖coordinateDerivative (Fin.last m)
      (coordinateDerivative (Fin.last m) (spatialDerivatives (pairAmplitude a x z))) v‖) ≤
        C * (2 * R) ^ (m + 1) := by
    apply integral_norm_le_boxVolume R C z hR hts2
    intro v
    simpa only [mixedDerivative_append, mixedDerivative, spatialDerivatives] using
      hpair (spatialDerivativeList m ++ [Fin.last m, Fin.last m]) (by simp) v
  unfold amplitudeSeminorm
  calc
    _ ≤ C * (2 * R) ^ (m + 1) + C * (2 * R) ^ (m + 1) := add_le_add h0 h2
    _ = _ := by dsimp [C, pairSeminormConstant]; ring

/-- The joint input-integral form of (3.19), now with a uniform amplitude constant.
The input regularity and derivative order are the `m+4` hypotheses of the paper. -/
theorem norm_integral_pairAmplitude_le_uniform
    (R c0 bmin M : ℝ) (hR : 1 ≤ R) (hc0 : 0 < c0) (hbmin : 0 < bmin) (hM : 0 ≤ M)
    (coeff : GraphCoefficients m) (lambda tau sigma : ℝ) (x z : Space m)
    (hlambda : 1 ≤ lambda) (htau : c0 * lambda ≤ |tau|)
    (hb : ∀ i, bmin ≤ coeff.quadratic x i)
    (a : Space m → Space (m + 1) → ℂ)
    (hax : ContDiff ℝ (m + 4 : ℕ) (a x)) (haz : ContDiff ℝ (m + 4 : ℕ) (a z))
    (hDax : InputDerivativeBound (m + 4) M (a x))
    (hDaz : InputDerivativeBound (m + 4) M (a z))
    (hsupport : Function.support (a z) ⊆ inputSupport R z) :
    ‖∫ v, oscillation (tau * graphGap coeff x v - sigma * graphGap coeff z v) *
        pairAmplitude a x z v‖ ≤
      4 * Quadratic1D.oscillationConstant R (c0 * bmin) ^ m * pairSeminormConstant m R M *
        frequencyDecay (tau - sigma) * ∏ i, spatialDecay lambda (x i - z i) := by
  have hx : ContDiff ℝ (m + 2 : ℕ) (a x) := hax.of_le (by norm_cast; omega)
  have hz : ContDiff ℝ (m + 2 : ℕ) (a z) := haz.of_le (by norm_cast; omega)
  have hS := amplitudeSeminorm_pair_le R M (by linarith) hM a x z hx hz
    (inputDerivativeBound_mono (by omega : m + 2 ≤ m + 4) hDax)
    (inputDerivativeBound_mono (by omega : m + 2 ≤ m + 4) hDaz) hsupport
  have htsz := tsupport_subset_inputSupport R z hsupport
  have hK := Quadratic1D.oscillationConstant_pos hR (mul_pos hc0 hbmin)
  calc
    _ ≤ 4 * Quadratic1D.oscillationConstant R (c0 * bmin) ^ m *
        amplitudeSeminorm (pairAmplitude a x z) * frequencyDecay (tau - sigma) *
          ∏ i, spatialDecay lambda (x i - z i) :=
      norm_integral_pairAmplitude_le R c0 bmin hR hc0 hbmin coeff lambda tau sigma x z
        hlambda htau hb a hx hz (hasCompactSupport_of_inputSupport R z htsz) htsz
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _
        (Finset.prod_nonneg fun i _ => spatialDecay_nonneg _ _ (by linarith))
      apply mul_le_mul_of_nonneg_right _ (frequencyDecay_nonneg _)
      exact mul_le_mul_of_nonneg_left hS (mul_nonneg (by norm_num) (pow_nonneg hK.le m))

/-- A single positive constant works before choosing the output-dependent coefficients,
amplitude family, phase parameters, and output points. No oscillatory bound is assumed. -/
theorem exists_uniform_pair_oscillation_bound (m : ℕ) (R c0 bmin M : ℝ)
    (hR : 1 ≤ R) (hc0 : 0 < c0) (hbmin : 0 < bmin) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (coeff : GraphCoefficients m) (a : Space m → Space (m + 1) → ℂ),
        (∀ y, ContDiff ℝ (m + 4 : ℕ) (a y)) →
        (∀ y, InputDerivativeBound (m + 4) M (a y)) →
        (∀ y, Function.support (a y) ⊆ inputSupport R y) →
        ∀ (lambda tau sigma : ℝ) (x z : Space m),
          1 ≤ lambda → c0 * lambda ≤ |tau| → (∀ i, bmin ≤ coeff.quadratic x i) →
          ‖∫ v, oscillation (tau * graphGap coeff x v - sigma * graphGap coeff z v) *
              pairAmplitude a x z v‖ ≤
            C * frequencyDecay (tau - sigma) * ∏ i, spatialDecay lambda (x i - z i) := by
  let K := Quadratic1D.oscillationConstant R (c0 * bmin)
  let B := pairSeminormConstant m R M
  have hK : 0 < K := Quadratic1D.oscillationConstant_pos hR (mul_pos hc0 hbmin)
  have hB : 0 ≤ B := pairSeminormConstant_nonneg m R M (by linarith)
  refine ⟨4 * K ^ m * (B + 1), mul_pos (mul_pos (by norm_num) (pow_pos hK m)) (by linarith), ?_⟩
  intro coeff a ha hDa hsupport lambda tau sigma x z hlambda htau hb
  calc
    _ ≤ 4 * K ^ m * B * frequencyDecay (tau - sigma) *
        ∏ i, spatialDecay lambda (x i - z i) :=
      norm_integral_pairAmplitude_le_uniform R c0 bmin M hR hc0 hbmin hM
        coeff lambda tau sigma x z hlambda htau hb a (ha x) (ha z) (hDa x) (hDa z) (hsupport z)
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _
        (Finset.prod_nonneg fun i _ => spatialDecay_nonneg _ _ (by linarith))
      apply mul_le_mul_of_nonneg_right _ (frequencyDecay_nonneg _)
      exact mul_le_mul_of_nonneg_left (by linarith : B ≤ B + 1)
        (mul_nonneg (by norm_num) (pow_nonneg hK.le m))

end StrongSpherical.AmplitudeBounds
