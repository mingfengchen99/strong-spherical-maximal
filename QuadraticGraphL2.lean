import KernelTTStar
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# The L² estimate for measurable quadratic graphs (Lemma 3.2)

Uniform support and size bounds first give a coarse global Schur bound for
the original kernel. This constructs the operator on the whole space before
the sharp Gram-kernel estimate is used to improve its norm.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal ComplexConjugate

namespace StrongSpherical.QuadraticGraphL2
open ProductOscillation QuadraticGraph GramKernel AmplitudeBounds SchurTest
variable {m : ℕ}

/-- The zero-frequency profile is the box indicator, with its exact volume. -/
theorem integral_spatialProfile_zero (R : ℝ) (hR : 0 ≤ R) (x : Space m) :
    (∫ z, spatialProfile 0 R x z) = (2 * R) ^ m := by
  rw [integral_spatialProfile]
  congr 1
  rw [localizedSpatialDecay, integral_indicator measurableSet_Icc]
  simp only [spatialDecay, zero_mul, add_zero, Real.one_rpow]
  rw [setIntegral_const]
  simp only [Measure.real, Real.volume_Icc, smul_eq_mul, mul_one]
  rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ R - -R)]
  ring

/-- Row mass of any uniformly bounded kernel with the original input support. -/
theorem lintegral_input_row_le (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (H : Space m → Space (m + 1) → ℂ)
    (hbound : ∀ x v, ‖H x v‖ ≤ B)
    (hsupport : ∀ x, Function.support (H x) ⊆ inputSupport R x) (x : Space m) :
    (∫⁻ v, ‖H x v‖ₑ) ≤ ENNReal.ofReal (B * (2 * R) ^ (m + 1)) := by
  calc
    _ ≤ ∫⁻ v, (inputSupport R x).indicator (fun _ => ENNReal.ofReal B) v := by
      apply lintegral_mono
      intro v
      by_cases hv : v ∈ inputSupport R x
      · rw [indicator_of_mem hv]
        change ‖H x v‖ₑ ≤ ENNReal.ofReal B
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal (hbound x v)
      · have hz : H x v = 0 := by
          by_contra hne
          exact hv (hsupport x hne)
        simp only [hz, enorm_zero, indicator_of_notMem hv, le_refl]
    _ = _ := by
      rw [lintegral_indicator (measurableSet_inputSupport R x), lintegral_const]
      simp only [Measure.restrict_apply_univ, volume_inputSupport]
      rw [ENNReal.ofReal_mul hB, ENNReal.ofReal_pow (by positivity)]

/-- The corresponding column is supported in a box in the output coordinates. -/
theorem norm_input_le_zeroProfile (R B : ℝ)
    (H : Space m → Space (m + 1) → ℂ)
    (hbound : ∀ x v, ‖H x v‖ ≤ B)
    (hsupport : ∀ x, Function.support (H x) ⊆ inputSupport R x)
    (x : Space m) (v : Space (m + 1)) :
    ‖H x v‖ ≤ B * spatialProfile 0 R (spatialInput v) x := by
  rw [spatialProfile_eq_cutoff]
  split_ifs with hbox
  · simpa only [spatialDecay, zero_mul, add_zero, Real.one_rpow, Finset.prod_const_one, mul_one]
      using hbound x v
  · have hz : H x v = 0 := by
      by_contra hne
      exact hbox (hsupport x hne).1
    simp only [hz, norm_zero, mul_zero, le_refl]

theorem lintegral_input_column_le (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (H : Space m → Space (m + 1) → ℂ)
    (hbound : ∀ x v, ‖H x v‖ ≤ B)
    (hsupport : ∀ x, Function.support (H x) ⊆ inputSupport R x) (v : Space (m + 1)) :
    (∫⁻ x, ‖H x v‖ₑ) ≤ ENNReal.ofReal (B * (2 * R) ^ m) := by
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (B * spatialProfile 0 R (spatialInput v) x) := by
      apply lintegral_mono
      intro x
      change ‖H x v‖ₑ ≤ ENNReal.ofReal (B * spatialProfile 0 R (spatialInput v) x)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (norm_input_le_zeroProfile R B H hbound hsupport x v)
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        ((integrable_spatialProfile 0 R (spatialInput v) le_rfl).const_mul B)
        (Filter.Eventually.of_forall fun x => mul_nonneg hB (spatialProfile_nonneg _ _ _ _ le_rfl)),
        integral_const_mul, integral_spatialProfile_zero R hR]

/-- Explicit L¹ bound following from the original frequency control. -/
theorem integral_norm_frequency_le {c0 C0 lambda : ℝ} {q : ℝ → ℂ}
    (hC0 : 0 ≤ C0) (hlambda : 0 ≤ lambda) (hq : FrequencyControl c0 C0 lambda q) :
    (∫ tau, ‖q tau‖) ≤ 2 * C0 ^ 2 * lambda := by
  have hrestrict : (∫ tau, ‖q tau‖) = ∫ tau in Icc (-C0 * lambda) (C0 * lambda), ‖q tau‖ := by
    symm
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro tau ht
    rw [hq.eq_zero_of_not_mem_interval ht, norm_zero]
  rw [hrestrict]
  calc
    _ ≤ ∫ _ in Icc (-C0 * lambda) (C0 * lambda), C0 :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
        (integrableOn_const (by simp)) (Filter.Eventually.of_forall hq.norm_le)
    _ = _ := by
      rw [setIntegral_const]
      simp only [Measure.real, Real.volume_Icc]
      rw [ENNReal.toReal_ofReal (by nlinarith [mul_nonneg hC0 hlambda])]
      simp only [smul_eq_mul]
      ring

theorem support_inputKernel_subset (R : ℝ) (b : GraphCoefficients m)
    (a : Space m → Space (m + 1) → ℂ) (q : Space m → ℝ → ℂ)
    (hs : ∀ x, Function.support (a x) ⊆ inputSupport R x) :
    ∀ x, Function.support (inputKernel b a q x) ⊆ inputSupport R x := by
  intro x v hv
  apply hs x
  intro ha
  exact hv (by simp only [inputKernel, ha, zero_mul])

theorem norm_inputKernel_le (C0 lambda M : ℝ) {c0 : ℝ}
    (hC0 : 0 ≤ C0) (hlambda : 0 ≤ lambda) (hM : 0 ≤ M)
    (b : GraphCoefficients m) (a : Space m → Space (m + 1) → ℂ) (q : Space m → ℝ → ℂ)
    (ha : ∀ x v, ‖a x v‖ ≤ M) (hq : ∀ x, FrequencyControl c0 C0 lambda (q x)) :
    ∀ x v, ‖inputKernel b a q x v‖ ≤ M * (2 * C0 ^ 2 * lambda) := by
  intro x v
  rw [inputKernel, norm_mul]
  exact mul_le_mul (ha x v)
    ((norm_frequencyKernel_le b q x v).trans (integral_norm_frequency_le hC0 hlambda (hq x)))
    (norm_nonneg _) hM

/-- Every row of the original kernel belongs to L². -/
theorem memLp_inputKernel (R : ℝ) (b : GraphCoefficients m)
    (a : Space m → Space (m + 1) → ℂ) (q : Space m → ℝ → ℂ)
    (ha : ∀ x, Continuous (a x))
    (hs : ∀ x, Function.support (a x) ⊆ inputSupport R x)
    (hq : ∀ x, Integrable (q x)) (x : Space m) :
    MemLp (inputKernel b a q x) 2 volume := by
  have hcompact := hasCompactSupport_of_inputSupport R x (tsupport_subset_inputSupport R x (hs x))
  exact ((ha x).mul (continuous_frequencyKernel b q x (hq x))).memLp_of_hasCompactSupport hcompact.mul_right

end StrongSpherical.QuadraticGraphL2

namespace StrongSpherical.QuadraticGraphL2
open QuadraticGraph GramKernel AmplitudeBounds SchurTest KernelTTStar
variable {m : ℕ}

/-- A coarse global bound suffices to construct the original operator. -/
def coarseBound (m : ℕ) (R B : ℝ) : ℝ := B * ((2 * R) ^ (m + 1) + (2 * R) ^ m)

theorem kernelControl_of_input_support (R B : ℝ) (hR : 0 ≤ R) (hB : 0 ≤ B)
    (H : Space m → Space (m + 1) → ℂ) (hH : Measurable (Function.uncurry H))
    (hbound : ∀ x v, ‖H x v‖ ≤ B)
    (hsupport : ∀ x, Function.support (H x) ⊆ inputSupport R x) :
    KernelControl (μ := volume) (ν := volume) H (coarseBound m R B) := by
  refine ⟨hH, by unfold coarseBound; positivity, ?_, ?_⟩
  · intro x
    apply (lintegral_input_row_le R B hR hB H hbound hsupport x).trans
    apply ENNReal.ofReal_le_ofReal
    unfold coarseBound
    nlinarith [mul_nonneg hB (pow_nonneg (by positivity : 0 ≤ 2 * R) m)]
  · intro v
    apply (lintegral_input_column_le R B hR hB H hbound hsupport v).trans
    apply ENNReal.ofReal_le_ofReal
    unfold coarseBound
    nlinarith [mul_nonneg hB (pow_nonneg (by positivity : 0 ≤ 2 * R) (m + 1))]

/-- Exact square-root conversion of the frequency power in the Gram estimate. -/
theorem sqrt_gram_scale (m : ℕ) (D lambda : ℝ) (hD : 0 ≤ D) (hlambda : 0 < lambda) :
    Real.sqrt (D * lambda ^ (1 - (m : ℝ) / 2)) =
      Real.sqrt D * lambda ^ (1 / 2 - (m : ℝ) / 4) := by
  have hpow : Real.sqrt (lambda ^ (1 - (m : ℝ) / 2)) = lambda ^ (1 / 2 - (m : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hlambda.le]
    congr 1
    ring
  rw [Real.sqrt_mul hD, hpow]

set_option maxHeartbeats 2000000 in
/-- Lemma 3.2 as an actual bounded operator, with the original integral action
and the TT* integral identity on the whole output space. -/
theorem exists_uniform_graphL2Operator (m : ℕ) (R c0 C0 bmin M : ℝ)
    (hR : 1 ≤ R) (hc0 : 0 < c0) (hC0 : 0 < C0) (hbmin : 0 < bmin) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (lambda : ℝ), 1 ≤ lambda →
      ∀ (b : GraphCoefficients m) (a : Space m → Space (m + 1) → ℂ) (q : Space m → ℝ → ℂ),
        (∀ y, ContDiff ℝ (m + 4 : ℕ) (a y)) →
        (∀ y, InputDerivativeBound (m + 4) M (a y)) →
        (∀ y, Function.support (a y) ⊆ inputSupport R y) →
        (∀ v, Measurable (fun y => a y v)) →
        Measurable (fun p : Space m × ℝ => q p.1 p.2) →
        (∀ y tau, ‖q y tau‖ ≤
          C0 * (frequencyAnnulus c0 C0 lambda).indicator (fun _ => 1) tau) →
        (∀ y i, bmin ≤ b.quadratic y i) →
        ∃ T : Lp ℂ 2 (volume : Measure (Space (m + 1))) →L[ℂ] Lp ℂ 2 (volume : Measure (Space m)),
          ‖T‖ ≤ C * lambda ^ (1 / 2 - (m : ℝ) / 4) ∧
          (∀ f, T f =ᵐ[volume] graphOperator b a q f) ∧
          ∀ f, (T ∘L T.adjoint) f =ᵐ[volume]
            kernelOperator (ν := volume) (QuadraticGraph.gramKernel b a q) f := by
  obtain ⟨D, hD, hGram⟩ := exists_uniform_gramL2Operator m R c0 C0 bmin M hR hc0 hC0 hbmin hM
  refine ⟨Real.sqrt D, Real.sqrt_pos.2 hD, ?_⟩
  intro lambda hlambda b a q ha hDa hs hameas hq hqbound hb
  obtain ⟨G, hGnorm, hGcoe⟩ := hGram lambda hlambda b a q ha hDa hs hameas hq hqbound hb
  have hqc := frequencyControl_of_joint_bound c0 C0 lambda hC0.le q hq hqbound
  have ha0 : ∀ x v, ‖a x v‖ ≤ M := fun x v => hDa x [] (by simp) v
  have hH := measurable_inputKernel b a q
    (measurable_amplitude_of_fibers a (fun x => (ha x).continuous) hameas) hq
  have hbound := norm_inputKernel_le C0 lambda M hC0.le (by linarith) hM b a q ha0 hqc
  have hsupport := support_inputKernel_subset R b a q hs
  have hcontrol := kernelControl_of_input_support R (M * (2 * C0 ^ 2 * lambda))
    (by linarith) (by positivity) (inputKernel b a q) hH hbound hsupport
  have hrows := memLp_inputKernel R b a q (fun x => (ha x).continuous) hs (fun x => (hqc x).integrable)
  have hG' : ∀ f, G f =ᵐ[volume]
      kernelOperator (ν := volume) (KernelTTStar.gram (ν := volume) (inputKernel b a q)) f := hGcoe
  have hTT := hcontrol.ttstar_eq hrows G hG'
  refine ⟨hcontrol.operator, ?_, ?_, ?_⟩
  · exact (hcontrol.norm_le_sqrt_of_gram hrows G hG' _ hGnorm).trans_eq
      (sqrt_gram_scale m D lambda hD.le (by linarith))
  · intro f
    exact hcontrol.operator_coe f
  · intro f
    rw [hTT]
    exact hGcoe f

/-- Lemma 3.2 / (3.13), for every square-integrable input function. The output
is the original graph integral, and membership in L² is part of the conclusion.
The constant is chosen uniformly before the scale and all coefficient choices. -/
theorem lemma_3_2 (m : ℕ) (R c0 C0 bmin M : ℝ)
    (hR : 1 ≤ R) (hc0 : 0 < c0) (hC0 : 0 < C0) (hbmin : 0 < bmin) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (lambda : ℝ), 1 ≤ lambda →
      ∀ (b : GraphCoefficients m) (a : Space m → Space (m + 1) → ℂ) (q : Space m → ℝ → ℂ),
        (∀ y, ContDiff ℝ (m + 4 : ℕ) (a y)) →
        (∀ y, InputDerivativeBound (m + 4) M (a y)) →
        (∀ y, Function.support (a y) ⊆ inputSupport R y) →
        (∀ v, Measurable (fun y => a y v)) →
        Measurable (fun p : Space m × ℝ => q p.1 p.2) →
        (∀ y tau, ‖q y tau‖ ≤
          C0 * (frequencyAnnulus c0 C0 lambda).indicator (fun _ => 1) tau) →
        (∀ y i, bmin ≤ b.quadratic y i) →
        ∀ g : Space (m + 1) → ℂ, MemLp g 2 volume →
          MemLp (graphOperator b a q g) 2 volume ∧
          eLpNorm (graphOperator b a q g) 2 volume ≤
            ENNReal.ofReal (C * lambda ^ (1 / 2 - (m : ℝ) / 4)) * eLpNorm g 2 volume := by
  obtain ⟨C, hC, hT⟩ := exists_uniform_graphL2Operator m R c0 C0 bmin M hR hc0 hC0 hbmin hM
  refine ⟨C, hC, ?_⟩
  intro lambda hlambda b a q ha hDa hs hameas hq hqbound hb g hg
  obtain ⟨T, hTnorm, hTcoe, _⟩ := hT lambda hlambda b a q ha hDa hs hameas hq hqbound hb
  let f := hg.toLp g
  have heq : T f =ᵐ[volume] graphOperator b a q g := by
    apply (hTcoe f).trans
    apply Filter.Eventually.of_forall
    intro x
    exact integral_congr_ae (hg.coeFn_toLp.mono fun v hv => congrArg (fun c => inputKernel b a q x v * c) hv)
  have hmem : MemLp (graphOperator b a q g) 2 volume := (memLp_congr_ae heq).mp (Lp.memLp (T f))
  have hscale : 0 ≤ C * lambda ^ (1 / 2 - (m : ℝ) / 4) := by positivity
  refine ⟨hmem, ?_⟩
  calc
    _ = ENNReal.ofReal ‖T f‖ := by rw [← eLpNorm_congr_ae heq, ← Lp.enorm_def, ofReal_norm]
    _ ≤ ENNReal.ofReal ((C * lambda ^ (1 / 2 - (m : ℝ) / 4)) * ‖f‖) :=
      ENNReal.ofReal_le_ofReal ((T.le_opNorm f).trans (mul_le_mul_of_nonneg_right hTnorm (norm_nonneg f)))
    _ = _ := by rw [ENNReal.ofReal_mul hscale, ofReal_norm, Lp.enorm_toLp hg]

end StrongSpherical.QuadraticGraphL2
