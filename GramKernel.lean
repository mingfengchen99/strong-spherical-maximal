import AmplitudeBounds

/-!
# The actual Gram kernel and its frequency expansion

We prove absolute integrability before exchanging the input variable with
the pair of frequency variables. The Gram kernel is the integral of the
original input kernels from QuadraticGraph, rather than a newly defined
frequency expression. The final target of this module is (3.21) of
arXiv:2609.32421v2.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace StrongSpherical.GramKernel

open ProductOscillation QuadraticGraph JointOscillation AmplitudeBounds
variable {m : ℕ}

/-- Lebesgue product measure for the two real frequency variables. -/
abbrev frequencyMeasure : Measure (ℝ × ℝ) := (volume : Measure ℝ).prod volume

/-- The two measurable frequency amplitudes in the Gram expansion. -/
def frequencyPair (q : Space m → ℝ → ℂ) (x z : Space m) (p : ℝ × ℝ) : ℂ :=
  q x p.1 * conj (q z p.2)

/-- The oscillatory input integral whose uniform bound was proved in AmplitudeBounds. -/
def pairIntegral (b : GraphCoefficients m) (a : Space m → Space (m + 1) → ℂ)
    (x z : Space m) (tau sigma : ℝ) : ℂ :=
  ∫ v, oscillation (tau * graphGap b x v - sigma * graphGap b z v) * pairAmplitude a x z v

/-- Joint integrand on input space times the frequency plane. -/
def gramIntegrand (b : GraphCoefficients m) (a : Space m → Space (m + 1) → ℂ)
    (q : Space m → ℝ → ℂ) (x z : Space m) (w : Space (m + 1) × (ℝ × ℝ)) : ℂ :=
  frequencyPair q x z w.2 *
    oscillation (w.2.1 * graphGap b x w.1 - w.2.2 * graphGap b z w.1) * pairAmplitude a x z w.1

theorem oscillation_mul_conj (s t : ℝ) :
    oscillation s * conj (oscillation t) = oscillation (s - t) := by
  rw [conj_oscillation, ← oscillation_add]
  rfl

theorem integrable_pairAmplitude (a : Space m → Space (m + 1) → ℂ) (x z : Space m)
    (hax : Continuous (a x)) (haz : Continuous (a z)) (hcompact : HasCompactSupport (a z)) :
    Integrable (pairAmplitude a x z) :=
  (hax.mul haz.star).integrable_of_hasCompactSupport (hasCompactSupport_pairAmplitude a x z hcompact)

/-- The majorant is the product of the integrable amplitude norm and the two
integrable frequency norms. This justifies the ensuing Fubini step. -/
theorem integrable_gramIntegrand (b : GraphCoefficients m)
    (a : Space m → Space (m + 1) → ℂ) (q : Space m → ℝ → ℂ) (x z : Space m)
    (hax : Continuous (a x)) (haz : Continuous (a z)) (hcompact : HasCompactSupport (a z))
    (hqx : Integrable (q x)) (hqz : Integrable (q z)) :
    Integrable (gramIntegrand b a q x z)
      ((volume : Measure (Space (m + 1))).prod
        ((volume : Measure ℝ).prod (volume : Measure ℝ))) := by
  have hA := integrable_pairAmplitude a x z hax haz hcompact
  have hQ : Integrable (fun p : ℝ × ℝ => ‖q x p.1‖ * ‖q z p.2‖)
      ((volume : Measure ℝ).prod volume) := hqx.norm.mul_prod hqz.norm
  have hmajor := hA.norm.mul_prod hQ
  have hqmeas : AEStronglyMeasurable (frequencyPair q x z)
      ((volume : Measure ℝ).prod volume) :=
    hqx.aestronglyMeasurable.comp_fst.mul hqz.aestronglyMeasurable.comp_snd.star
  have hchar : Continuous (fun w : Space (m + 1) × (ℝ × ℝ) =>
      oscillation (w.2.1 * graphGap b x w.1 - w.2.2 * graphGap b z w.1)) := by
    apply continuous_oscillation.comp
    exact (continuous_snd.fst.mul ((continuous_graphGap b x).comp continuous_fst)).sub
      (continuous_snd.snd.mul ((continuous_graphGap b z).comp continuous_fst))
  apply hmajor.mono'
    ((hqmeas.comp_snd.mul hchar.aestronglyMeasurable).mul hA.aestronglyMeasurable.comp_fst)
  apply Filter.Eventually.of_forall
  intro w
  change ‖gramIntegrand b a q x z w‖ ≤
    ‖pairAmplitude a x z w.1‖ * (‖q x w.2.1‖ * ‖q z w.2.2‖)
  simp only [gramIntegrand, frequencyPair, norm_mul, Complex.norm_conj, norm_oscillation, mul_one]
  exact le_of_eq (by ring)

/-- Expand the product of the two original frequency kernels at a fixed input point. -/
theorem inputKernel_mul_conj_eq_frequencyIntegral (b : GraphCoefficients m)
    (a : Space m → Space (m + 1) → ℂ) (q : Space m → ℝ → ℂ)
    (x z : Space m) (v : Space (m + 1)) :
    inputKernel b a q x v * conj (inputKernel b a q z v) =
      ∫ p : ℝ × ℝ, gramIntegrand b a q x z (v, p) ∂frequencyMeasure := by
  have hprod : frequencyKernel b q x v * conj (frequencyKernel b q z v) =
      ∫ p : ℝ × ℝ, (q x p.1 * oscillation (p.1 * graphGap b x v)) *
        conj (q z p.2 * oscillation (p.2 * graphGap b z v)) ∂frequencyMeasure := by
    unfold frequencyKernel
    rw [← integral_conj, ← integral_prod_mul]
  calc
    _ = (frequencyKernel b q x v * conj (frequencyKernel b q z v)) * pairAmplitude a x z v := by
      simp only [inputKernel, pairAmplitude, map_mul]
      ring
    _ = ∫ p : ℝ × ℝ, ((q x p.1 * oscillation (p.1 * graphGap b x v)) *
        conj (q z p.2 * oscillation (p.2 * graphGap b z v))) * pairAmplitude a x z v ∂frequencyMeasure := by
      rw [hprod, integral_mul_const]
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro p
      simp only [gramIntegrand, frequencyPair, map_mul]
      calc
        _ = (q x p.1 * conj (q z p.2)) *
            (oscillation (p.1 * graphGap b x v) * conj (oscillation (p.2 * graphGap b z v))) *
              pairAmplitude a x z v := by ring
        _ = _ := by rw [oscillation_mul_conj]

/-- Integrate out the input variable after the absolute-integrability argument. -/
theorem integral_gramIntegrand_input (b : GraphCoefficients m)
    (a : Space m → Space (m + 1) → ℂ) (q : Space m → ℝ → ℂ)
    (x z : Space m) (p : ℝ × ℝ) :
    (∫ v, gramIntegrand b a q x z (v, p)) = frequencyPair q x z p * pairIntegral b a x z p.1 p.2 := by
  unfold gramIntegrand pairIntegral
  simp only [mul_assoc]
  exact integral_const_mul _ _

theorem integrable_frequencyPair_mul_pairIntegral (b : GraphCoefficients m)
    (a : Space m → Space (m + 1) → ℂ) (q : Space m → ℝ → ℂ) (x z : Space m)
    (hax : Continuous (a x)) (haz : Continuous (a z)) (hcompact : HasCompactSupport (a z))
    (hqx : Integrable (q x)) (hqz : Integrable (q z)) :
    Integrable (fun p : ℝ × ℝ => frequencyPair q x z p * pairIntegral b a x z p.1 p.2)
      ((volume : Measure ℝ).prod volume) := by
  have h := (integrable_gramIntegrand b a q x z hax haz hcompact hqx hqz).integral_prod_right
  simpa only [integral_gramIntegrand_input] using h

/-- Fubini for the actual Gram kernel, with all required integrability proved above. -/
theorem gramKernel_eq_frequencyIntegral (b : GraphCoefficients m)
    (a : Space m → Space (m + 1) → ℂ) (q : Space m → ℝ → ℂ) (x z : Space m)
    (hax : Continuous (a x)) (haz : Continuous (a z)) (hcompact : HasCompactSupport (a z))
    (hqx : Integrable (q x)) (hqz : Integrable (q z)) :
    gramKernel b a q x z =
      ∫ p : ℝ × ℝ, frequencyPair q x z p * pairIntegral b a x z p.1 p.2 ∂frequencyMeasure := by
  unfold gramKernel
  simp_rw [inputKernel_mul_conj_eq_frequencyIntegral]
  rw [integral_integral_swap
    (f := fun v p => gramIntegrand b a q x z (v, p))
    (integrable_gramIntegrand b a q x z hax haz hcompact hqx hqz)]
  simp_rw [integral_gramIntegrand_input]

/-- The double-frequency expansion corresponding to (3.15), using the joint input integral. -/
theorem gramKernel_eq_double_frequencyIntegral (b : GraphCoefficients m)
    (a : Space m → Space (m + 1) → ℂ) (q : Space m → ℝ → ℂ) (x z : Space m)
    (hax : Continuous (a x)) (haz : Continuous (a z)) (hcompact : HasCompactSupport (a z))
    (hqx : Integrable (q x)) (hqz : Integrable (q z)) :
    gramKernel b a q x z = ∫ tau, ∫ sigma,
      q x tau * conj (q z sigma) * pairIntegral b a x z tau sigma := by
  rw [gramKernel_eq_frequencyIntegral b a q x z hax haz hcompact hqx hqz]
  exact integral_prod _ (integrable_frequencyPair_mul_pairIntegral b a q x z hax haz hcompact hqx hqz)

end StrongSpherical.GramKernel

namespace StrongSpherical.GramKernel
open ProductOscillation QuadraticGraph JointOscillation AmplitudeBounds
variable {m : ℕ}

/-- The normal-frequency band in (3.11). -/
def frequencyAnnulus (c0 C0 lambda : ℝ) : Set ℝ :=
  {tau | c0 * lambda ≤ |tau| ∧ |tau| ≤ C0 * lambda}

/-- Measurability, the uniform size bound, and the support band of one frequency amplitude. -/
structure FrequencyControl (c0 C0 lambda : ℝ) (q : ℝ → ℂ) : Prop where
  measurable : Measurable q
  norm_le : ∀ tau, ‖q tau‖ ≤ C0
  support_subset : Function.support q ⊆ frequencyAnnulus c0 C0 lambda

theorem frequencyControl_of_indicator_bound (c0 C0 lambda : ℝ) (hC0 : 0 ≤ C0)
    (q : ℝ → ℂ) (hq : Measurable q)
    (hbound : ∀ tau, ‖q tau‖ ≤ C0 * (frequencyAnnulus c0 C0 lambda).indicator (fun _ => 1) tau) :
    FrequencyControl c0 C0 lambda q := by
  refine ⟨hq, ?_, ?_⟩
  · intro tau
    by_cases ht : tau ∈ frequencyAnnulus c0 C0 lambda
    · simpa only [indicator_of_mem ht, mul_one] using hbound tau
    · have hzero : ‖q tau‖ ≤ 0 := by
        simpa only [indicator_of_notMem ht, mul_zero] using hbound tau
      exact hzero.trans hC0
  · intro tau hneq
    by_contra ht
    have hzero : ‖q tau‖ ≤ 0 := by
      simpa only [indicator_of_notMem ht, mul_zero] using hbound tau
    exact hneq (norm_le_zero_iff.mp hzero)

theorem FrequencyControl.support_subset_interval {c0 C0 lambda : ℝ} {q : ℝ → ℂ}
    (hq : FrequencyControl c0 C0 lambda q) :
    Function.support q ⊆ Icc (-C0 * lambda) (C0 * lambda) := by
  intro tau ht
  have h := abs_le.mp (hq.support_subset ht).2
  constructor <;> linarith [h.1, h.2]

theorem FrequencyControl.eq_zero_of_not_mem_interval {c0 C0 lambda : ℝ} {q : ℝ → ℂ}
    (hq : FrequencyControl c0 C0 lambda q) {tau : ℝ}
    (ht : tau ∉ Icc (-C0 * lambda) (C0 * lambda)) : q tau = 0 := by
  by_contra hneq
  exact ht (hq.support_subset_interval hneq)

/-- The bounded frequency band makes each measurable frequency amplitude integrable. -/
theorem FrequencyControl.integrable {c0 C0 lambda : ℝ} {q : ℝ → ℂ}
    (hq : FrequencyControl c0 C0 lambda q) : Integrable q := by
  have hmajor : Integrable ((Icc (-C0 * lambda) (C0 * lambda)).indicator (fun _ : ℝ => C0)) :=
    (integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp))
  apply hmajor.mono' hq.measurable.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro tau
  by_cases ht : tau ∈ Icc (-C0 * lambda) (C0 * lambda)
  · simpa only [indicator_of_mem ht] using hq.norm_le tau
  · simp only [indicator_of_notMem ht, hq.eq_zero_of_not_mem_interval ht, norm_zero, le_refl]

/-- The original joint measurability hypothesis supplies every frequency fiber. -/
theorem frequencyControl_of_joint_bound (c0 C0 lambda : ℝ) (hC0 : 0 ≤ C0)
    (q : Space m → ℝ → ℂ) (hq : Measurable (fun p : Space m × ℝ => q p.1 p.2))
    (hbound : ∀ x tau, ‖q x tau‖ ≤
      C0 * (frequencyAnnulus c0 C0 lambda).indicator (fun _ => 1) tau) :
    ∀ x, FrequencyControl c0 C0 lambda (q x) := by
  intro x
  exact frequencyControl_of_indicator_bound c0 C0 lambda hC0 (q x)
    (hq.comp (measurable_const.prodMk measurable_id)) (hbound x)

/-- Compact rectangle containing both frequency supports. -/
def frequencyRectangle (C0 lambda : ℝ) : Set (ℝ × ℝ) :=
  Icc (-C0 * lambda) (C0 * lambda) ×ˢ Icc (-C0 * lambda) (C0 * lambda)

theorem integrableOn_frequencyDifference (C0 lambda : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => frequencyDecay (p.1 - p.2))
      (frequencyRectangle C0 lambda) ((volume : Measure ℝ).prod volume) :=
  (continuous_frequencyDecay.comp (continuous_fst.sub continuous_snd)).continuousOn.integrableOn_compact
    (isCompact_Icc.prod isCompact_Icc)

/-- Product-space form of the already-proved double-frequency estimate (3.20). -/
theorem integral_frequencyDifference_le (C0 lambda : ℝ) (hC0 : 0 ≤ C0) (hlambda : 0 ≤ lambda) :
    (∫ p in frequencyRectangle C0 lambda, frequencyDecay (p.1 - p.2)
      ∂((volume : Measure ℝ).prod volume)) ≤ 2 * C0 * frequencyMass * lambda := by
  unfold frequencyRectangle
  rw [setIntegral_prod _ (integrableOn_frequencyDifference C0 lambda)]
  exact double_frequency_integral_le C0 lambda hC0 hlambda

end StrongSpherical.GramKernel


namespace StrongSpherical.GramKernel

open ProductOscillation QuadraticGraph JointOscillation AmplitudeBounds
variable {m : ℕ}

/-- Convert the proved input oscillation bound into a bound for the actual Gram kernel.
The only loss from the two frequency integrations is one power of `lambda`. -/
theorem norm_gramKernel_le_of_pair_bound
    (c0 C0 lambda L D : ℝ) (hC0 : 0 ≤ C0) (hlambda : 0 ≤ lambda) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (b : GraphCoefficients m) (a : Space m → Space (m + 1) → ℂ)
    (q : Space m → ℝ → ℂ) (x z : Space m)
    (hax : Continuous (a x)) (haz : Continuous (a z)) (hcompact : HasCompactSupport (a z))
    (hqx : FrequencyControl c0 C0 lambda (q x)) (hqz : FrequencyControl c0 C0 lambda (q z))
    (hpair : ∀ tau sigma, c0 * lambda ≤ |tau| →
      ‖pairIntegral b a x z tau sigma‖ ≤ L * frequencyDecay (tau - sigma) * D) :
    ‖gramKernel b a q x z‖ ≤ (2 * C0 ^ 3 * frequencyMass * L) * lambda * D := by
  let F := fun p : ℝ × ℝ => frequencyPair q x z p * pairIntegral b a x z p.1 p.2
  let A := C0 ^ 2 * L * D
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hzero : ∀ p ∉ frequencyRectangle C0 lambda, F p = 0 := by
    intro p hp
    by_cases hx : p.1 ∈ Icc (-C0 * lambda) (C0 * lambda)
    · have hz : p.2 ∉ Icc (-C0 * lambda) (C0 * lambda) := fun hz => hp ⟨hx, hz⟩
      simp only [F, frequencyPair, hqz.eq_zero_of_not_mem_interval hz, map_zero, mul_zero, zero_mul]
    · simp only [F, frequencyPair, hqx.eq_zero_of_not_mem_interval hx, zero_mul]
  have hrestrict : (∫ p, F p ∂frequencyMeasure) =
      ∫ p in frequencyRectangle C0 lambda, F p ∂frequencyMeasure :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm
  have hbound : ∀ p, ‖F p‖ ≤ A * frequencyDecay (p.1 - p.2) := by
    intro p
    by_cases hx : q x p.1 = 0
    · simp only [F, frequencyPair, hx, zero_mul, norm_zero]
      exact mul_nonneg hA (frequencyDecay_nonneg _)
    by_cases hz : q z p.2 = 0
    · simp only [F, frequencyPair, hz, map_zero, mul_zero, zero_mul, norm_zero]
      exact mul_nonneg hA (frequencyDecay_nonneg _)
    have hQ : ‖frequencyPair q x z p‖ ≤ C0 ^ 2 := by
      rw [frequencyPair, norm_mul, Complex.norm_conj, pow_two]
      exact mul_le_mul (hqx.norm_le _) (hqz.norm_le _) (norm_nonneg _) hC0
    have hJ := hpair p.1 p.2 (hqx.support_subset hx).1
    calc
      _ = ‖frequencyPair q x z p‖ * ‖pairIntegral b a x z p.1 p.2‖ := norm_mul _ _
      _ ≤ C0 ^ 2 * (L * frequencyDecay (p.1 - p.2) * D) :=
        mul_le_mul hQ hJ (norm_nonneg _) (sq_nonneg C0)
      _ = _ := by dsimp [A]; ring
  rw [gramKernel_eq_frequencyIntegral b a q x z hax haz hcompact hqx.integrable hqz.integrable]
  rw [hrestrict]
  calc
    _ ≤ ∫ p in frequencyRectangle C0 lambda, A * frequencyDecay (p.1 - p.2) ∂frequencyMeasure :=
      norm_integral_le_of_norm_le ((integrableOn_frequencyDifference C0 lambda).const_mul A)
        (Filter.Eventually.of_forall hbound)
    _ = A * ∫ p in frequencyRectangle C0 lambda, frequencyDecay (p.1 - p.2) ∂frequencyMeasure :=
      integral_const_mul _ _
    _ ≤ A * (2 * C0 * frequencyMass * lambda) :=
      mul_le_mul_of_nonneg_left (integral_frequencyDifference_le C0 lambda hC0 hlambda) hA
    _ = _ := by dsimp [A]; ring

/-- Equation (3.21) for the actual Gram kernel, with one constant chosen before the
frequency scale, coefficient functions, amplitude family, and frequency amplitudes.
The cutoff is the already-defined product profile on the box `|x-z|∞ ≤ 2R`. -/
theorem exists_uniform_gramKernel_bound (m : ℕ) (R c0 C0 bmin M : ℝ)
    (hR : 1 ≤ R) (hc0 : 0 < c0) (hC0 : 0 < C0) (hbmin : 0 < bmin) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (lambda : ℝ), 1 ≤ lambda →
      ∀ (b : GraphCoefficients m) (a : Space m → Space (m + 1) → ℂ) (q : Space m → ℝ → ℂ),
        (∀ y, ContDiff ℝ (m + 4 : ℕ) (a y)) →
        (∀ y, InputDerivativeBound (m + 4) M (a y)) →
        (∀ y, Function.support (a y) ⊆ inputSupport R y) →
        Measurable (fun p : Space m × ℝ => q p.1 p.2) →
        (∀ y tau, ‖q y tau‖ ≤
          C0 * (frequencyAnnulus c0 C0 lambda).indicator (fun _ => 1) tau) →
        (∀ y i, bmin ≤ b.quadratic y i) →
        ∀ x z, ‖gramKernel b a q x z‖ ≤ C * lambda * spatialProfile lambda (2 * R) x z := by
  obtain ⟨L, hL, hpair⟩ := exists_uniform_pair_oscillation_bound m R c0 bmin M hR hc0 hbmin hM
  have hmass := frequencyMass_pos
  refine ⟨2 * C0 ^ 3 * frequencyMass * L, by positivity, ?_⟩
  intro lambda hlambda b a q ha hDa hsupport hq hqbound hb x z
  have hqc := frequencyControl_of_joint_bound c0 C0 lambda hC0.le q hq hqbound
  have htsz := tsupport_subset_inputSupport R z (hsupport z)
  have hcompact := hasCompactSupport_of_inputSupport R z htsz
  rw [spatialProfile_eq_cutoff]
  split_ifs with hbox
  · apply norm_gramKernel_le_of_pair_bound c0 C0 lambda L
      (∏ i, spatialDecay lambda (x i - z i)) hC0.le (by linarith) hL.le
      (Finset.prod_nonneg fun i _ => spatialDecay_nonneg _ _ (by linarith))
      b a q x z (ha x).continuous (ha z).continuous hcompact (hqc x) (hqc z)
    intro tau sigma htau
    exact hpair b a ha hDa hsupport lambda tau sigma x z hlambda htau (hb x)
  · obtain ⟨i, hi⟩ := not_forall.mp hbox
    rw [gramKernel_eq_zero_of_separated R b a q hsupport x z i (lt_of_not_ge hi)]
    simp

end StrongSpherical.GramKernel
