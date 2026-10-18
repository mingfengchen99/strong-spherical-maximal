import GramKernel
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# Schur's test for the quadratic-graph Gram kernel

The argument uses nonnegative integrals, so Tonelli applies before any
integrability conclusion. The resulting estimate controls the actual
integral operator on square-integrable functions.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal ComplexConjugate

namespace StrongSpherical.SchurTest

section Nonnegative

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

/-- Weighted Cauchy--Schwarz, including infinite nonnegative integrals. -/
theorem lintegral_weighted_sq_le (k f : β → ℝ≥0∞)
    (hk : Measurable k) (hf : Measurable f) :
    (∫⁻ z, k z * f z ∂ν) ^ 2 ≤
      (∫⁻ z, k z ∂ν) * ∫⁻ z, k z * f z ^ 2 ∂ν := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (ν.withDensity k)
    Real.HolderConjugate.two_two hf.aemeasurable
    (measurable_const.aemeasurable : AEMeasurable (fun _ : β => (1 : ℝ≥0∞)) _)
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  have hs := pow_le_pow_left' h 2
  rw [mul_pow] at hs
  simp only [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul] at hs
  norm_num at hs
  rw [lintegral_withDensity_eq_lintegral_mul ν hk hf,
    lintegral_withDensity_eq_lintegral_mul ν hk (hf.pow_const 2)] at hs
  simpa only [Pi.mul_apply, ENNReal.rpow_two, mul_comm] using hs

/-- Schur's test for a nonnegative kernel, in squared integral form. -/
theorem lintegral_schur_sq_le [SFinite μ] [SFinite ν]
    (k : α → β → ℝ≥0∞) (f : β → ℝ≥0∞) (A B : ℝ≥0∞)
    (hk : Measurable (Function.uncurry k)) (hf : Measurable f)
    (hrow : ∀ x, ∫⁻ z, k x z ∂ν ≤ A)
    (hcolumn : ∀ z, ∫⁻ x, k x z ∂μ ≤ B) :
    (∫⁻ x, (∫⁻ z, k x z * f z ∂ν) ^ 2 ∂μ) ≤
      A * B * ∫⁻ z, f z ^ 2 ∂ν := by
  have hmeas : Measurable (fun p : α × β => k p.1 p.2 * f p.2 ^ 2) :=
    hk.mul ((hf.comp measurable_snd).pow_const 2)
  calc
    _ ≤ ∫⁻ x, A * ∫⁻ z, k x z * f z ^ 2 ∂ν ∂μ := by
      apply lintegral_mono
      intro x
      exact (lintegral_weighted_sq_le (k x) f
        (hk.comp measurable_prodMk_left) hf).trans (mul_le_mul' (hrow x) le_rfl)
    _ = A * ∫⁻ x, ∫⁻ z, k x z * f z ^ 2 ∂ν ∂μ :=
      lintegral_const_mul _ hmeas.lintegral_prod_right
    _ = A * ∫⁻ z, ∫⁻ x, k x z * f z ^ 2 ∂μ ∂ν := by
      rw [lintegral_lintegral_swap hmeas.aemeasurable]
    _ ≤ A * ∫⁻ z, B * f z ^ 2 ∂ν := by
      gcongr with z
      rw [lintegral_mul_const _ (show Measurable (fun x => k x z) from
        hk.comp (measurable_id.prodMk measurable_const))]
      gcongr
      exact hcolumn z
    _ = _ := by
      rw [lintegral_const_mul _ (hf.pow_const 2), mul_assoc]

end Nonnegative

section ComplexKernel

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β}

/-- The actual Bochner integral operator associated to a complex kernel. -/
def kernelOperator (K : α → β → ℂ) (f : β → ℂ) (x : α) : ℂ :=
  ∫ z, K x z * f z ∂ν

theorem measurable_kernelOperator [SFinite ν]
    (K : α → β → ℂ) (f : β → ℂ)
    (hK : Measurable (Function.uncurry K)) (hf : Measurable f) :
    Measurable (kernelOperator (ν := ν) K f) :=
  (hK.mul (hf.comp measurable_snd)).stronglyMeasurable.integral_prod_right'.measurable

/-- Schur's squared L² estimate for the actual complex integral operator. -/
theorem lintegral_enorm_kernelOperator_sq_le [SFinite μ] [SFinite ν]
    (K : α → β → ℂ) (f : β → ℂ) (A B : ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hf : Measurable f)
    (hrow : ∀ x, ∫⁻ z, ‖K x z‖ₑ ∂ν ≤ A)
    (hcolumn : ∀ z, ∫⁻ x, ‖K x z‖ₑ ∂μ ≤ B) :
    (∫⁻ x, ‖kernelOperator (ν := ν) K f x‖ₑ ^ 2 ∂μ) ≤
      A * B * ∫⁻ z, ‖f z‖ₑ ^ 2 ∂ν := by
  calc
    _ ≤ ∫⁻ x, (∫⁻ z, ‖K x z‖ₑ * ‖f z‖ₑ ∂ν) ^ 2 ∂μ := by
      apply lintegral_mono
      intro x
      apply pow_le_pow_left'
      simpa only [kernelOperator, enorm_mul] using
        (enorm_integral_le_lintegral_enorm (μ := ν) (fun z => K x z * f z))
    _ ≤ _ := lintegral_schur_sq_le (fun x z => ‖K x z‖ₑ) (fun z => ‖f z‖ₑ)
      A B hK.enorm hf.enorm hrow hcolumn

/-- The squared extended L² norm is exactly the nonnegative square integral. -/
theorem eLpNorm_two_sq (f : β → ℂ) :
    eLpNorm f 2 ν ^ 2 = ∫⁻ z, ‖f z‖ₑ ^ 2 ∂ν := by
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] using
    (eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := ν) (p := (2 : ℝ≥0)) (by norm_num))

/-- Equal row and column bounds give the same constant as the L² norm bound. -/
theorem eLpNorm_kernelOperator_le [SFinite μ] [SFinite ν]
    (K : α → β → ℂ) (f : β → ℂ) (A : ℝ≥0∞)
    (hK : Measurable (Function.uncurry K)) (hf : Measurable f)
    (hrow : ∀ x, ∫⁻ z, ‖K x z‖ₑ ∂ν ≤ A)
    (hcolumn : ∀ z, ∫⁻ x, ‖K x z‖ₑ ∂μ ≤ A) :
    eLpNorm (kernelOperator (ν := ν) K f) 2 μ ≤ A * eLpNorm f 2 ν := by
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  simp only [ENNReal.rpow_two]
  rw [eLpNorm_two_sq, mul_pow, eLpNorm_two_sq]
  simpa only [pow_two, mul_assoc] using
    lintegral_enorm_kernelOperator_sq_le K f A A hK hf hrow hcolumn

/-- In particular, the actual integral operator maps L² functions into L². -/
theorem memLp_kernelOperator [SFinite μ] [SFinite ν]
    (K : α → β → ℂ) (f : β → ℂ) (A : ℝ)
    (hK : Measurable (Function.uncurry K)) (hf : Measurable f)
    (hrow : ∀ x, ∫⁻ z, ‖K x z‖ₑ ∂ν ≤ ENNReal.ofReal A)
    (hcolumn : ∀ z, ∫⁻ x, ‖K x z‖ₑ ∂μ ≤ ENNReal.ofReal A)
    (hfp : MemLp f 2 ν) : MemLp (kernelOperator (ν := ν) K f) 2 μ := by
  refine ⟨(measurable_kernelOperator K f hK hf).aestronglyMeasurable, ?_⟩
  exact (eLpNorm_kernelOperator_le K f (ENNReal.ofReal A) hK hf hrow hcolumn).trans_lt
    (ENNReal.mul_lt_top (by finiteness) hfp.2)

/-- The same bound on genuine L² equivalence classes, with a real constant. -/
theorem norm_toLp_kernelOperator_le [SFinite μ] [SFinite ν]
    (K : α → β → ℂ) (f : β → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hK : Measurable (Function.uncurry K)) (hf : Measurable f)
    (hrow : ∀ x, ∫⁻ z, ‖K x z‖ₑ ∂ν ≤ ENNReal.ofReal A)
    (hcolumn : ∀ z, ∫⁻ x, ‖K x z‖ₑ ∂μ ≤ ENNReal.ofReal A)
    (hfp : MemLp f 2 ν) :
    ‖(memLp_kernelOperator K f A hK hf hrow hcolumn hfp).toLp _‖ ≤ A * ‖hfp.toLp f‖ := by
  rw [Lp.norm_toLp, Lp.norm_toLp]
  calc
    _ ≤ (ENNReal.ofReal A * eLpNorm f 2 ν).toReal :=
      ENNReal.toReal_mono
        (ENNReal.mul_ne_top (by finiteness) hfp.eLpNorm_ne_top)
        (eLpNorm_kernelOperator_le K f (ENNReal.ofReal A) hK hf hrow hcolumn)
    _ = _ := by rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hA]

end ComplexKernel

end StrongSpherical.SchurTest

namespace StrongSpherical.SchurTest

open QuadraticGraph GramKernel AmplitudeBounds
variable {m : ℕ}

/-- Joint measurability of the phase follows from measurability of its coefficients. -/
theorem measurable_graphGap (b : GraphCoefficients m) :
    Measurable (fun p : Space m × Space (m + 1) => graphGap b p.1 p.2) := by
  have hnormal : Measurable (fun p : Space m × Space (m + 1) => normalInput p.2) := by
    unfold normalInput
    fun_prop
  apply hnormal.sub
  apply (b.measurable_constant.comp measurable_fst).sub
  apply Finset.measurable_sum
  intro i _
  apply ((b.measurable_quadratic i).comp measurable_fst).mul
  have hcoord : Continuous (fun p : Space m × Space (m + 1) =>
      spatialInput p.2 i - p.1 i) := by
    simp only [spatialInput_apply]
    fun_prop
  exact hcoord.measurable.pow_const 2

theorem measurable_frequencyKernel (b : GraphCoefficients m) (q : Space m → ℝ → ℂ)
    (hq : Measurable (fun p : Space m × ℝ => q p.1 p.2)) :
    Measurable (fun p : Space m × Space (m + 1) => frequencyKernel b q p.1 p.2) := by
  have hq' : Measurable (fun p : (Space m × Space (m + 1)) × ℝ => q p.1.1 p.2) :=
    hq.comp (measurable_fst.fst.prodMk measurable_snd)
  have hphase : Measurable (fun p : (Space m × Space (m + 1)) × ℝ =>
      oscillation (p.2 * graphGap b p.1.1 p.1.2)) :=
    continuous_oscillation.measurable.comp
      (measurable_snd.mul ((measurable_graphGap b).comp measurable_fst))
  exact (hq'.mul hphase).stronglyMeasurable.integral_prod_right'.measurable

theorem measurable_inputKernel (b : GraphCoefficients m)
    (a : Space m → Space (m + 1) → ℂ) (q : Space m → ℝ → ℂ)
    (ha : Measurable (fun p : Space m × Space (m + 1) => a p.1 p.2))
    (hq : Measurable (fun p : Space m × ℝ => q p.1 p.2)) :
    Measurable (Function.uncurry (inputKernel b a q)) :=
  ha.mul (measurable_frequencyKernel b q hq)

/-- Measurability of the original Gram kernel, without redefining it by its estimate. -/
theorem measurable_gramKernel (b : GraphCoefficients m)
    (a : Space m → Space (m + 1) → ℂ) (q : Space m → ℝ → ℂ)
    (ha : Measurable (fun p : Space m × Space (m + 1) => a p.1 p.2))
    (hq : Measurable (fun p : Space m × ℝ => q p.1 p.2)) :
    Measurable (Function.uncurry (gramKernel b a q)) := by
  have hK := measurable_inputKernel b a q ha hq
  have hx : Measurable (fun p : (Space m × Space m) × Space (m + 1) =>
      inputKernel b a q p.1.1 p.2) :=
    hK.comp (measurable_fst.fst.prodMk measurable_snd)
  have hz : Measurable (fun p : (Space m × Space m) × Space (m + 1) =>
      inputKernel b a q p.1.2 p.2) :=
    hK.comp (measurable_fst.snd.prodMk measurable_snd)
  exact (hx.mul (continuous_star.measurable.comp hz)).stronglyMeasurable.integral_prod_right'.measurable

/-- The real Schur constant after factoring out the scale dependence. -/
def schurConstant (m : ℕ) (L C : ℝ) : ℝ := C * (4 * Real.sqrt (L + 1)) ^ m

theorem schurConstant_pos (m : ℕ) (L C : ℝ) (hL : 0 ≤ L) (hC : 0 < C) :
    0 < schurConstant m L C := by unfold schurConstant; positivity

/-- The row-mass expression is exactly a constant times λ^(1-m/2). -/
theorem schur_scale_eq (m : ℕ) (lambda L C : ℝ) (hlambda : 0 < lambda) :
    C * lambda * (4 * Real.sqrt (L + 1) / Real.sqrt lambda) ^ m =
      schurConstant m L C * lambda ^ (1 - (m : ℝ) / 2) := by
  have hpow : (Real.sqrt lambda) ^ m = lambda ^ ((m : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hlambda.le]
    congr 1
    ring
  have hscale : lambda / (Real.sqrt lambda) ^ m = lambda ^ (1 - (m : ℝ) / 2) := by
    rw [hpow, Real.rpow_sub hlambda, Real.rpow_one]
  calc
    _ = C * (4 * Real.sqrt (L + 1)) ^ m * (lambda / (Real.sqrt lambda) ^ m) := by
      rw [div_pow]
      ring
    _ = _ := by rw [hscale]; rfl

/-- The profile estimate yields the nonnegative row bound used by Schur's test. -/
theorem lintegral_row_le_of_spatialProfile (lambda L C : ℝ)
    (hlambda : 1 ≤ lambda) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (K : Space m → Space m → ℂ)
    (hK : ∀ x z, ‖K x z‖ ≤ C * lambda * spatialProfile lambda L x z) (x : Space m) :
    (∫⁻ z, ‖K x z‖ₑ) ≤
      ENNReal.ofReal (schurConstant m L C * lambda ^ (1 - (m : ℝ) / 2)) := by
  have hl : 0 ≤ lambda := by linarith
  have hcl : 0 ≤ C * lambda := mul_nonneg hC hl
  calc
    _ ≤ ∫⁻ z, ENNReal.ofReal (C * lambda * spatialProfile lambda L x z) := by
      apply lintegral_mono
      intro z
      change ‖K x z‖ₑ ≤ ENNReal.ofReal (C * lambda * spatialProfile lambda L x z)
      rw [← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hK x z)
    _ = ENNReal.ofReal (C * lambda * ∫ z, spatialProfile lambda L x z) := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        ((integrable_spatialProfile lambda L x hl).const_mul (C * lambda))
        (Filter.Eventually.of_forall fun z => mul_nonneg hcl (spatialProfile_nonneg _ _ _ _ hl)),
        integral_const_mul]
    _ ≤ ENNReal.ofReal (C * lambda * (4 * Real.sqrt (L + 1) / Real.sqrt lambda) ^ m) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (integral_spatialProfile_le lambda L x hlambda hL) hcl)
    _ = _ := by rw [schur_scale_eq m lambda L C (by linarith)]

/-- The corresponding column bound follows from the symmetry of the profile. -/
theorem lintegral_column_le_of_spatialProfile (lambda L C : ℝ)
    (hlambda : 1 ≤ lambda) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (K : Space m → Space m → ℂ)
    (hK : ∀ x z, ‖K x z‖ ≤ C * lambda * spatialProfile lambda L x z) (z : Space m) :
    (∫⁻ x, ‖K x z‖ₑ) ≤
      ENNReal.ofReal (schurConstant m L C * lambda ^ (1 - (m : ℝ) / 2)) := by
  apply lintegral_row_le_of_spatialProfile lambda L C hlambda hL hC (fun x z => K z x) ?_ z
  intro x z
  simpa only [spatialProfile_symm lambda L z x] using hK z x

/-- The actual integral operator of any measurable kernel satisfying (3.21) has
the L² bound in (3.23). The conclusion includes membership in L². -/
theorem gramOperator_bound_of_spatialProfile (lambda L C : ℝ)
    (hlambda : 1 ≤ lambda) (hL : 0 ≤ L) (hC : 0 ≤ C)
    (K : Space m → Space m → ℂ) (hKmeas : Measurable (Function.uncurry K))
    (hK : ∀ x z, ‖K x z‖ ≤ C * lambda * spatialProfile lambda L x z)
    (f : Space m → ℂ) (hf : Measurable f) (hfp : MemLp f 2 volume) :
    MemLp (kernelOperator (ν := volume) K f) 2 volume ∧
      eLpNorm (kernelOperator (ν := volume) K f) 2 volume ≤
        ENNReal.ofReal (schurConstant m L C * lambda ^ (1 - (m : ℝ) / 2)) * eLpNorm f 2 volume := by
  have hrow := lintegral_row_le_of_spatialProfile lambda L C hlambda hL hC K hK
  have hcolumn := lintegral_column_le_of_spatialProfile lambda L C hlambda hL hC K hK
  exact ⟨memLp_kernelOperator K f _ hKmeas hf hrow hcolumn hfp,
    eLpNorm_kernelOperator_le K f _ hKmeas hf hrow hcolumn⟩

/-- Uniform Schur bound for the original Gram kernel, derived from the original
coefficient, amplitude, support, and frequency hypotheses. -/
theorem exists_uniform_gramOperator_bound (m : ℕ) (R c0 C0 bmin M : ℝ)
    (hR : 1 ≤ R) (hc0 : 0 < c0) (hC0 : 0 < C0) (hbmin : 0 < bmin) (hM : 0 ≤ M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (lambda : ℝ), 1 ≤ lambda →
      ∀ (b : GraphCoefficients m) (a : Space m → Space (m + 1) → ℂ) (q : Space m → ℝ → ℂ),
        (∀ y, ContDiff ℝ (m + 4 : ℕ) (a y)) →
        (∀ y, InputDerivativeBound (m + 4) M (a y)) →
        (∀ y, Function.support (a y) ⊆ inputSupport R y) →
        Measurable (fun p : Space m × Space (m + 1) => a p.1 p.2) →
        Measurable (fun p : Space m × ℝ => q p.1 p.2) →
        (∀ y tau, ‖q y tau‖ ≤
          C0 * (frequencyAnnulus c0 C0 lambda).indicator (fun _ => 1) tau) →
        (∀ y i, bmin ≤ b.quadratic y i) →
        ∀ (f : Space m → ℂ), Measurable f → MemLp f 2 volume →
          MemLp (kernelOperator (ν := volume) (gramKernel b a q) f) 2 volume ∧
          eLpNorm (kernelOperator (ν := volume) (gramKernel b a q) f) 2 volume ≤
            ENNReal.ofReal (C * lambda ^ (1 - (m : ℝ) / 2)) * eLpNorm f 2 volume := by
  obtain ⟨C, hC, hkernel⟩ := exists_uniform_gramKernel_bound m R c0 C0 bmin M hR hc0 hC0 hbmin hM
  refine ⟨schurConstant m (2 * R) C, schurConstant_pos _ _ _ (by linarith) hC, ?_⟩
  intro lambda hlambda b a q ha hDa hs hameas hq hqbound hb f hf hfp
  exact gramOperator_bound_of_spatialProfile lambda (2 * R) C hlambda (by linarith) hC.le
    (gramKernel b a q) (measurable_gramKernel b a q hameas hq)
    (hkernel lambda hlambda b a q ha hDa hs hq hqbound hb) f hf hfp

end StrongSpherical.SchurTest

namespace StrongSpherical.SchurTest

section L2Operator
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

/-- The kernel integral is absolutely convergent at almost every output point.
This prevents the L² conclusion from relying on the zero convention for
nonintegrable Bochner integrals. -/
theorem integrable_kernel_mul_ae
    (K : α → β → ℂ) (f : β → ℂ) (A : ℝ)
    (hK : Measurable (Function.uncurry K)) (hf : Measurable f)
    (hrow : ∀ x, ∫⁻ z, ‖K x z‖ₑ ∂ν ≤ ENNReal.ofReal A)
    (hcolumn : ∀ z, ∫⁻ x, ‖K x z‖ₑ ∂μ ≤ ENNReal.ofReal A)
    (hfp : MemLp f 2 ν) : ∀ᵐ x ∂μ, Integrable (fun z => K x z * f z) ν := by
  have hmeas : Measurable (fun p : α × β => ‖K p.1 p.2‖ₑ * ‖f p.2‖ₑ) :=
    hK.enorm.mul (hf.enorm.comp measurable_snd)
  have hbound := lintegral_schur_sq_le (fun x z => ‖K x z‖ₑ) (fun z => ‖f z‖ₑ)
    (ENNReal.ofReal A) (ENNReal.ofReal A) hK.enorm hf.enorm hrow hcolumn
  rw [← eLpNorm_two_sq] at hbound
  have hfinite := hbound.trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (by finiteness) (by finiteness)) (ENNReal.pow_lt_top hfp.2))
  filter_upwards [ae_lt_top (hmeas.lintegral_prod_right'.pow_const 2) hfinite.ne] with x hx
  refine ⟨((hK.comp (measurable_const.prodMk measurable_id)).mul hf).aestronglyMeasurable, ?_⟩
  change (∫⁻ z, ‖K x z * f z‖ₑ ∂ν) < ∞
  simp only [enorm_mul]
  simpa only [ENNReal.pow_lt_top_iff, OfNat.ofNat_ne_zero, or_false] using hx

variable (K : α → β → ℂ) (A : ℝ)
variable (hK : Measurable (Function.uncurry K))
variable (hrow : ∀ x, ∫⁻ z, ‖K x z‖ₑ ∂ν ≤ ENNReal.ofReal A)
variable (hcolumn : ∀ z, ∫⁻ x, ‖K x z‖ₑ ∂μ ≤ ENNReal.ofReal A)

/-- The integral operator, as a map of genuine L² equivalence classes. -/
def kernelL2Apply (f : Lp ℂ 2 ν) : Lp ℂ 2 μ :=
  (memLp_kernelOperator K f A hK (Lp.stronglyMeasurable f).measurable hrow hcolumn
    (Lp.memLp f)).toLp _

theorem kernelL2Apply_coe (f : Lp ℂ 2 ν) :
    kernelL2Apply K A hK hrow hcolumn f =ᵐ[μ] kernelOperator (ν := ν) K f :=
  MemLp.coeFn_toLp _

theorem norm_kernelL2Apply_le (hA : 0 ≤ A) (f : Lp ℂ 2 ν) :
    ‖kernelL2Apply K A hK hrow hcolumn f‖ ≤ A * ‖f‖ := by
  have h := norm_toLp_kernelOperator_le K f A hA hK
    (Lp.stronglyMeasurable f).measurable hrow hcolumn (Lp.memLp f)
  simpa only [kernelL2Apply, Lp.toLp_coeFn] using h

theorem kernelL2Apply_add (f g : Lp ℂ 2 ν) :
    kernelL2Apply K A hK hrow hcolumn (f + g) =
      kernelL2Apply K A hK hrow hcolumn f + kernelL2Apply K A hK hrow hcolumn g := by
  apply Lp.ext
  filter_upwards [kernelL2Apply_coe K A hK hrow hcolumn (f + g),
    kernelL2Apply_coe K A hK hrow hcolumn f, kernelL2Apply_coe K A hK hrow hcolumn g,
    Lp.coeFn_add (kernelL2Apply K A hK hrow hcolumn f) (kernelL2Apply K A hK hrow hcolumn g),
    integrable_kernel_mul_ae K f A hK (Lp.stronglyMeasurable f).measurable hrow hcolumn (Lp.memLp f),
    integrable_kernel_mul_ae K g A hK (Lp.stronglyMeasurable g).measurable hrow hcolumn (Lp.memLp g)]
    with x hsum hf hg hadd hif hig
  rw [hsum, hadd]
  simp only [Pi.add_apply, hf, hg]
  change (∫ z, K x z * (f + g) z ∂ν) = (∫ z, K x z * f z ∂ν) + ∫ z, K x z * g z ∂ν
  rw [← integral_add hif hig]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_add f g] with z hz
  rw [hz]
  exact mul_add _ _ _

theorem kernelL2Apply_smul (c : ℂ) (f : Lp ℂ 2 ν) :
    kernelL2Apply K A hK hrow hcolumn (c • f) = c • kernelL2Apply K A hK hrow hcolumn f := by
  apply Lp.ext
  filter_upwards [kernelL2Apply_coe K A hK hrow hcolumn (c • f),
    kernelL2Apply_coe K A hK hrow hcolumn f,
    Lp.coeFn_smul c (kernelL2Apply K A hK hrow hcolumn f)] with x hcf hf hsmul
  rw [hcf, hsmul]
  simp only [Pi.smul_apply, hf, smul_eq_mul]
  change (∫ z, K x z * (c • f) z ∂ν) = c * ∫ z, K x z * f z ∂ν
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_smul c f] with z hz
  rw [hz]
  change K x z * (c * f z) = c * (K x z * f z)
  ring

/-- Schur's test constructs a bounded complex-linear operator on L². -/
def kernelL2Operator (hA : 0 ≤ A) : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous
    { toFun := kernelL2Apply K A hK hrow hcolumn
      map_add' := kernelL2Apply_add K A hK hrow hcolumn
      map_smul' := kernelL2Apply_smul K A hK hrow hcolumn }
    A (norm_kernelL2Apply_le K A hK hrow hcolumn hA)

theorem norm_kernelL2Operator_le (hA : 0 ≤ A) :
    ‖kernelL2Operator K A hK hrow hcolumn hA‖ ≤ A :=
  LinearMap.mkContinuous_norm_le _ hA (norm_kernelL2Apply_le K A hK hrow hcolumn hA)

theorem kernelL2Operator_coe (hA : 0 ≤ A) (f : Lp ℂ 2 ν) :
    kernelL2Operator K A hK hrow hcolumn hA f =ᵐ[μ] kernelOperator (ν := ν) K f :=
  kernelL2Apply_coe K A hK hrow hcolumn f

end L2Operator
end StrongSpherical.SchurTest

namespace StrongSpherical.SchurTest
open QuadraticGraph GramKernel AmplitudeBounds

/-- Separate measurability in the output and continuity in the input suffice
for the joint amplitude measurability needed by the integral operator. -/
theorem measurable_amplitude_of_fibers {m : ℕ}
    (a : Space m → Space (m + 1) → ℂ)
    (ha : ∀ x, Continuous (a x))
    (hameas : ∀ v, Measurable (fun x => a x v)) :
    Measurable (fun p : Space m × Space (m + 1) => a p.1 p.2) :=
  (measurable_uncurry_of_continuous_of_measurable
    (u := fun v x => a x v) ha hameas).comp measurable_swap

/-- The bounded L² operator associated to the original Gram kernel satisfies
(3.23), uniformly in the frequency scale and measurable coefficient choices.
Its action is the original Gram-kernel integral almost everywhere.
The identification with the original graph operator's TT* is a later step. -/
theorem exists_uniform_gramL2Operator (m : ℕ) (R c0 C0 bmin M : ℝ)
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
        ∃ G : Lp ℂ 2 (volume : Measure (Space m)) →L[ℂ] Lp ℂ 2 (volume : Measure (Space m)),
          ‖G‖ ≤ C * lambda ^ (1 - (m : ℝ) / 2) ∧
          ∀ f, G f =ᵐ[volume] kernelOperator (ν := volume) (gramKernel b a q) f := by
  obtain ⟨C, hC, hkernel⟩ := exists_uniform_gramKernel_bound m R c0 C0 bmin M hR hc0 hC0 hbmin hM
  refine ⟨schurConstant m (2 * R) C, schurConstant_pos _ _ _ (by linarith) hC, ?_⟩
  intro lambda hlambda b a q ha hDa hs hameas hq hqbound hb
  have hK := measurable_gramKernel b a q
    (measurable_amplitude_of_fibers a (fun y => (ha y).continuous) hameas) hq
  have hprofile := hkernel lambda hlambda b a q ha hDa hs hq hqbound hb
  have hrow := lintegral_row_le_of_spatialProfile lambda (2 * R) C hlambda (by linarith) hC.le _ hprofile
  have hcolumn := lintegral_column_le_of_spatialProfile lambda (2 * R) C hlambda (by linarith) hC.le _ hprofile
  have hA : 0 ≤ schurConstant m (2 * R) C * lambda ^ (1 - (m : ℝ) / 2) := by
    exact mul_nonneg (schurConstant_pos _ _ _ (by linarith) hC).le (Real.rpow_nonneg (by linarith) _)
  refine ⟨kernelL2Operator (gramKernel b a q) _ hK hrow hcolumn hA,
    norm_kernelL2Operator_le (gramKernel b a q) _ hK hrow hcolumn hA, ?_⟩
  intro f
  exact kernelL2Operator_coe (gramKernel b a q) _ hK hrow hcolumn hA f

end StrongSpherical.SchurTest
