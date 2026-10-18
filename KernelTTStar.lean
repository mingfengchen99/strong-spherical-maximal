import SchurTest
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Adjoint and TT* identities for actual integral kernels

Absolute integrability is established before each application of Fubini.
The initial Schur bound only constructs the operators; a separate bound on
the Gram kernel will subsequently improve the norm of the original operator.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal NNReal ComplexConjugate InnerProduct

namespace StrongSpherical.KernelTTStar
open SchurTest

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]

/-- A preliminary finite Schur bound, not the desired sharp operator estimate. -/
structure KernelControl (H : α → β → ℂ) (A : ℝ) : Prop where
  measurable : Measurable (Function.uncurry H)
  nonneg : 0 ≤ A
  row : ∀ x, ∫⁻ v, ‖H x v‖ₑ ∂ν ≤ ENNReal.ofReal A
  column : ∀ v, ∫⁻ x, ‖H x v‖ₑ ∂μ ≤ ENNReal.ofReal A

variable {H : α → β → ℂ} {A : ℝ}

/-- The conjugate transpose kernel. -/
def adjointKernel (H : α → β → ℂ) (v : β) (x : α) : ℂ := conj (H x v)

omit [SFinite μ] [SFinite ν] in
theorem KernelControl.adjoint (h : KernelControl (μ := μ) (ν := ν) H A) :
    KernelControl (μ := ν) (ν := μ) (adjointKernel H) A := by
  refine ⟨continuous_star.measurable.comp (h.measurable.comp measurable_swap), h.nonneg, ?_, ?_⟩
  · intro v
    simpa only [adjointKernel, RCLike.enorm_conj] using h.column v
  · intro x
    simpa only [adjointKernel, RCLike.enorm_conj] using h.row x

/-- The preliminary bounded L² realization of the original integral kernel. -/
def KernelControl.operator (h : KernelControl (μ := μ) (ν := ν) H A) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 μ :=
  kernelL2Operator H A h.measurable h.row h.column h.nonneg

theorem KernelControl.operator_coe (h : KernelControl (μ := μ) (ν := ν) H A)
    (f : Lp ℂ 2 ν) : h.operator f =ᵐ[μ] kernelOperator (ν := ν) H f :=
  kernelL2Operator_coe H A h.measurable h.row h.column h.nonneg f

/-- The double integral used in the adjoint identity is absolutely integrable. -/
theorem KernelControl.integrable_bilinear (h : KernelControl (μ := μ) (ν := ν) H A)
    (f : β → ℂ) (g : α → ℂ) (hf : Measurable f) (hg : Measurable g)
    (hfp : MemLp f 2 ν) (hgp : MemLp g 2 μ) :
    Integrable (fun p : α × β => g p.1 * H p.1 p.2 * f p.2) (μ.prod ν) := by
  have hmeas : Measurable (fun p : α × β => g p.1 * H p.1 p.2 * f p.2) :=
    ((hg.comp measurable_fst).mul h.measurable).mul (hf.comp measurable_snd)
  have hinner : Measurable (fun x => ∫⁻ v, ‖H x v‖ₑ * ‖f v‖ₑ ∂ν) :=
    (h.measurable.enorm.mul (hf.enorm.comp measurable_snd)).lintegral_prod_right'
  have hs := lintegral_schur_sq_le (fun x v => ‖H x v‖ₑ) (fun v => ‖f v‖ₑ)
    (ENNReal.ofReal A) (ENNReal.ofReal A) h.measurable.enorm hf.enorm h.row h.column
  rw [← eLpNorm_two_sq] at hs
  have hsfin := hs.trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (by finiteness) (by finiteness)) (ENNReal.pow_lt_top hfp.2))
  have hgfin : (∫⁻ x, ‖g x‖ₑ ^ 2 ∂μ) < ∞ := by
    rw [← eLpNorm_two_sq]
    exact ENNReal.pow_lt_top hgp.2
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    hg.enorm.aemeasurable hinner.aemeasurable
  simp only [Pi.mul_apply, ENNReal.rpow_two] at hcs
  have hfinite := hcs.trans_lt (ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hgfin.ne)
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hsfin.ne))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hmeas.enorm.aemeasurable]
  simp only [enorm_mul, mul_assoc]
  have heq (x : α) := lintegral_const_mul (μ := ν) ‖g x‖ₑ
    (show Measurable (fun v => ‖H x v‖ₑ * ‖f v‖ₑ) from
      (h.measurable.enorm.comp (measurable_const.prodMk measurable_id)).mul hf.enorm)
  simpa only [heq] using hfinite

/-- The operator of the conjugate transpose kernel is the Hilbert-space adjoint. -/
theorem KernelControl.operator_adjoint (h : KernelControl (μ := μ) (ν := ν) H A) :
    h.adjoint.operator = h.operator.adjoint := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
  intro g f
  have hint := h.integrable_bilinear f (fun x => conj (g x))
    (Lp.stronglyMeasurable f).measurable
    (continuous_star.measurable.comp (Lp.stronglyMeasurable g).measurable)
    (Lp.memLp f) (Lp.memLp g).star
  rw [L2.inner_def, L2.inner_def]
  calc
    _ = ∫ v, ∫ x, conj (g x) * H x v * f v ∂μ ∂ν := by
      apply integral_congr_ae
      filter_upwards [h.adjoint.operator_coe g] with v hv
      rw [RCLike.inner_apply', hv]
      change conj (∫ x, conj (H x v) * g x ∂μ) * f v = _
      rw [← integral_conj, ← integral_mul_const]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by simp only [map_mul, Complex.conj_conj]; ring
    _ = ∫ x, ∫ v, conj (g x) * H x v * f v ∂ν ∂μ :=
      integral_integral_swap (f := fun v x => conj (g x) * H x v * f v) hint.swap
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [h.operator_coe f] with x hx
      rw [RCLike.inner_apply', hx]
      change _ = conj (g x) * ∫ v, H x v * f v ∂ν
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by ring

end StrongSpherical.KernelTTStar

namespace StrongSpherical.KernelTTStar
open SchurTest
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
variable {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
variable {H : α → β → ℂ} {A : ℝ}

/-- The Gram kernel formed from the original kernel. -/
def gram (H : α → β → ℂ) (x z : α) : ℂ := ∫ v, H x v * conj (H z v) ∂ν

/-- Fubini identifies composition with the integral of the actual Gram kernel. -/
theorem KernelControl.operator_comp_adjoint_coe
    (h : KernelControl (μ := μ) (ν := ν) H A)
    (hrows : ∀ x, MemLp (H x) 2 ν) (f : Lp ℂ 2 μ) :
    h.operator (h.adjoint.operator f) =ᵐ[μ] kernelOperator (ν := μ) (gram (ν := ν) H) f := by
  filter_upwards [h.operator_coe (h.adjoint.operator f)] with x hx
  rw [hx]
  have hint := h.adjoint.integrable_bilinear f (H x)
    (Lp.stronglyMeasurable f).measurable
    (h.measurable.comp (measurable_const.prodMk measurable_id)) (Lp.memLp f) (hrows x)
  calc
    _ = ∫ v, H x v * (∫ z, conj (H z v) * f z ∂μ) ∂ν := by
      apply integral_congr_ae
      filter_upwards [h.adjoint.operator_coe f] with v hv
      rw [hv]
      rfl
    _ = ∫ v, ∫ z, H x v * conj (H z v) * f z ∂μ ∂ν := by
      simp_rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => integral_congr_ae
        (Filter.Eventually.of_forall fun z => by ring)
    _ = ∫ z, ∫ v, H x v * conj (H z v) * f z ∂ν ∂μ :=
      integral_integral_swap (f := fun v z => H x v * conj (H z v) * f z) hint
    _ = _ := by simp only [kernelOperator, gram, integral_mul_const]

/-- Equality of bounded operators, not just a formal kernel calculation. -/
theorem KernelControl.ttstar_eq (h : KernelControl (μ := μ) (ν := ν) H A)
    (hrows : ∀ x, MemLp (H x) 2 ν) (G : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hG : ∀ f, G f =ᵐ[μ] kernelOperator (ν := μ) (gram (ν := ν) H) f) :
    h.operator ∘L h.operator.adjoint = G := by
  rw [← h.operator_adjoint]
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  exact (h.operator_comp_adjoint_coe hrows f).trans (hG f).symm

/-- The sharp Gram-operator bound gives the square-root bound for the original operator. -/
theorem KernelControl.norm_le_sqrt_of_gram (h : KernelControl (μ := μ) (ν := ν) H A)
    (hrows : ∀ x, MemLp (H x) 2 ν) (G : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ)
    (hG : ∀ f, G f =ᵐ[μ] kernelOperator (ν := μ) (gram (ν := ν) H) f)
    (B : ℝ) (hB : ‖G‖ ≤ B) : ‖h.operator‖ ≤ Real.sqrt B := by
  have heq := h.ttstar_eq hrows G hG
  have hnorm : ‖h.operator‖ ^ 2 = ‖G‖ := by
    have hnorm := ContinuousLinearMap.norm_adjoint_comp_self h.operator.adjoint
    simpa only [ContinuousLinearMap.adjoint_adjoint, heq, LinearIsometryEquiv.norm_map, pow_two] using hnorm.symm
  calc
    _ = Real.sqrt ‖G‖ := by rw [← hnorm, Real.sqrt_sq (norm_nonneg _)]
    _ ≤ _ := Real.sqrt_le_sqrt hB

end StrongSpherical.KernelTTStar
