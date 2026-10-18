import EllipsoidGraph

/-! # Exact signed-coordinate covariance of the original kernels and L² norms -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators FourierTransform
namespace StrongSpherical.CoordinateTransport
variable {n : ℕ}

def coordinateChange (e : Fin n ≃ Fin n) (negative : Bool) : Space n ≃ₗᵢ[ℝ] Space n :=
  if negative then (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e).trans (LinearIsometryEquiv.neg ℝ)
  else LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

@[simp] theorem coordinateChange_apply (e : Fin n ≃ Fin n) (negative : Bool) (u : Space n) (i : Fin n) :
    coordinateChange e negative u i = if negative then -u (e.symm i) else u (e.symm i) := by
  cases negative <;> rfl

def transportRadii (e : Fin n ≃ Fin n) (r : Radii n) : Radii n :=
  ⟨fun i => r.1 (e i), fun i => r.2 (e i)⟩

theorem transportRadii_local (e : Fin n ≃ Fin n) (r : Radii n) (hr : r ∈ localRadii n) :
    transportRadii e r ∈ localRadii n := fun i => hr (e i)

theorem dilationJacobian_transport (e : Fin n ≃ Fin n) (r : Radii n) :
    dilationJacobian (transportRadii e r) = dilationJacobian r := by
  exact e.prod_comp r.1

theorem inverseDilation_transport (e : Fin n ≃ Fin n) (negative : Bool) (r : Radii n) (u : Space n) :
    coordinateChange e negative (inverseDilation (transportRadii e r) u) =
      inverseDilation r (coordinateChange e negative u) := by
  ext i
  simp only [coordinateChange_apply, inverseDilation, diagonalDilation_apply, transportRadii,
    Equiv.apply_symm_apply]
  cases negative <;> simp only [Bool.false_eq_true, ↓reduceIte]
  ring

theorem dilatedNormalKernel_transport (e : Fin n ≃ Fin n) (negative : Bool)
    (chi : Space n → ℂ) (beta : ℝ → ℂ) (lambda : ℝ) (r : Radii n) (u : Space n) :
    dilatedNormalKernel (chi ∘ coordinateChange e negative) beta lambda (transportRadii e r) u =
      dilatedNormalKernel chi beta lambda r (coordinateChange e negative u) := by
  simp only [dilatedNormalKernel, dilatedKernel, normalKernel, dilationJacobian_transport,
    Function.comp_apply]
  rw [← inverseDilation_transport, LinearIsometryEquiv.norm_map]

/-- Genuine convolution covariance follows by a measure-preserving change of variables. -/
theorem kernelConvolution_transport (e : Fin n ≃ Fin n) (negative : Bool)
    (chi : Space n → ℂ) (beta : ℝ → ℂ) (lambda : ℝ) (r : Radii n) (f : Space n → ℂ) (x : Space n) :
    kernelConvolution (dilatedNormalKernel (chi ∘ coordinateChange e negative) beta lambda
      (transportRadii e r)) (f ∘ coordinateChange e negative) x =
      kernelConvolution (dilatedNormalKernel chi beta lambda r) f (coordinateChange e negative x) := by
  let Q := coordinateChange e negative
  rw [kernelConvolution_eq_integral, kernelConvolution_eq_integral]
  calc
    _ = ∫ y, dilatedNormalKernel chi beta lambda r (Q y) * f (Q x - Q y) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun y => by
        dsimp only
        rw [dilatedNormalKernel_transport]
        simp only [Function.comp_apply, map_sub, Q]
    _ = _ := by
      convert Q.measurePreserving.integral_comp Q.toHomeomorph.toMeasurableEquiv.measurableEmbedding
        (fun y => dilatedNormalKernel chi beta lambda r y * f (Q x - y)) using 1

/-- Exact L² invariance, including for functions with infinite L² norm. -/
theorem eLpNorm_comp_coordinateChange (e : Fin n ≃ Fin n) (negative : Bool) (f : Space n → ℂ) :
    eLpNorm (f ∘ coordinateChange e negative) 2 volume = eLpNorm f 2 volume := by
  apply (ENNReal.rpow_left_injective (by norm_num : (2 : ℝ) ≠ 0))
  simp only [ENNReal.rpow_two, SchurTest.eLpNorm_two_sq, Function.comp_apply]
  convert (coordinateChange e negative).measurePreserving.lintegral_comp_emb
    (coordinateChange e negative).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun y => ‖f y‖ₑ ^ 2) using 1

end StrongSpherical.CoordinateTransport
