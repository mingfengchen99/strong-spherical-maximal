import ProductTail

/-! # The full physical-coordinate small-scale kernel estimate (5.20) -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace StrongSpherical.KernelSmoothing
open ProductSmoothing ScalarSmoothing SmoothingGeometry ProductTail
variable {n : ℕ}

def relativeRadii (r a : Radii n) : Radii n :=
  ⟨fun i => a.1 i / r.1 i, fun i => div_pos (a.2 i) (r.2 i)⟩

theorem multiply_relativeRadii (r a : Radii n) :
    DyadicRadii.multiply r (relativeRadii r a) = a := by
  apply Subtype.ext
  funext i
  change r.1 i * (a.1 i / r.1 i) = a.1 i
  field_simp [ne_of_gt (r.2 i)]

/-- Smoothing at coordinate scales at most epsilon times the kernel radii
leaves a genuine error dominated by the full product Schwartz weight. -/
theorem exists_small_scale_kernel_bound (n : ℕ) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : Space n → ℂ, Differentiable ℝ K →
      Function.support K ⊆ MarginalEnergy.coordinateBox n R →
      ∀ B : ℝ, (∀ x, ‖K x‖ ≤ B) → (∀ x, ‖fderiv ℝ K x‖ ≤ B) →
      ∀ r a : Radii n, ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ 1 →
      (∀ i, a.1 i / r.1 i ≤ epsilon) → ∀ y : Space n,
      ‖dilatedKernel K r y - kernelConvolution (dilatedKernel K r) (productPhi a) y‖ ≤
        C * epsilon * B * productWeight r y := by
  refine ⟨errorConstant n R, errorConstant_pos n R hR, ?_⟩
  intro K hK hs B hb hd r a epsilon heps0 heps hscale y
  let eta := relativeRadii r a
  let w := inverseDilation r y
  have hy : diagonalDilation r.1 w = y := diagonalDilation_inverseDilation r y
  have hjoin : DyadicRadii.multiply r eta = a := multiply_relativeRadii r a
  have hconv : kernelConvolution (dilatedKernel K r) (productPhi a) y =
      (dilationJacobian r : ℂ)⁻¹ * kernelConvolution K (productPhi eta) w := by
    simpa only [hy, hjoin] using kernelConvolution_productPhi_dilation K r eta w
  have hweight : productWeight r y = (dilationJacobian r)⁻¹ * ∏ i, unitWeight (w i) := by
    simpa only [hy] using productWeight_dilation r w
  have hnorm := norm_sub_convolution_weighted K hK R B epsilon hR heps0 heps hs hb hd
    eta (fun i => hscale i) w
  have hJac : ‖(dilationJacobian r : ℂ)⁻¹‖ = (dilationJacobian r)⁻¹ := by
    simp [abs_of_pos (dilationJacobian_pos r)]
  change ‖(dilationJacobian r : ℂ)⁻¹ * K w - _‖ ≤ _
  rw [hconv, ← mul_sub, norm_mul, hJac]
  calc
    _ ≤ (dilationJacobian r)⁻¹ *
        (errorConstant n R * epsilon * B * ∏ i, unitWeight (w i)) :=
      mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr (dilationJacobian_pos r).le)
    _ = _ := by rw [hweight]; ring

end StrongSpherical.KernelSmoothing
