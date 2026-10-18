import ScalarSmoothing
import MarginalEnergy

/-! # Product boxes and exact covariance of the actual smoothers -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace StrongSpherical.SmoothingGeometry
open ProductSmoothing FourierCutoff DilationL2 ScalarSmoothing
variable {n : ℕ}

theorem indicator_product_box {𝕜 : Type*} [RCLike 𝕜]
    (R : ℝ) (F : Fin n → ℝ → 𝕜) :
    (MarginalEnergy.coordinateBox n R).indicator (fun x : Space n => ∏ i, F i (x i)) =
      fun x => ∏ i, (Icc (-R) R).indicator (F i) (x i) := by
  classical
  funext x
  by_cases hx : x ∈ MarginalEnergy.coordinateBox n R
  · rw [indicator_of_mem hx]
    apply Finset.prod_congr rfl
    intro i _
    rw [indicator_of_mem (hx i)]
  · rw [indicator_of_notMem hx]
    have hn : ∃ i : Fin n, x i ∉ Icc (-R) R := by
      simpa only [MarginalEnergy.coordinateBox, mem_setOf_eq, not_forall] using hx
    obtain ⟨i, hi⟩ := hn
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ i) (indicator_of_notMem hi _)

theorem integral_product_box {𝕜 : Type*} [RCLike 𝕜]
    (R : ℝ) (F : Fin n → ℝ → 𝕜) :
    (∫ x : Space n in MarginalEnergy.coordinateBox n R, ∏ i, F i (x i)) =
      ∏ i, ∫ t in Icc (-R) R, F i t := by
  rw [← integral_indicator (MarginalEnergy.measurableSet_coordinateBox n R),
    indicator_product_box R F,
    integral_product_functions (fun i t => (Icc (-R) R).indicator (F i) t)]
  simp_rw [integral_indicator measurableSet_Icc]

theorem dilatedKernel_unit (K : Space n → ℂ) : dilatedKernel K (unitRadii n) = K := by
  funext x
  simp [dilatedKernel, dilationJacobian, inverseDilation, unitRadii, diagonalDilation_one]

theorem productPhi_multiply_dilation (r s : Radii n) (x : Space n) :
    productPhi (DyadicRadii.multiply r s) (diagonalDilation r.1 x) =
      (dilationJacobian r : ℂ)⁻¹ * productPhi s x := by
  have hpoint : ∀ i : Fin n,
      scaledPhi ((DyadicRadii.multiply r s).1 i) (diagonalDilation r.1 x i) =
        ((r.1 i : ℂ)⁻¹) * scaledPhi (s.1 i) (x i) := by
    intro i
    have harg : (r.1 i * s.1 i)⁻¹ * (r.1 i * x i) = (s.1 i)⁻¹ * x i := by
      field_simp [ne_of_gt (r.2 i), ne_of_gt (s.2 i)]
    simp only [scaledPhi, DyadicRadii.multiply_apply, diagonalDilation_apply]
    rw [harg]
    simp only [mul_inv, Complex.ofReal_mul, mul_assoc]
  unfold productPhi
  simp_rw [hpoint]
  rw [Finset.prod_mul_distrib]
  congr 1
  simp only [dilationJacobian, Complex.ofReal_prod, Finset.prod_inv_distrib]

theorem productWeight_dilation (r : Radii n) (x : Space n) :
    productWeight r (diagonalDilation r.1 x) =
      (dilationJacobian r)⁻¹ * ∏ i, unitWeight (x i) := by
  have hpoint : ∀ i : Fin n, |diagonalDilation r.1 x i| / r.1 i = |x i| := by
    intro i
    rw [diagonalDilation_apply, abs_mul, abs_of_pos (r.2 i)]
    field_simp [ne_of_gt (r.2 i)]
  unfold productWeight
  simp_rw [hpoint]
  rw [Finset.prod_mul_distrib]
  simp only [dilationJacobian, Finset.prod_inv_distrib, unitWeight]

theorem kernelConvolution_const_mul_right (K f : Space n → ℂ) (c : ℂ) (x : Space n) :
    kernelConvolution K (fun y => c * f y) x = c * kernelConvolution K f x := by
  simp only [kernelConvolution_eq_integral]
  calc
    _ = ∫ y, c * (K y * f (x - y)) := by
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = _ := integral_const_mul c _

/-- The actual smoothed kernel rescales with exactly the same reciprocal Jacobian. -/
theorem kernelConvolution_productPhi_dilation (K : Space n → ℂ) (r s : Radii n)
    (x : Space n) :
    kernelConvolution (dilatedKernel K r) (productPhi (DyadicRadii.multiply r s))
        (diagonalDilation r.1 x) =
      (dilationJacobian r : ℂ)⁻¹ * kernelConvolution K (productPhi s) x := by
  have h := kernelConvolution_multiply_dilation K (productPhi (DyadicRadii.multiply r s))
    r (unitRadii n) x
  rw [DyadicRadii.multiply_unit, dilatedKernel_unit] at h
  rw [h]
  have he : productPhi (DyadicRadii.multiply r s) ∘ diagonalDilation r.1 =
      fun y => (dilationJacobian r : ℂ)⁻¹ * productPhi s y := by
    funext y
    exact productPhi_multiply_dilation r s y
  rw [he, kernelConvolution_const_mul_right]

end StrongSpherical.SmoothingGeometry
