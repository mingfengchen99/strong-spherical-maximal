import ProductSmoothing
import MarginalLocalEstimate

/-! # The small-scale smoothing error for C¹ compact kernels -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace StrongSpherical.SmoothingError
open ProductSmoothing
variable {n : ℕ}

theorem norm_difference_le (K : Space n → ℂ) (hK : Differentiable ℝ K)
    (B : ℝ) (hB : ∀ x, ‖fderiv ℝ K x‖ ≤ B) (x y : Space n) :
    ‖K x - K (x - y)‖ ≤ B * ‖y‖ := by
  have h := (convex_univ : Convex ℝ (univ : Set (Space n))).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hK x) (fun x _ => hB x) (mem_univ (x - y)) (mem_univ x)
  simpa only [sub_sub_cancel] using h

theorem integrable_kernel_smoothing_row (K : Space n → ℂ) (hK : Continuous K)
    (B : ℝ) (hb : ∀ x, ‖K x‖ ≤ B) (r : Radii n) (x : Space n) :
    Integrable (fun y => K (x - y) * productPhi r y) := by
  apply ((integrable_productPhi r).norm.const_mul B).mono'
  · exact ((hK.comp (continuous_const.sub continuous_id)).mul
      (continuous_productPhi r)).aestronglyMeasurable
  · filter_upwards with y
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hb (x - y)) (norm_nonneg _)

/-- The mean-value estimate behind (5.22), with the actual product smoother. -/
theorem norm_sub_convolution_le_moment (K : Space n → ℂ) (hK : Differentiable ℝ K)
    (B : ℝ) (hb : ∀ x, ‖K x‖ ≤ B) (hd : ∀ x, ‖fderiv ℝ K x‖ ≤ B)
    (r : Radii n) (x : Space n) :
    ‖K x - kernelConvolution K (productPhi r) x‖ ≤
      B * ∫ y, ‖y‖ * ‖productPhi r y‖ := by
  have hi := integrable_kernel_smoothing_row K hK.continuous B hb r x
  have hc := (integrable_productPhi r).const_mul (K x)
  have hconst : (∫ y, K x * productPhi r y) = K x := by
    rw [integral_const_mul, integral_productPhi, mul_one]
  rw [MarginalLocalEstimate.convolution_eq_centered_integral, ← hconst,
    ← integral_sub hc hi]
  calc
    _ ≤ ∫ y, ‖K x * productPhi r y - K (x - y) * productPhi r y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y, B * (‖y‖ * ‖productPhi r y‖) := by
      apply integral_mono (hc.sub hi).norm ((integrable_normMoment r).const_mul B)
      intro y
      change ‖K x * productPhi r y - K (x - y) * productPhi r y‖ ≤ B * (‖y‖ * ‖productPhi r y‖)
      rw [← sub_mul, norm_mul]
      exact (mul_le_mul_of_nonneg_right (norm_difference_le K hK B hd x y)
        (norm_nonneg _)).trans_eq (mul_assoc _ _ _)
    _ = _ := integral_const_mul B _

theorem norm_sub_convolution_le_small_scale (K : Space n → ℂ) (hK : Differentiable ℝ K)
    (B : ℝ) (hb : ∀ x, ‖K x‖ ≤ B) (hd : ∀ x, ‖fderiv ℝ K x‖ ≤ B)
    (r : Radii n) (epsilon : ℝ) (hscale : ∀ i, r.1 i ≤ epsilon) (x : Space n) :
    ‖K x - kernelConvolution K (productPhi r) x‖ ≤
      (n : ℝ) * momentBase ^ (n + 1) * epsilon * B := by
  have hB : 0 ≤ B := (norm_nonneg (K 0)).trans (hb 0)
  calc
    _ ≤ B * ∫ y, ‖y‖ * ‖productPhi r y‖ := norm_sub_convolution_le_moment K hK B hb hd r x
    _ ≤ B * ((n : ℝ) * epsilon * momentBase ^ (n + 1)) :=
      mul_le_mul_of_nonneg_left (integral_normMoment_le r epsilon hscale) hB
    _ = _ := by ring

end StrongSpherical.SmoothingError
