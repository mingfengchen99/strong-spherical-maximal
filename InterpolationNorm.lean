import MaximalChebyshev

/-! # Taking the positive-exponent root of an interpolation energy estimate -/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace StrongSpherical.InterpolationNorm
variable {X : Type*} [MeasurableSpace X]

theorem eLpNorm_le_of_energy (μ : Measure X) (G : X → ℝ≥0∞) (f : X → ℂ)
    (p : ℝ) (hp : 0 < p) (C : ℝ) (hC : 0 ≤ C)
    (he : (∫⁻ x, G x ^ p ∂μ) ≤
      ENNReal.ofReal (C ^ p) * ∫⁻ x, ‖f x‖ₑ ^ p ∂μ) :
    eLpNorm G (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) μ := by
  apply (ENNReal.rpow_le_rpow_iff hp).mp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hp.le,
    ENNReal.ofReal_rpow_of_nonneg hC hp.le,
    RectangularMaximalLp.eLpNorm_ofReal_rpow μ G p hp,
    MaximalChebyshev.complex_energy μ f p hp]
  exact he

end StrongSpherical.InterpolationNorm
