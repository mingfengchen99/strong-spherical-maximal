import RectangularMaximalLp
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-! # Distribution bounds from genuine finite-exponent norm estimates -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StrongSpherical.MaximalChebyshev
variable {X : Type*} [MeasurableSpace X]

theorem complex_energy (μ : Measure X) (f : X → ℂ) (s : ℝ) (hs : 0 < s) :
    eLpNorm f (ENNReal.ofReal s) μ ^ s = ∫⁻ x, ‖f x‖ₑ ^ s ∂μ := by
  rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hs) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hs.le]
  exact (lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := f) (μ := μ) hs).symm

/-- Chebyshev's estimate retains zero and infinite energies. -/
theorem measure_lt_le_energy (μ : Measure X) (G : X → ℝ≥0∞) (hG : Measurable G)
    (s : ℝ) (hs : 0 < s) (t : ℝ) (ht : 0 < t) :
    μ {x | ENNReal.ofReal t < G x} ≤
      ENNReal.ofReal (t ^ (-s)) * ∫⁻ x, G x ^ s ∂μ := by
  have htsp : 0 < t ^ s := Real.rpow_pos_of_pos ht s
  have hsub : {x | ENNReal.ofReal t < G x} ⊆
      {x | ENNReal.ofReal (t ^ s) ≤ G x ^ s} := by
    intro x hx
    rw [← ENNReal.ofReal_rpow_of_pos ht]
    exact (ENNReal.rpow_lt_rpow hx hs).le
  calc
    _ ≤ μ {x | ENNReal.ofReal (t ^ s) ≤ G x ^ s} := measure_mono hsub
    _ ≤ (∫⁻ x, G x ^ s ∂μ) / ENNReal.ofReal (t ^ s) :=
      meas_ge_le_lintegral_div (hG.pow_const s).aemeasurable
        (ENNReal.ofReal_ne_zero_iff.mpr htsp) ENNReal.ofReal_ne_top
    _ = _ := by
      rw [ENNReal.div_eq_inv_mul, Real.rpow_neg ht.le,
        ENNReal.ofReal_inv_of_pos htsp]

/-- A strong norm estimate gives the distribution bound needed for truncation
interpolation, with its endpoint constant appearing to the actual exponent. -/
theorem measure_lt_le_of_eLpNorm (μ : Measure X) (G : X → ℝ≥0∞) (hG : Measurable G)
    (f : X → ℂ) (s : ℝ) (hs : 0 < s) (A : ℝ) (hA : 0 ≤ A)
    (t : ℝ) (ht : 0 < t)
    (hbound : eLpNorm G (ENNReal.ofReal s) μ ≤
      ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal s) μ) :
    μ {x | ENNReal.ofReal t < G x} ≤
      ENNReal.ofReal (A ^ s * t ^ (-s)) * ∫⁻ x, ‖f x‖ₑ ^ s ∂μ := by
  calc
    _ ≤ ENNReal.ofReal (t ^ (-s)) * (eLpNorm G (ENNReal.ofReal s) μ ^ s) := by
      rw [RectangularMaximalLp.eLpNorm_ofReal_rpow μ G s hs]
      exact measure_lt_le_energy μ G hG s hs t ht
    _ ≤ ENNReal.ofReal (t ^ (-s)) *
        ((ENNReal.ofReal A * eLpNorm f (ENNReal.ofReal s) μ) ^ s) :=
      mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hbound hs.le)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ hs.le,
        ENNReal.ofReal_rpow_of_nonneg hA hs.le, complex_energy μ f s hs,
        ENNReal.ofReal_mul (Real.rpow_nonneg hA s)]
      ring

end StrongSpherical.MaximalChebyshev
