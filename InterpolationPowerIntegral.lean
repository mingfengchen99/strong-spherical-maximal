import LayercakePowerIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Scalar power integrals for real-variable interpolation -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StrongSpherical.InterpolationPowerIntegral

theorem lintegral_power_Ioo (b z : ℝ) (hb : 0 < b) (hz : 0 < z) :
    (∫⁻ t in Ioo (0 : ℝ) b, ENNReal.ofReal (t ^ (z - 1))) =
      ENNReal.ofReal (b ^ z / z) := by
  have h := LayercakePowerIntegral.integral_power_interval
    (z + 1) (by linarith) (b / 2) (by positivity)
  simpa only [show z + 1 - 2 = z - 1 by ring,
    show z + 1 - 1 = z by ring, show 2 * (b / 2) = b by ring] using h

theorem lintegral_power_Ioi (b z : ℝ) (hb : 0 < b) (hz : 0 < z) :
    (∫⁻ t in Ioi b, ENNReal.ofReal (t ^ (-z - 1))) =
      ENNReal.ofReal (b ^ (-z) / z) := by
  have he : -z - 1 < -1 := by linarith
  have hn : 0 ≤ᵐ[volume.restrict (Ioi b)] (fun t : ℝ => t ^ (-z - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact Real.rpow_nonneg (hb.trans ht).le _
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_Ioi_rpow_of_lt he hb) hn,
    integral_Ioi_rpow_of_lt he hb]
  have hexp : -z - 1 + 1 = -z := by ring
  rw [hexp, neg_div_neg_eq]

end StrongSpherical.InterpolationPowerIntegral
