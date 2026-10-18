import Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-! # The scalar power integral in the general Lq layer-cake estimate -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StrongSpherical.LayercakePowerIntegral

theorem coefficient_pos (q : ℝ) (hq : 1 < q) :
    0 < (2 : ℝ) ^ (q - 1) / (q - 1) :=
  div_pos (Real.rpow_pos_of_pos (by norm_num) _) (by linarith)

theorem integral_power_interval (q : ℝ) (hq : 1 < q) (a : ℝ) (ha : 0 ≤ a) :
    (∫⁻ t in Ioo (0 : ℝ) (2 * a), ENNReal.ofReal (t ^ (q - 2))) =
      ENNReal.ofReal ((2 * a) ^ (q - 1) / (q - 1)) := by
  have he : -1 < q - 2 := by linarith
  have hi : IntervalIntegrable (fun t : ℝ => t ^ (q - 2)) volume 0 (2 * a) :=
    intervalIntegral.intervalIntegrable_rpow' he
  have hn : 0 ≤ᵐ[volume.restrict (Ioc (0 : ℝ) (2 * a))]
      (fun t : ℝ => t ^ (q - 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal hi.1 hn,
    ← intervalIntegral.integral_of_le (mul_nonneg (by norm_num) ha),
    integral_rpow (Or.inl he)]
  have hp : q - 2 + 1 = q - 1 := by ring
  rw [hp, Real.zero_rpow (by linarith : q - 1 ≠ 0), sub_zero]

theorem high_tail_coefficient (q : ℝ) (hq : 1 < q) (a : ℝ) (ha : 0 ≤ a) :
    a * ((2 * a) ^ (q - 1) / (q - 1)) =
      ((2 : ℝ) ^ (q - 1) / (q - 1)) * a ^ q := by
  by_cases haz : a = 0
  · simp [haz, Real.zero_rpow (by linarith : q ≠ 0)]
  · have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm haz)
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) ha]
    have he : a * a ^ (q - 1) = a ^ q := by
      calc
        _ = a ^ (1 : ℝ) * a ^ (q - 1) := by rw [Real.rpow_one]
        _ = a ^ (1 + (q - 1)) := (Real.rpow_add hap _ _).symm
        _ = a ^ q := by congr 1; ring
    calc
      _ = ((2 : ℝ) ^ (q - 1) / (q - 1)) * (a * a ^ (q - 1)) := by ring
      _ = _ := by rw [he]

end StrongSpherical.LayercakePowerIntegral
