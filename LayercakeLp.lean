import Definitions
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Prod
import LayercakePowerIntegral

/-! # The high-tail layer-cake estimate for every real exponent greater than one -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace StrongSpherical.LayercakeLp
set_option maxHeartbeats 1000000

def tailCoefficient (q : ℝ) : ℝ := (2 : ℝ) ^ (q - 1) / (q - 1)

theorem tailCoefficient_pos (q : ℝ) (hq : 1 < q) : 0 < tailCoefficient q :=
  div_pos (Real.rpow_pos_of_pos (by norm_num) _) (sub_pos.mpr hq)

theorem lintegral_rpow_eq_tail (G : ℝ → ℝ) (hG : Measurable G)
    (hn : ∀ x, 0 ≤ G x) (q : ℝ) (hq : 0 < q) :
    (∫⁻ x, ENNReal.ofReal (G x) ^ q) = ENNReal.ofReal q *
      ∫⁻ t in Ioi (0 : ℝ), volume {x | t < G x} * ENNReal.ofReal (t ^ (q - 1)) := by
  have h := lintegral_rpow_eq_lintegral_meas_lt_mul (volume : Measure ℝ)
    (Filter.Eventually.of_forall hn) hG.aemeasurable hq
  simpa only [← ENNReal.ofReal_rpow_of_nonneg (hn _) hq.le] using h

/-- Tonelli computes the weighted moving truncation threshold exactly. -/
theorem lintegral_high_tail (F : ℝ → ℝ) (hF : Measurable F)
    (hn : ∀ x, 0 ≤ F x) (q : ℝ) (hq : 1 < q) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 2)) *
      ∫⁻ x, {x | t / 2 < F x}.indicator (fun x => ENNReal.ofReal (F x)) x) =
      ENNReal.ofReal (tailCoefficient q) * ∫⁻ x, ENNReal.ofReal (F x) ^ q := by
  let H : ℝ × ℝ → ℝ≥0∞ := fun p => ENNReal.ofReal (p.1 ^ (q - 2)) *
    {p : ℝ × ℝ | p.1 / 2 < F p.2}.indicator (fun p => ENNReal.ofReal (F p.2)) p
  have hH : Measurable H :=
    ((measurable_fst.pow_const (q - 2)).ennreal_ofReal).mul
      ((ENNReal.measurable_ofReal.comp (hF.comp measurable_snd)).indicator
        (measurableSet_lt (by fun_prop) (hF.comp measurable_snd)))
  have hstart :
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (q - 2)) *
        ∫⁻ x, {x | t / 2 < F x}.indicator (fun x => ENNReal.ofReal (F x)) x) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, H (t, x) := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t _
    exact (lintegral_const_mul _ ((ENNReal.measurable_ofReal.comp hF).indicator
      (measurableSet_lt measurable_const hF))).symm
  have hinner : ∀ x : ℝ, (∫⁻ t in Ioi (0 : ℝ), H (t, x)) =
      ENNReal.ofReal (tailCoefficient q) * ENNReal.ofReal (F x) ^ q := by
    intro x
    have heq : (Ioi (0 : ℝ)).indicator (fun t => H (t, x)) =
        (Ioo 0 (2 * F x)).indicator
          (fun t => ENNReal.ofReal (t ^ (q - 2)) * ENNReal.ofReal (F x)) := by
      ext t
      have ht : t / 2 < F x ↔ t < 2 * F x := by constructor <;> intro h <;> linarith
      by_cases h0 : 0 < t <;> by_cases h1 : t / 2 < F x <;>
        simp [H, h0, h1, ← ht]
    rw [← lintegral_indicator measurableSet_Ioi, heq,
      lintegral_indicator measurableSet_Ioo,
      lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
      LayercakePowerIntegral.integral_power_interval q hq (F x) (hn x)]
    have hv : 0 ≤ (2 * F x) ^ (q - 1) / (q - 1) :=
      div_nonneg (Real.rpow_nonneg (by linarith [hn x]) _) (by linarith)
    rw [← ENNReal.ofReal_mul hv]
    have hc := LayercakePowerIntegral.high_tail_coefficient q hq (F x) (hn x)
    calc
      _ = ENNReal.ofReal (tailCoefficient q * (F x) ^ q) := by
        apply congrArg ENNReal.ofReal
        simpa only [tailCoefficient, mul_comm] using hc
      _ = _ := by
        rw [ENNReal.ofReal_mul (tailCoefficient_pos q hq).le,
          ← ENNReal.ofReal_rpow_of_nonneg (hn x) (by linarith : 0 ≤ q)]
  rw [hstart, lintegral_lintegral_swap hH.aemeasurable]
  simp_rw [hinner]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The genuine high-tail estimate yields the finite real-exponent energy
bound. No finiteness assumption on either integral is imposed. -/
theorem lintegral_rpow_le_of_high_tail (F G : ℝ → ℝ)
    (hF : Measurable F) (hnF : ∀ x, 0 ≤ F x)
    (hG : Measurable G) (hnG : ∀ x, 0 ≤ G x)
    (q : ℝ) (hq : 1 < q) (C : ℝ) (hC : 0 ≤ C)
    (htail : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * volume {x | t < G x} ≤
      ENNReal.ofReal C * ∫⁻ x,
        {x | t / 2 < F x}.indicator (fun x => ENNReal.ofReal (F x)) x) :
    (∫⁻ x, ENNReal.ofReal (G x) ^ q) ≤
      ENNReal.ofReal (q * C * tailCoefficient q) * ∫⁻ x, ENNReal.ofReal (F x) ^ q := by
  rw [lintegral_rpow_eq_tail G hG hnG q (by linarith)]
  calc
    _ ≤ ENNReal.ofReal q * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal C *
        (ENNReal.ofReal (t ^ (q - 2)) *
          ∫⁻ x, {x | t / 2 < F x}.indicator (fun x => ENNReal.ofReal (F x)) x) := by
      apply mul_le_mul' le_rfl
      apply setLIntegral_mono' measurableSet_Ioi
      intro t ht
      have hp : t ^ (q - 1) = t * t ^ (q - 2) := by
        rw [show q - 1 = 1 + (q - 2) by ring, Real.rpow_add ht, Real.rpow_one]
      rw [hp, ENNReal.ofReal_mul ht.le]
      calc
        _ = (ENNReal.ofReal t * volume {x | t < G x}) * ENNReal.ofReal (t ^ (q - 2)) := by ring
        _ ≤ (ENNReal.ofReal C * ∫⁻ x,
            {x | t / 2 < F x}.indicator (fun x => ENNReal.ofReal (F x)) x) *
            ENNReal.ofReal (t ^ (q - 2)) := mul_le_mul' (htail t ht) le_rfl
        _ = _ := by ring
    _ = ENNReal.ofReal q * (ENNReal.ofReal C * ENNReal.ofReal (tailCoefficient q) *
        ∫⁻ x, ENNReal.ofReal (F x) ^ q) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_high_tail F hF hnF q hq]
      simp only [mul_assoc]
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg (by linarith) hC), ENNReal.ofReal_mul (by linarith : 0 ≤ q)]
      ring

end StrongSpherical.LayercakeLp
