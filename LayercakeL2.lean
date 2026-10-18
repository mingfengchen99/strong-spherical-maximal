import Definitions
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The layer-cake step from a truncated-tail estimate to squared L² energy -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace StrongSpherical.LayercakeL2

theorem lintegral_sq_eq_tail (G : ℝ → ℝ) (hG : Measurable G) (hn : ∀ x, 0 ≤ G x) :
    (∫⁻ x, ENNReal.ofReal (G x) ^ 2) =
      ∫⁻ t in Ioi (0 : ℝ), volume {x | t < G x} * ENNReal.ofReal (2 * t) := by
  have hi : ∀ a : ℝ, (∫ t in (0 : ℝ)..a, 2 * t) = a ^ 2 := by
    intro a
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  have h := lintegral_comp_eq_lintegral_meas_lt_mul (volume : Measure ℝ)
    (Filter.Eventually.of_forall hn) hG.aemeasurable
    (g := fun t : ℝ => 2 * t)
    (fun _ _ => (by fun_prop : Continuous (fun t : ℝ => 2 * t)).intervalIntegrable _ _)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact mul_nonneg (by norm_num) ht.le)
  simp only [hi] at h
  calc
    _ = ∫⁻ x, ENNReal.ofReal (G x ^ 2) := by
      congr 1
      ext x
      exact (ENNReal.ofReal_pow (hn x) 2).symm
    _ = _ := h

/-- Tonelli turns the moving truncation threshold into exactly twice the input energy. -/
theorem lintegral_high_tail (F : ℝ → ℝ) (hF : Measurable F) (_hn : ∀ x, 0 ≤ F x) :
    (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x,
      {x | t / 2 < F x}.indicator (fun x => ENNReal.ofReal (F x)) x) =
      2 * ∫⁻ x, ENNReal.ofReal (F x) ^ 2 := by
  let H : ℝ × ℝ → ℝ≥0∞ := fun p =>
    {p : ℝ × ℝ | p.1 / 2 < F p.2}.indicator
      (fun p => ENNReal.ofReal (F p.2)) p
  have hH : Measurable H :=
    (ENNReal.measurable_ofReal.comp (hF.comp measurable_snd)).indicator
      (measurableSet_lt (by fun_prop) (hF.comp measurable_snd))
  have hswap : (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, H (t, x)) =
      ∫⁻ x, ∫⁻ t in Ioi (0 : ℝ), H (t, x) :=
    lintegral_lintegral_swap hH.aemeasurable
  have hinner : ∀ x : ℝ, (∫⁻ t in Ioi (0 : ℝ), H (t, x)) =
      2 * ENNReal.ofReal (F x) ^ 2 := by
    intro x
    have heq : (Ioi (0 : ℝ)).indicator (fun t => H (t, x)) =
        (Ioo 0 (2 * F x)).indicator (fun _ => ENNReal.ofReal (F x)) := by
      ext t
      have ht : t / 2 < F x ↔ t < 2 * F x := by constructor <;> intro h <;> linarith
      by_cases h0 : 0 < t <;> by_cases h1 : t / 2 < F x <;>
        simp [H, h0, h1, ← ht]
    rw [← lintegral_indicator measurableSet_Ioi, heq,
      lintegral_indicator_const measurableSet_Ioo, Real.volume_Ioo, sub_zero,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
    ring
  change (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, H (t, x)) = _
  rw [hswap]
  simp_rw [hinner]
  exact lintegral_const_mul _ ((ENNReal.measurable_ofReal.comp hF).pow_const 2)

/-- The explicit high-tail inequality yields a squared L² estimate with constant 4C. -/
theorem lintegral_sq_le_of_high_tail (F G : ℝ → ℝ)
    (hF : Measurable F) (hnF : ∀ x, 0 ≤ F x)
    (hG : Measurable G) (hnG : ∀ x, 0 ≤ G x) (C : ℝ≥0∞)
    (htail : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * volume {x | t < G x} ≤
        C * ∫⁻ x, {x | t / 2 < F x}.indicator (fun x => ENNReal.ofReal (F x)) x) :
    (∫⁻ x, ENNReal.ofReal (G x) ^ 2) ≤
      (4 * C) * ∫⁻ x, ENNReal.ofReal (F x) ^ 2 := by
  rw [lintegral_sq_eq_tail G hG hnG]
  have hH : Measurable (fun t : ℝ => ∫⁻ x,
      {x | t / 2 < F x}.indicator (fun x => ENNReal.ofReal (F x)) x) := by
    have hm : Measurable (fun p : ℝ × ℝ =>
        {p : ℝ × ℝ | p.1 / 2 < F p.2}.indicator
          (fun p => ENNReal.ofReal (F p.2)) p) :=
      (ENNReal.measurable_ofReal.comp (hF.comp measurable_snd)).indicator
        (measurableSet_lt (by fun_prop) (hF.comp measurable_snd))
    exact hm.lintegral_prod_right' (ν := (volume : Measure ℝ))
  calc
    _ ≤ ∫⁻ t in Ioi (0 : ℝ), (2 * C) * ∫⁻ x,
        {x | t / 2 < F x}.indicator (fun x => ENNReal.ofReal (F x)) x := by
      apply setLIntegral_mono' measurableSet_Ioi
      intro t ht
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      norm_num
      calc
        _ = 2 * (ENNReal.ofReal t * volume {x | t < G x}) := by ring
        _ ≤ 2 * (C * ∫⁻ x, {x | t / 2 < F x}.indicator
            (fun x => ENNReal.ofReal (F x)) x) := mul_le_mul' le_rfl (htail t ht)
        _ = _ := by rw [mul_assoc]
    _ = (2 * C) * (∫⁻ t in Ioi (0 : ℝ), ∫⁻ x,
        {x | t / 2 < F x}.indicator (fun x => ENNReal.ofReal (F x)) x) :=
      lintegral_const_mul _ hH
    _ = _ := by rw [lintegral_high_tail F hF hnF]; ring

end StrongSpherical.LayercakeL2
