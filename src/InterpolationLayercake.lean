import InterpolationPowerIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Integral.Prod

/-! # Weighted truncation identities and real-variable interpolation

The measure is s-finite so that the nonnegative double integrals may be
interchanged. Neither the input nor the output energy is assumed finite.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace StrongSpherical.InterpolationLayercake
set_option maxHeartbeats 1000000

variable {X : Type*} [MeasurableSpace X]

private theorem high_coefficient (a q p gamma : ℝ) (ha : 0 < a)
    (_hqp : q < p) (hg : 0 < gamma) :
    ((a / gamma) ^ (p - q) / (p - q)) * a ^ q =
      (gamma ^ (-(p - q)) / (p - q)) * a ^ p := by
  have hpq : a ^ p = a ^ (p - q) * a ^ q := by
    rw [← Real.rpow_add ha]
    congr 1
    ring
  rw [Real.div_rpow ha.le hg.le, Real.rpow_neg hg.le, hpq]
  ring

private theorem low_coefficient (a p r gamma : ℝ) (ha : 0 < a)
    (_hpr : p < r) (hg : 0 < gamma) :
    ((a / gamma) ^ (-(r - p)) / (r - p)) * a ^ r =
      (gamma ^ (r - p) / (r - p)) * a ^ p := by
  have hrp : a ^ r = a ^ (r - p) * a ^ p := by
    rw [← Real.rpow_add ha]
    congr 1
    ring
  rw [Real.div_rpow ha.le hg.le, Real.rpow_neg ha.le,
    Real.rpow_neg hg.le, hrp]
  have hn : a ^ (r - p) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ha _)
  field_simp

/-- The high part of a moving truncation, including infinite input energy. -/
theorem lintegral_high_tail (mu : Measure X) [SFinite mu]
    (F : X → ℝ) (hF : Measurable F) (hn : ∀ x, 0 ≤ F x)
    (q p : ℝ) (hq : 0 < q) (hqp : q < p) (gamma : ℝ) (hg : 0 < gamma) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - q - 1)) *
      ∫⁻ x, {x | gamma * t < F x}.indicator
        (fun x => ENNReal.ofReal (F x) ^ q) x ∂mu) =
      ENNReal.ofReal (gamma ^ (-(p - q)) / (p - q)) *
        ∫⁻ x, ENNReal.ofReal (F x) ^ p ∂mu := by
  let H : ℝ × X → ℝ≥0∞ := fun z => ENNReal.ofReal (z.1 ^ (p - q - 1)) *
    {z : ℝ × X | gamma * z.1 < F z.2}.indicator
      (fun z => ENNReal.ofReal (F z.2) ^ q) z
  have hH : Measurable H :=
    ((measurable_fst.pow_const _).ennreal_ofReal).mul
      ((((hF.comp measurable_snd).ennreal_ofReal).pow_const q).indicator
        (measurableSet_lt (measurable_const.mul measurable_fst) (hF.comp measurable_snd)))
  have hstart :
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - q - 1)) *
        ∫⁻ x, {x | gamma * t < F x}.indicator
          (fun x => ENNReal.ofReal (F x) ^ q) x ∂mu) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, H (t, x) ∂mu := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t _
    exact (lintegral_const_mul _ (((hF.ennreal_ofReal).pow_const q).indicator
      (measurableSet_lt measurable_const hF))).symm
  have hinner : ∀ x : X, (∫⁻ t in Ioi (0 : ℝ), H (t, x)) =
      ENNReal.ofReal (gamma ^ (-(p - q)) / (p - q)) * ENNReal.ofReal (F x) ^ p := by
    intro x
    by_cases ha : F x = 0
    · simp [H, Set.indicator_apply, ha, ENNReal.zero_rpow_of_pos hq,
        ENNReal.zero_rpow_of_pos (hq.trans hqp)]
    have ha0 : 0 < F x := lt_of_le_of_ne (hn x) (Ne.symm ha)
    have heq : (Ioi (0 : ℝ)).indicator (fun t => H (t, x)) =
        (Ioo 0 (F x / gamma)).indicator
          (fun t => ENNReal.ofReal (t ^ (p - q - 1)) * ENNReal.ofReal (F x) ^ q) := by
      ext t
      have ht : gamma * t < F x ↔ t < F x / gamma := by
        rw [lt_div_iff₀ hg, mul_comm]
      by_cases h0 : 0 < t <;> by_cases h1 : gamma * t < F x <;>
        simp [H, h0, h1, ← ht]
    rw [← lintegral_indicator measurableSet_Ioi, heq,
      lintegral_indicator measurableSet_Ioo,
      lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg hq.le ENNReal.ofReal_ne_top),
      InterpolationPowerIntegral.lintegral_power_Ioo (F x / gamma) (p - q)
        (div_pos ha0 hg) (sub_pos.mpr hqp)]
    rw [ENNReal.ofReal_rpow_of_pos ha0]
    rw [← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg (div_pos ha0 hg).le _) (sub_pos.mpr hqp).le),
      high_coefficient (F x) q p gamma ha0 hqp hg,
      ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hg.le _) (sub_pos.mpr hqp).le),
      ← ENNReal.ofReal_rpow_of_pos ha0]
  rw [hstart, lintegral_lintegral_swap hH.aemeasurable]
  simp_rw [hinner]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- The low truncation. At a zero input the integrand is zero before
integrating the singular scalar weight at the origin. -/
theorem lintegral_low_tail (mu : Measure X) [SFinite mu]
    (F : X → ℝ) (hF : Measurable F) (hn : ∀ x, 0 ≤ F x)
    (p r : ℝ) (hp : 0 < p) (hpr : p < r) (gamma : ℝ) (hg : 0 < gamma) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - r - 1)) *
      ∫⁻ x, {x | F x ≤ gamma * t}.indicator
        (fun x => ENNReal.ofReal (F x) ^ r) x ∂mu) =
      ENNReal.ofReal (gamma ^ (r - p) / (r - p)) *
        ∫⁻ x, ENNReal.ofReal (F x) ^ p ∂mu := by
  let H : ℝ × X → ℝ≥0∞ := fun z => ENNReal.ofReal (z.1 ^ (p - r - 1)) *
    {z : ℝ × X | F z.2 ≤ gamma * z.1}.indicator
      (fun z => ENNReal.ofReal (F z.2) ^ r) z
  have hH : Measurable H :=
    ((measurable_fst.pow_const _).ennreal_ofReal).mul
      ((((hF.comp measurable_snd).ennreal_ofReal).pow_const r).indicator
        (measurableSet_le (hF.comp measurable_snd) (measurable_const.mul measurable_fst)))
  have hstart :
      (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - r - 1)) *
        ∫⁻ x, {x | F x ≤ gamma * t}.indicator
          (fun x => ENNReal.ofReal (F x) ^ r) x ∂mu) =
      ∫⁻ t in Ioi (0 : ℝ), ∫⁻ x, H (t, x) ∂mu := by
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t _
    exact (lintegral_const_mul _ (((hF.ennreal_ofReal).pow_const r).indicator
      (measurableSet_le hF measurable_const))).symm
  have hinner : ∀ x : X, (∫⁻ t in Ioi (0 : ℝ), H (t, x)) =
      ENNReal.ofReal (gamma ^ (r - p) / (r - p)) * ENNReal.ofReal (F x) ^ p := by
    intro x
    by_cases ha : F x = 0
    · simp [H, Set.indicator_apply, ha, ENNReal.zero_rpow_of_pos (hp.trans hpr), ENNReal.zero_rpow_of_pos hp]
    have ha0 : 0 < F x := lt_of_le_of_ne (hn x) (Ne.symm ha)
    have hb : 0 < F x / gamma := div_pos ha0 hg
    have heq : (Ioi (0 : ℝ)).indicator (fun t => H (t, x)) =
        (Ici (F x / gamma)).indicator
          (fun t => ENNReal.ofReal (t ^ (p - r - 1)) * ENNReal.ofReal (F x) ^ r) := by
      ext t
      have ht : F x ≤ gamma * t ↔ F x / gamma ≤ t := by
        rw [div_le_iff₀ hg, mul_comm]
      by_cases h1 : F x ≤ gamma * t
      · have h0 : 0 < t := hb.trans_le (ht.mp h1)
        simp [H, h0, h1, ← ht]
      · by_cases h0 : 0 < t <;> simp [H, h0, h1, ← ht]
    rw [← lintegral_indicator measurableSet_Ioi, heq,
      lintegral_indicator measurableSet_Ici,
      ← Measure.restrict_congr_set (Ioi_ae_eq_Ici : Ioi (F x / gamma) =ᵐ[volume] Ici (F x / gamma)),
      lintegral_mul_const' _ _ (ENNReal.rpow_ne_top_of_nonneg (hp.trans hpr).le ENNReal.ofReal_ne_top)]
    rw [show p - r - 1 = -(r - p) - 1 by ring,
      InterpolationPowerIntegral.lintegral_power_Ioi (F x / gamma) (r - p) hb (sub_pos.mpr hpr),
      ENNReal.ofReal_rpow_of_pos ha0]
    rw [← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hb.le _) (sub_pos.mpr hpr).le),
      low_coefficient (F x) p r gamma ha0 hpr hg,
      ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hg.le _) (sub_pos.mpr hpr).le),
      ← ENNReal.ofReal_rpow_of_pos ha0]
  rw [hstart, lintegral_lintegral_swap hH.aemeasurable]
  simp_rw [hinner]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Layer cake for a nonnegative finite-valued function on an arbitrary
measure space. The measure need not be finite. -/
theorem lintegral_rpow_eq_tail_real (mu : Measure X) (G : X → ℝ)
    (hG : Measurable G) (hn : ∀ x, 0 ≤ G x) (p : ℝ) (hp : 0 < p) :
    (∫⁻ x, ENNReal.ofReal (G x) ^ p ∂mu) = ENNReal.ofReal p *
      ∫⁻ t in Ioi (0 : ℝ), mu {x | t < G x} * ENNReal.ofReal (t ^ (p - 1)) := by
  have h := lintegral_rpow_eq_lintegral_meas_lt_mul mu
    (Filter.Eventually.of_forall hn) hG.aemeasurable hp
  simpa only [← ENNReal.ofReal_rpow_of_nonneg (hn _) hp.le] using h

private theorem weighted_power (t p q A : ℝ) (ht : 0 < t) (hA : 0 ≤ A) :
    ENNReal.ofReal (A * t ^ (-q)) * ENNReal.ofReal (t ^ (p - 1)) =
      ENNReal.ofReal A * ENNReal.ofReal (t ^ (p - q - 1)) := by
  rw [← ENNReal.ofReal_mul (mul_nonneg hA (Real.rpow_nonneg ht.le _)),
    ← ENNReal.ofReal_mul hA]
  congr 1
  rw [mul_assoc, ← Real.rpow_add ht]
  congr 2
  ring

/-- Integrating a two-tail distribution estimate, with a real-valued output. -/
theorem energy_real_le_of_two_tail (mu : Measure X) [SFinite mu]
    (F G : X → ℝ) (hF : Measurable F) (hnF : ∀ x, 0 ≤ F x)
    (hG : Measurable G) (hnG : ∀ x, 0 ≤ G x)
    (q p r : ℝ) (hq : 0 < q) (hqp : q < p) (hpr : p < r)
    (gamma : ℝ) (hg : 0 < gamma) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (htail : ∀ t : ℝ, 0 < t → mu {x | t < G x} ≤
      ENNReal.ofReal (A * t ^ (-q)) *
        (∫⁻ x, {x | gamma * t < F x}.indicator
          (fun x => ENNReal.ofReal (F x) ^ q) x ∂mu) +
      ENNReal.ofReal (B * t ^ (-r)) *
        (∫⁻ x, {x | F x ≤ gamma * t}.indicator
          (fun x => ENNReal.ofReal (F x) ^ r) x ∂mu)) :
    (∫⁻ x, ENNReal.ofReal (G x) ^ p ∂mu) ≤
      ENNReal.ofReal (p * (A * gamma ^ (-(p - q)) / (p - q) +
        B * gamma ^ (r - p) / (r - p))) * ∫⁻ x, ENNReal.ofReal (F x) ^ p ∂mu := by
  have hp : 0 < p := hq.trans hqp
  have hhigh : Measurable (fun t : ℝ => ∫⁻ x,
      {x | gamma * t < F x}.indicator (fun x => ENNReal.ofReal (F x) ^ q) x ∂mu) := by
    have hh : Measurable (fun z : ℝ × X =>
        {z : ℝ × X | gamma * z.1 < F z.2}.indicator
          (fun z => ENNReal.ofReal (F z.2) ^ q) z) :=
      (((hF.comp measurable_snd).ennreal_ofReal).pow_const q).indicator
        (measurableSet_lt (measurable_const.mul measurable_fst) (hF.comp measurable_snd))
    exact hh.lintegral_prod_right'
  have hca : 0 ≤ gamma ^ (-(p - q)) / (p - q) :=
    div_nonneg (Real.rpow_nonneg hg.le _) (sub_pos.mpr hqp).le
  have hcb : 0 ≤ gamma ^ (r - p) / (r - p) :=
    div_nonneg (Real.rpow_nonneg hg.le _) (sub_pos.mpr hpr).le
  have hweight : Measurable (fun t : ℝ => ENNReal.ofReal A *
      (ENNReal.ofReal (t ^ (p - q - 1)) * ∫⁻ x,
        {x | gamma * t < F x}.indicator (fun x => ENNReal.ofReal (F x) ^ q) x ∂mu)) :=
    measurable_const.mul (((measurable_id.pow_const (p - q - 1)).ennreal_ofReal).mul hhigh)
  rw [lintegral_rpow_eq_tail_real mu G hG hnG p hp]
  calc
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ),
        ENNReal.ofReal A * (ENNReal.ofReal (t ^ (p - q - 1)) *
          ∫⁻ x, {x | gamma * t < F x}.indicator
            (fun x => ENNReal.ofReal (F x) ^ q) x ∂mu) +
        ENNReal.ofReal B * (ENNReal.ofReal (t ^ (p - r - 1)) *
          ∫⁻ x, {x | F x ≤ gamma * t}.indicator
            (fun x => ENNReal.ofReal (F x) ^ r) x ∂mu) := by
      apply mul_le_mul' le_rfl
      apply setLIntegral_mono' measurableSet_Ioi
      intro t ht
      calc
        _ ≤ (ENNReal.ofReal (A * t ^ (-q)) *
            (∫⁻ x, {x | gamma * t < F x}.indicator
              (fun x => ENNReal.ofReal (F x) ^ q) x ∂mu) +
            ENNReal.ofReal (B * t ^ (-r)) *
            (∫⁻ x, {x | F x ≤ gamma * t}.indicator
              (fun x => ENNReal.ofReal (F x) ^ r) x ∂mu)) *
              ENNReal.ofReal (t ^ (p - 1)) := mul_le_mul' (htail t ht) le_rfl
        _ = _ := by
          rw [add_mul]
          apply congrArg₂ (· + ·)
          · rw [mul_right_comm, weighted_power t p q A ht hA, mul_assoc]
          · rw [mul_right_comm, weighted_power t p r B ht hB, mul_assoc]
    _ = ENNReal.ofReal p *
        (ENNReal.ofReal A * (ENNReal.ofReal (gamma ^ (-(p - q)) / (p - q)) *
          ∫⁻ x, ENNReal.ofReal (F x) ^ p ∂mu) +
        ENNReal.ofReal B * (ENNReal.ofReal (gamma ^ (r - p) / (r - p)) *
          ∫⁻ x, ENNReal.ofReal (F x) ^ p ∂mu)) := by
      rw [lintegral_add_left hweight,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_high_tail mu F hF hnF q p hq hqp gamma hg,
        lintegral_low_tail mu F hF hnF p r hp hpr gamma hg]
    _ = _ := by
      rw [show ENNReal.ofReal p *
          (ENNReal.ofReal A * (ENNReal.ofReal (gamma ^ (-(p - q)) / (p - q)) *
            ∫⁻ x, ENNReal.ofReal (F x) ^ p ∂mu) +
          ENNReal.ofReal B * (ENNReal.ofReal (gamma ^ (r - p) / (r - p)) *
            ∫⁻ x, ENNReal.ofReal (F x) ^ p ∂mu)) =
          (ENNReal.ofReal p * (ENNReal.ofReal A * ENNReal.ofReal (gamma ^ (-(p - q)) / (p - q)) +
            ENNReal.ofReal B * ENNReal.ofReal (gamma ^ (r - p) / (r - p)))) *
            ∫⁻ x, ENNReal.ofReal (F x) ^ p ∂mu by ring]
      rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul hB,
        ← ENNReal.ofReal_add (mul_nonneg hA hca) (mul_nonneg hB hcb),
        ← ENNReal.ofReal_mul hp.le]
      congr 2
      ring

/-- A two-tail distribution estimate controls the full extended-valued
output. Truncation and monotone convergence include outputs equal to infinity. -/
theorem energy_le_of_two_tail (mu : Measure X) [SFinite mu]
    (F : X → ℝ) (hF : Measurable F) (hnF : ∀ x, 0 ≤ F x)
    (G : X → ℝ≥0∞) (hG : Measurable G)
    (q p r : ℝ) (hq : 0 < q) (hqp : q < p) (hpr : p < r)
    (gamma : ℝ) (hg : 0 < gamma) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (htail : ∀ t : ℝ, 0 < t → mu {x | ENNReal.ofReal t < G x} ≤
      ENNReal.ofReal (A * t ^ (-q)) *
        (∫⁻ x, {x | gamma * t < F x}.indicator
          (fun x => ENNReal.ofReal (F x) ^ q) x ∂mu) +
      ENNReal.ofReal (B * t ^ (-r)) *
        (∫⁻ x, {x | F x ≤ gamma * t}.indicator
          (fun x => ENNReal.ofReal (F x) ^ r) x ∂mu)) :
    (∫⁻ x, G x ^ p ∂mu) ≤
      ENNReal.ofReal (p * (A * gamma ^ (-(p - q)) / (p - q) +
        B * gamma ^ (r - p) / (r - p))) * ∫⁻ x, ENNReal.ofReal (F x) ^ p ∂mu := by
  have hp : 0 < p := hq.trans hqp
  let GN : ℕ → X → ℝ := fun N x => (min (G x) (N : ℝ≥0∞)).toReal
  have hcap : ∀ (N : ℕ) (x : X), min (G x) (N : ℝ≥0∞) ≠ ∞ := fun N x =>
    ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  have hGN : ∀ N : ℕ, Measurable (GN N) := fun N => (hG.min measurable_const).ennreal_toReal
  have hnGN : ∀ (N : ℕ) (x : X), 0 ≤ GN N x := fun N x => ENNReal.toReal_nonneg
  have hpow : ∀ (N : ℕ) (x : X),
      ENNReal.ofReal (GN N x) ^ p = min (G x) (N : ℝ≥0∞) ^ p := by
    intro N x
    change ENNReal.ofReal ((min (G x) (N : ℝ≥0∞)).toReal) ^ p = _
    rw [ENNReal.ofReal_toReal (hcap N x)]
  have hb : ∀ N : ℕ, (∫⁻ x, min (G x) (N : ℝ≥0∞) ^ p ∂mu) ≤
      ENNReal.ofReal (p * (A * gamma ^ (-(p - q)) / (p - q) +
        B * gamma ^ (r - p) / (r - p))) * ∫⁻ x, ENNReal.ofReal (F x) ^ p ∂mu := by
    intro N
    have h := energy_real_le_of_two_tail mu F (GN N) hF hnF (hGN N) (hnGN N)
      q p r hq hqp hpr gamma hg A B hA hB (fun t ht => by
        have hsub : {x | t < GN N x} ⊆ {x | ENNReal.ofReal t < G x} := by
          intro x hx
          exact ((ENNReal.ofReal_lt_iff_lt_toReal ht.le (hcap N x)).2 hx).trans_le
            (min_le_left _ _)
        exact (measure_mono hsub).trans (htail t ht))
    simpa only [hpow] using h
  have heq : ∀ x, G x ^ p = ⨆ N : ℕ, min (G x) (N : ℝ≥0∞) ^ p := by
    intro x
    have hs := (ENNReal.orderIsoRpow p hp).map_iSup
      (fun N : ℕ => min (G x) (N : ℝ≥0∞))
    change (⨆ N : ℕ, min (G x) (N : ℝ≥0∞)) ^ p =
      ⨆ N : ℕ, min (G x) (N : ℝ≥0∞) ^ p at hs
    rw [← hs]
    congr 1
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  simp_rw [heq]
  rw [lintegral_iSup (fun N => (hG.min measurable_const).pow_const p)
    (fun i j hij x => ENNReal.rpow_le_rpow
      (min_le_min_left _ (by exact_mod_cast hij)) hp.le)]
  exact iSup_le hb

/-- Integrating any distribution-function majorant controls the extended
output energy. No s-finiteness or measurability of the majorant is needed. -/
theorem energy_le_of_tail (mu : Measure X) (G : X → ℝ≥0∞) (hG : Measurable G)
    (p : ℝ) (hp : 0 < p) (tail : ℝ → ℝ≥0∞)
    (htail : ∀ t : ℝ, 0 < t → mu {x | ENNReal.ofReal t < G x} ≤ tail t) :
    (∫⁻ x, G x ^ p ∂mu) ≤ ENNReal.ofReal p *
      ∫⁻ t in Ioi (0 : ℝ), tail t * ENNReal.ofReal (t ^ (p - 1)) := by
  let GN : ℕ → X → ℝ := fun N x => (min (G x) (N : ℝ≥0∞)).toReal
  have hcap : ∀ (N : ℕ) (x : X), min (G x) (N : ℝ≥0∞) ≠ ∞ := fun N x =>
    ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  have hGN : ∀ N : ℕ, Measurable (GN N) := fun N => (hG.min measurable_const).ennreal_toReal
  have hnGN : ∀ (N : ℕ) (x : X), 0 ≤ GN N x := fun N x => ENNReal.toReal_nonneg
  have hpow : ∀ (N : ℕ) (x : X),
      ENNReal.ofReal (GN N x) ^ p = min (G x) (N : ℝ≥0∞) ^ p := by
    intro N x
    change ENNReal.ofReal ((min (G x) (N : ℝ≥0∞)).toReal) ^ p = _
    rw [ENNReal.ofReal_toReal (hcap N x)]
  have hb : ∀ N : ℕ, (∫⁻ x, min (G x) (N : ℝ≥0∞) ^ p ∂mu) ≤
      ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ), tail t * ENNReal.ofReal (t ^ (p - 1)) := by
    intro N
    rw [← show (∫⁻ x, ENNReal.ofReal (GN N x) ^ p ∂mu) =
        ∫⁻ x, min (G x) (N : ℝ≥0∞) ^ p ∂mu by simp_rw [hpow],
      lintegral_rpow_eq_tail_real mu (GN N) (hGN N) (hnGN N) p hp]
    apply mul_le_mul' le_rfl
    apply setLIntegral_mono' measurableSet_Ioi
    intro t ht
    apply mul_le_mul' _ le_rfl
    have hsub : {x | t < GN N x} ⊆ {x | ENNReal.ofReal t < G x} := by
      intro x hx
      exact ((ENNReal.ofReal_lt_iff_lt_toReal ht.le (hcap N x)).2 hx).trans_le
        (min_le_left _ _)
    exact (measure_mono hsub).trans (htail t ht)
  have heq : ∀ x, G x ^ p = ⨆ N : ℕ, min (G x) (N : ℝ≥0∞) ^ p := by
    intro x
    have hs := (ENNReal.orderIsoRpow p hp).map_iSup
      (fun N : ℕ => min (G x) (N : ℝ≥0∞))
    change (⨆ N : ℕ, min (G x) (N : ℝ≥0∞)) ^ p =
      ⨆ N : ℕ, min (G x) (N : ℝ≥0∞) ^ p at hs
    rw [← hs]
    congr 1
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  simp_rw [heq]
  rw [lintegral_iSup (fun N => (hG.min measurable_const).pow_const p)
    (fun i j hij x => ENNReal.rpow_le_rpow
      (min_le_min_left _ (by exact_mod_cast hij)) hp.le)]
  exact iSup_le hb

end StrongSpherical.InterpolationLayercake
