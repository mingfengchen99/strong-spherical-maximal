import HardyLittlewoodOneDim
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-! # Product-decay weight domination by actual centered interval averages -/
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal NNReal BigOperators Topology

namespace StrongSpherical.MaximalWeight
open HardyLittlewoodOneDim

def oneDimWeight (v t : ℝ) : ℝ := v⁻¹ * (1 + |t| / v) ^ (-(3 : ℤ))
def dyadicRadius (v : ℝ) (k : ℕ) : ℝ := 2 ^ (k + 1) * v
def dyadicCoefficient (v : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (v⁻¹ * (1 / 8 : ℝ) ^ k)

theorem continuous_oneDimWeight (v : ℝ) (hv : 0 < v) : Continuous (oneDimWeight v) := by
  have ha : Continuous (fun t : ℝ => 1 + |t| / v) := by fun_prop
  exact continuous_const.mul (ha.zpow₀ (-(3 : ℤ))
    (fun t => Or.inl (ne_of_gt (by positivity : (0 : ℝ) < 1 + |t| / v))))

theorem oneDimWeight_nonneg (v t : ℝ) (hv : 0 < v) : 0 ≤ oneDimWeight v t :=
  mul_nonneg (inv_nonneg.mpr hv.le)
    (zpow_nonneg (by positivity : 0 ≤ 1 + |t| / v) _)

theorem oneDimWeight_le_dyadic (v t : ℝ) (hv : 0 < v) :
    ENNReal.ofReal (oneDimWeight v t) ≤
      ∑' k : ℕ, dyadicCoefficient v k *
        (ball (0 : ℝ) (dyadicRadius v k)).indicator (fun _ => (1 : ℝ≥0∞)) t := by
  have ha : 1 ≤ 1 + |t| / v := by
    have hh := div_nonneg (abs_nonneg t) hv.le
    linarith
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near ha (by norm_num : (1 : ℝ) < 2)
  have ht : t ∈ ball (0 : ℝ) (dyadicRadius v k) := by
    rw [mem_ball, Real.dist_eq, sub_zero, dyadicRadius]
    have h := (div_lt_iff₀ hv).1 (by linarith : |t| / v < (2 : ℝ) ^ (k + 1))
    exact h
  have hcoeff : oneDimWeight v t ≤ v⁻¹ * (1 / 8 : ℝ) ^ k := by
    have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 2 ^ k) hk1 3
    have hp : (0 : ℝ) < 1 + |t| / v := by positivity
    have hkpos : (0 : ℝ) < 2 ^ k := by positivity
    have hinv := one_div_le_one_div_of_le (pow_pos hkpos 3) hpow
    have hid : (1 : ℝ) / ((2 : ℝ) ^ k) ^ 3 = (1 / 8 : ℝ) ^ k := by
      rw [one_div_pow, ← pow_mul, mul_comm k 3, pow_mul]
      norm_num
    unfold oneDimWeight
    simp only [zpow_neg, zpow_ofNat, inv_eq_one_div]
    rw [hid] at hinv
    exact mul_le_mul_of_nonneg_left hinv (by positivity : (0 : ℝ) ≤ 1 / v)
  exact (ENNReal.ofReal_le_ofReal hcoeff).trans
    (le_trans (by simp [ht, dyadicCoefficient]) (ENNReal.le_tsum k))

theorem lintegral_interval_reflection (F : ℝ → ℝ≥0∞) (hF : Measurable F)
    (r x : ℝ) :
    (∫⁻ y in ball (0 : ℝ) r, F (x - y)) = ∫⁻ y in ball x r, F y := by
  have h := ((volume : Measure ℝ).measurePreserving_sub_left x).lintegral_comp
    (hF.indicator (measurableSet_ball : MeasurableSet (ball x r)))
  rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
  convert h using 1
  congr 1
  ext y
  have heq : x - y ∈ ball x r ↔ y ∈ ball (0 : ℝ) r := by
    simp [mem_ball]
  by_cases hy : y ∈ ball (0 : ℝ) r <;> simp [hy, heq]

theorem dyadicCoefficient_volume (v : ℝ) (hv : 0 < v) (k : ℕ) :
    dyadicCoefficient v k * ENNReal.ofReal (2 * dyadicRadius v k) =
      4 * (ENNReal.ofReal (1 / 4 : ℝ)) ^ k := by
  rw [dyadicCoefficient, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 4),
    ← show ENNReal.ofReal (4 : ℝ) = 4 by norm_num,
    ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  congr 1
  unfold dyadicRadius
  rw [pow_succ]
  calc
    _ = 4 * ((1 / 8 : ℝ) * 2) ^ k := by rw [mul_pow]; field_simp; ring
    _ = _ := by norm_num

/-- Actual convolution with the scale-v decay weight is dominated uniformly
by the centered rational maximal function. -/
theorem lintegral_weight_le (v : ℝ) (hv : 0 < v) (F : ℝ → ℝ≥0∞)
    (hF : Measurable F) (x : ℝ) :
    (∫⁻ y, ENNReal.ofReal (oneDimWeight v y) * F (x - y)) ≤
      16 * rationalMaximal F x := by
  let A : ℕ → ℝ → ℝ≥0∞ := fun k y => dyadicCoefficient v k *
    (ball (0 : ℝ) (dyadicRadius v k)).indicator (fun _ => (1 : ℝ≥0∞)) y * F (x - y)
  have hA : ∀ k, Measurable (A k) := by
    intro k
    exact (measurable_const.mul (measurable_const.indicator measurableSet_ball)).mul
      (hF.comp (by fun_prop))
  have hterm : ∀ k, (∫⁻ y, A k y) ≤
      8 * (ENNReal.ofReal (1 / 4 : ℝ)) ^ k * rationalMaximal F x := by
    intro k
    have hr : 0 < dyadicRadius v k := by unfold dyadicRadius; positivity
    have hr0 : ENNReal.ofReal (2 * dyadicRadius v k) ≠ 0 := by positivity
    have heq : (∫⁻ y, A k y) =
        dyadicCoefficient v k * ∫⁻ y in ball x (dyadicRadius v k), F y := by
      have hi : ∀ y, A k y = dyadicCoefficient v k *
          (ball (0 : ℝ) (dyadicRadius v k)).indicator (fun y => F (x - y)) y := by
        intro y
        by_cases hy : y ∈ ball (0 : ℝ) (dyadicRadius v k) <;> simp [A, hy]
      simp_rw [hi]
      have hfsub : Measurable (fun y : ℝ => F (x - y)) :=
        hF.comp (measurable_const.sub measurable_id)
      rw [lintegral_const_mul _ (hfsub.indicator measurableSet_ball),
        lintegral_indicator measurableSet_ball, lintegral_interval_reflection F hF]
    have hm := intervalAverage_le_two_rationalMaximal (dyadicRadius v k) hr F x
    calc
      _ = (dyadicCoefficient v k * ENNReal.ofReal (2 * dyadicRadius v k)) *
          intervalAverage (dyadicRadius v k) F x := by
        rw [heq, intervalAverage, mul_assoc, ← mul_assoc (ENNReal.ofReal _),
          ENNReal.mul_inv_cancel hr0 ENNReal.ofReal_ne_top, one_mul]
      _ ≤ (4 * (ENNReal.ofReal (1 / 4 : ℝ)) ^ k) * (2 * rationalMaximal F x) := by
        rw [dyadicCoefficient_volume v hv]
        exact mul_le_mul' le_rfl hm
      _ = _ := by ring
  calc
    _ ≤ ∫⁻ y, ∑' k, A k y := by
      apply lintegral_mono
      intro y
      have h := mul_le_mul' (oneDimWeight_le_dyadic v y hv) (le_rfl : F (x - y) ≤ F (x - y))
      simpa only [ENNReal.tsum_mul_right, A] using h
    _ = ∑' k, ∫⁻ y, A k y := lintegral_tsum (fun k => (hA k).aemeasurable)
    _ ≤ ∑' k : ℕ, 8 * (ENNReal.ofReal (1 / 4 : ℝ)) ^ k * rationalMaximal F x :=
      ENNReal.tsum_le_tsum hterm
    _ ≤ ∑' k : ℕ, 8 * ((2 : ℝ≥0∞)⁻¹) ^ k * rationalMaximal F x := by
      have hquarter : ENNReal.ofReal (1 / 4 : ℝ) ≤ (2 : ℝ≥0∞)⁻¹ := by
        calc
          _ ≤ ENNReal.ofReal (1 / 2 : ℝ) := ENNReal.ofReal_le_ofReal (by norm_num)
          _ = _ := by
            rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num,
              ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
            norm_num
      gcongr with k
    _ = _ := by rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]; ring

end StrongSpherical.MaximalWeight
