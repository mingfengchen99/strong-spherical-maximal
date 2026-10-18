import DyadicKernelScales

/-! # Numerical constants in the bounded-to-arbitrary-radii estimate -/
noncomputable section
namespace StrongSpherical.Lemma14Constants
open DyadicKernelScales

theorem frequencyGrowth_sq (d M : ℕ) :
    frequencyGrowth d M ^ 2 = (1 + (M : ℝ)) ^ d := by
  rw [frequencyGrowth, ← Real.rpow_natCast _ 2,
    ← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 + (M : ℝ))]
  rw [show (d : ℝ) / 2 * (2 : ℕ) = (d : ℝ) by push_cast; ring, Real.rpow_natCast]

theorem sqrt_overlap_le (d M : ℕ) :
    Real.sqrt (((2 * M + 2) ^ d : ℕ) : ℝ) ≤ (2 : ℝ) ^ d * frequencyGrowth d M := by
  have hg := frequencyGrowth_nonneg d M
  have hp : 1 ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
  have hsq : (2 : ℝ) ^ d ≤ ((2 : ℝ) ^ d) ^ 2 := by nlinarith
  apply (Real.sqrt_le_iff).mpr
  refine ⟨mul_nonneg (by positivity) hg, ?_⟩
  rw [mul_pow, frequencyGrowth_sq]
  have he : (((2 * M + 2) ^ d : ℕ) : ℝ) = (2 : ℝ) ^ d * (1 + (M : ℝ)) ^ d := by
    push_cast
    rw [← mul_pow]
    congr 1
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_right hsq (by positivity)

theorem frequencyGrowth_zero (M : ℕ) : frequencyGrowth 0 M = 1 := by
  simp [frequencyGrowth]

end StrongSpherical.Lemma14Constants
