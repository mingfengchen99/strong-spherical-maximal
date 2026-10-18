import DilationL2

/-! # The relative scales used in the low and high frequency kernel estimates -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace StrongSpherical.DyadicKernelScales
variable {n : ℕ}

def epsilon (M : ℕ) : ℝ := (2 : ℝ) ^ (-(M : ℤ))
def smallRadii (M : ℕ) (k : Fin n → ℤ) : Radii n :=
  DyadicRadii.scales (fun i => k i - (M : ℤ))
def largeRadii (M : ℕ) (k : Fin n → ℤ) : Radii n :=
  DyadicRadii.scales (fun i => k i + (M : ℤ))

theorem epsilon_pos (M : ℕ) : 0 < epsilon M := zpow_pos (by norm_num) _

theorem epsilon_le_one (M : ℕ) : epsilon M ≤ 1 := by
  simpa only [epsilon, zpow_zero] using
    zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show -(M : ℤ) ≤ 0 by omega)

theorem smallRadii_apply (M : ℕ) (k : Fin n → ℤ) (i : Fin n) :
    (smallRadii M k).1 i = (2 : ℝ) ^ k i * epsilon M := by
  simp only [smallRadii, DyadicRadii.scales_apply, sub_eq_add_neg,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), epsilon]

theorem largeRadii_apply (M : ℕ) (k : Fin n → ℤ) (i : Fin n) :
    (largeRadii M k).1 i = (2 : ℝ) ^ k i * (2 : ℝ) ^ (M : ℤ) := by
  simp only [largeRadii, DyadicRadii.scales_apply,
    zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]

theorem small_relative_eq (M : ℕ) (k : Fin n → ℤ) (t : Radii n) (i : Fin n) :
    (smallRadii M k).1 i / (DyadicRadii.rectangle k t).1 i = epsilon M / t.1 i := by
  rw [smallRadii_apply, DyadicRadii.rectangle_apply]
  field_simp [ne_of_gt (zpow_pos (by norm_num : (0 : ℝ) < 2) (k i)), ne_of_gt (t.2 i)]

theorem large_relative_eq (M : ℕ) (k : Fin n → ℤ) (t : Radii n) (i : Fin n) :
    (DyadicRadii.rectangle k t).1 i / (largeRadii M k).1 i = epsilon M * t.1 i := by
  rw [largeRadii_apply, DyadicRadii.rectangle_apply]
  simp only [epsilon, zpow_neg]
  field_simp [ne_of_gt (zpow_pos (by norm_num : (0 : ℝ) < 2) (k i)),
    ne_of_gt (zpow_pos (by norm_num : (0 : ℝ) < 2) (M : ℤ))]

theorem small_relative_bounds (M : ℕ) (k : Fin n → ℤ) (t : Radii n)
    (ht : t ∈ localRadii n) (i : Fin n) :
    epsilon M / 2 ≤ (smallRadii M k).1 i / (DyadicRadii.rectangle k t).1 i ∧
      (smallRadii M k).1 i / (DyadicRadii.rectangle k t).1 i ≤ epsilon M := by
  rw [small_relative_eq]
  have heps := (epsilon_pos M).le
  constructor
  · apply (le_div_iff₀ (t.2 i)).mpr
    nlinarith [(ht i).2]
  · apply (div_le_iff₀ (t.2 i)).mpr
    nlinarith [(ht i).1]

theorem large_relative_le (M : ℕ) (k : Fin n → ℤ) (t : Radii n)
    (ht : t ∈ localRadii n) (i : Fin n) :
    (DyadicRadii.rectangle k t).1 i / (largeRadii M k).1 i ≤ 2 * epsilon M := by
  rw [large_relative_eq]
  nlinarith [(ht i).2, epsilon_pos M]

def frequencyGrowth (d M : ℕ) : ℝ := (1 + (M : ℝ)) ^ ((d : ℝ) / 2)

theorem frequencyGrowth_nonneg (d M : ℕ) : 0 ≤ frequencyGrowth d M :=
  Real.rpow_nonneg (by positivity) _

theorem frequencyGrowth_mono_dimension {m d : ℕ} (hmd : m ≤ d) (M : ℕ) :
    frequencyGrowth m M ≤ frequencyGrowth d M := by
  apply Real.rpow_le_rpow_of_exponent_le (le_add_of_nonneg_right (Nat.cast_nonneg M))
  have h : (m : ℝ) ≤ d := by exact_mod_cast hmd
  linarith

end StrongSpherical.DyadicKernelScales
