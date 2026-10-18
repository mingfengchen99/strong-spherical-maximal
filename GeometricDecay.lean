import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-! # Summability of polynomially weighted dyadic decay -/
noncomputable section
namespace StrongSpherical.GeometricDecay

def dyadicWeight (n : ℕ) (ε : ℝ) (j : ℕ) : ℝ :=
  (1 + (j : ℝ)) ^ ((n : ℝ) / 2) * (2 : ℝ) ^ (-ε * (j : ℝ))

lemma dyadicWeight_nonneg (n : ℕ) (ε : ℝ) (j : ℕ) : 0 ≤ dyadicWeight n ε j :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by norm_num) _)

/-- A genuine positive exponential rate dominates this polynomial factor. -/
theorem summable_dyadicWeight (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    Summable (dyadicWeight n ε) := by
  let c : ℝ := (2 : ℝ) ^ (-ε)
  have hc : 0 < c := Real.rpow_pos_of_pos (by norm_num) _
  have hc1 : c < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hε)
  have hnorm : ‖c‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hc]; exact hc1
  have hs := summable_pow_mul_geometric_of_norm_lt_one n hnorm
  have hshift : Summable (fun j : ℕ => ((j + 1 : ℕ) : ℝ) ^ n * c ^ (j + 1)) :=
    (summable_nat_add_iff 1).mpr hs
  have hmajorant : Summable (fun j : ℕ => (1 + (j : ℝ)) ^ n * c ^ j) := by
    apply (hshift.mul_left c⁻¹).congr
    intro j
    simp only [Nat.cast_add, Nat.cast_one, pow_succ]
    rw [add_comm (1 : ℝ) (j : ℝ)]
    field_simp [hc.ne']
  have hexp (j : ℕ) : (2 : ℝ) ^ (-ε * (j : ℝ)) = c ^ j := by
    dsimp only [c]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  apply Summable.of_nonneg_of_le (dyadicWeight_nonneg n ε) _ hmajorant
  intro j
  dsimp only [dyadicWeight]
  rw [hexp]
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hc.le _)
  rw [← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le (by
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

end StrongSpherical.GeometricDecay
