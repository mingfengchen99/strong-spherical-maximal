import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! # The exact radial substitution t = r² - 1 -/
noncomputable section
open MeasureTheory Set
namespace StrongSpherical.QuadraticRadialChange

/-- The factor 1/2 and the power n-2 are the actual Jacobian of t=r²-1.
Vanishing at radius zero permits extension to all real t without an indicator. -/
theorem integral_quadratic (n : ℕ) (hn : 2 ≤ n) (k A : ℝ → ℂ) (hA : A 0 = 0) :
    (∫ r in Ioi (0 : ℝ), ((r ^ (n - 1) : ℝ) : ℂ) * k (r ^ 2 - 1) * A r) =
      ∫ t, k t * ((1 / 2 : ℂ) *
        ((Real.sqrt (t + 1) ^ (n - 2) : ℝ) : ℂ) * A (Real.sqrt (t + 1))) := by
  let G : ℝ → ℂ := fun s => (1 / 2 : ℂ) *
    ((Real.sqrt s ^ (n - 2) : ℝ) : ℂ) * k (s - 1) * A (Real.sqrt s)
  have hchange := integral_comp_rpow_Ioi_of_pos (g := G)
    (by norm_num : (0 : ℝ) < 2)
  have heq : (∫ r in Ioi (0 : ℝ),
      (2 * r ^ ((2 : ℝ) - 1)) • G (r ^ (2 : ℝ))) =
      ∫ r in Ioi (0 : ℝ), ((r ^ (n - 1) : ℝ) : ℂ) * k (r ^ 2 - 1) * A r := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hs : Real.sqrt (r ^ 2) = r := Real.sqrt_sq hr.le
    have hn' : n - 1 = (n - 2) + 1 := by omega
    norm_num only [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
      Real.rpow_two]
    dsimp only [G]
    rw [hs, hn', pow_succ, Complex.real_smul]
    push_cast
    ring
  rw [heq] at hchange
  rw [hchange]
  have hfull : (∫ s in Ioi (0 : ℝ), G s) = ∫ s, G s := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro s hs
    have hs' : s ≤ 0 := le_of_not_gt hs
    simp only [G, Real.sqrt_eq_zero_of_nonpos hs', hA, mul_zero]
  rw [hfull, ← integral_add_right_eq_self G (1 : ℝ)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun t => by
    dsimp only [G]
    rw [add_sub_cancel_right]
    ring

end StrongSpherical.QuadraticRadialChange
