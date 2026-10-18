import SphericalLp
import SphericalLInfinity

/-! # Theorem 1.1: the exact target stated in Definitions.lean

The finite exponents use the proved normal-frequency decomposition, actual
piece estimates, interpolation, and summation. The exponent infinity uses
the mass-one spherical average. All original definitions remain unchanged.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal CompactlySupported

namespace StrongSpherical

/-- Theorem 1.1, with the exact original quantifiers and spherical measure. -/
theorem main_theorem : MainTheorem := by
  intro n hn p hp
  by_cases htop : p = ∞
  · subst p
    exact SphericalLInfinity.strongSphericalBound_top n (by omega)
  · have hcrit : 0 ≤ InterpolationParameters.critical n :=
      (zero_lt_one.trans (SphericalLp.critical_gt_one n hn)).le
    have hp' : ENNReal.ofReal (InterpolationParameters.critical n) < p := hp
    have hreal : InterpolationParameters.critical n < p.toReal :=
      (ENNReal.ofReal_lt_iff_lt_toReal hcrit htop).mp hp'
    have h := SphericalLp.strongSphericalBound_finite n hn p.toReal hreal
    rw [ENNReal.ofReal_toReal htop] at h
    exact h

/-- The sharp strong spherical maximal inequality, including p = infinity. -/
theorem strong_spherical_maximal_bound (n : ℕ) (hn : 4 ≤ n) (p : ℝ≥0∞)
    (hp : criticalExponent n < p) :
    ∃ C : ℝ≥0, ∀ f : C_c(Space n, ℂ),
      AEMeasurable (strongSphericalMaximal (f : Space n → ℂ)) volume ∧
        eLpNorm (strongSphericalMaximal (f : Space n → ℂ)) p volume ≤
          (C : ℝ≥0∞) * eLpNorm (f : Space n → ℂ) p volume :=
  main_theorem n hn p hp

end StrongSpherical
