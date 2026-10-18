import NormalPieceSummation
import SphericalDomination
import SphericalRegularity
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-! # The strong spherical bound at every finite exponent in the sharp range -/
noncomputable section
open MeasureTheory
open scoped ENNReal CompactlySupported

namespace StrongSpherical.SphericalLp

/-- The real critical exponent is above one in the dimensions of the theorem. -/
theorem critical_gt_one (n : ℕ) (hn : 4 ≤ n) :
    1 < InterpolationParameters.critical n := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  unfold InterpolationParameters.critical
  apply (one_lt_div (show (0 : ℝ) < (n : ℝ) - 1 by linarith)).mpr
  linarith

/-- The actual spherical maximal function is bounded by the sum of the
actual pieces; the proved summation bound supplies a constant before f. -/
theorem strongSphericalBound_finite (n : ℕ) (hn : 4 ≤ n) (p : ℝ)
    (hp : InterpolationParameters.critical n < p) :
    StrongSphericalBound n (ENNReal.ofReal p) := by
  obtain ⟨C, _hC, hsum⟩ := NormalPieceSummation.uniform_pieceSum_Lp n hn p hp
  refine ⟨C.toNNReal, ?_⟩
  intro f
  have hf : MemLp (f : Space n → ℂ) (ENNReal.ofReal p) volume :=
    f.continuous.memLp_of_hasCompactSupport f.hasCompactSupport
  obtain ⟨_hmeas, hnorm⟩ := hsum f hf
  refine ⟨(SphericalRegularity.measurable_strongSphericalMaximal n (by omega) f).aemeasurable, ?_⟩
  change eLpNorm (strongSphericalMaximal (f : Space n → ℂ)) (ENNReal.ofReal p) volume ≤
    ENNReal.ofReal C * eLpNorm (f : Space n → ℂ) (ENNReal.ofReal p) volume
  apply le_trans _ hnorm
  apply eLpNorm_mono_enorm
  intro x
  simpa only [enorm_eq_self, NormalPieceSummation.pieceSum] using
    SphericalDomination.compact_strongSphericalMaximal_le_tsum n (by omega) f x

end StrongSpherical.SphericalLp
