import Definitions
import Mathlib.Topology.Algebra.Support

/-! # The normalized positive-frequency pieces in Section 6 -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace StrongSpherical.NormalFrequencyPieces
variable {n : ℕ}

/-- The normalization `2 / |S^(n-1)|` in (6.1), using the existing unnormalized
Euclidean surface measure. -/
def normalization (n : ℕ) : ℝ := 2 / (surfaceMeasure n univ).toReal

theorem normalization_pos (n : ℕ) [NeZero n] : 0 < normalization n := by
  apply div_pos (by norm_num : (0 : ℝ) < 2)
  exact ENNReal.toReal_pos
    (Measure.measure_univ_ne_zero.mpr (surfaceMeasure_ne_zero n)) (measure_ne_top _ _)

def normalizedCutoff (chi : Space n → ℂ) : Space n → ℂ :=
  fun u => (normalization n : ℂ) * chi u

/-- Formula (6.3), used for j ≥ 1 in the paper. -/
def dyadicPiece (chi : Space n → ℂ) (beta : ℝ → ℂ) (j : ℕ) : Space n → ℂ :=
  fun u => (normalization n : ℂ) * normalKernel chi beta ((2 : ℝ) ^ j) u

theorem dyadicPiece_eq_normalKernel (chi : Space n → ℂ) (beta : ℝ → ℂ) (j : ℕ) :
    dyadicPiece chi beta j = normalKernel (normalizedCutoff chi) beta ((2 : ℝ) ^ j) := by
  funext u
  unfold dyadicPiece normalizedCutoff normalKernel
  ring

theorem normalizedCutoff_contDiff (chi : Space n → ℂ) (hchi : ContDiff ℝ ∞ chi) :
    ContDiff ℝ ∞ (normalizedCutoff chi) := contDiff_const.mul hchi

theorem normalizedCutoff_compact (chi : Space n → ℂ) (hc : HasCompactSupport chi) :
    HasCompactSupport (normalizedCutoff chi) := hc.mul_left

theorem tsupport_normalizedCutoff_subset (chi : Space n → ℂ) :
    tsupport (normalizedCutoff chi) ⊆ tsupport chi := tsupport_mul_subset_right

end StrongSpherical.NormalFrequencyPieces
