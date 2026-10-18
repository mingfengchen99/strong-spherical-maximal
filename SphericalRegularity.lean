import Definitions
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Semicontinuity.Basic

/-! # Regularity of the actual spherical maximal operator -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology CompactlySupported

namespace StrongSpherical.SphericalRegularity

/-- The actual pushed-forward spherical average is continuous in its center. -/
theorem continuous_sphericalAverage (n : ℕ) (hn : 1 ≤ n)
    (f : C_c(Space n, ℂ)) (r : Radii n) :
    Continuous (sphericalAverage (f : Space n → ℂ) r) := by
  letI : NeZero n := ⟨ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)⟩
  have hjoint : Continuous (Function.uncurry
      (fun (x : Space n) (omega : UnitSphere n) => f (x - diagonalDilation r.1 omega))) := by
    exact f.continuous.comp (continuous_fst.sub
      ((continuous_diagonalDilation r.1).comp (continuous_subtype_val.comp continuous_snd)))
  have h := continuous_parametric_integral_of_continuous
    (μ := sphereMeasure n) hjoint (isCompact_univ : IsCompact (univ : Set (UnitSphere n)))
  have heq : (fun x : Space n =>
      ∫ omega : UnitSphere n in univ, f (x - diagonalDilation r.1 omega) ∂sphereMeasure n) =
      sphericalAverage (f : Space n → ℂ) r := by
    funext x
    rw [setIntegral_univ]
    exact (sphericalAverage_eq_sphere_integral (f : Space n → ℂ) f.continuous r x).symm
  rw [heq] at h
  exact h

/-- An arbitrary supremum of continuous averages is lower semicontinuous. -/
theorem lowerSemicontinuous_strongSphericalMaximal (n : ℕ) (hn : 1 ≤ n)
    (f : C_c(Space n, ℂ)) :
    LowerSemicontinuous (strongSphericalMaximal (f : Space n → ℂ)) := by
  unfold strongSphericalMaximal maximalOver
  exact lowerSemicontinuous_biSup fun r _ =>
    (continuous_sphericalAverage n hn f r).enorm.lowerSemicontinuous

theorem measurable_strongSphericalMaximal (n : ℕ) (hn : 1 ≤ n)
    (f : C_c(Space n, ℂ)) :
    Measurable (strongSphericalMaximal (f : Space n → ℂ)) :=
  (lowerSemicontinuous_strongSphericalMaximal n hn f).measurable

end StrongSpherical.SphericalRegularity
