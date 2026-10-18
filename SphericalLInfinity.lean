import SphericalRegularity
import Mathlib.MeasureTheory.Measure.OpenPos

/-! # The genuine L∞ endpoint for normalized spherical averages -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology CompactlySupported

namespace StrongSpherical.SphericalLInfinity

/-- Lebesgue measure has full support, so a continuous function obeys its
essential bound at every point. This also covers an infinite essential bound. -/
theorem continuous_enorm_le_eLpNorm_top {n : ℕ} (f : Space n → ℂ)
    (hf : Continuous f) (x : Space n) : ‖f x‖ₑ ≤ eLpNorm f ∞ volume := by
  have hclosed : IsClosed {y : Space n | ‖f y‖ₑ ≤ eLpNorm f ∞ volume} :=
    isClosed_le hf.enorm continuous_const
  have hae : {y : Space n | ‖f y‖ₑ ≤ eLpNorm f ∞ volume} =ᵐ[volume] univ := by
    filter_upwards [enorm_ae_le_eLpNormEssSup f volume] with y hy
    apply propext
    exact ⟨fun _ => trivial, fun _ => by
      change ‖f y‖ₑ ≤ eLpNorm f ∞ volume
      simpa only [eLpNorm_exponent_top] using hy⟩
  have hall : {y : Space n | ‖f y‖ₑ ≤ eLpNorm f ∞ volume} = univ :=
    hclosed.ae_eq_univ_iff_eq.mp hae
  have hx : x ∈ (univ : Set (Space n)) := mem_univ x
  rwa [← hall] at hx

/-- Each average uses a probability measure, with no surface-area loss. -/
theorem sphericalAverage_enorm_le (n : ℕ) (hn : 1 ≤ n)
    (f : C_c(Space n, ℂ)) (r : Radii n) (x : Space n) :
    ‖sphericalAverage (f : Space n → ℂ) r x‖ₑ ≤ eLpNorm (f : Space n → ℂ) ∞ volume := by
  letI : NeZero n := ⟨ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)⟩
  rw [sphericalAverage_eq_sphere_integral (f : Space n → ℂ) f.continuous r x]
  calc
    _ ≤ ∫⁻ omega : UnitSphere n,
        ‖f (x - diagonalDilation r.1 omega)‖ₑ ∂sphereMeasure n :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ _omega : UnitSphere n,
        eLpNorm (f : Space n → ℂ) ∞ volume ∂sphereMeasure n :=
      lintegral_mono fun omega => continuous_enorm_le_eLpNorm_top
        (f : Space n → ℂ) f.continuous _
    _ = _ := by simp

theorem strongSphericalMaximal_le (n : ℕ) (hn : 1 ≤ n)
    (f : C_c(Space n, ℂ)) (x : Space n) :
    strongSphericalMaximal (f : Space n → ℂ) x ≤ eLpNorm (f : Space n → ℂ) ∞ volume := by
  unfold strongSphericalMaximal maximalOver
  refine iSup_le fun r => iSup_le fun _ => ?_
  exact sphericalAverage_enorm_le n hn f r x

theorem eLpNorm_strongSphericalMaximal_top_le (n : ℕ) (hn : 1 ≤ n)
    (f : C_c(Space n, ℂ)) :
    eLpNorm (strongSphericalMaximal (f : Space n → ℂ)) ∞ volume ≤
      eLpNorm (f : Space n → ℂ) ∞ volume := by
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  exact Filter.Eventually.of_forall fun x => by
    simpa only [enorm_eq_self] using strongSphericalMaximal_le n hn f x

/-- The actual target predicate at infinity, with the sharp constant one. -/
theorem strongSphericalBound_top (n : ℕ) (hn : 1 ≤ n) : StrongSphericalBound n ∞ := by
  refine ⟨1, fun f => ⟨(SphericalRegularity.measurable_strongSphericalMaximal n hn f).aemeasurable, ?_⟩⟩
  simpa only [ENNReal.coe_one, one_mul] using eLpNorm_strongSphericalMaximal_top_le n hn f

end StrongSpherical.SphericalLInfinity
