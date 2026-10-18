import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Scalar complex approximate identities

The kernel may have complex values and need not be nonnegative.  A change of
variables keeps the integrable kernel fixed, so dominated convergence applies
against every bounded continuous test function.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology

namespace StrongSpherical.ScalarApproximation

/-- Multiplicative change of variables for a positive scalar dilation. -/
theorem rescaled_integral_eq (a : ℝ) (ha : 0 < a) (k g : ℝ → ℂ) :
    (∫ t : ℝ, (a : ℂ) * k (a * t) * g t) = ∫ s : ℝ, k s * g (s / a) := by
  have harg : (fun t : ℝ => k (a * t) * g t) =
      fun t : ℝ => k (a * t) * g ((a * t) / a) := by
    funext t
    rw [mul_div_cancel_left₀ t ha.ne']
  calc
    _ = (a : ℂ) * ∫ t : ℝ, k (a * t) * g t := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with t
      ring
    _ = (a : ℂ) * ∫ t : ℝ, k (a * t) * g ((a * t) / a) := by rw [harg]
    _ = (a : ℂ) * (|a⁻¹| • ∫ s : ℝ, k s * g (s / a)) := by
      rw [Measure.integral_comp_mul_left (fun s : ℝ => k s * g (s / a)) a]
    _ = _ := by
      rw [abs_of_pos (inv_pos.mpr ha), Complex.real_smul, Complex.ofReal_inv,
        ← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr ha.ne'), one_mul]

/-- For positive scales whose inverses tend to zero, a complex integrable
kernel converges against every bounded continuous test function. -/
theorem positive_scales_tendsto (a : ℕ → ℝ) (ha : ∀ J, 0 < a J)
    (hinv : Tendsto (fun J => (a J)⁻¹) atTop (𝓝 (0 : ℝ)))
    (k : ℝ → ℂ) (hk : Integrable k) (g : ℝ → ℂ) (hg : Continuous g)
    (hbounded : ∃ B : ℝ, ∀ t, ‖g t‖ ≤ B) :
    Tendsto (fun J : ℕ => ∫ t : ℝ, (a J : ℂ) * k (a J * t) * g t)
      atTop (𝓝 ((∫ t : ℝ, k t) * g 0)) := by
  obtain ⟨B, hB⟩ := hbounded
  have hlim : ∀ s : ℝ,
      Tendsto (fun J : ℕ => k s * g (s / a J)) atTop (𝓝 (k s * g 0)) := by
    intro s
    have hs : Tendsto (fun J : ℕ => s / a J) atTop (𝓝 (0 : ℝ)) := by
      simpa only [div_eq_mul_inv, mul_zero] using tendsto_const_nhds.mul hinv
    exact tendsto_const_nhds.mul (hg.continuousAt.tendsto.comp hs)
  have hdc := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure ℝ)) (F := fun J s => k s * g (s / a J))
    (f := fun s => k s * g 0) (fun s => ‖k s‖ * B)
    (fun J => hk.aestronglyMeasurable.mul
      (hg.comp (continuous_id.div_const (a J))).aestronglyMeasurable)
    (hk.norm.mul_const B)
    (fun J => Filter.Eventually.of_forall fun s => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _))
    (Filter.Eventually.of_forall hlim)
  simp_rw [rescaled_integral_eq _ (ha _)]
  simpa only [integral_mul_const] using hdc

/-- The dyadic complex approximate identity, normalized to have mass one. -/
theorem dyadic_tendsto (k : ℝ → ℂ) (hk : Integrable k) (hmass : (∫ t, k t) = 1)
    (g : ℝ → ℂ) (hg : Continuous g) (hc : HasCompactSupport g) :
    Tendsto (fun J : ℕ => ∫ t : ℝ,
      (((2 : ℝ) ^ J : ℝ) : ℂ) * k ((2 : ℝ) ^ J * t) * g t)
      atTop (𝓝 (g 0)) := by
  have hinv : Tendsto (fun J : ℕ => ((2 : ℝ) ^ J)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    simpa only [inv_pow] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1))
  simpa only [hmass, one_mul] using positive_scales_tendsto
    (fun J => (2 : ℝ) ^ J) (fun J => pow_pos (by norm_num) J) hinv
    k hk g hg (hc.exists_bound_of_continuous hg)

end StrongSpherical.ScalarApproximation
