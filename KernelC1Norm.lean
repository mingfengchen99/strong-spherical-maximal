import MarginalC1

/-! # The global C¹ size of an actual compactly supported kernel -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace StrongSpherical.KernelC1Norm
variable {d : ℕ}

/-- The sup norm of the kernel plus the sup operator norm of its real derivative. -/
def c1Norm (K : Space d → ℂ) : ℝ :=
  sSup (Set.range (fun x => ‖K x‖)) + sSup (Set.range (fun x => ‖fderiv ℝ K x‖))

theorem c1Norm_bounds (K : Space d → ℂ) (hK : ContDiff ℝ 1 K)
    (hc : HasCompactSupport K) :
    0 ≤ c1Norm K ∧ (∀ x, ‖K x‖ ≤ c1Norm K) ∧
      (∀ x, ‖fderiv ℝ K x‖ ≤ c1Norm K) := by
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hK.continuous
  obtain ⟨D, hD⟩ := (hc.fderiv ℝ).exists_bound_of_continuous (hK.continuous_fderiv one_ne_zero)
  have hb : BddAbove (Set.range (fun x => ‖K x‖)) := ⟨B, by rintro _ ⟨x, rfl⟩; exact hB x⟩
  have hd : BddAbove (Set.range (fun x => ‖fderiv ℝ K x‖)) :=
    ⟨D, by rintro _ ⟨x, rfl⟩; exact hD x⟩
  have hf : ∀ x, ‖K x‖ ≤ sSup (Set.range (fun x => ‖K x‖)) :=
    fun x => le_csSup hb (Set.mem_range_self x)
  have hg : ∀ x, ‖fderiv ℝ K x‖ ≤ sSup (Set.range (fun x => ‖fderiv ℝ K x‖)) :=
    fun x => le_csSup hd (Set.mem_range_self x)
  have hf0 := (norm_nonneg (K 0)).trans (hf 0)
  have hg0 := (norm_nonneg (fderiv ℝ K 0)).trans (hg 0)
  refine ⟨add_nonneg hf0 hg0, ?_, ?_⟩
  · intro x
    exact (hf x).trans (le_add_of_nonneg_right hg0)
  · intro x
    exact (hg x).trans (le_add_of_nonneg_left hf0)

end StrongSpherical.KernelC1Norm
