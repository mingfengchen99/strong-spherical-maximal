import EllipsoidGraph
import Mathlib.Topology.Bases
import Mathlib.Topology.DenseEmbedding

/-! # Measurable linearization of a compact continuous family -/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology
namespace StrongSpherical.MaximalLinearization

variable {X P : Type*} [MeasurableSpace X] {μ : Measure X}

/-- A factor-two measurable selector is enough for an L² estimate. It avoids
requiring attainment of a countable supremum. -/
theorem exists_countable_selector (A : ℕ → X → ℂ)
    (hA : ∀ k, Measurable (A k))
    (hfinite : ∀ x, (⨆ k, ‖A k x‖ₑ) ≠ ∞) :
    ∃ j : X → ℕ, Measurable j ∧ ∀ x, (⨆ k, ‖A k x‖ₑ) ≤ 2 * ‖A (j x) x‖ₑ := by
  classical
  let M : X → ℝ≥0∞ := fun x => ⨆ k, ‖A k x‖ₑ
  have hM : Measurable M := Measurable.iSup (fun k => (hA k).enorm)
  let p : X → ℕ → Prop := fun x k => M x ≤ 2 * ‖A k x‖ₑ
  have hp : ∀ x, ∃ k, p x k := by
    intro x
    by_cases hz : M x = 0
    · exact ⟨0, by simp [p, hz]⟩
    · obtain ⟨k, hk⟩ := (lt_iSup_iff).mp (ENNReal.half_lt_self hz (hfinite x))
      exact ⟨k, (ENNReal.div_le_iff' (by norm_num) (by norm_num)).mp hk.le⟩
  refine ⟨fun x => Nat.find (hp x), measurable_find hp (fun k => ?_), ?_⟩
  · exact measurableSet_le hM (measurable_const.mul (hA k).enorm)
  · intro x
    exact Nat.find_spec (hp x)

theorem eLpNorm_iSup_le_of_selections (A : ℕ → X → ℂ)
    (hA : ∀ k, Measurable (A k))
    (hfinite : ∀ x, (⨆ k, ‖A k x‖ₑ) ≠ ∞) (B : ℝ≥0∞)
    (hselect : ∀ j : X → ℕ, Measurable j → eLpNorm (fun x => A (j x) x) 2 μ ≤ B) :
    eLpNorm (fun x => ⨆ k, ‖A k x‖ₑ) 2 μ ≤ 2 * B := by
  have h2 : ‖(2 : ℂ)‖ₑ = 2 := by rw [← ofReal_norm]; norm_num
  obtain ⟨j, hj, hbound⟩ := exists_countable_selector A hA hfinite
  calc
    _ ≤ eLpNorm ((2 : ℂ) • (fun x => A (j x) x)) 2 μ := by
      apply eLpNorm_mono_enorm
      intro x
      simpa only [enorm_eq_self, Pi.smul_apply, smul_eq_mul, enorm_mul, h2] using hbound x
    _ = 2 * eLpNorm (fun x => A (j x) x) 2 μ := by
      rw [eLpNorm_const_smul]
      simp only [h2]
    _ ≤ 2 * B := mul_le_mul_right (hselect j hj) _

variable [TopologicalSpace P] [CompactSpace P] [SeparableSpace P] [Nonempty P]

/-- A continuous compact parameter family has the same pointwise supremum
on a dense sequence, and the resulting maximal function is measurable. -/
theorem exists_dense_maximal_representation (A : P → X → ℂ)
    (hmeas : ∀ p, Measurable (A p)) (hcont : ∀ x, Continuous (fun p => A p x)) :
    ∃ d : ℕ → P, DenseRange d ∧
      (∀ x, (⨆ p, ‖A p x‖ₑ) = ⨆ k, ‖A (d k) x‖ₑ) ∧
      Measurable (fun x => ⨆ p, ‖A p x‖ₑ) ∧
      (∀ x, (⨆ k, ‖A (d k) x‖ₑ) ≠ ∞) := by
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq (α := P)
  have heq : ∀ x, (⨆ p, ‖A p x‖ₑ) = ⨆ k, ‖A (d k) x‖ₑ := by
    intro x
    apply le_antisymm
    · apply iSup_le
      intro p
      exact hd.induction_on p (isClosed_le (hcont x).enorm continuous_const)
        (fun k => le_iSup (fun k => ‖A (d k) x‖ₑ) k)
    · exact iSup_le (fun k => le_iSup (fun p => ‖A p x‖ₑ) (d k))
  refine ⟨d, hd, heq, ?_, ?_⟩
  · have hh := Measurable.iSup (fun k => (hmeas (d k)).enorm)
    simpa only [← heq] using hh
  · intro x
    obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn (hcont x).continuousOn
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    apply iSup_le
    intro k
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hB (d k) (mem_univ _))

/-- Linearized estimates uniform over measurable parameter selections imply
the full compact-parameter maximal estimate. -/
theorem compact_maximal_L2 (A : P → X → ℂ)
    (hmeas : ∀ p, Measurable (A p)) (hcont : ∀ x, Continuous (fun p => A p x))
    [MeasurableSpace P] [BorelSpace P] (B : ℝ≥0∞)
    (hselect : ∀ r : X → P, Measurable r → eLpNorm (fun x => A (r x) x) 2 μ ≤ B) :
    Measurable (fun x => ⨆ p, ‖A p x‖ₑ) ∧
      eLpNorm (fun x => ⨆ p, ‖A p x‖ₑ) 2 μ ≤ 2 * B := by
  obtain ⟨d, _, heq, hm, hf⟩ := exists_dense_maximal_representation A hmeas hcont
  refine ⟨hm, ?_⟩
  simp only [heq]
  apply eLpNorm_iSup_le_of_selections (fun k => A (d k)) (fun k => hmeas (d k)) hf B
  intro j hj
  exact hselect (fun x => d (j x)) ((measurable_of_countable d).comp hj)

end StrongSpherical.MaximalLinearization
