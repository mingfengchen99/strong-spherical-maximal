import CoordinateSubsets
import DyadicKernelScales

/-! # Uniform lower-dimensional induction constants for all coordinate marginals -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace StrongSpherical.MarginalInduction
open CoordinateSubsets CoordinateMarginals DyadicKernelScales

def LocalKernelBound {d : ℕ} (K : Space d → ℂ) (A : ℝ) : Prop :=
  ∀ f : Space d → ℂ, MemLp f 2 volume →
    eLpNorm (localKernelMaximal K f) 2 volume ≤ ENNReal.ofReal A * eLpNorm f 2 volume

/-- Lemma 1.4 with explicit uniform bounds on the function and its true derivative. -/
def GlobalKernelBound (d : ℕ) (R C : ℝ) : Prop :=
  ∀ K : Space d → ℂ, ContDiff ℝ 1 K →
    Function.support K ⊆ MarginalEnergy.coordinateBox d R →
    ∀ A B : ℝ, 0 ≤ A → (∀ x, ‖K x‖ ≤ B) → (∀ x, ‖fderiv ℝ K x‖ ≤ B) →
    LocalKernelBound K A → ∀ M : ℕ, 3 ≤ M →
    ∀ f : Space d → ℂ, MemLp f 2 volume →
      eLpNorm (strongKernelMaximal K f) 2 volume ≤
        ENNReal.ofReal (C * (frequencyGrowth d M * A + epsilon M * B)) * eLpNorm f 2 volume

theorem strongKernelMaximal_zero_eq_local (K f : Space 0 → ℂ) :
    strongKernelMaximal K f = localKernelMaximal K f := by
  funext x
  apply le_antisymm
  · refine iSup_le fun r => iSup_le fun _ => ?_
    exact le_maximalOver _ _ _ (fun i => Fin.elim0 i)
  · exact maximalOver_mono (subset_univ _) _ x

theorem globalKernelBound_zero (R : ℝ) : GlobalKernelBound 0 R 1 := by
  intro K _ _ A B _ hb _ hl M _ f hf
  rw [strongKernelMaximal_zero_eq_local]
  refine (hl f hf).trans (mul_le_mul' ?_ le_rfl)
  apply ENNReal.ofReal_le_ofReal
  simp only [frequencyGrowth, Nat.cast_zero, zero_div, Real.rpow_zero, one_mul]
  have hB : 0 ≤ B := (norm_nonneg (K 0)).trans (hb 0)
  exact le_add_of_nonneg_right (mul_nonneg (epsilon_pos M).le hB)

theorem real_volume_coordinateCube (j : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    (volume : Measure (Space j)).real (coordinateCube j R) = (2 * R) ^ j := by
  rw [measureReal_def, coordinateCube_eq_coordinateBox, MarginalEnergy.volume_coordinateBox,
    ← ENNReal.ofReal_pow (by positivity : 0 ≤ 2 * R),
    ENNReal.toReal_ofReal (by positivity)]

theorem marginal_growth_le {m d j : ℕ} (hmd : m ≤ d) (hjd : j ≤ d)
    (R c D A B : ℝ) (hR : 1 ≤ R) (hc : 0 ≤ c) (hcD : c ≤ D)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (M : ℕ) :
    c * (frequencyGrowth m M * A + epsilon M * ((2 * R) ^ j * B)) ≤
      (D * (2 * R) ^ d) * (frequencyGrowth d M * A + epsilon M * B) := by
  have hp : 1 ≤ (2 * R) ^ d := one_le_pow₀ (by linarith)
  have hj : (2 * R) ^ j ≤ (2 * R) ^ d := pow_le_pow_right₀ (by linarith) hjd
  have hD : 0 ≤ D := hc.trans hcD
  have heps := (epsilon_pos M).le
  have hf := frequencyGrowth_nonneg d M
  have hfm := frequencyGrowth_nonneg m M
  have hfa : frequencyGrowth m M * A ≤ (2 * R) ^ d * (frequencyGrowth d M * A) := by
    exact (mul_le_mul_of_nonneg_right (frequencyGrowth_mono_dimension hmd M) hA).trans
      (le_mul_of_one_le_left (mul_nonneg hf hA) hp)
  have hfb : epsilon M * ((2 * R) ^ j * B) ≤ (2 * R) ^ d * (epsilon M * B) := by
    nlinarith [mul_le_mul_of_nonneg_right hj (mul_nonneg heps hB)]
  calc
    _ ≤ D * (frequencyGrowth m M * A + epsilon M * ((2 * R) ^ j * B)) :=
      mul_le_mul_of_nonneg_right hcD (by positivity)
    _ ≤ D * ((2 * R) ^ d * (frequencyGrowth d M * A + epsilon M * B)) :=
      mul_le_mul_of_nonneg_left (by nlinarith [hfa, hfb]) hD
    _ = _ := by ring

/-- One finite positive constant controls all the proper coordinate marginals,
including the scalar marginal, throughout the induction step. -/
theorem exists_uniform_marginal_bound (d : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (ih : ∀ m < d, ∃ c : ℝ, 0 < c ∧ GlobalKernelBound m R c) :
    ∃ D : ℝ, 0 < D ∧ ∀ I : Set (Fin d), Fintype.card I < d →
      ∀ K : Space d → ℂ, ContDiff ℝ 1 K →
        Function.support K ⊆ MarginalEnergy.coordinateBox d R →
      ∀ A B : ℝ, 0 ≤ A → (∀ x, ‖K x‖ ≤ B) → (∀ x, ‖fderiv ℝ K x‖ ≤ B) →
        LocalKernelBound K A → ∀ M : ℕ, 3 ≤ M →
      ∀ f : Space (Fintype.card I) → ℂ, MemLp f 2 volume →
        eLpNorm (strongKernelMaximal (subsetMarginal I K) f) 2 volume ≤
          ENNReal.ofReal (D * (frequencyGrowth d M * A + epsilon M * B)) * eLpNorm f 2 volume := by
  classical
  choose c hc hbound using fun m : Fin d => ih m.1 m.2
  let L : ℝ := 1 + ∑ m : Fin d, c m
  have hL : 0 < L := by
    have hs : 0 ≤ ∑ m : Fin d, c m := Finset.sum_nonneg fun m _ => (hc m).le
    dsimp [L]
    linarith
  have hcle : ∀ m : Fin d, c m ≤ L := by
    intro m
    have hs := Finset.single_le_sum (fun i _ => (hc i).le) (Finset.mem_univ m)
    dsimp [L]
    linarith
  refine ⟨L * (2 * R) ^ d, mul_pos hL (pow_pos (by linarith) _), ?_⟩
  intro I hI K hK hs A B hA hb hd hl M hM f hf
  let m : Fin d := ⟨Fintype.card I, hI⟩
  let j : ℕ := Fintype.card (↥(Iᶜ : Set (Fin d)))
  have hj : j ≤ d := by
    have he := Fintype.card_congr (subsetEnumeration I)
    simp only [Fintype.card_fin] at he
    dsimp [j]
    omega
  have hB : 0 ≤ B := (norm_nonneg (K 0)).trans (hb 0)
  have hnorm : ∀ x, ‖subsetMarginal I K x‖ ≤ (2 * R) ^ j * B := by
    intro x
    simpa only [real_volume_coordinateCube _ R (by linarith)] using
      norm_subsetMarginal_le I K hK R B hs hb x
  have hderiv : ∀ x, ‖fderiv ℝ (subsetMarginal I K) x‖ ≤ (2 * R) ^ j * B := by
    intro x
    simpa only [real_volume_coordinateCube _ R (by linarith)] using
      norm_fderiv_subsetMarginal_le I K hK R B hs hd x
  have hlocal : LocalKernelBound (subsetMarginal I K) A := fun g hg =>
    (subset_marginal_local_bound I K hK.continuous R (by linarith) hs
      (ENNReal.ofReal A) hl g hg).2
  have h := hbound m (subsetMarginal I K) (contDiff_subsetMarginal I K hK R hs)
    (subsetMarginal_support I K R hs) A ((2 * R) ^ j * B) hA hnorm hderiv hlocal M hM f hf
  refine h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
  exact marginal_growth_le (Nat.le_of_lt hI) hj R (c m) L A B hR
    (hc m).le (hcle m) hA hB M

end StrongSpherical.MarginalInduction
