import EllipsoidGraph
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # Finite smooth coordinate patches for the annular cutoff -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff Manifold
namespace StrongSpherical.EllipsoidPatches
variable {n : ℕ}

abbrev PatchIndex (n : ℕ) := Fin n × Bool

def patchThreshold (n : ℕ) : ℝ := 1 / (4 * ((n : ℝ) + 1))

theorem patchThreshold_pos (n : ℕ) : 0 < patchThreshold n := by
  unfold patchThreshold
  positivity

def patchOpen (n : ℕ) (j : PatchIndex n) : Set (Space n) :=
  if j.2 then {u | patchThreshold n < u j.1} else {u | u j.1 < -patchThreshold n}

theorem isOpen_patchOpen (n : ℕ) (j : PatchIndex n) : IsOpen (patchOpen n j) := by
  unfold patchOpen
  split_ifs <;> exact isOpen_lt (by fun_prop) (by fun_prop)

theorem exists_large_coordinate (u : Space n) (hu : (1 / 2 : ℝ) ≤ ‖u‖) :
    ∃ j : Fin n, patchThreshold n < |u j| := by
  by_contra! hn
  have hc := patchThreshold_pos n
  have hsum : (∑ j : Fin n, (u j) ^ 2) ≤ (n : ℝ) * (patchThreshold n) ^ 2 := by
    calc
      _ ≤ ∑ _j : Fin n, (patchThreshold n) ^ 2 := Finset.sum_le_sum (fun j _ => by
        nlinarith [hn j, sq_abs (u j), abs_nonneg (u j)])
      _ = _ := by simp
  have hsmall : (n : ℝ) * (patchThreshold n) ^ 2 < 1 / 4 := by
    have hd : 0 < (n : ℝ) + 1 := by positivity
    have he : (n : ℝ) * (patchThreshold n) ^ 2 = (n : ℝ) / (16 * ((n : ℝ) + 1) ^ 2) := by
      unfold patchThreshold
      field_simp [ne_of_gt hd]
      ring
    rw [he]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 16 * ((n : ℝ) + 1) ^ 2)).2
    nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]
  rw [← norm_sq_eq_sum_coordinates] at hsum
  nlinarith [norm_nonneg u]

theorem annulus_subset_patch_cover :
    {u : Space n | (1 / 2 : ℝ) ≤ ‖u‖} ⊆ ⋃ j : PatchIndex n, patchOpen n j := by
  intro u hu
  obtain ⟨j, hj⟩ := exists_large_coordinate u hu
  by_cases hsign : 0 ≤ u j
  · exact mem_iUnion_of_mem (j, true) (by simpa [patchOpen, abs_of_nonneg hsign] using hj)
  · exact mem_iUnion_of_mem (j, false) (by
      have hh : u j < 0 := lt_of_not_ge hsign
      have hj' : patchThreshold n < -u j := by simpa only [abs_of_neg hh] using hj
      simp only [patchOpen, Bool.false_eq_true, ↓reduceIte, mem_setOf_eq]
      linarith)

/-- The original annular cutoff decomposes as a finite sum of smooth cutoffs,
each supported away from zero in one signed coordinate. -/
theorem exists_finite_patch_decomposition (chi : Space n → ℂ) (hchi : ContDiff ℝ ∞ chi)
    (hcompact : HasCompactSupport chi)
    (hsupport : tsupport chi ⊆ {u | (1 / 2 : ℝ) ≤ ‖u‖ ∧ ‖u‖ ≤ 2}) :
    ∃ a : PatchIndex n → Space n → ℂ,
      (∀ u, chi u = ∑ j, a j u) ∧
      (∀ j, ContDiff ℝ ∞ (a j)) ∧
      (∀ j, HasCompactSupport (a j)) ∧
      (∀ j, Function.support (a j) ⊆ {u | ‖u‖ ≤ 2}) ∧
      (∀ j, Function.support (a j) ⊆ patchOpen n j) := by
  classical
  obtain ⟨p, hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate (I := 𝓘(ℝ, Space n))
    (isClosed_tsupport chi) (patchOpen n) (isOpen_patchOpen n)
    (fun u hu => annulus_subset_patch_cover (hsupport hu).1)
  let a : PatchIndex n → Space n → ℂ := fun j u => chi u * (p j u : ℂ)
  refine ⟨a, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    by_cases hu : u ∈ tsupport chi
    · have hh := p.sum_eq_one hu
      rw [finsum_eq_sum_of_fintype] at hh
      dsimp only [a]
      rw [← Finset.mul_sum, ← Complex.ofReal_sum, hh, Complex.ofReal_one, mul_one]
    · have hz := image_eq_zero_of_notMem_tsupport hu
      simp [a, hz]
  · intro j
    exact hchi.mul (Complex.ofRealCLM.contDiff.comp (p j).contMDiff.contDiff)
  · intro j
    exact hcompact.mul_right
  · intro j u hu
    have hne : chi u ≠ 0 := by
      intro hz
      exact hu (by simp [a, hz])
    exact (hsupport (subset_tsupport chi hne)).2
  · intro j u hu
    apply hp j
    apply subset_tsupport (p j)
    intro hz
    exact hu (by simp [a, hz])

end StrongSpherical.EllipsoidPatches
