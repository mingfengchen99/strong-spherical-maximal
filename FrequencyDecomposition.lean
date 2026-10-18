import Definitions
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Scalar frequency symbols for Section 5.2

This file proves the algebraic decomposition (5.13), the absorption of low
frequencies into high frequencies, and the middle-frequency support (5.14).
The symbols are actual functions of the Fourier variable. Their realization
as bounded Fourier multiplier operators and the Plancherel overlap estimate
are separate results, not assumptions or conclusions of this file.
-/

noncomputable section

open Set
open scoped BigOperators

namespace StrongSpherical.FrequencyDecomposition

/-- The pointwise properties of the real cutoff used in Section 5.2. -/
structure CutoffControl (theta : ℝ → ℝ) : Prop where
  nonneg : ∀ t, 0 ≤ theta t
  le_one : ∀ t, theta t ≤ 1
  eq_one : ∀ t, |t| ≤ 1 → theta t = 1
  support_subset : Function.support theta ⊆ Icc (-2) 2

variable {d : ℕ} {theta : ℝ → ℝ}

/-- The low-frequency cutoff in one coordinate. -/
def lowCoordinate (theta : ℝ → ℝ) (M : ℕ) (k : ℤ) (t : ℝ) : ℝ :=
  theta ((2 : ℝ) ^ (k + (M : ℤ)) * t)

/-- The high-frequency truncation in one coordinate. -/
def highCoordinate (theta : ℝ → ℝ) (M : ℕ) (k : ℤ) (t : ℝ) : ℝ :=
  theta ((2 : ℝ) ^ (k - (M : ℤ)) * t)

/-- The symbol of the middle-frequency operator `P_k`. -/
def middle (theta : ℝ → ℝ) (M : ℕ) (k : Fin d → ℤ) (xi : Space d) : ℝ :=
  ∏ i, (highCoordinate theta M (k i) (xi i) - lowCoordinate theta M (k i) (xi i))

/-- The symbol of `L_{J,k}` for a subset of the coordinates. -/
def lowSubset (theta : ℝ → ℝ) (M : ℕ) (k : Fin d → ℤ)
    (J : Finset (Fin d)) (xi : Space d) : ℝ :=
  ∏ i ∈ J, lowCoordinate theta M (k i) (xi i)

/-- The error symbol `(1 - ∏ H_i) ∏ (1 - L_i)` in (5.13). -/
def error (theta : ℝ → ℝ) (M : ℕ) (k : Fin d → ℤ) (xi : Space d) : ℝ :=
  (1 - ∏ i, highCoordinate theta M (k i) (xi i)) *
    ∏ i, (1 - lowCoordinate theta M (k i) (xi i))

/-- The inclusion-exclusion sum over nonempty low-frequency subsets. -/
def lowCorrection (theta : ℝ → ℝ) (M : ℕ) (k : Fin d → ℤ) (xi : Space d) : ℝ :=
  ∑ J ∈ (Finset.univ.powerset.erase ∅),
    (-1 : ℝ) ^ (J.card + 1) * lowSubset theta M k J xi

theorem cutoff_abs_le_two (h : CutoffControl theta) {t : ℝ} (ht : theta t ≠ 0) :
    |t| ≤ 2 := by
  exact abs_le.mpr (h.support_subset ht)

theorem lowCoordinate_nonneg (h : CutoffControl theta) (M : ℕ) (k : ℤ) (t : ℝ) :
    0 ≤ lowCoordinate theta M k t := h.nonneg _

theorem lowCoordinate_le_one (h : CutoffControl theta) (M : ℕ) (k : ℤ) (t : ℝ) :
    lowCoordinate theta M k t ≤ 1 := h.le_one _

theorem highCoordinate_nonneg (h : CutoffControl theta) (M : ℕ) (k : ℤ) (t : ℝ) :
    0 ≤ highCoordinate theta M k t := h.nonneg _

theorem highCoordinate_le_one (h : CutoffControl theta) (M : ℕ) (k : ℤ) (t : ℝ) :
    highCoordinate theta M k t ≤ 1 := h.le_one _

private theorem abs_dyadic_mul (k : ℤ) (t : ℝ) :
    |(2 : ℝ) ^ k * t| = (2 : ℝ) ^ k * |t| := by
  rw [abs_mul, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) k)]

/-- The high cutoff is identically one wherever the low cutoff is nonzero. -/
theorem highCoordinate_eq_one_of_low_ne_zero (h : CutoffControl theta)
    (M : ℕ) (hM : 3 ≤ M) (k : ℤ) (t : ℝ)
    (hl : lowCoordinate theta M k t ≠ 0) : highCoordinate theta M k t = 1 := by
  have hb : (2 : ℝ) ^ (k + (M : ℤ)) * |t| ≤ 2 := by
    simpa only [lowCoordinate, abs_dyadic_mul] using cutoff_abs_le_two h hl
  have hc : 2 * (2 : ℝ) ^ (k - (M : ℤ)) ≤ (2 : ℝ) ^ (k + (M : ℤ)) := by
    have hp := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (show k - (M : ℤ) + 1 ≤ k + (M : ℤ) by omega)
    simpa only [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, mul_comm] using hp
  have hm := mul_le_mul_of_nonneg_right hc (abs_nonneg t)
  have ha : (2 : ℝ) ^ (k - (M : ℤ)) * |t| ≤ 1 := by nlinarith
  exact h.eq_one _ (by simpa only [abs_dyadic_mul] using ha)

/-- Pointwise absorption `H_i L_i = L_i`. -/
theorem high_mul_low (h : CutoffControl theta) (M : ℕ) (hM : 3 ≤ M) (k : ℤ) (t : ℝ) :
    highCoordinate theta M k t * lowCoordinate theta M k t = lowCoordinate theta M k t := by
  by_cases hl : lowCoordinate theta M k t = 0
  · simp [hl]
  · rw [highCoordinate_eq_one_of_low_ne_zero h M hM k t hl, one_mul]

theorem coordinate_middle_eq (h : CutoffControl theta) (M : ℕ) (hM : 3 ≤ M)
    (k : ℤ) (t : ℝ) :
    highCoordinate theta M k t - lowCoordinate theta M k t =
      highCoordinate theta M k t * (1 - lowCoordinate theta M k t) := by
  rw [mul_sub, mul_one, high_mul_low h M hM]

theorem middle_eq_prod_high_mul (h : CutoffControl theta) (M : ℕ) (hM : 3 ≤ M)
    (k : Fin d → ℤ) (xi : Space d) :
    middle theta M k xi = (∏ i, highCoordinate theta M (k i) (xi i)) *
      ∏ i, (1 - lowCoordinate theta M (k i) (xi i)) := by
  simp only [middle, coordinate_middle_eq h M hM, Finset.prod_mul_distrib]

/-- The finite inclusion-exclusion identity, independent of the cutoff. -/
theorem prod_one_sub_add_correction (L : Fin d → ℝ) :
    (∏ i, (1 - L i)) +
      (∑ J ∈ (Finset.univ.powerset.erase ∅), (-1 : ℝ) ^ (J.card + 1) * ∏ i ∈ J, L i) = 1 := by
  classical
  have hp := Finset.prod_sub (fun _ : Fin d => (1 : ℝ)) L Finset.univ
  simp only [Finset.prod_const_one, mul_one] at hp
  have hs := Finset.sum_erase_add (s := Finset.univ.powerset)
    (f := fun J : Finset (Fin d) => (-1 : ℝ) ^ J.card * ∏ i ∈ J, L i)
    (by simp : ∅ ∈ Finset.univ.powerset)
  simp only [Finset.card_empty, pow_zero, Finset.prod_empty, mul_one] at hs
  have hn : (∑ J ∈ (Finset.univ.powerset.erase ∅),
      (-1 : ℝ) ^ (J.card + 1) * ∏ i ∈ J, L i) =
      -(∑ J ∈ (Finset.univ.powerset.erase ∅), (-1 : ℝ) ^ J.card * ∏ i ∈ J, L i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    rw [pow_succ]
    ring
  rw [hn]
  linarith

/-- The exact scalar symbol identity (5.13), including dimension zero. -/
theorem decomposition (h : CutoffControl theta) (M : ℕ) (hM : 3 ≤ M)
    (k : Fin d → ℤ) (xi : Space d) :
    1 = middle theta M k xi + lowCorrection theta M k xi + error theta M k xi := by
  rw [middle_eq_prod_high_mul h M hM]
  have hp := prod_one_sub_add_correction (fun i => lowCoordinate theta M (k i) (xi i))
  change 1 = _ + (∑ J ∈ (Finset.univ.powerset.erase ∅),
    (-1 : ℝ) ^ (J.card + 1) * ∏ i ∈ J, lowCoordinate theta M (k i) (xi i)) + _
  unfold error
  linarith

/-- A nonzero middle factor lies in the enlarged dyadic frequency band. -/
theorem coordinate_band (h : CutoffControl theta) (M : ℕ) (hM : 3 ≤ M)
    (k : ℤ) (t : ℝ)
    (hm : highCoordinate theta M k t - lowCoordinate theta M k t ≠ 0) :
    (2 : ℝ) ^ (-(M : ℤ)) ≤ (2 : ℝ) ^ k * |t| ∧
      (2 : ℝ) ^ k * |t| ≤ (2 : ℝ) ^ ((M : ℤ) + 1) := by
  have hh : highCoordinate theta M k t ≠ 0 := by
    intro he
    have hab := high_mul_low h M hM k t
    rw [he, zero_mul] at hab
    exact hm (by rw [he, ← hab, sub_self])
  have hl : lowCoordinate theta M k t ≠ 1 := by
    intro he
    have hab := high_mul_low h M hM k t
    rw [he, mul_one] at hab
    exact hm (by rw [hab, he, sub_self])
  have hlow : 1 < (2 : ℝ) ^ (k + (M : ℤ)) * |t| := by
    by_contra hn
    apply hl
    exact h.eq_one _ (by simpa only [abs_dyadic_mul] using (le_of_not_gt hn))
  have hhigh : (2 : ℝ) ^ (k - (M : ℤ)) * |t| ≤ 2 := by
    simpa only [highCoordinate, abs_dyadic_mul] using cutoff_abs_le_two h hh
  have hpos : 0 < (2 : ℝ) ^ (M : ℤ) := zpow_pos (by norm_num) _
  have hinv : (2 : ℝ) ^ (M : ℤ) * (2 : ℝ) ^ (-(M : ℤ)) = 1 := by
    rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    simp
  constructor
  · apply le_of_lt
    apply (mul_lt_mul_iff_right₀ hpos).mp
    rw [hinv]
    have hid : (2 : ℝ) ^ (M : ℤ) * ((2 : ℝ) ^ k * |t|) =
        (2 : ℝ) ^ (k + (M : ℤ)) * |t| := by
      rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      ring
    rwa [hid]
  · have hm' := mul_le_mul_of_nonneg_right hhigh hpos.le
    have hid : ((2 : ℝ) ^ (k - (M : ℤ)) * |t|) * (2 : ℝ) ^ (M : ℤ) =
        (2 : ℝ) ^ k * |t| := by
      rw [mul_right_comm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      simp
    rw [hid] at hm'
    simpa only [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, mul_comm] using hm'

/-- Support statement (5.14) for every coordinate of the actual middle symbol. -/
theorem middle_nonzero_band (h : CutoffControl theta) (M : ℕ) (hM : 3 ≤ M)
    (k : Fin d → ℤ) (xi : Space d) (hm : middle theta M k xi ≠ 0) (i : Fin d) :
    (2 : ℝ) ^ (-(M : ℤ)) ≤ (2 : ℝ) ^ (k i) * |xi i| ∧
      (2 : ℝ) ^ (k i) * |xi i| ≤ (2 : ℝ) ^ ((M : ℤ) + 1) := by
  apply coordinate_band h M hM
  exact (Finset.prod_ne_zero_iff.mp hm) i (Finset.mem_univ i)

theorem coordinate_middle_nonneg (h : CutoffControl theta) (M : ℕ) (hM : 3 ≤ M)
    (k : ℤ) (t : ℝ) :
    0 ≤ highCoordinate theta M k t - lowCoordinate theta M k t := by
  rw [coordinate_middle_eq h M hM]
  exact mul_nonneg (h.nonneg _) (sub_nonneg.mpr (h.le_one _))

theorem coordinate_middle_le_one (h : CutoffControl theta) (M : ℕ) (k : ℤ) (t : ℝ) :
    highCoordinate theta M k t - lowCoordinate theta M k t ≤ 1 := by
  have hhigh := h.le_one ((2 : ℝ) ^ (k - (M : ℤ)) * t)
  have hlow := h.nonneg ((2 : ℝ) ^ (k + (M : ℤ)) * t)
  unfold highCoordinate lowCoordinate
  linarith

/-- The absolute value of the middle symbol is at most one. -/
theorem abs_middle_le_one (h : CutoffControl theta) (M : ℕ) (hM : 3 ≤ M)
    (k : Fin d → ℤ) (xi : Space d) : |middle theta M k xi| ≤ 1 := by
  have hn : 0 ≤ middle theta M k xi :=
    Finset.prod_nonneg fun i _ => coordinate_middle_nonneg h M hM (k i) (xi i)
  rw [abs_of_nonneg hn]
  exact Finset.prod_le_one (fun i _ => coordinate_middle_nonneg h M hM (k i) (xi i))
    (fun i _ => coordinate_middle_le_one h M (k i) (xi i))

/-- The set of integer scales where a single middle-frequency factor is nonzero. -/
def coordinateActive (theta : ℝ → ℝ) (M : ℕ) (t : ℝ) : Set ℤ :=
  {k | highCoordinate theta M k t - lowCoordinate theta M k t ≠ 0}

/-- Any two active scales are separated by at most `2M + 1`. -/
theorem coordinate_active_span (h : CutoffControl theta) (M : ℕ) (hM : 3 ≤ M)
    (t : ℝ) {k l : ℤ} (hk : k ∈ coordinateActive theta M t)
    (hl : l ∈ coordinateActive theta M t) : k - l ≤ 2 * (M : ℤ) + 1 := by
  have hbk := coordinate_band h M hM k t hk
  have hbl := coordinate_band h M hM l t hl
  have hp : 0 ≤ (2 : ℝ) ^ (k - l) := (zpow_pos (by norm_num) _).le
  have hpow : (2 : ℝ) ^ (k - l - (M : ℤ)) ≤ (2 : ℝ) ^ ((M : ℤ) + 1) := by
    calc
      (2 : ℝ) ^ (k - l - (M : ℤ)) =
          (2 : ℝ) ^ (-(M : ℤ)) * (2 : ℝ) ^ (k - l) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        congr 1
        ring
      _ ≤ ((2 : ℝ) ^ l * |t|) * (2 : ℝ) ^ (k - l) :=
        mul_le_mul_of_nonneg_right hbl.1 hp
      _ = (2 : ℝ) ^ k * |t| := by
        rw [mul_right_comm, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        simp
      _ ≤ (2 : ℝ) ^ ((M : ℤ) + 1) := hbk.2
  have he := (zpow_le_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mp hpow
  omega

/-- The full set of active scales in one coordinate is finite. -/
theorem coordinateActive_finite (h : CutoffControl theta) (M : ℕ) (hM : 3 ≤ M)
    (t : ℝ) : (coordinateActive theta M t).Finite := by
  by_cases hn : (coordinateActive theta M t).Nonempty
  · obtain ⟨l, hl⟩ := hn
    apply (Set.finite_Icc (l - (2 * (M : ℤ) + 1)) (l + (2 * (M : ℤ) + 1))).subset
    intro k hk
    have hk' := coordinate_active_span h M hM t hk hl
    have hl' := coordinate_active_span h M hM t hl hk
    constructor <;> omega
  · rw [Set.not_nonempty_iff_eq_empty.mp hn]
    exact Set.finite_empty

/-- Every finite family of active scales has at most `2M + 2` members. -/
theorem coordinate_overlap_card (h : CutoffControl theta) (M : ℕ) (hM : 3 ≤ M)
    (t : ℝ) (S : Finset ℤ) (hS : ∀ k ∈ S, k ∈ coordinateActive theta M t) :
    S.card ≤ 2 * M + 2 := by
  classical
  by_cases hn : S.Nonempty
  · let a := S.min' hn
    have ha : a ∈ S := Finset.min'_mem S hn
    have hs : S ⊆ Finset.Icc a (a + (2 * (M : ℤ) + 1)) := by
      intro k hk
      have hka := coordinate_active_span h M hM t (hS k hk) (hS a ha)
      have hal : a ≤ k := Finset.min'_le S k hk
      exact Finset.mem_Icc.mpr ⟨hal, by omega⟩
    have hc := Finset.card_le_card hs
    rw [Int.card_Icc] at hc
    have hi : a + (2 * (M : ℤ) + 1) + 1 - a = (2 * M + 2 : ℕ) := by omega
    simpa only [hi, Int.toNat_natCast] using hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
    simp

/-- The cardinality bound for the entire one-coordinate overlap set. -/
theorem coordinateActive_card_le (h : CutoffControl theta) (M : ℕ) (hM : 3 ≤ M)
    (t : ℝ) : (coordinateActive_finite h M hM t).toFinset.card ≤ 2 * M + 2 := by
  apply coordinate_overlap_card h M hM t
  intro k hk
  exact (coordinateActive_finite h M hM t).mem_toFinset.mp hk

/-- A finite product of the genuine one-coordinate active scale sets. -/
def activeBox (h : CutoffControl theta) (M : ℕ) (hM : 3 ≤ M) (xi : Space d) :
    Finset (Fin d → ℤ) :=
  Fintype.piFinset (fun i => (coordinateActive_finite h M hM (xi i)).toFinset)

theorem mem_activeBox_iff (h : CutoffControl theta) (M : ℕ) (hM : 3 ≤ M)
    (xi : Space d) (k : Fin d → ℤ) :
    k ∈ activeBox h M hM xi ↔ middle theta M k xi ≠ 0 := by
  classical
  constructor
  · intro hk
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact (coordinateActive_finite h M hM (xi i)).mem_toFinset.mp
      (Fintype.mem_piFinset.mp hk i)
  · intro hk
    apply Fintype.mem_piFinset.mpr
    intro i
    apply (coordinateActive_finite h M hM (xi i)).mem_toFinset.mpr
    exact (Finset.prod_ne_zero_iff.mp hk) i (Finset.mem_univ i)

/-- The number of nonzero middle symbols at any fixed frequency is at most `(2M+2)^d`. -/
theorem activeBox_card_le (h : CutoffControl theta) (M : ℕ) (hM : 3 ≤ M)
    (xi : Space d) : (activeBox h M hM xi).card ≤ (2 * M + 2) ^ d := by
  unfold activeBox
  rw [Fintype.card_piFinset]
  calc
    (∏ i : Fin d, (coordinateActive_finite h M hM (xi i)).toFinset.card) ≤
        ∏ _i : Fin d, (2 * M + 2) :=
      Finset.prod_le_prod' fun i _ => coordinateActive_card_le h M hM (xi i)
    _ = (2 * M + 2) ^ d := by simp

/-- The pointwise squared-symbol overlap bound used before Plancherel. -/
theorem tsum_middle_sq_le (h : CutoffControl theta) (M : ℕ) (hM : 3 ≤ M)
    (xi : Space d) :
    (∑' k : Fin d → ℤ, |middle theta M k xi| ^ 2) ≤ ((2 * M + 2) ^ d : ℕ) := by
  classical
  have hz : ∀ k ∉ activeBox h M hM xi, |middle theta M k xi| ^ 2 = 0 := by
    intro k hk
    have hm : middle theta M k xi = 0 := by
      by_contra hn
      exact hk ((mem_activeBox_iff h M hM xi k).mpr hn)
    simp [hm]
  rw [tsum_eq_sum hz]
  calc
    (∑ k ∈ activeBox h M hM xi, |middle theta M k xi| ^ 2) ≤
        ∑ _k ∈ activeBox h M hM xi, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k hk
      have ha := abs_middle_le_one h M hM k xi
      have hn := abs_nonneg (middle theta M k xi)
      nlinarith
    _ = (activeBox h M hM xi).card := by simp
    _ ≤ ((2 * M + 2) ^ d : ℕ) := by exact_mod_cast activeBox_card_le h M hM xi

end StrongSpherical.FrequencyDecomposition
