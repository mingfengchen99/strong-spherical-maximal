import NormalPieceInterpolation
import GeometricDecay
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Summing all actual normal-frequency maximal pieces on the sharp Lᵖ range -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators
namespace StrongSpherical.NormalPieceSummation

/-- Positive powers preserve countable suprema, including infinite values. -/
theorem ennreal_rpow_iSup (F : ℕ → ℝ≥0∞) (p : ℝ) (hp : 0 < p) :
    (⨆ j, F j) ^ p = ⨆ j, F j ^ p := by
  apply le_antisymm
  · apply (ENNReal.rpow_le_rpow_iff (inv_pos.mpr hp)).mp
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hp.ne', ENNReal.rpow_one]
    apply iSup_le
    intro j
    have h := ENNReal.rpow_le_rpow (le_iSup (fun j => F j ^ p) j) (inv_nonneg.mpr hp.le)
    simpa only [← ENNReal.rpow_mul, mul_inv_cancel₀ hp.ne', ENNReal.rpow_one] using h
  · exact iSup_le fun j => ENNReal.rpow_le_rpow (le_iSup F j) hp.le

set_option maxHeartbeats 1000000 in
/-- Finite Minkowski followed by monotone convergence proves the countable
estimate directly for extended-valued positive functions. No pointwise
summability hypothesis is used. -/
theorem eLpNorm_tsum_le (X : Type*) [MeasurableSpace X] (μ : Measure X)
    (p : ℝ) (hp1 : 1 ≤ p) (G : ℕ → X → ℝ≥0∞) (hG : ∀ j, Measurable (G j))
    (c : ℕ → ℝ) (hc0 : ∀ j, 0 ≤ c j) (hc : Summable c) (F : ℝ≥0∞)
    (hbound : ∀ j, eLpNorm (G j) (ENNReal.ofReal p) μ ≤ ENNReal.ofReal (c j) * F) :
    eLpNorm (fun x => ∑' j, G j x) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (∑' j, c j) * F := by
  have hp : 0 < p := zero_lt_one.trans_le hp1
  have hpe : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp1
  let S : ℕ → X → ℝ≥0∞ := fun N x => ∑ j ∈ Finset.range N, G j x
  have hS (N : ℕ) : Measurable (S N) :=
    Finset.measurable_sum _ (fun j _ => hG j)
  have hSmono : Monotone S := by
    intro N M hNM x
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM) (fun _ _ _ => zero_le)
  have hfinite (N : ℕ) : eLpNorm (S N) (ENNReal.ofReal p) μ ≤
      ENNReal.ofReal (∑' j, c j) * F := by
    have hM := eLpNorm_sum_le (f := G) (s := Finset.range N) (μ := μ)
      (p := ENNReal.ofReal p) (fun j _ => (hG j).aestronglyMeasurable) hpe
    have heq : (∑ j ∈ Finset.range N, G j) = S N := by
      funext x
      simp only [Finset.sum_apply, S]
    rw [heq] at hM
    calc
      _ ≤ ∑ j ∈ Finset.range N, eLpNorm (G j) (ENNReal.ofReal p) μ := hM
      _ ≤ ∑ j ∈ Finset.range N, ENNReal.ofReal (c j) * F :=
        Finset.sum_le_sum (fun j _ => hbound j)
      _ = (∑ j ∈ Finset.range N, ENNReal.ofReal (c j)) * F := by rw [Finset.sum_mul]
      _ ≤ (∑' j, ENNReal.ofReal (c j)) * F :=
        mul_le_mul' (ENNReal.sum_le_tsum _) le_rfl
      _ = _ := by rw [← ENNReal.ofReal_tsum_of_nonneg hc0 hc]
  have henergy : (∫⁻ x, (∑' j, G j x) ^ p ∂μ) ≤
      (ENNReal.ofReal (∑' j, c j) * F) ^ p := by
    calc
      _ = ∫⁻ x, ⨆ N, S N x ^ p ∂μ := by
        apply lintegral_congr
        intro x
        rw [ENNReal.tsum_eq_iSup_nat, ennreal_rpow_iSup _ p hp]
      _ = ⨆ N, ∫⁻ x, S N x ^ p ∂μ := by
        apply lintegral_iSup
        · intro N
          exact ENNReal.continuous_rpow_const.measurable.comp (hS N)
        · intro N M hNM x
          exact ENNReal.rpow_le_rpow (hSmono hNM x) hp.le
      _ ≤ _ := by
        apply iSup_le
        intro N
        rw [← RectangularMaximalLp.eLpNorm_ofReal_rpow μ (S N) p hp]
        exact ENNReal.rpow_le_rpow (hfinite N) hp.le
  apply (ENNReal.rpow_le_rpow_iff hp).mp
  rw [RectangularMaximalLp.eLpNorm_ofReal_rpow μ _ p hp]
  exact henergy

/-- The actual nonnegative frequency majorant, with the rho-piece at zero. -/
def pieceSum (n : ℕ) (f : Space n → ℂ) (x : Space n) : ℝ≥0∞ :=
  ∑' j : ℕ, strongKernelMaximal (NormalDecomposition.kernelPiece n j) f x

private lemma one_lt_exponent (n : ℕ) (hn : 4 ≤ n) (p : ℝ)
    (hp : InterpolationParameters.critical n < p) : 1 < p := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hd : 0 < (n : ℝ) - 1 := by linarith
  have hcrit : 1 < InterpolationParameters.critical n := by
    unfold InterpolationParameters.critical
    apply (one_lt_div hd).mpr
    linarith
  exact hcrit.trans hp

/-- The coefficients in (6.19) form a genuinely summable real sequence,
chosen before every frequency index and raw input. -/
theorem exists_summable_piece_coefficients (n : ℕ) (hn : 4 ≤ n) (p : ℝ)
    (hp : InterpolationParameters.critical n < p) :
    ∃ c : ℕ → ℝ, (∀ j, 0 ≤ c j) ∧ Summable c ∧
      ∀ (j : ℕ) (f : Space n → ℂ), MemLp f (ENNReal.ofReal p) volume →
        Measurable (strongKernelMaximal (NormalDecomposition.kernelPiece n j) f) ∧
          eLpNorm (strongKernelMaximal (NormalDecomposition.kernelPiece n j) f)
            (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (c j) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hp1 : 1 < p := one_lt_exponent n hn p hp
  obtain ⟨C0, hC0, hzero⟩ := NormalPieceLp.lowFrequency_Lp n p hp1
  obtain ⟨ε, C, hε, hC, hpositive⟩ := NormalPieceInterpolation.sharp_piece_Lp n hn p hp
  let c : ℕ → ℝ := fun j => if j = 0 then C0 else C * GeometricDecay.dyadicWeight n ε j
  have hc0 : ∀ j, 0 ≤ c j := by
    intro j
    by_cases hj : j = 0
    · simp only [c, if_pos hj]; exact hC0.le
    · simp only [c, if_neg hj]
      exact mul_nonneg hC.le (GeometricDecay.dyadicWeight_nonneg n ε j)
  have hc : Summable c := by
    apply (summable_nat_add_iff 1).mp
    have hs := ((summable_nat_add_iff 1).mpr (GeometricDecay.summable_dyadicWeight n ε hε)).mul_left C
    simpa only [c, Nat.add_one_ne_zero, if_false] using hs
  refine ⟨c, hc0, hc, ?_⟩
  intro j f hf
  by_cases hj : j = 0
  · subst j
    simpa only [c, if_pos rfl] using hzero f hf
  · simpa only [c, if_neg hj, GeometricDecay.dyadicWeight, mul_assoc] using
      hpositive j (by omega) f hf

/-- The complete actual sum, including K₀, is bounded for all raw Lᵖ inputs
in the sharp finite range. The constant precedes the input. -/
theorem uniform_pieceSum_Lp (n : ℕ) (hn : 4 ≤ n) (p : ℝ)
    (hp : InterpolationParameters.critical n < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Space n → ℂ, MemLp f (ENNReal.ofReal p) volume →
      Measurable (pieceSum n f) ∧ eLpNorm (pieceSum n f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨c, hc0, hc, hpiece⟩ := exists_summable_piece_coefficients n hn p hp
  let D : ℝ := (∑' j, c j) + 1
  have hD : 0 < D := by
    dsimp only [D]
    have hs : 0 ≤ ∑' j, c j := tsum_nonneg hc0
    linarith
  refine ⟨D, hD, ?_⟩
  intro f hf
  let G : ℕ → Space n → ℝ≥0∞ := fun j =>
    strongKernelMaximal (NormalDecomposition.kernelPiece n j) f
  have hG : ∀ j, Measurable (G j) := fun j => (hpiece j f hf).1
  have hper : ∀ j, eLpNorm (G j) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (c j) * eLpNorm f (ENNReal.ofReal p) volume := fun j => (hpiece j f hf).2
  have hm : Measurable (pieceSum n f) := by
    unfold pieceSum
    simp_rw [ENNReal.tsum_eq_iSup_nat]
    exact Measurable.iSup fun N => Finset.measurable_sum _ (fun j _ => hG j)
  have he := eLpNorm_tsum_le (Space n) volume p (one_lt_exponent n hn p hp).le G hG c hc0 hc
    (eLpNorm f (ENNReal.ofReal p) volume) hper
  refine ⟨hm, he.trans ?_⟩
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by dsimp only [D]; linarith)) le_rfl

/-- Finiteness almost everywhere is a consequence of the norm bound, rather
than an assumption used to define the frequency sum. -/
theorem pieceSum_ae_lt_top (n : ℕ) (hn : 4 ≤ n) (p : ℝ)
    (hp : InterpolationParameters.critical n < p) (f : Space n → ℂ)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    ∀ᵐ x ∂volume, pieceSum n f x < ∞ := by
  obtain ⟨C, _hC, hbound⟩ := uniform_pieceSum_Lp n hn p hp
  obtain ⟨hm, he⟩ := hbound f hf
  have hp0 : 0 < p := zero_lt_one.trans (one_lt_exponent n hn p hp)
  have hnorm : eLpNorm (pieceSum n f) (ENNReal.ofReal p) volume < ∞ :=
    lt_of_le_of_lt he (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf.2)
  have hI : (∫⁻ x, pieceSum n f x ^ p) < ∞ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
      (f := pieceSum n f) (ENNReal.ofReal_ne_zero_iff.mpr hp0) ENNReal.ofReal_ne_top hnorm
    simpa only [enorm_eq_self, ENNReal.toReal_ofReal hp0.le] using h
  have hae := ae_lt_top (ENNReal.continuous_rpow_const.measurable.comp hm) hI.ne
  filter_upwards [hae] with x hx
  exact (ENNReal.rpow_lt_top_iff_of_pos hp0).mp hx

end StrongSpherical.NormalPieceSummation
