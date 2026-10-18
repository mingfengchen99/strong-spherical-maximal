import NormalPieceLp
import NormalPieceEndpoints
import InterpolationParameters
import KernelInterpolationFinite
import KernelInterpolationAboveTwo

/-! # Interpolation estimates for the actual normalized normal-frequency pieces -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace StrongSpherical.NormalPieceInterpolation
open InterpolationParameters

/-- Equation (6.17) for the actual K_j, including the surface normalization.
The constant is chosen before the positive frequency index and raw input. -/
theorem below_two_piece_Lp (n : ℕ) (hn : 4 ≤ n) (q p θ : ℝ)
    (hq1 : 1 < q) (hqp : q < p) (hp2 : p < 2)
    (hinterp : 1 / p = (1 - θ) / q + θ / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j → ∀ f : Space n → ℂ,
      MemLp f (ENNReal.ofReal p) volume →
        Measurable (strongKernelMaximal (NormalDecomposition.kernelPiece n j) f) ∧
          eLpNorm (strongKernelMaximal (NormalDecomposition.kernelPiece n j) f)
            (ENNReal.ofReal p) volume ≤
              ENNReal.ofReal (C * (1 + (j : ℝ)) ^ ((n : ℝ) * θ / 2) *
                (2 : ℝ) ^ ((j : ℝ) * (1 - (1 + a n) * θ))) *
                  eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨Cq, hCq, hqbound⟩ := NormalPieceLp.uniform_piece_Lp n q hq1
  obtain ⟨C2, hC2, h2bound⟩ := NormalDecomposition.actual_positive_piece_L2 n hn
  let D := KernelInterpolationFinite.interpolationConstant q p 2
  let C := D * (Cq ^ (1 - θ) * C2 ^ θ)
  have hD : 0 < D := KernelInterpolationFinite.interpolationConstant_pos q p 2
    (zero_lt_one.trans hq1) hqp hp2
  have hC : 0 < C := mul_pos hD
    (mul_pos (Real.rpow_pos_of_pos hCq _) (Real.rpow_pos_of_pos hC2 _))
  refine ⟨C, hC, ?_⟩
  intro j hj f hf
  let A := Cq * (2 : ℝ) ^ j
  let B := C2 * (1 + (j : ℝ)) ^ ((n : ℝ) / 2) * (2 : ℝ) ^ (-a n * (j : ℝ))
  have hA : 0 < A := mul_pos hCq (pow_pos (by norm_num) _)
  have hB : 0 < B := mul_pos
    (mul_pos hC2 (Real.rpow_pos_of_pos (by positivity) _))
    (Real.rpow_pos_of_pos (by norm_num) _)
  have hleft : ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal q) volume →
      eLpNorm (strongKernelMaximal (NormalDecomposition.kernelPiece n j) g)
        (ENNReal.ofReal q) volume ≤ ENNReal.ofReal A * eLpNorm g (ENNReal.ofReal q) volume := by
    intro g hg
    exact (hqbound j g hg).2
  have hright : ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal (2 : ℝ)) volume →
      eLpNorm (strongKernelMaximal (NormalDecomposition.kernelPiece n j) g)
        (ENNReal.ofReal (2 : ℝ)) volume ≤
          ENNReal.ofReal B * eLpNorm g (ENNReal.ofReal (2 : ℝ)) volume := by
    intro g hg
    have hg2 : MemLp g 2 volume := by simpa only [ENNReal.ofReal_ofNat] using hg
    simpa only [B, a, ENNReal.ofReal_ofNat] using (h2bound j hj g hg2).2
  obtain ⟨hm, he⟩ := KernelInterpolationFinite.strongKernelMaximal_Lp
    (NormalDecomposition.kernelPiece n j) (NormalDecomposition.contDiff_kernelPiece n j).continuous
    (NormalDecomposition.hasCompactSupport_kernelPiece n j) q p 2 θ hq1 hqp hp2 hinterp
    A B hA hB hleft hright f hf
  have hcoefficient : D * (A ^ (1 - θ) * B ^ θ) =
      C * (1 + (j : ℝ)) ^ ((n : ℝ) * θ / 2) *
        (2 : ℝ) ^ ((j : ℝ) * (1 - (1 + a n) * θ)) := by
    dsimp only [A, B, C]
    rw [below_two_frequency_coefficient n j Cq C2 θ hCq.le hC2.le]
    ring
  refine ⟨hm, ?_⟩
  change eLpNorm (strongKernelMaximal (NormalDecomposition.kernelPiece n j) f)
    (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (D * (A ^ (1 - θ) * B ^ θ)) *
      eLpNorm f (ENNReal.ofReal p) volume at he
  rw [hcoefficient] at he
  exact he

/-- The sharp range (n+1)/(n-1)<p<2 supplies a genuine positive exponential
decay rate for every actual positive-frequency piece; no endpoint estimate
or desired decay inequality is left as an extra assumption. -/
theorem sharp_below_two_piece_Lp (n : ℕ) (hn : 4 ≤ n) (p : ℝ)
    (hcritical : critical n < p) (hp2 : p < 2) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ j : ℕ, 1 ≤ j → ∀ f : Space n → ℂ,
      MemLp f (ENNReal.ofReal p) volume →
        Measurable (strongKernelMaximal (NormalDecomposition.kernelPiece n j) f) ∧
          eLpNorm (strongKernelMaximal (NormalDecomposition.kernelPiece n j) f)
            (ENNReal.ofReal p) volume ≤
              ENNReal.ofReal (C * (1 + (j : ℝ)) ^ ((n : ℝ) / 2) *
                (2 : ℝ) ^ (-ε * (j : ℝ))) * eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨q, θ, hq1, hqp, _hθ0, hθ1, hinterp, hneg⟩ :=
    exists_below_two_parameters n hn p hcritical hp2
  obtain ⟨C, hC, hbound⟩ := below_two_piece_Lp n hn q p θ hq1 hqp hp2 hinterp
  let ε := (1 + a n) * θ - 1
  have hε : 0 < ε := by dsimp only [ε]; linarith
  refine ⟨ε, C, hε, hC, ?_⟩
  intro j hj f hf
  obtain ⟨hm, he⟩ := hbound j hj f hf
  refine ⟨hm, he.trans ?_⟩
  apply mul_le_mul' _ le_rfl
  apply ENNReal.ofReal_le_ofReal
  rw [show (j : ℝ) * (1 - (1 + a n) * θ) = -ε * (j : ℝ) by dsimp only [ε]; ring]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le (by have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hθ1.le)]

/-- Equation (6.20), obtained from the actual L² and uniform L-infinity
endpoints of the normalized K_j. The constant is independent of j and f. -/
theorem above_two_piece_Lp (n : ℕ) (hn : 4 ≤ n) (p : ℝ) (hp2 : 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j → ∀ f : Space n → ℂ,
      MemLp f (ENNReal.ofReal p) volume →
        Measurable (strongKernelMaximal (NormalDecomposition.kernelPiece n j) f) ∧
          eLpNorm (strongKernelMaximal (NormalDecomposition.kernelPiece n j) f)
            (ENNReal.ofReal p) volume ≤
              ENNReal.ofReal (C * (1 + (j : ℝ)) ^ ((n : ℝ) / p) *
                (2 : ℝ) ^ (-2 * a n * (j : ℝ) / p)) *
                  eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨D, hD, hinterpolate⟩ := KernelInterpolationAboveTwo.exists_interpolation_above_two p hp2
  obtain ⟨C2, hC2, h2bound⟩ := NormalDecomposition.actual_positive_piece_L2 n hn
  obtain ⟨Cinf, hCinf, hinfbound⟩ := NormalPieceEndpoints.uniform_piece_pointwise n (by omega)
  let C := D * (C2 ^ (2 / p) * Cinf ^ (1 - 2 / p))
  have hC : 0 < C := mul_pos hD
    (mul_pos (Real.rpow_pos_of_pos hC2 _) (Real.rpow_pos_of_pos hCinf _))
  refine ⟨C, hC, ?_⟩
  intro j hj f hf
  let A := C2 * (1 + (j : ℝ)) ^ ((n : ℝ) / 2) * (2 : ℝ) ^ (-a n * (j : ℝ))
  have hA : 0 < A := mul_pos
    (mul_pos hC2 (Real.rpow_pos_of_pos (by positivity) _))
    (Real.rpow_pos_of_pos (by norm_num) _)
  have hleft : ∀ g : Space n → ℂ, MemLp g 2 volume →
      eLpNorm (strongKernelMaximal (NormalDecomposition.kernelPiece n j) g) 2 volume ≤
        ENNReal.ofReal A * eLpNorm g 2 volume := by
    intro g hg
    simpa only [A, a] using (h2bound j hj g hg).2
  have hright : ∀ g : Space n → ℂ, MemLp g ∞ volume → ∀ x,
      strongKernelMaximal (NormalDecomposition.kernelPiece n j) g x ≤
        ENNReal.ofReal Cinf * eLpNorm g ∞ volume := by
    intro g _hg x
    exact hinfbound j g x
  obtain ⟨hm, he⟩ := hinterpolate n (NormalDecomposition.kernelPiece n j)
    (NormalDecomposition.contDiff_kernelPiece n j).continuous
    (NormalDecomposition.hasCompactSupport_kernelPiece n j) A hA hleft Cinf hCinf hright f hf
  have hcoefficient : D * A ^ (2 / p) * Cinf ^ (1 - 2 / p) =
      C * (1 + (j : ℝ)) ^ ((n : ℝ) / p) * (2 : ℝ) ^ (-2 * a n * (j : ℝ) / p) := by
    calc
      _ = D * (A ^ (2 / p) * Cinf ^ (1 - 2 / p)) := by ring
      _ = _ := by
        dsimp only [A, C]
        rw [above_two_frequency_coefficient n j C2 Cinf p hC2.le]
        ring
  rw [hcoefficient] at he
  exact ⟨hm, he⟩

/-- A unified positive-frequency decay estimate throughout the sharp finite
range, including p=2. This is the input for the subsequent dyadic summation. -/
theorem sharp_piece_Lp (n : ℕ) (hn : 4 ≤ n) (p : ℝ) (hcritical : critical n < p) :
    ∃ ε C : ℝ, 0 < ε ∧ 0 < C ∧ ∀ j : ℕ, 1 ≤ j → ∀ f : Space n → ℂ,
      MemLp f (ENNReal.ofReal p) volume →
        Measurable (strongKernelMaximal (NormalDecomposition.kernelPiece n j) f) ∧
          eLpNorm (strongKernelMaximal (NormalDecomposition.kernelPiece n j) f)
            (ENNReal.ofReal p) volume ≤
              ENNReal.ofReal (C * (1 + (j : ℝ)) ^ ((n : ℝ) / 2) *
                (2 : ℝ) ^ (-ε * (j : ℝ))) * eLpNorm f (ENNReal.ofReal p) volume := by
  have ha : 0 < a n := by
    have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
    unfold a
    linarith
  rcases lt_trichotomy p 2 with hp2 | rfl | hp2
  · exact sharp_below_two_piece_Lp n hn p hcritical hp2
  · obtain ⟨C, hC, hbound⟩ := NormalDecomposition.actual_positive_piece_L2 n hn
    refine ⟨a n, C, ha, hC, ?_⟩
    intro j hj f hf
    have hf2 : MemLp f 2 volume := by simpa only [ENNReal.ofReal_ofNat] using hf
    simpa only [a, ENNReal.ofReal_ofNat] using hbound j hj f hf2
  · obtain ⟨C, hC, hbound⟩ := above_two_piece_Lp n hn p hp2
    let ε := 2 * a n / p
    have hp : 0 < p := lt_trans (by norm_num) hp2
    have hε : 0 < ε := div_pos (mul_pos (by norm_num) ha) hp
    refine ⟨ε, C, hε, hC, ?_⟩
    intro j hj f hf
    obtain ⟨hm, he⟩ := hbound j hj f hf
    refine ⟨hm, he.trans ?_⟩
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    rw [show -2 * a n * (j : ℝ) / p = -ε * (j : ℝ) by dsimp only [ε]; ring]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply Real.rpow_le_rpow_of_exponent_le (by have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j; linarith)
    apply (div_le_div_iff₀ hp (by norm_num : (0 : ℝ) < 2)).mpr
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith [mul_nonneg hn0 (sub_nonneg.mpr hp2.le)]

end StrongSpherical.NormalPieceInterpolation
