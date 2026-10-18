import NormalDecomposition
import NormalCutoffBounds

/-! # Uniform size and box support of the actual normal-frequency kernels -/
noncomputable section
open MeasureTheory Set FourierTransform
open scoped FourierTransform SchwartzMap

namespace StrongSpherical.NormalPieceSize

theorem support_kernelPiece_box (n j : ℕ) :
    Function.support (NormalDecomposition.kernelPiece n j) ⊆
      MarginalEnergy.coordinateBox n 2 := by
  intro u hu i
  have hchi := NormalDecomposition.tsupport_kernelPiece_subset n j
    (subset_tsupport _ hu)
  have hn := (NormalCutoffs.tsupport_chi_subset n hchi).2.le
  have hi : |u i| ≤ ‖u‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i
  exact abs_le.mp (hi.trans hn)

/-- One constant is fixed before the frequency index, including the rho-piece at zero. -/
theorem uniform_kernelPiece_size (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ (j : ℕ) (u : Space n),
      ‖NormalDecomposition.kernelPiece n j u‖ ≤ B * (2 : ℝ) ^ j := by
  let R := NormalDecomposition.inverseRho
  let P := NormalKernelC1.inverseBeta NormalCutoffs.beta NormalCutoffs.contDiff_beta
    NormalCutoffs.hasCompactSupport_beta
  let V := SchwartzMap.seminorm ℝ 0 0 R
  let W := SchwartzMap.seminorm ℝ 0 0 P
  let c := |NormalFrequencyPieces.normalization n|
  let B := 1 + c * (V + W)
  have hV : 0 ≤ V := apply_nonneg _ _
  have hW : 0 ≤ W := apply_nonneg _ _
  have hc : 0 ≤ c := abs_nonneg _
  have hB : 0 < B := by dsimp [B]; positivity
  have hR : ∀ t : ℝ, ‖(𝓕⁻ NormalCutoffs.rho) t‖ ≤ V := by
    intro t
    rw [NormalDecomposition.inverse_rho_eq_schwartz]
    exact SchwartzMap.norm_le_seminorm ℝ R t
  have hP : ∀ t : ℝ, ‖(𝓕⁻ NormalCutoffs.beta) t‖ ≤ W := by
    intro t
    rw [← NormalKernelC1.inverseBeta_coe NormalCutoffs.beta
      NormalCutoffs.contDiff_beta NormalCutoffs.hasCompactSupport_beta]
    exact SchwartzMap.norm_le_seminorm ℝ P t
  refine ⟨B, hB, ?_⟩
  intro j u
  cases j with
  | zero =>
    simp only [NormalDecomposition.kernelPiece_zero,
      NormalDecomposition.lowFrequencyKernel, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, pow_zero, mul_one]
    calc
      _ ≤ c * 1 * V := by
        exact mul_le_mul (mul_le_mul_of_nonneg_left
          (NormalCutoffBounds.norm_chi_le_one n u) hc) (hR _)
          (norm_nonneg _) (mul_nonneg hc zero_le_one)
      _ ≤ B := by dsimp [B]; nlinarith
  | succ j =>
    simp only [NormalDecomposition.kernelPiece_succ, NormalFrequencyPieces.dyadicPiece,
      normalKernel, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (j + 1))]
    calc
      _ ≤ c * (1 * (2 : ℝ) ^ (j + 1) * W) := by
        apply mul_le_mul_of_nonneg_left _ hc
        exact mul_le_mul (mul_le_mul_of_nonneg_right
          (NormalCutoffBounds.norm_chi_le_one n u) (by positivity)) (hP _)
          (norm_nonneg _) (by positivity)
      _ ≤ B * (2 : ℝ) ^ (j + 1) := by
        have hcb : c * W ≤ B := by dsimp [B]; nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hcb
          (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (j + 1))]

end StrongSpherical.NormalPieceSize
