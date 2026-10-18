import NormalSphereLimit
import NormalCutoffBounds
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Uniform L¹ mass of the actual normal-frequency pieces -/
noncomputable section
open MeasureTheory Set
open scoped FourierTransform

namespace StrongSpherical.NormalKernelL1

/-- Positive dilation preserves the mass of the normalized inverse Fourier norm. -/
theorem integral_scaled_inverse_norm (beta : ℝ → ℂ) (lambda : ℝ) (hlambda : 0 < lambda) :
    (∫ t : ℝ, lambda * ‖(𝓕⁻ beta) (lambda * t)‖) = ∫ t : ℝ, ‖(𝓕⁻ beta) t‖ := by
  have hs := Measure.integral_comp_mul_left (fun t : ℝ => ‖(𝓕⁻ beta) t‖) lambda
  rw [integral_const_mul, hs, abs_of_pos (inv_pos.mpr hlambda)]
  simp only [smul_eq_mul]
  field_simp [hlambda.ne']

lemma integrable_scaled_inverse_norm (beta : ℝ → ℂ)
    (hi : Integrable (𝓕⁻ beta : ℝ → ℂ)) (lambda : ℝ) (hlambda : 0 < lambda) :
    Integrable (fun t : ℝ => lambda * ‖(𝓕⁻ beta) (lambda * t)‖) :=
  (hi.comp_mul_left' hlambda.ne').norm.const_mul lambda

/-- Actual compact support ensures these normal kernels are integrable,
independently of the later uniform estimate. -/
theorem integrable_normalKernel (n : ℕ) (beta : ℝ → ℂ)
    (hc : Continuous (𝓕⁻ beta : ℝ → ℂ)) (lambda : ℝ) :
    Integrable (normalKernel (NormalCutoffs.chi n) beta lambda) := by
  have hK : Continuous (normalKernel (NormalCutoffs.chi n) beta lambda) := by
    exact ((NormalCutoffs.contDiff_chi n).continuous.mul continuous_const).mul
      (hc.comp (continuous_const.mul ((continuous_norm.pow 2).sub continuous_const)))
  exact hK.integrable_of_hasCompactSupport
    (NormalKernelC1.hasCompactSupport_normalKernel (NormalCutoffs.chi n)
      (NormalCutoffs.hasCompactSupport_chi n) beta lambda)

/-- The true coarea density controls the normal kernel by the fixed L¹ mass
of its inverse Fourier cutoff. No estimate in lambda is assumed. -/
theorem normalKernel_L1_le (n : ℕ) (hn : 2 ≤ n) (beta : ℝ → ℂ)
    (hc : Continuous (𝓕⁻ beta : ℝ → ℂ)) (hi : Integrable (𝓕⁻ beta : ℝ → ℂ))
    (D : ℝ) (hD : ∀ t : ℝ, ‖NormalRadialDensity.density n (fun _ => 1) t‖ ≤ D)
    (lambda : ℝ) (hlambda : 0 < lambda) :
    (∫ u : Space n, ‖normalKernel (NormalCutoffs.chi n) beta lambda u‖) ≤
      D * ∫ t : ℝ, ‖(𝓕⁻ beta) t‖ := by
  let k : ℝ → ℂ := fun t => (lambda : ℂ) * (‖(𝓕⁻ beta) (lambda * t)‖ : ℂ)
  have hk : Continuous k := continuous_const.mul
    (Complex.continuous_ofReal.comp (hc.norm.comp (continuous_const.mul continuous_id)))
  have hco := NormalSphereLimit.quadratic_coarea n hn k hk (fun _ => 1) continuous_const
  have hreal :
      ((∫ u : Space n, ‖normalKernel (NormalCutoffs.chi n) beta lambda u‖ : ℝ) : ℂ) =
        ∫ t : ℝ, k t * NormalRadialDensity.density n (fun _ => 1) t := by
    rw [← integral_complex_ofReal]
    calc
      _ = ∫ u : Space n, NormalCutoffs.chi n u * k (‖u‖ ^ 2 - 1) * 1 := by
        apply integral_congr_ae
        filter_upwards with u
        simp only [normalKernel, norm_mul, Complex.norm_real,
          Real.norm_of_nonneg hlambda.le, Complex.ofReal_mul, k, mul_one]
        rw [← NormalCutoffBounds.chi_eq_coe_norm n u]
        ring
      _ = _ := hco
  have hmass :
      (∫ u : Space n, ‖normalKernel (NormalCutoffs.chi n) beta lambda u‖) =
        ‖∫ t : ℝ, k t * NormalRadialDensity.density n (fun _ => 1) t‖ := by
    rw [← hreal, Complex.norm_real, Real.norm_of_nonneg
      (integral_nonneg (fun _ => norm_nonneg _))]
  have hknorm (t : ℝ) : ‖k t‖ = lambda * ‖(𝓕⁻ beta) (lambda * t)‖ := by
    simp only [k, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlambda.le,
      Real.norm_of_nonneg (norm_nonneg _)]
  calc
    (∫ u : Space n, ‖normalKernel (NormalCutoffs.chi n) beta lambda u‖) =
        ‖∫ t : ℝ, k t * NormalRadialDensity.density n (fun _ => 1) t‖ := hmass
    _ ≤ ∫ t : ℝ, ‖k t * NormalRadialDensity.density n (fun _ => 1) t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (lambda * ‖(𝓕⁻ beta) (lambda * t)‖) * D := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun _ => norm_nonneg _))
        ((integrable_scaled_inverse_norm beta hi lambda hlambda).mul_const D)
      filter_upwards with t
      rw [norm_mul, hknorm]
      exact mul_le_mul_of_nonneg_left (hD t) (mul_nonneg hlambda.le (norm_nonneg _))
    _ = (∫ t : ℝ, lambda * ‖(𝓕⁻ beta) (lambda * t)‖) * D := integral_mul_const _ _
    _ ≤ D * ∫ t : ℝ, ‖(𝓕⁻ beta) t‖ := by
      rw [integral_scaled_inverse_norm beta lambda hlambda]
      exact le_of_eq (mul_comm _ _)
  exact le_rfl

/-- One positive constant controls every positive real normal frequency. -/
theorem normalKernel_L1_bound (n : ℕ) (hn : 2 ≤ n) (beta : ℝ → ℂ)
    (hc : Continuous (𝓕⁻ beta : ℝ → ℂ)) (hi : Integrable (𝓕⁻ beta : ℝ → ℂ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ lambda : ℝ, 0 < lambda →
      (∫ u : Space n, ‖normalKernel (NormalCutoffs.chi n) beta lambda u‖) ≤ C := by
  obtain ⟨D, hD, hb⟩ := NormalCutoffBounds.density_one_bound n
  let C : ℝ := D * (∫ t : ℝ, ‖(𝓕⁻ beta) t‖) + 1
  have hI : 0 ≤ ∫ t : ℝ, ‖(𝓕⁻ beta) t‖ := integral_nonneg (fun _ => norm_nonneg _)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro lambda hlambda
  exact (normalKernel_L1_le n hn beta hc hi D hb lambda hlambda).trans (by dsimp [C]; linarith)

lemma integral_norm_const_mul {n : ℕ} (c : ℂ) (K : Space n → ℂ) :
    (∫ u, ‖c * K u‖) = ‖c‖ * ∫ u, ‖K u‖ := by
  simp only [norm_mul, integral_const_mul]

/-- The j=0 piece uses rho at frequency one, with the actual surface normalization. -/
theorem integral_kernelPiece_zero (n : ℕ) :
    (∫ u : Space n, ‖NormalDecomposition.kernelPiece n 0 u‖) =
      ‖(NormalFrequencyPieces.normalization n : ℂ)‖ *
        ∫ u : Space n, ‖normalKernel (NormalCutoffs.chi n) NormalCutoffs.rho 1 u‖ := by
  rw [← integral_norm_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  simp only [NormalDecomposition.kernelPiece_zero, NormalDecomposition.lowFrequencyKernel,
    normalKernel, Complex.ofReal_one, mul_one, one_mul, mul_assoc]

/-- Every positive piece has exactly the same fixed normalization. -/
theorem integral_kernelPiece_succ (n j : ℕ) :
    (∫ u : Space n, ‖NormalDecomposition.kernelPiece n (j + 1) u‖) =
      ‖(NormalFrequencyPieces.normalization n : ℂ)‖ *
        ∫ u : Space n, ‖normalKernel (NormalCutoffs.chi n) NormalCutoffs.beta ((2 : ℝ) ^ (j + 1)) u‖ := by
  rw [← integral_norm_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  rfl

/-- Equation (6.9), including the genuine rho-piece at zero. The constant is
chosen before j, and the normalization 2/|S^(n-1)| is inside every kernel. -/
theorem uniform_kernelPiece_L1 (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ,
      (∫ u : Space n, ‖NormalDecomposition.kernelPiece n j u‖) ≤ C := by
  obtain ⟨A, hA, hArho⟩ := normalKernel_L1_bound n hn NormalCutoffs.rho
    (NormalKernelC1.contDiff_inverseFourier NormalCutoffs.rho NormalCutoffs.contDiff_rho
      NormalCutoffs.hasCompactSupport_rho).continuous NormalDecomposition.integrable_inverse_rho
  obtain ⟨B, hB, hBbeta⟩ := normalKernel_L1_bound n hn NormalCutoffs.beta
    (NormalKernelC1.contDiff_inverseFourier NormalCutoffs.beta NormalCutoffs.contDiff_beta
      NormalCutoffs.hasCompactSupport_beta).continuous NormalDecomposition.integrable_inverse_beta
  let c : ℝ := ‖(NormalFrequencyPieces.normalization n : ℂ)‖
  let C : ℝ := c * (A + B) + 1
  have hc : 0 ≤ c := norm_nonneg _
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro j
  cases j with
  | zero =>
    rw [integral_kernelPiece_zero]
    have h := mul_le_mul_of_nonneg_left (hArho 1 (by norm_num)) hc
    change c * _ ≤ C
    exact h.trans (by dsimp [C]; nlinarith [mul_nonneg hc hB.le])
  | succ j =>
    rw [integral_kernelPiece_succ]
    have h := mul_le_mul_of_nonneg_left
      (hBbeta ((2 : ℝ) ^ (j + 1)) (pow_pos (by norm_num) _)) hc
    change c * _ ≤ C
    exact h.trans (by dsimp [C]; nlinarith [mul_nonneg hc hA.le])

end StrongSpherical.NormalKernelL1
