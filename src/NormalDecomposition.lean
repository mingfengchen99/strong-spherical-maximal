import NormalFrequencyPieces
import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals
import NormalFourierScaling
import NormalCutoffs
import NormalKernelGlobal

/-! # Finite normal-frequency decomposition in Section 6.1 -/
noncomputable section
open MeasureTheory Set FourierTransform
open scoped BigOperators FourierTransform SchwartzMap ContDiff
namespace StrongSpherical.NormalDecomposition
variable {n : ℕ}

theorem two_mul_inverse_dyadic_succ (j : ℕ) :
    2 * (2 : ℝ) ^ (-((j + 1 : ℕ) : ℤ)) = (2 : ℝ) ^ (-(j : ℤ)) := by
  have he : -((j + 1 : ℕ) : ℤ) = -(j : ℤ) + (-1) := by omega
  rw [he, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  norm_num
  ring

/-- The telescoping identity (6.4) for an arbitrary scalar cutoff.
The index j in range J represents the positive frequency j+1. -/
theorem spectral_telescoping (rho : ℝ → ℂ) (J : ℕ) (tau : ℝ) :
    rho tau + ∑ j ∈ Finset.range J,
      (rho ((2 : ℝ) ^ (-((j + 1 : ℕ) : ℤ)) * tau) -
        rho (2 * ((2 : ℝ) ^ (-((j + 1 : ℕ) : ℤ)) * tau))) =
      rho ((2 : ℝ) ^ (-(J : ℤ)) * tau) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ← add_assoc, ih]
    rw [← mul_assoc, two_mul_inverse_dyadic_succ]
    ring

/-- The scalar telescoping form used after inverse Fourier transformation. -/
theorem sequence_telescoping (F : ℕ → ℂ) (J : ℕ) :
    F 0 + ∑ j ∈ Finset.range J, (F (j + 1) - F j) = F J := by
  induction J with
  | zero => simp
  | succ J ih => rw [Finset.sum_range_succ, ← add_assoc, ih]; ring

/-- Equation (6.4), with exactly the paper's interval of positive frequencies. -/
theorem spectral_telescoping_Icc (rho : ℝ → ℂ) (J : ℕ) (tau : ℝ) :
    rho tau + ∑ j ∈ Finset.Icc 1 J,
      (rho ((2 : ℝ) ^ (-(j : ℤ)) * tau) -
        rho (2 * ((2 : ℝ) ^ (-(j : ℤ)) * tau))) =
      rho ((2 : ℝ) ^ (-(J : ℤ)) * tau) := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc, ih]
    rw [← mul_assoc, two_mul_inverse_dyadic_succ]
    ring

/-- The actual inverse transform of the chosen rho, as a Schwartz function. -/
def inverseRho : 𝓢(ℝ, ℂ) :=
  NormalKernelC1.inverseBeta NormalCutoffs.rho NormalCutoffs.contDiff_rho
    NormalCutoffs.hasCompactSupport_rho

theorem inverse_rho_eq_schwartz :
    (𝓕⁻ NormalCutoffs.rho : ℝ → ℂ) = (inverseRho : ℝ → ℂ) :=
  (NormalKernelC1.inverseBeta_coe NormalCutoffs.rho NormalCutoffs.contDiff_rho
    NormalCutoffs.hasCompactSupport_rho).symm

theorem integrable_inverse_rho : Integrable (𝓕⁻ NormalCutoffs.rho : ℝ → ℂ) := by
  rw [inverse_rho_eq_schwartz]
  exact inverseRho.integrable

theorem integral_inverse_rho : (∫ t, (𝓕⁻ NormalCutoffs.rho) t) = 1 := by
  rw [inverse_rho_eq_schwartz]
  have hFourier : (𝓕 inverseRho : 𝓢(ℝ, ℂ)) =
      NormalCutoffs.hasCompactSupport_rho.toSchwartzMap NormalCutoffs.contDiff_rho :=
    fourier_fourierInv_eq _
  have h := congrArg (fun f : 𝓢(ℝ, ℂ) => f 0) hFourier
  change (∫ t : ℝ, 𝐞 (-inner ℝ t 0) • inverseRho t) = NormalCutoffs.rho 0 at h
  simpa only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one,
    one_smul, NormalCutoffs.rho_zero] using h

theorem integrable_inverse_beta : Integrable (𝓕⁻ NormalCutoffs.beta : ℝ → ℂ) := by
  rw [← NormalKernelC1.inverseBeta_coe NormalCutoffs.beta NormalCutoffs.contDiff_beta
    NormalCutoffs.hasCompactSupport_beta]
  exact (NormalKernelC1.inverseBeta NormalCutoffs.beta NormalCutoffs.contDiff_beta
    NormalCutoffs.hasCompactSupport_beta).integrable

/-- The true low-frequency kernel (6.2), separate from the positive-frequency formula. -/
def lowFrequencyKernel (chi : Space n → ℂ) (rho : ℝ → ℂ) (u : Space n) : ℂ :=
  (NormalFrequencyPieces.normalization n : ℂ) * chi u * (𝓕⁻ rho) (‖u‖ ^ 2 - 1)

/-- The finite approximate identity on the right side of (6.5). -/
def approximateKernel (chi : Space n → ℂ) (rho : ℝ → ℂ) (J : ℕ) (u : Space n) : ℂ :=
  (NormalFrequencyPieces.normalization n : ℂ) * chi u * ((2 : ℝ) ^ J : ℂ) *
    (𝓕⁻ rho) ((2 : ℝ) ^ J * (‖u‖ ^ 2 - 1))

theorem lowFrequencyKernel_eq_normalKernel (chi : Space n → ℂ) (rho : ℝ → ℂ) :
    lowFrequencyKernel chi rho =
      normalKernel (NormalFrequencyPieces.normalizedCutoff chi) rho 1 := by
  funext u
  simp [lowFrequencyKernel, normalKernel, NormalFrequencyPieces.normalizedCutoff]

theorem approximateKernel_zero (chi : Space n → ℂ) (rho : ℝ → ℂ) :
    approximateKernel chi rho 0 = lowFrequencyKernel chi rho := by
  funext u
  simp [approximateKernel, lowFrequencyKernel]

/-- The actual inverse Fourier scaling makes each positive-frequency piece
the difference between two consecutive finite approximate identities. -/
theorem dyadicPiece_eq_approximateKernel_sub (chi : Space n → ℂ) (rho : ℝ → ℂ)
    (hrho : Integrable rho) (j : ℕ) (u : Space n) :
    NormalFrequencyPieces.dyadicPiece chi (fun t => rho t - rho (2 * t)) (j + 1) u =
      approximateKernel chi rho (j + 1) u - approximateKernel chi rho j u := by
  have h := NormalFourierScaling.dyadic_inverse_beta_difference rho hrho j (‖u‖ ^ 2 - 1)
  have hh := congrArg (fun z : ℂ => (NormalFrequencyPieces.normalization n : ℂ) * chi u * z) h
  dsimp only [NormalFrequencyPieces.dyadicPiece, normalKernel, approximateKernel]
  push_cast at hh ⊢
  linear_combination hh

/-- Equation (6.5) for actual inverse Fourier transforms and actual kernels,
with the positive frequencies represented by j+1 for j in range J. -/
theorem finite_kernel_decomposition (chi : Space n → ℂ) (rho : ℝ → ℂ)
    (hrho : Integrable rho) (J : ℕ) (u : Space n) :
    lowFrequencyKernel chi rho u + ∑ j ∈ Finset.range J,
      NormalFrequencyPieces.dyadicPiece chi (fun t => rho t - rho (2 * t)) (j + 1) u =
      approximateKernel chi rho J u := by
  simp_rw [dyadicPiece_eq_approximateKernel_sub chi rho hrho]
  rw [← approximateKernel_zero chi rho]
  exact sequence_telescoping (fun j => approximateKernel chi rho j u) J

/-- Equation (6.5), with exactly the paper's positive-frequency index interval. -/
theorem finite_kernel_decomposition_Icc (chi : Space n → ℂ) (rho : ℝ → ℂ)
    (hrho : Integrable rho) (J : ℕ) (u : Space n) :
    lowFrequencyKernel chi rho u + ∑ j ∈ Finset.Icc 1 J,
      NormalFrequencyPieces.dyadicPiece chi (fun t => rho t - rho (2 * t)) j u =
      approximateKernel chi rho J u := by
  induction J with
  | zero => simp [approximateKernel_zero]
  | succ J ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ← add_assoc, ih,
      dyadicPiece_eq_approximateKernel_sub chi rho hrho]
    ring

/-- The chosen full kernel sequence: the rho-piece at zero and beta-pieces at
positive indices. This uses the same normalization as the existing L² estimates. -/
def kernelPiece (n : ℕ) : ℕ → Space n → ℂ
  | 0 => lowFrequencyKernel (NormalCutoffs.chi n) NormalCutoffs.rho
  | j + 1 => NormalFrequencyPieces.dyadicPiece (NormalCutoffs.chi n) NormalCutoffs.beta (j + 1)

@[simp] theorem kernelPiece_zero (n : ℕ) :
    kernelPiece n 0 = lowFrequencyKernel (NormalCutoffs.chi n) NormalCutoffs.rho := rfl

@[simp] theorem kernelPiece_succ (n j : ℕ) :
    kernelPiece n (j + 1) =
      NormalFrequencyPieces.dyadicPiece (NormalCutoffs.chi n) NormalCutoffs.beta (j + 1) := rfl

theorem contDiff_kernelPiece (n j : ℕ) : ContDiff ℝ ∞ (kernelPiece n j) := by
  cases j with
  | zero =>
    rw [kernelPiece_zero, lowFrequencyKernel_eq_normalKernel]
    exact NormalKernelC1.contDiff_normalKernel _
      (NormalFrequencyPieces.normalizedCutoff_contDiff _ (NormalCutoffs.contDiff_chi n))
      _ NormalCutoffs.contDiff_rho NormalCutoffs.hasCompactSupport_rho 1
  | succ j =>
    rw [kernelPiece_succ, NormalFrequencyPieces.dyadicPiece_eq_normalKernel]
    exact NormalKernelC1.contDiff_normalKernel _
      (NormalFrequencyPieces.normalizedCutoff_contDiff _ (NormalCutoffs.contDiff_chi n))
      _ NormalCutoffs.contDiff_beta NormalCutoffs.hasCompactSupport_beta _

theorem tsupport_kernelPiece_subset (n j : ℕ) :
    tsupport (kernelPiece n j) ⊆ tsupport (NormalCutoffs.chi n) := by
  cases j with
  | zero =>
    rw [kernelPiece_zero, lowFrequencyKernel_eq_normalKernel]
    exact (NormalKernelC1.tsupport_normalKernel_subset _ _ _).trans
      (NormalFrequencyPieces.tsupport_normalizedCutoff_subset _)
  | succ j =>
    rw [kernelPiece_succ, NormalFrequencyPieces.dyadicPiece_eq_normalKernel]
    exact (NormalKernelC1.tsupport_normalKernel_subset _ _ _).trans
      (NormalFrequencyPieces.tsupport_normalizedCutoff_subset _)

theorem hasCompactSupport_kernelPiece (n j : ℕ) : HasCompactSupport (kernelPiece n j) :=
  (NormalCutoffs.hasCompactSupport_chi n).of_isClosed_subset
    (isClosed_tsupport _) (tsupport_kernelPiece_subset n j)

theorem integrable_kernelPiece (n j : ℕ) : Integrable (kernelPiece n j) :=
  (contDiff_kernelPiece n j).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_kernelPiece n j)

/-- Equation (6.4) for the concrete smooth even cutoff and its beta band. -/
theorem actual_spectral_decomposition (J : ℕ) (tau : ℝ) :
    NormalCutoffs.rho tau + ∑ j ∈ Finset.Icc 1 J,
      NormalCutoffs.beta ((2 : ℝ) ^ (-(j : ℤ)) * tau) =
      NormalCutoffs.rho ((2 : ℝ) ^ (-(J : ℤ)) * tau) :=
  spectral_telescoping_Icc NormalCutoffs.rho J tau

/-- Equation (6.5) for the concrete normalized low and positive-frequency pieces. -/
theorem actual_kernel_decomposition (n J : ℕ) (u : Space n) :
    kernelPiece n 0 u + ∑ j ∈ Finset.range J, kernelPiece n (j + 1) u =
      approximateKernel (NormalCutoffs.chi n) NormalCutoffs.rho J u := by
  exact finite_kernel_decomposition (NormalCutoffs.chi n) NormalCutoffs.rho
    NormalCutoffs.integrable_rho J u

/-- Finite sums of the actual full sequence, ready for the later coarea limit. -/
theorem sum_kernelPiece (n J : ℕ) (u : Space n) :
    ∑ j ∈ Finset.range (J + 1), kernelPiece n j u =
      approximateKernel (NormalCutoffs.chi n) NormalCutoffs.rho J u := by
  rw [Finset.sum_range_succ']
  simpa only [add_comm] using actual_kernel_decomposition n J u

/-- The concrete cutoff choices discharge all smoothness and frequency-band
hypotheses of the already proved positive-frequency L² estimate. -/
theorem actual_positive_piece_L2 (n : ℕ) (hn : 4 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
      ∀ f : Space n → ℂ, MemLp f 2 volume →
        Measurable (strongKernelMaximal (kernelPiece n j) f) ∧
          eLpNorm (strongKernelMaximal (kernelPiece n j) f) 2 volume ≤
            ENNReal.ofReal (C * (1 + (j : ℝ)) ^ ((n : ℝ) / 2) *
              (2 : ℝ) ^ (-(((n : ℝ) - 3) / 4) * (j : ℝ))) * eLpNorm f 2 volume := by
  obtain ⟨C, hC, hbound⟩ := NormalKernelGlobal.single_piece_L2 n hn
    (NormalCutoffs.chi n) (NormalCutoffs.contDiff_chi n)
    (NormalCutoffs.hasCompactSupport_chi n) (NormalCutoffs.tsupport_chi_subset n)
    NormalCutoffs.beta NormalCutoffs.contDiff_beta NormalCutoffs.hasCompactSupport_beta
    NormalCutoffs.tsupport_beta_subset
  refine ⟨C, hC, ?_⟩
  intro j hj f hf
  cases j with
  | zero => omega
  | succ j => exact hbound (j + 1) hj f hf

end StrongSpherical.NormalDecomposition
