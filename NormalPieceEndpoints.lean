import NormalKernelL1
import KernelLInfinity

/-! # Uniform L¹ kernel bounds and the L∞ endpoint for the actual pieces

The same positive constant is chosen before the frequency index, dilation,
and raw L∞ input. The low-frequency rho-piece is included.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace StrongSpherical.NormalPieceEndpoints

theorem kernelPiece_eLpNorm_one (n j : ℕ) :
    eLpNorm (NormalDecomposition.kernelPiece n j) 1 volume =
      ENNReal.ofReal (∫ u, ‖NormalDecomposition.kernelPiece n j u‖) := by
  rw [eLpNorm_one_eq_lintegral_enorm,
    ofReal_integral_norm_eq_lintegral_enorm (NormalDecomposition.integrable_kernelPiece n j)]

/-- Equations (6.9) and (6.14), including every positive diagonal dilation.
The L∞ conclusion records measurability of the actual uncountable supremum. -/
theorem uniform_piece_endpoints (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ,
      eLpNorm (NormalDecomposition.kernelPiece n j) 1 volume ≤ ENNReal.ofReal C ∧
      (∀ r : Radii n, Integrable (dilatedKernel (NormalDecomposition.kernelPiece n j) r) ∧
        eLpNorm (dilatedKernel (NormalDecomposition.kernelPiece n j) r) 1 volume ≤
          ENNReal.ofReal C) ∧
      (∀ f : Space n → ℂ, MemLp f ∞ volume →
        Measurable (strongKernelMaximal (NormalDecomposition.kernelPiece n j) f) ∧
          eLpNorm (strongKernelMaximal (NormalDecomposition.kernelPiece n j) f) ∞ volume ≤
            ENNReal.ofReal C * eLpNorm f ∞ volume) := by
  obtain ⟨C, hC, hbound⟩ := NormalKernelL1.uniform_kernelPiece_L1 n hn
  have hLp (j : ℕ) : eLpNorm (NormalDecomposition.kernelPiece n j) 1 volume ≤
      ENNReal.ofReal C := by
    rw [kernelPiece_eLpNorm_one]
    exact ENNReal.ofReal_le_ofReal (hbound j)
  refine ⟨C, hC, fun j => ⟨hLp j, ?_, ?_⟩⟩
  · intro r
    refine ⟨DilationL1.integrable_dilatedKernel _
      (NormalDecomposition.integrable_kernelPiece n j) r, ?_⟩
    rw [DilationL1.eLpNorm_dilatedKernel_one]
    exact hLp j
  · intro f hf
    obtain ⟨hm, he⟩ := KernelLInfinity.strongKernelMaximal_LInfinity _
      (NormalDecomposition.contDiff_kernelPiece n j).continuous
      (NormalDecomposition.hasCompactSupport_kernelPiece n j) f hf
    refine ⟨hm, he.trans ?_⟩
    exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hbound j)) _

/-- A uniform pointwise bound, before taking any L∞ seminorm in x. -/
theorem uniform_piece_pointwise (n : ℕ) (hn : 2 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, ∀ f : Space n → ℂ, ∀ x : Space n,
      strongKernelMaximal (NormalDecomposition.kernelPiece n j) f x ≤
        ENNReal.ofReal C * eLpNorm f ∞ volume := by
  obtain ⟨C, hC, hbound⟩ := NormalKernelL1.uniform_kernelPiece_L1 n hn
  refine ⟨C, hC, fun j f x => ?_⟩
  exact (KernelLInfinity.strongKernelMaximal_le _
    (NormalDecomposition.contDiff_kernelPiece n j).continuous
    (NormalDecomposition.hasCompactSupport_kernelPiece n j) f x).trans
      (mul_le_mul_left (ENNReal.ofReal_le_ofReal (hbound j)) _)

end StrongSpherical.NormalPieceEndpoints
