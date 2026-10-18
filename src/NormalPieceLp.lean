import NormalPieceSize
import KernelMaximalLp
import RectangularAverages

/-! # The actual normal-frequency pieces on every finite Lq, q>1

Both the actual rectangular maximal function and the previously constructed
iterated coordinate maximal operator give pointwise bounds. The latter yields
(6.13); the index zero gives (6.21), with the same normalization as the L2 bounds.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace StrongSpherical.NormalPieceLp

/-- Equation (6.12) with actual volume-normalized rectangular averages.
The estimate holds at every point for the original raw complex input. -/
theorem uniform_piece_rectangular (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (f : Space n → ℂ) (x : Space n),
      strongKernelMaximal (NormalDecomposition.kernelPiece n j) f x ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ j) *
          RectangularAverages.rectangularMaximal (fun y => ‖f y‖ₑ) x := by
  obtain ⟨B, hB, hsize⟩ := NormalPieceSize.uniform_kernelPiece_size n
  refine ⟨(4 : ℝ) ^ n * B, mul_pos (pow_pos (by norm_num) n) hB, ?_⟩
  intro j f x
  have h := RectangularAverages.strongKernelMaximal_le_rectangular
    (NormalDecomposition.kernelPiece n j) (NormalPieceSize.support_kernelPiece_box n j)
    (B * (2 : ℝ) ^ j) (hsize j) f x
  simpa only [mul_assoc] using h

/-- The low-frequency pointwise rectangular bound (6.21). -/
theorem lowFrequency_pointwise (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Space n → ℂ) (x : Space n),
      strongKernelMaximal (NormalDecomposition.kernelPiece n 0) f x ≤
        ENNReal.ofReal C *
          RectangularAverages.rectangularMaximal (fun y => ‖f y‖ₑ) x := by
  obtain ⟨C, hC, h⟩ := uniform_piece_rectangular n
  refine ⟨C, hC, ?_⟩
  intro f x
  simpa only [pow_zero, mul_one] using h 0 f x

/-- A concrete pointwise majorant, with its constant fixed before j and f. -/
theorem uniform_piece_pointwise (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (f : Space n → ℂ), Measurable f →
      ∀ x, strongKernelMaximal (NormalDecomposition.kernelPiece n j) f x ≤
        ENNReal.ofReal (C * (2 : ℝ) ^ j) *
          RectangularMaximal.controllingMaximal n (fun y => ‖f y‖ₑ) x := by
  obtain ⟨B, hB, hsize⟩ := NormalPieceSize.uniform_kernelPiece_size n
  refine ⟨KernelMaximalLp.boxMaximalConstant n 2 * B,
    mul_pos (KernelMaximalLp.boxMaximalConstant_pos n 2 (by norm_num)) hB, ?_⟩
  intro j f hf x
  have h := KernelMaximalLp.strongKernelMaximal_le_controlling
    (NormalDecomposition.kernelPiece n j) 2 (by norm_num)
    (NormalPieceSize.support_kernelPiece_box n j) (B * (2 : ℝ) ^ j)
    (hsize j) f hf x
  simpa only [mul_assoc] using h

/-- Equation (6.13) for the actual kernels, including zero, on raw MemLp inputs.
The real positive constant depends on n and q, and is chosen before j and f. -/
theorem uniform_piece_Lp (n : ℕ) (q : ℝ) (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (j : ℕ) (f : Space n → ℂ),
      MemLp f (ENNReal.ofReal q) volume →
        Measurable (strongKernelMaximal (NormalDecomposition.kernelPiece n j) f) ∧
          eLpNorm (strongKernelMaximal (NormalDecomposition.kernelPiece n j) f)
            (ENNReal.ofReal q) volume ≤
              ENNReal.ofReal (C * (2 : ℝ) ^ j) * eLpNorm f (ENNReal.ofReal q) volume := by
  obtain ⟨B, hB, hsize⟩ := NormalPieceSize.uniform_kernelPiece_size n
  obtain ⟨A, hA, hAK⟩ := KernelMaximalLp.exists_strongKernelMaximal_Lp
    n 2 (by norm_num) q hq
  refine ⟨A * B, mul_pos hA hB, ?_⟩
  intro j f hf
  have h := hAK (NormalDecomposition.kernelPiece n j)
    (NormalDecomposition.contDiff_kernelPiece n j).continuous
    (NormalPieceSize.support_kernelPiece_box n j) (B * (2 : ℝ) ^ j)
    (hsize j) f hf
  simpa only [mul_assoc] using h

/-- The low-frequency estimate (6.21), for every finite real exponent q>1. -/
theorem lowFrequency_Lp (n : ℕ) (q : ℝ) (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Space n → ℂ,
      MemLp f (ENNReal.ofReal q) volume →
        Measurable (strongKernelMaximal (NormalDecomposition.kernelPiece n 0) f) ∧
          eLpNorm (strongKernelMaximal (NormalDecomposition.kernelPiece n 0) f)
            (ENNReal.ofReal q) volume ≤
              ENNReal.ofReal C * eLpNorm f (ENNReal.ofReal q) volume := by
  obtain ⟨C, hC, h⟩ := uniform_piece_Lp n q hq
  refine ⟨C, hC, ?_⟩
  intro f hf
  simpa only [pow_zero, mul_one] using h 0 f hf

end StrongSpherical.NormalPieceLp
