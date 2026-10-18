import GlobalKernelEstimate
import LocalEstimate
import NormalKernelC1
import LogarithmicScales
import NormalFrequencyPieces

/-! # Global L² estimates for the actual normal-frequency kernels -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal FourierTransform ContDiff
namespace StrongSpherical.NormalKernelGlobal
open DyadicKernelScales MarginalInduction
variable {n : ℕ}

/-- Separating the fixed constants in the local and C¹ bounds preserves the
two frequency terms used in the logarithmic choice of the scale gap. -/
theorem frequency_coefficient_le (n M : ℕ) (lambda A B : ℝ)
    (hlambda : 0 < lambda) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    frequencyGrowth n M * (A * lambda ^ (-((n : ℝ) - 3) / 4)) +
      epsilon M * (B * lambda ^ 2) ≤
      (A + B) * (frequencyGrowth n M * lambda ^ (-((n : ℝ) - 3) / 4) +
        epsilon M * lambda ^ 2) := by
  have hg := frequencyGrowth_nonneg n M
  have he := (epsilon_pos M).le
  have hp := (Real.rpow_pos_of_pos hlambda (-((n : ℝ) - 3) / 4)).le
  have ha : 0 ≤ A * (epsilon M * lambda ^ 2) := by positivity
  have hb : 0 ≤ B * (frequencyGrowth n M * lambda ^ (-((n : ℝ) - 3) / 4)) := by positivity
  nlinarith

/-- Applying Lemma 1.4 to an actual family whose local and C¹ bounds have
already been proved. The final normal-kernel theorem supplies these bounds. -/
theorem exists_gap_bound_of_local_C1 (K : ℝ → Space n → ℂ)
    (hK : ∀ lambda : ℝ, 1 ≤ lambda → ContDiff ℝ 1 (K lambda))
    (hs : ∀ lambda : ℝ, 1 ≤ lambda →
      Function.support (K lambda) ⊆ MarginalEnergy.coordinateBox n 2)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hlocal : ∀ lambda : ℝ, 1 ≤ lambda →
      LocalKernelBound (K lambda) (A * lambda ^ (-((n : ℝ) - 3) / 4)))
    (hb : ∀ lambda : ℝ, 1 ≤ lambda → ∀ x, ‖K lambda x‖ ≤ B * lambda ^ 2)
    (hd : ∀ lambda : ℝ, 1 ≤ lambda → ∀ x, ‖fderiv ℝ (K lambda) x‖ ≤ B * lambda ^ 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ lambda : ℝ, 1 ≤ lambda →
      ∀ M : ℕ, 3 ≤ M → ∀ f : Space n → ℂ, MemLp f 2 volume →
        Measurable (strongKernelMaximal (K lambda) f) ∧
          eLpNorm (strongKernelMaximal (K lambda) f) 2 volume ≤
            ENNReal.ofReal (C * (frequencyGrowth n M * lambda ^ (-((n : ℝ) - 3) / 4) +
              epsilon M * lambda ^ 2)) * eLpNorm f 2 volume := by
  obtain ⟨C0, hC0, hbound⟩ := GlobalKernelEstimate.exists_globalKernelBound n 2 (by norm_num)
  refine ⟨C0 * (A + B), mul_pos hC0 (add_pos hA hB), ?_⟩
  intro lambda hlambda M hM f hf
  have hlambda0 : 0 < lambda := lt_of_lt_of_le zero_lt_one hlambda
  have hA0 : 0 ≤ A * lambda ^ (-((n : ℝ) - 3) / 4) := by positivity
  have h := hbound (K lambda) (hK lambda hlambda) (hs lambda hlambda)
    (A * lambda ^ (-((n : ℝ) - 3) / 4)) (B * lambda ^ 2) hA0
    (hb lambda hlambda) (hd lambda hlambda) (hlocal lambda hlambda) M hM f hf
  refine ⟨DilationL2.strongKernelMaximal_measurable (K lambda) (hK lambda hlambda).continuous
    2 (by norm_num) (hs lambda hlambda) f hf, h.trans ?_⟩
  apply mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
  calc
    _ ≤ C0 * ((A + B) * (frequencyGrowth n M * lambda ^ (-((n : ℝ) - 3) / 4) +
        epsilon M * lambda ^ 2)) :=
      mul_le_mul_of_nonneg_left (frequency_coefficient_le n M lambda A B hlambda0 hA.le hB.le) hC0.le
    _ = _ := by ring

/-- The two actual estimates, Proposition 1.3 and the quadratic C¹ growth,
give a uniform all-radii bound for every allowed choice of the gap M. -/
theorem exists_normalKernel_gap_bound (n : ℕ) (hn : 2 ≤ n)
    (chi : Space n → ℂ) (hchi : ContDiff ℝ ∞ chi) (hchic : HasCompactSupport chi)
    (hs : tsupport chi ⊆ {u | (1 / 2 : ℝ) < ‖u‖ ∧ ‖u‖ < 2})
    (beta : ℝ → ℂ) (hb : ContDiff ℝ ∞ beta) (hbc : HasCompactSupport beta)
    (hbs : tsupport beta ⊆ {t | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ lambda : ℝ, 1 ≤ lambda →
      ∀ M : ℕ, 3 ≤ M → ∀ f : Space n → ℂ, MemLp f 2 volume →
        Measurable (strongKernelMaximal (normalKernel chi beta lambda) f) ∧
          eLpNorm (strongKernelMaximal (normalKernel chi beta lambda) f) 2 volume ≤
            ENNReal.ofReal (C * (frequencyGrowth n M * lambda ^ (-((n : ℝ) - 3) / 4) +
              epsilon M * lambda ^ 2)) * eLpNorm f 2 volume := by
  have hs' : tsupport chi ⊆ {u | ‖u‖ ≤ 2} := fun u hu => (hs hu).2.le
  obtain ⟨A, hA, hlocal⟩ := LocalEstimate.proposition_1_3 n hn chi hchi hchic hs beta hb hbc hbs
  obtain ⟨B, hB, hC1⟩ := NormalKernelC1.exists_normalKernel_C1_bound chi hchi hchic hs' beta hb hbc
  exact exists_gap_bound_of_local_C1 (normalKernel chi beta)
    (fun lambda _ => (NormalKernelC1.contDiff_normalKernel chi hchi beta hb hbc lambda).of_le
      (by simp))
    (fun lambda _ => NormalKernelC1.support_normalKernel_box chi hs' beta lambda)
    A B hA hB (fun lambda hlambda f hf => (hlocal lambda hlambda f hf).2)
    (fun lambda hlambda x => (hC1 lambda hlambda x).1)
    (fun lambda hlambda x => (hC1 lambda hlambda x).2)

/-- Equation (1.14), for every real normal frequency and every original L² input.
The fixed constant is selected before lambda and f. -/
theorem global_normalKernel_L2 (n : ℕ) (hn : 2 ≤ n)
    (chi : Space n → ℂ) (hchi : ContDiff ℝ ∞ chi) (hchic : HasCompactSupport chi)
    (hs : tsupport chi ⊆ {u | (1 / 2 : ℝ) < ‖u‖ ∧ ‖u‖ < 2})
    (beta : ℝ → ℂ) (hb : ContDiff ℝ ∞ beta) (hbc : HasCompactSupport beta)
    (hbs : tsupport beta ⊆ {t | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ lambda : ℝ, 1 ≤ lambda →
      ∀ f : Space n → ℂ, MemLp f 2 volume →
        Measurable (strongKernelMaximal (normalKernel chi beta lambda) f) ∧
          eLpNorm (strongKernelMaximal (normalKernel chi beta lambda) f) 2 volume ≤
            ENNReal.ofReal (C * (Real.log (2 + lambda)) ^ ((n : ℝ) / 2) *
              lambda ^ (-((n : ℝ) - 3) / 4)) * eLpNorm f 2 volume := by
  obtain ⟨C0, hC0, hgap⟩ := exists_normalKernel_gap_bound n hn chi hchi hchic hs beta hb hbc hbs
  obtain ⟨C1, hC1, hscale⟩ := LogarithmicScales.exists_logarithmic_scale n
  refine ⟨C0 * C1, mul_pos hC0 hC1, ?_⟩
  intro lambda hlambda f hf
  obtain ⟨M, hM, hnum⟩ := hscale lambda hlambda
  have h := hgap lambda hlambda M hM f hf
  refine ⟨h.1, h.2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)⟩
  have hnum' : frequencyGrowth n M * lambda ^ (-((n : ℝ) - 3) / 4) +
      epsilon M * lambda ^ 2 ≤
        C1 * (Real.log (2 + lambda)) ^ ((n : ℝ) / 2) * lambda ^ (-((n : ℝ) - 3) / 4) := by
    simpa only [frequencyGrowth, epsilon, LogarithmicScales.decayExponent, neg_div] using hnum
  calc
    _ ≤ C0 * (C1 * (Real.log (2 + lambda)) ^ ((n : ℝ) / 2) *
        lambda ^ (-((n : ℝ) - 3) / 4)) := mul_le_mul_of_nonneg_left hnum' hC0.le
    _ = _ := by ring

theorem dyadic_decay_eq (n j : ℕ) :
    ((2 : ℝ) ^ j) ^ (-((n : ℝ) - 3) / 4) =
      (2 : ℝ) ^ (-LogarithmicScales.decayExponent n * (j : ℝ)) := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) j]
  congr 1
  unfold LogarithmicScales.decayExponent
  ring

theorem dyadic_square_eq (j : ℕ) :
    ((2 : ℝ) ^ j) ^ 2 = (2 : ℝ) ^ (2 * (j : ℝ)) := by
  calc
    _ = ((2 : ℝ) ^ j) ^ (2 : ℝ) := (Real.rpow_natCast _ 2).symm
    _ = (2 : ℝ) ^ ((j : ℝ) * 2) :=
      (Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) j 2).symm
    _ = _ := by congr 1; ring

/-- The dyadic form of (6.11), before the fixed surface-area normalization. -/
theorem dyadic_normalKernel_L2 (n : ℕ) (hn : 2 ≤ n)
    (chi : Space n → ℂ) (hchi : ContDiff ℝ ∞ chi) (hchic : HasCompactSupport chi)
    (hs : tsupport chi ⊆ {u | (1 / 2 : ℝ) < ‖u‖ ∧ ‖u‖ < 2})
    (beta : ℝ → ℂ) (hb : ContDiff ℝ ∞ beta) (hbc : HasCompactSupport beta)
    (hbs : tsupport beta ⊆ {t | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, ∀ f : Space n → ℂ, MemLp f 2 volume →
      Measurable (strongKernelMaximal (normalKernel chi beta ((2 : ℝ) ^ j)) f) ∧
        eLpNorm (strongKernelMaximal (normalKernel chi beta ((2 : ℝ) ^ j)) f) 2 volume ≤
          ENNReal.ofReal (C * (1 + (j : ℝ)) ^ ((n : ℝ) / 2) *
            (2 : ℝ) ^ (-(((n : ℝ) - 3) / 4) * (j : ℝ))) * eLpNorm f 2 volume := by
  obtain ⟨C0, hC0, hgap⟩ := exists_normalKernel_gap_bound n hn chi hchi hchic hs beta hb hbc hbs
  obtain ⟨C1, hC1, hscale⟩ := LogarithmicScales.exists_dyadic_scale n
  refine ⟨C0 * C1, mul_pos hC0 hC1, ?_⟩
  intro j f hf
  obtain ⟨M, hM, hnum⟩ := hscale j
  have hlambda : 1 ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have h := hgap ((2 : ℝ) ^ j) hlambda M hM f hf
  rw [dyadic_decay_eq, dyadic_square_eq] at h
  refine ⟨h.1, h.2.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)⟩
  have hnum' : frequencyGrowth n M * (2 : ℝ) ^ (-LogarithmicScales.decayExponent n * (j : ℝ)) +
      epsilon M * (2 : ℝ) ^ (2 * (j : ℝ)) ≤
        C1 * (1 + (j : ℝ)) ^ ((n : ℝ) / 2) *
          (2 : ℝ) ^ (-LogarithmicScales.decayExponent n * (j : ℝ)) := hnum
  calc
    _ ≤ C0 * (C1 * (1 + (j : ℝ)) ^ ((n : ℝ) / 2) *
        (2 : ℝ) ^ (-LogarithmicScales.decayExponent n * (j : ℝ))) :=
      mul_le_mul_of_nonneg_left hnum' hC0.le
    _ = _ := by unfold LogarithmicScales.decayExponent; ring

/-- Equation (6.8) for the actual normalized positive-frequency pieces (6.3). -/
theorem single_piece_C1 (chi : Space n → ℂ) (hchi : ContDiff ℝ ∞ chi)
    (hchic : HasCompactSupport chi) (hs : tsupport chi ⊆ {u | ‖u‖ ≤ 2})
    (beta : ℝ → ℂ) (hb : ContDiff ℝ ∞ beta) (hbc : HasCompactSupport beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ,
      KernelC1Norm.c1Norm (NormalFrequencyPieces.dyadicPiece chi beta j) ≤
        C * (2 : ℝ) ^ (2 * (j : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := NormalKernelC1.exists_c1Norm_normalKernel_bound
    (NormalFrequencyPieces.normalizedCutoff chi)
    (NormalFrequencyPieces.normalizedCutoff_contDiff chi hchi)
    (NormalFrequencyPieces.normalizedCutoff_compact chi hchic)
    ((NormalFrequencyPieces.tsupport_normalizedCutoff_subset chi).trans hs) beta hb hbc
  refine ⟨C, hC, ?_⟩
  intro j
  rw [NormalFrequencyPieces.dyadicPiece_eq_normalKernel]
  simpa only [dyadic_square_eq] using hbound ((2 : ℝ) ^ j) (one_le_pow₀ (by norm_num))

/-- Equation (6.11) for the actual normalized positive-frequency pieces (6.3). -/
theorem single_piece_L2 (n : ℕ) (hn : 4 ≤ n)
    (chi : Space n → ℂ) (hchi : ContDiff ℝ ∞ chi) (hchic : HasCompactSupport chi)
    (hs : tsupport chi ⊆ {u | (1 / 2 : ℝ) < ‖u‖ ∧ ‖u‖ < 2})
    (beta : ℝ → ℂ) (hb : ContDiff ℝ ∞ beta) (hbc : HasCompactSupport beta)
    (hbs : tsupport beta ⊆ {t | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, 1 ≤ j →
      ∀ f : Space n → ℂ, MemLp f 2 volume →
        Measurable (strongKernelMaximal (NormalFrequencyPieces.dyadicPiece chi beta j) f) ∧
          eLpNorm (strongKernelMaximal (NormalFrequencyPieces.dyadicPiece chi beta j) f) 2 volume ≤
            ENNReal.ofReal (C * (1 + (j : ℝ)) ^ ((n : ℝ) / 2) *
              (2 : ℝ) ^ (-(((n : ℝ) - 3) / 4) * (j : ℝ))) * eLpNorm f 2 volume := by
  obtain ⟨C, hC, hbound⟩ := dyadic_normalKernel_L2 n (by omega)
    (NormalFrequencyPieces.normalizedCutoff chi)
    (NormalFrequencyPieces.normalizedCutoff_contDiff chi hchi)
    (NormalFrequencyPieces.normalizedCutoff_compact chi hchic)
    ((NormalFrequencyPieces.tsupport_normalizedCutoff_subset chi).trans hs) beta hb hbc hbs
  refine ⟨C, hC, ?_⟩
  intro j _hj f hf
  rw [NormalFrequencyPieces.dyadicPiece_eq_normalKernel]
  exact hbound j f hf

end StrongSpherical.NormalKernelGlobal
