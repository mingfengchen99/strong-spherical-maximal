import Lemma14Assembly
import KernelC1Norm
import LowProjectionL2
import HighProjectionL2

/-! # Lemma 1.4: from the local estimate to all positive radii

The proof uses the actual Fourier projections, the two physical kernel error
estimates, and strong induction on the dimension. Its only operator estimate
assumed in the final statement is the local estimate (1.12).
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators SchwartzMap ContDiff
namespace StrongSpherical.GlobalKernelEstimate
open DyadicKernelScales MarginalInduction Lemma14Assembly MaximalAssembly

/-- The uniform quantitative form of Lemma 1.4, with explicit C¹ majorants. -/
theorem exists_globalKernelBound (d : ℕ) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ GlobalKernelBound d R C := by
  classical
  induction d using Nat.strong_induction_on with
  | h d ih =>
    by_cases hd : d = 0
    · subst d
      exact ⟨1, zero_lt_one, globalKernelBound_zero R⟩
    obtain ⟨D, hD, hmarg⟩ := exists_uniform_marginal_bound d R hR ih
    obtain ⟨L, hL, hlow⟩ := LowProjectionL2.exists_lowProjection_sum_bound d R (by linarith)
    obtain ⟨H, hH, hhigh⟩ := HighProjectionL2.exists_errorProjectionMaximal_L2 d R hR
    refine ⟨assemblyConstant d L H D, assemblyConstant_pos d L H D hL.le hH.le hD.le, ?_⟩
    intro K hK hs A B hA hb hderiv hlocal M hM f hf
    have hB : 0 ≤ B := (norm_nonneg (K 0)).trans (hb 0)
    have hT : 0 ≤ frequencyGrowth d M * A + epsilon M * B := by
      have hg := frequencyGrowth_nonneg d M
      have he := (epsilon_pos M).le
      positivity
    apply (MaximalDensity.schwartz_bound_to_L2 K hK.continuous R (by linarith) hs
      (ENNReal.ofReal (assemblyConstant d L H D *
        (frequencyGrowth d M * A + epsilon M * B))) ENNReal.ofReal_ne_top ?_ f hf).2
    intro F
    apply schwartz_bound_of_pieces K hK.continuous R (by linarith) hs
      L H D A B hL.le hH.le hD.le hA hB hlocal M hM F
    · have hm : ∀ I : Set (Fin d), Fintype.card I < d →
          ∀ g : Space (Fintype.card I) → ℂ, MemLp g 2 volume →
            eLpNorm (strongKernelMaximal (CoordinateSubsets.subsetMarginal I K) g) 2 volume ≤
              ENNReal.ofReal (D * (frequencyGrowth d M * A + epsilon M * B)) *
                eLpNorm g 2 volume :=
        fun I hI g hg => hmarg I hI K hK hs A B hA hb hderiv hlocal M hM g hg
      have hl := hlow K hK.continuous hs B hb M
        (ENNReal.ofReal (D * (frequencyGrowth d M * A + epsilon M * B))) hm F
      simpa only [ENNReal.ofReal_add (mul_nonneg hD.le hT)
        (mul_nonneg (epsilon_pos M).le hB),
        ENNReal.ofReal_mul hL.le] using hl
    · have hh := hhigh K (hK.differentiable one_ne_zero) hs B hb hderiv M F
      have he : HighProjectionL2.errorProjectionMaximal K M (F.toLp 2 volume) =
          projectionMaximal K (FourierMiddle.errorOperator M) (F.toLp 2 volume) := by
        funext x
        rfl
      rw [he] at hh
      exact hh

/-- Lemma 1.4, with the canonical global C¹ size and every raw L² input.
The constant is independent of K, A, M, and f. -/
theorem lemma14 (d : ℕ) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : Space d → ℂ, ContDiff ℝ 1 K →
      Function.support K ⊆ MarginalEnergy.coordinateBox d R →
      ∀ A : ℝ, 0 ≤ A → LocalKernelBound K A →
      ∀ M : ℕ, 3 ≤ M → ∀ f : Space d → ℂ, MemLp f 2 volume →
        Measurable (strongKernelMaximal K f) ∧
          eLpNorm (strongKernelMaximal K f) 2 volume ≤
            ENNReal.ofReal (C * ((1 + (M : ℝ)) ^ ((d : ℝ) / 2) * A +
              (2 : ℝ) ^ (-(M : ℤ)) * KernelC1Norm.c1Norm K)) * eLpNorm f 2 volume := by
  obtain ⟨C, hC, hbound⟩ := exists_globalKernelBound d R hR
  refine ⟨C, hC, ?_⟩
  intro K hK hs A hA hlocal M hM f hf
  have hc := MarginalLocalEstimate.hasCompactSupport_of_box (m := d) (j := 0) K R hs
  obtain ⟨_, hb, hd⟩ := KernelC1Norm.c1Norm_bounds K hK hc
  refine ⟨DilationL2.strongKernelMaximal_measurable K hK.continuous R (by linarith) hs f hf, ?_⟩
  exact hbound K hK hs A (KernelC1Norm.c1Norm K) hA hb hd hlocal M hM f hf

end StrongSpherical.GlobalKernelEstimate
