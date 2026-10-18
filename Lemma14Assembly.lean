import MaximalAssembly
import MarginalInduction
import Lemma14Constants

/-! # Quantitative assembly of the three frequency estimates -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators SchwartzMap
namespace StrongSpherical.Lemma14Assembly
open FourierMiddle MaximalAssembly DyadicKernelScales MarginalInduction
variable {d : ℕ}

theorem eLpNorm_toLp_schwartz (f : 𝓢(Space d, ℂ)) :
    ENNReal.ofReal ‖f.toLp 2 volume‖ = eLpNorm f 2 volume := by
  rw [← MiddleMaximalL2.eLpNorm_coe_L2]
  exact eLpNorm_congr_ae (f.coeFn_toLp 2 volume)

def assemblyConstant (d : ℕ) (L H D : ℝ) : ℝ := (2 : ℝ) ^ d + L * (D + 1) + H

theorem assemblyConstant_pos (d : ℕ) (L H D : ℝ)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (hD : 0 ≤ D) : 0 < assemblyConstant d L H D := by
  unfold assemblyConstant
  positivity

theorem coefficient_le (d M : ℕ) (L H D A B : ℝ)
    (hL : 0 ≤ L) (hH : 0 ≤ H) (_hD : 0 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    (2 : ℝ) ^ d * frequencyGrowth d M * A +
      L * (D * (frequencyGrowth d M * A + epsilon M * B) + epsilon M * B) +
      H * epsilon M * B ≤
      assemblyConstant d L H D * (frequencyGrowth d M * A + epsilon M * B) := by
  have hf := frequencyGrowth_nonneg d M
  have he := (epsilon_pos M).le
  have h1 : 0 ≤ (2 : ℝ) ^ d * (epsilon M * B) := by positivity
  have h2 : 0 ≤ L * (frequencyGrowth d M * A) := by positivity
  have h3 : 0 ≤ H * (frequencyGrowth d M * A) := by positivity
  unfold assemblyConstant
  nlinarith

/-- This assembly lemma has only the two explicit frequency-piece bounds as
inputs. The final induction discharges them using the physical kernel estimates. -/
theorem schwartz_bound_of_pieces (K : Space d → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox d R)
    (L H D A B : ℝ) (hL : 0 ≤ L) (hH : 0 ≤ H) (hD : 0 ≤ D)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hloc : LocalKernelBound K A)
    (M : ℕ) (hM : 3 ≤ M) (f : 𝓢(Space d, ℂ))
    (hlow : (∑ J ∈ (Finset.univ.powerset.erase ∅),
        eLpNorm (projectionMaximal K (fun k => lowSubsetOperator M k J)
          (f.toLp 2 volume)) 2 volume) ≤
      ENNReal.ofReal (L * (D * (frequencyGrowth d M * A + epsilon M * B) + epsilon M * B)) *
        eLpNorm f 2 volume)
    (hhigh : eLpNorm (projectionMaximal K (errorOperator M) (f.toLp 2 volume)) 2 volume ≤
      ENNReal.ofReal (H * epsilon M * B) * eLpNorm f 2 volume) :
    eLpNorm (strongKernelMaximal K f) 2 volume ≤
      ENNReal.ofReal (assemblyConstant d L H D *
        (frequencyGrowth d M * A + epsilon M * B)) * eLpNorm f 2 volume := by
  have hmid := MiddleMaximalL2.eLpNorm_middleMaximal_le K hK R hR hs
    (ENNReal.ofReal A) hloc M hM (f.toLp 2 volume)
  rw [eLpNorm_toLp_schwartz] at hmid
  have hmid' : eLpNorm (MiddleMaximalL2.middleMaximal K M (f.toLp 2 volume)) 2 volume ≤
      ENNReal.ofReal ((2 : ℝ) ^ d * frequencyGrowth d M * A) * eLpNorm f 2 volume := by
    refine hmid.trans (mul_le_mul' ?_ le_rfl)
    rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    exact ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (Lemma14Constants.sqrt_overlap_le d M) hA)
  have hraw := strongKernelMaximal_congr_ae K _ _ (f.coeFn_toLp 2 volume)
  rw [← hraw]
  calc
    _ ≤ _ := eLpNorm_strongKernelMaximal_le_pieces K hK R hR hs M hM (f.toLp 2 volume)
    _ ≤ (ENNReal.ofReal ((2 : ℝ) ^ d * frequencyGrowth d M * A) * eLpNorm f 2 volume +
        ENNReal.ofReal (L * (D * (frequencyGrowth d M * A + epsilon M * B) + epsilon M * B)) *
          eLpNorm f 2 volume) + ENNReal.ofReal (H * epsilon M * B) * eLpNorm f 2 volume :=
      add_le_add (add_le_add hmid' hlow) hhigh
    _ = ENNReal.ofReal ((2 : ℝ) ^ d * frequencyGrowth d M * A +
        L * (D * (frequencyGrowth d M * A + epsilon M * B) + epsilon M * B) +
        H * epsilon M * B) * eLpNorm f 2 volume := by
      have hf := frequencyGrowth_nonneg d M
      have he := (epsilon_pos M).le
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_add (by positivity) (by positivity)]
      ring
    _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal
      (coefficient_le d M L H D A B hL hH hD hA hB)) le_rfl

end StrongSpherical.Lemma14Assembly
