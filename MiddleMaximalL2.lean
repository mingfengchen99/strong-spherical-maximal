import DilationL2
import FourierMiddle
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! # The actual middle-frequency maximal estimate (5.16)--(5.17) -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StrongSpherical.MiddleMaximalL2
open FourierMiddle DilationL2
variable {d : ℕ}

/-- Each dyadic rectangle acts on its actual Plancherel middle-frequency projection. -/
def middleMaximal (K : Space d → ℂ) (M : ℕ) (f : L2 d) (x : Space d) : ℝ≥0∞ :=
  ⨆ k : Fin d → ℤ, rectangleMaximal K (DyadicRadii.scales k)
    (middleOperator M k f) x

theorem measurable_middleMaximal (K : Space d → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox d R)
    (M : ℕ) (f : L2 d) : Measurable (middleMaximal K M f) := by
  exact Measurable.iSup fun k => measurable_rectangleMaximal K hK R hR hs
    (DyadicRadii.scales k) (middleOperator M k f) (Lp.memLp _)

theorem eLpNorm_coe_L2 (f : L2 d) :
    eLpNorm (f : Space d → ℂ) 2 volume = ENNReal.ofReal ‖f‖ := by
  rw [← Lp.enorm_def, ← ofReal_norm]

/-- Squared middle-frequency energy: the local bound and genuine Plancherel
overlap give exactly the polynomial loss from (5.16). -/
theorem middleMaximal_energy (K : Space d → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox d R)
    (A : ℝ≥0∞)
    (hlocal : ∀ g : Space d → ℂ, MemLp g 2 volume →
      eLpNorm (localKernelMaximal K g) 2 volume ≤ A * eLpNorm g 2 volume)
    (M : ℕ) (hM : 3 ≤ M) (f : L2 d) :
    (∫⁻ x, middleMaximal K M f x ^ 2) ≤
      ENNReal.ofReal (((2 * M + 2) ^ d : ℕ) : ℝ) * A ^ 2 * ENNReal.ofReal (‖f‖ ^ 2) := by
  let B : (Fin d → ℤ) → Space d → ℝ≥0∞ := fun k =>
    rectangleMaximal K (DyadicRadii.scales k) (middleOperator M k f)
  have hB : ∀ k, Measurable (B k) := fun k =>
    measurable_rectangleMaximal K hK R hR hs (DyadicRadii.scales k)
      (middleOperator M k f) (Lp.memLp _)
  have hterm : ∀ k, (∫⁻ x, B k x ^ 2) ≤ A ^ 2 * ENNReal.ofReal (‖middleOperator M k f‖ ^ 2) := by
    intro k
    have h := pow_le_pow_left'
      (rectangle_local_bound K A hlocal (DyadicRadii.scales k)
        (middleOperator M k f) (Lp.memLp _)) 2
    rw [mul_pow, eLpNorm_coe_L2,
      ← ENNReal.ofReal_pow (norm_nonneg _) 2] at h
    simpa only [DilationL2.eLpNorm_two_sq, enorm_eq_self, B] using h
  calc
    _ ≤ ∫⁻ x, ∑' k : Fin d → ℤ, B k x ^ 2 := by
      apply lintegral_mono
      intro x
      change (⨆ k, B k x) ^ 2 ≤ _
      rw [ENNReal.iSup_pow]
      exact iSup_le fun k => ENNReal.le_tsum k
    _ = ∑' k : Fin d → ℤ, ∫⁻ x, B k x ^ 2 :=
      lintegral_tsum (fun k => (hB k).pow_const 2 |>.aemeasurable)
    _ ≤ ∑' k : Fin d → ℤ, A ^ 2 * ENNReal.ofReal (‖middleOperator M k f‖ ^ 2) :=
      ENNReal.tsum_le_tsum hterm
    _ = A ^ 2 * ENNReal.ofReal (∑' k : Fin d → ℤ, ‖middleOperator M k f‖ ^ 2) := by
      rw [ENNReal.tsum_mul_left,
        ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (summable_middle_energy M hM f)]
    _ ≤ A ^ 2 * ENNReal.ofReal
        ((((2 * M + 2) ^ d : ℕ) : ℝ) * ‖f‖ ^ 2) := by
      exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (middle_plancherel M hM f))
    _ = _ := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      ring

theorem eLpNorm_middleMaximal_le (K : Space d → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox d R)
    (A : ℝ≥0∞)
    (hlocal : ∀ g : Space d → ℂ, MemLp g 2 volume →
      eLpNorm (localKernelMaximal K g) 2 volume ≤ A * eLpNorm g 2 volume)
    (M : ℕ) (hM : 3 ≤ M) (f : L2 d) :
    eLpNorm (middleMaximal K M f) 2 volume ≤
      ENNReal.ofReal (Real.sqrt (((2 * M + 2) ^ d : ℕ) : ℝ)) * A * ENNReal.ofReal ‖f‖ := by
  apply (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [mul_pow, mul_pow, DilationL2.eLpNorm_two_sq]
  simp only [enorm_eq_self]
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _) 2, Real.sq_sqrt (Nat.cast_nonneg _),
    ← ENNReal.ofReal_pow (norm_nonneg _) 2]
  exact middleMaximal_energy K hK R hR hs A hlocal M hM f

end StrongSpherical.MiddleMaximalL2
