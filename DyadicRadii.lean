import Definitions
import Mathlib.Algebra.Order.Archimedean.Basic

/-! # Dyadic rectangles of radii

Every positive radius tuple has the form `2^k * t` with `t` in the original
local range.  The identities below use the normalized dilations and maximal
functions from `Definitions`, including in dimension zero.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StrongSpherical.DyadicRadii

variable {n : ℕ}

/-- Coordinatewise multiplication of positive radius tuples. -/
def multiply (a b : Radii n) : Radii n :=
  ⟨fun i => a.1 i * b.1 i, fun i => mul_pos (a.2 i) (b.2 i)⟩

@[simp] theorem multiply_apply (a b : Radii n) (i : Fin n) :
    (multiply a b).1 i = a.1 i * b.1 i := rfl

@[simp] theorem multiply_unit (a : Radii n) : multiply a (unitRadii n) = a := by
  apply Subtype.ext
  funext i
  simp [unitRadii]

@[simp] theorem unit_multiply (a : Radii n) : multiply (unitRadii n) a = a := by
  apply Subtype.ext
  funext i
  simp [unitRadii]

theorem dilationJacobian_multiply (a b : Radii n) :
    dilationJacobian (multiply a b) = dilationJacobian a * dilationJacobian b := by
  simp [dilationJacobian, Finset.prod_mul_distrib]

theorem inverseDilation_multiply (a b : Radii n) (u : Space n) :
    inverseDilation (multiply a b) u = inverseDilation b (inverseDilation a u) := by
  ext i
  simp [inverseDilation, mul_assoc, mul_left_comm, mul_comm]

/-- Normalized kernel dilation is an action of coordinatewise radii multiplication. -/
theorem dilatedKernel_multiply (K : Space n → ℂ) (a b : Radii n) :
    dilatedKernel K (multiply a b) = dilatedKernel (dilatedKernel K b) a := by
  funext u
  simp [dilatedKernel, dilationJacobian_multiply, inverseDilation_multiply,
    mul_assoc, mul_comm]

/-- The positive coordinate scales corresponding to an integer tuple. -/
def scales (k : Fin n → ℤ) : Radii n :=
  ⟨fun i => (2 : ℝ) ^ k i, fun i => zpow_pos (by norm_num) (k i)⟩

@[simp] theorem scales_apply (k : Fin n → ℤ) (i : Fin n) :
    (scales k).1 i = (2 : ℝ) ^ k i := rfl

/-- The dyadic rectangle of radii indexed by `k`. -/
def rectangle (k : Fin n → ℤ) (t : Radii n) : Radii n := multiply (scales k) t

@[simp] theorem rectangle_apply (k : Fin n → ℤ) (t : Radii n) (i : Fin n) :
    (rectangle k t).1 i = (2 : ℝ) ^ k i * t.1 i := rfl

/-- Each positive real has a dyadic scale with a remainder in `[1,2)`. -/
theorem exists_scalar_rectangle (r : ℝ) (hr : 0 < r) :
    ∃ k : ℤ, ∃ t : ℝ, t ∈ Ico (1 : ℝ) 2 ∧ r = (2 : ℝ) ^ k * t := by
  obtain ⟨k, hk⟩ := exists_mem_Ico_zpow hr (by norm_num : (1 : ℝ) < 2)
  have hpos : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
  refine ⟨k, r / (2 : ℝ) ^ k, ⟨?_, ?_⟩, ?_⟩
  · exact (le_div_iff₀ hpos).2 (by simpa using hk.1)
  · apply (div_lt_iff₀ hpos).2
    simpa [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), mul_comm] using hk.2
  · field_simp

/-- The original local range covers all radii after dyadic rescaling. -/
theorem exists_rectangle (r : Radii n) :
    ∃ k : Fin n → ℤ, ∃ t : Radii n, t ∈ localRadii n ∧ r = rectangle k t := by
  classical
  have h : ∀ i : Fin n, ∃ k : ℤ, ∃ t : ℝ,
      t ∈ Ico (1 : ℝ) 2 ∧ r.1 i = (2 : ℝ) ^ k * t :=
    fun i => exists_scalar_rectangle (r.1 i) (r.2 i)
  choose k t ht he using h
  let t' : Radii n := ⟨t, fun i => lt_of_lt_of_le zero_lt_one (ht i).1⟩
  refine ⟨k, t', (fun i => ⟨(ht i).1, (ht i).2.le⟩), ?_⟩
  apply Subtype.ext
  funext i
  exact he i

/-- The full kernel supremum is exactly the supremum over dyadic local rectangles. -/
theorem strongKernelMaximal_eq_dyadic (K f : Space n → ℂ) (x : Space n) :
    strongKernelMaximal K f x =
      ⨆ k : Fin n → ℤ, ⨆ t ∈ localRadii n,
        ‖kernelConvolution (dilatedKernel K (rectangle k t)) f x‖ₑ := by
  apply le_antisymm
  · refine iSup_le fun r => iSup_le fun _ => ?_
    obtain ⟨k, t, ht, rfl⟩ := exists_rectangle r
    exact le_iSup_of_le k (le_iSup_of_le t (le_iSup_of_le ht le_rfl))
  · refine iSup_le fun k => iSup_le fun t => iSup_le fun _ => ?_
    exact le_maximalOver univ _ x (mem_univ _)

end StrongSpherical.DyadicRadii
