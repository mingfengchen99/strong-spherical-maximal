import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Exact balancing identities for distribution-function interpolation -/
noncomputable section
namespace StrongSpherical.InterpolationScaling

/-- The positive cutoff threshold that balances the two endpoint powers. -/
def balancingThreshold (A B q r : ℝ) : ℝ :=
  (A ^ q / B ^ r) ^ (1 / (r - q))

theorem balancingThreshold_pos (A B q r : ℝ) (hA : 0 < A) (hB : 0 < B) :
    0 < balancingThreshold A B q r :=
  Real.rpow_pos_of_pos (div_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hB _)) _

theorem log_balancingThreshold (A B q r : ℝ) (hA : 0 < A) (hB : 0 < B) :
    Real.log (balancingThreshold A B q r) = (q * Real.log A - r * Real.log B) / (r - q) := by
  unfold balancingThreshold
  rw [Real.log_rpow (div_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hB _)),
    Real.log_div (Real.rpow_pos_of_pos hA _).ne' (Real.rpow_pos_of_pos hB _).ne',
    Real.log_rpow hA, Real.log_rpow hB]
  ring

private theorem balance_power_product (A B q r p θ u v s : ℝ)
    (hA : 0 < A) (hB : 0 < B)
    (hu : u + s * q / (r - q) = p * (1 - θ))
    (hv : v - s * r / (r - q) = p * θ) :
    A ^ u * B ^ v * balancingThreshold A B q r ^ s =
      (A ^ (1 - θ) * B ^ θ) ^ p := by
  have hγ := balancingThreshold_pos A B q r hA hB
  have hC : 0 < A ^ (1 - θ) * B ^ θ :=
    mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hB _)
  apply Real.log_injOn_pos
    (mul_pos (mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hB _))
      (Real.rpow_pos_of_pos hγ _)) (Real.rpow_pos_of_pos hC _)
  have hleft : Real.log (A ^ u * B ^ v * balancingThreshold A B q r ^ s) =
      (u + s * q / (r - q)) * Real.log A +
        (v - s * r / (r - q)) * Real.log B := by
    rw [Real.log_mul
        (mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hB _)).ne'
        (Real.rpow_pos_of_pos hγ _).ne',
      Real.log_mul (Real.rpow_pos_of_pos hA _).ne' (Real.rpow_pos_of_pos hB _).ne',
      Real.log_rpow hA, Real.log_rpow hB, Real.log_rpow hγ,
      log_balancingThreshold A B q r hA hB]
    ring
  rw [hleft, Real.log_rpow hC,
    Real.log_mul (Real.rpow_pos_of_pos hA _).ne' (Real.rpow_pos_of_pos hB _).ne',
    Real.log_rpow hA, Real.log_rpow hB, hu, hv]
  ring

/-- Both terms in the split layer-cake integral have exactly the interpolated
coefficient to the p-th power. The interpolation relation is the usual one. -/
theorem balanced_terms (A B q p r θ : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hq : 0 < q) (hqp : q < p) (hpr : p < r)
    (hinterp : 1 / p = (1 - θ) / q + θ / r) :
    A ^ q * balancingThreshold A B q r ^ (q - p) =
        (A ^ (1 - θ) * B ^ θ) ^ p ∧
      B ^ r * balancingThreshold A B q r ^ (r - p) =
        (A ^ (1 - θ) * B ^ θ) ^ p := by
  have hp : 0 < p := hq.trans hqp
  have hr : 0 < r := hp.trans hpr
  have hrq : 0 < r - q := sub_pos.mpr (hqp.trans hpr)
  have hrel : θ * p * (r - q) = r * (p - q) := by
    have h := congrArg (fun z : ℝ => z * (p * q * r)) hinterp
    field_simp [hq.ne', hp.ne', hr.ne'] at h
    nlinarith [h]
  constructor
  · have h := balance_power_product A B q r p θ q 0 (q - p) hA hB
      (by field_simp [hrq.ne']; nlinarith [hrel])
      (by field_simp [hrq.ne']; nlinarith [hrel])
    simpa only [Real.rpow_zero, mul_one] using h
  · have h := balance_power_product A B q r p θ 0 r (r - p) hA hB
      (by field_simp [hrq.ne']; nlinarith [hrel])
      (by field_simp [hrq.ne']; nlinarith [hrel])
    simpa only [Real.rpow_zero, one_mul] using h

end StrongSpherical.InterpolationScaling
