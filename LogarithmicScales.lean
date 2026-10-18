import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-! # Choosing the separation scale in the local-to-global estimate

The scale is an actual natural ceiling. All constants below are independent
of the spectral parameter; no estimate on the chosen scale is assumed.
-/
noncomputable section

namespace StrongSpherical.LogarithmicScales

/-- The decay exponent in (1.14) and (6.11). -/
def decayExponent (n : ℕ) : ℝ := ((n : ℝ) - 3) / 4

def halfDimension (n : ℕ) : ℝ := (n : ℝ) / 2

def scaleSlope (n : ℕ) : ℝ := decayExponent n + 2

/-- A separation scale for a base-two logarithmic parameter. -/
def scaleAt (n : ℕ) (t : ℝ) : ℕ := ⌈scaleSlope n * t⌉₊ + 3

def dyadicConstant (n : ℕ) : ℝ := 2 * (scaleSlope n + 5) ^ halfDimension n

def logarithmicConstant (n : ℕ) : ℝ :=
  dyadicConstant n * (2 / Real.log 2) ^ halfDimension n

lemma scaleSlope_pos (n : ℕ) : 0 < scaleSlope n := by
  unfold scaleSlope decayExponent
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith

lemma halfDimension_nonneg (n : ℕ) : 0 ≤ halfDimension n := by
  unfold halfDimension
  positivity

lemma scaleAt_ge_three (n : ℕ) (t : ℝ) : 3 ≤ scaleAt n t := by
  unfold scaleAt
  omega

lemma scaleAt_lower (n : ℕ) (t : ℝ) : scaleSlope n * t ≤ (scaleAt n t : ℝ) := by
  have h := Nat.le_ceil (scaleSlope n * t)
  unfold scaleAt
  push_cast
  linarith

lemma scaleAt_upper (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    1 + (scaleAt n t : ℝ) ≤ (scaleSlope n + 5) * (1 + t) := by
  have h := Nat.ceil_lt_add_one (mul_nonneg (scaleSlope_pos n).le ht)
  unfold scaleAt
  push_cast
  nlinarith [scaleSlope_pos n]

lemma dyadicConstant_pos (n : ℕ) : 0 < dyadicConstant n := by
  unfold dyadicConstant
  exact mul_pos (by norm_num) (Real.rpow_pos_of_pos (by linarith [scaleSlope_pos n]) _)

lemma logarithmicConstant_pos (n : ℕ) : 0 < logarithmicConstant n := by
  unfold logarithmicConstant
  exact mul_pos (dyadicConstant_pos n)
    (Real.rpow_pos_of_pos (div_pos (by norm_num) (Real.log_pos (by norm_num))) _)

/-- The ceiling makes the exponentially small error no larger than the principal decay. -/
lemma scaleAt_error (n : ℕ) (t : ℝ) :
    (2 : ℝ) ^ (-(scaleAt n t : ℤ)) * (2 : ℝ) ^ (2 * t) ≤
      (2 : ℝ) ^ (-decayExponent n * t) := by
  have hM := scaleAt_lower n t
  have hz : (2 : ℝ) ^ (-(scaleAt n t : ℤ)) = (2 : ℝ) ^ (-(scaleAt n t : ℝ)) := by
    rw [← Real.rpow_intCast]
    simp only [Int.cast_neg, Int.cast_natCast]
  rw [hz, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  unfold scaleSlope at hM
  nlinarith

/-- The quantitative estimate with a real base-two logarithmic parameter. -/
theorem scaleAt_bound (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (1 + (scaleAt n t : ℝ)) ^ halfDimension n * (2 : ℝ) ^ (-decayExponent n * t) +
      (2 : ℝ) ^ (-(scaleAt n t : ℤ)) * (2 : ℝ) ^ (2 * t) ≤
        dyadicConstant n * (1 + t) ^ halfDimension n *
          (2 : ℝ) ^ (-decayExponent n * t) := by
  let W : ℝ := (2 : ℝ) ^ (-decayExponent n * t)
  have hW : 0 ≤ W := (Real.rpow_pos_of_pos (by norm_num) _).le
  have hq := halfDimension_nonneg n
  have hM0 : (0 : ℝ) ≤ (scaleAt n t : ℝ) := Nat.cast_nonneg _
  have hA : 1 ≤ (1 + (scaleAt n t : ℝ)) ^ halfDimension n :=
    Real.one_le_rpow (x := 1 + (scaleAt n t : ℝ)) (by linarith) hq
  have htop : (1 + (scaleAt n t : ℝ)) ^ halfDimension n ≤
      (scaleSlope n + 5) ^ halfDimension n * (1 + t) ^ halfDimension n := by
    rw [← Real.mul_rpow (by linarith [scaleSlope_pos n]) (by linarith)]
    exact Real.rpow_le_rpow (by positivity) (scaleAt_upper n t ht) hq
  have he := scaleAt_error n t
  change _ ≤ dyadicConstant n * (1 + t) ^ halfDimension n * W
  have hfirst := mul_le_mul_of_nonneg_right htop hW
  have hsecond := mul_le_mul_of_nonneg_right hA hW
  unfold dyadicConstant
  dsimp [W] at *
  nlinarith

/-- The dyadic parameter choice, with a constant depending only on dimension. -/
theorem dyadic_scale_bound (n j : ℕ) :
    ∃ M : ℕ, 3 ≤ M ∧
      (1 + (M : ℝ)) ^ ((n : ℝ) / 2) * (2 : ℝ) ^ (-decayExponent n * (j : ℝ)) +
        (2 : ℝ) ^ (-(M : ℤ)) * (2 : ℝ) ^ (2 * (j : ℝ)) ≤
          dyadicConstant n * (1 + (j : ℝ)) ^ ((n : ℝ) / 2) *
            (2 : ℝ) ^ (-decayExponent n * (j : ℝ)) := by
  exact ⟨scaleAt n j, scaleAt_ge_three n j, scaleAt_bound n j (Nat.cast_nonneg j)⟩

lemma one_add_logb_le (lam : ℝ) (hlam : 1 ≤ lam) :
    1 + Real.logb 2 lam ≤ (2 / Real.log 2) * Real.log (2 + lam) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlam0 : 0 < lam := by linarith
  have h1 : Real.log 2 ≤ Real.log (2 + lam) := Real.log_le_log (by norm_num) (by linarith)
  have h2 : Real.log lam ≤ Real.log (2 + lam) := Real.log_le_log hlam0 (by linarith)
  unfold Real.logb
  calc
    1 + Real.log lam / Real.log 2 = (Real.log 2 + Real.log lam) / Real.log 2 := by
      field_simp
    _ ≤ (2 * Real.log (2 + lam)) / Real.log 2 :=
      div_le_div_of_nonneg_right (by linarith) hl2.le
    _ = (2 / Real.log 2) * Real.log (2 + lam) := by ring

/-- The explicit ceiling choice giving the logarithmic loss in (1.14). -/
theorem logarithmic_scale_bound (n : ℕ) (lam : ℝ) (hlam : 1 ≤ lam) :
    ∃ M : ℕ, 3 ≤ M ∧
      (1 + (M : ℝ)) ^ ((n : ℝ) / 2) * lam ^ (-decayExponent n) +
        (2 : ℝ) ^ (-(M : ℤ)) * lam ^ 2 ≤
          logarithmicConstant n * (Real.log (2 + lam)) ^ ((n : ℝ) / 2) *
            lam ^ (-decayExponent n) := by
  let t := Real.logb 2 lam
  have ht : 0 ≤ t := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) hlam
  have hlam0 : 0 < lam := by linarith
  have hpow : (2 : ℝ) ^ t = lam :=
    Real.rpow_logb (by norm_num) (by norm_num) hlam0
  have hdec : (2 : ℝ) ^ (-decayExponent n * t) = lam ^ (-decayExponent n) := by
    rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), hpow]
  have hsq : (2 : ℝ) ^ (2 * t) = lam ^ 2 := by
    rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), hpow]
    norm_cast
  refine ⟨scaleAt n t, scaleAt_ge_three n t, ?_⟩
  have h := scaleAt_bound n t ht
  rw [hdec, hsq] at h
  apply h.trans
  have hlog : (1 + t) ^ halfDimension n ≤
      (2 / Real.log 2) ^ halfDimension n * Real.log (2 + lam) ^ halfDimension n := by
    rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 / Real.log 2)
      (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + lam))]
    exact Real.rpow_le_rpow (by linarith) (one_add_logb_le lam hlam) (halfDimension_nonneg n)
  have hC : 0 ≤ dyadicConstant n := (dyadicConstant_pos n).le
  have hW : 0 ≤ lam ^ (-decayExponent n) := (Real.rpow_pos_of_pos hlam0 _).le
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog hC) hW
  simpa only [logarithmicConstant, halfDimension, mul_assoc] using hh

/-- A fixed positive constant works for every real spectral parameter. -/
theorem exists_logarithmic_scale (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 1 ≤ lam → ∃ M : ℕ, 3 ≤ M ∧
      (1 + (M : ℝ)) ^ ((n : ℝ) / 2) * lam ^ (-decayExponent n) +
        (2 : ℝ) ^ (-(M : ℤ)) * lam ^ 2 ≤
          C * (Real.log (2 + lam)) ^ ((n : ℝ) / 2) * lam ^ (-decayExponent n) :=
  ⟨logarithmicConstant n, logarithmicConstant_pos n, logarithmic_scale_bound n⟩

/-- A fixed positive constant works for every dyadic spectral parameter. -/
theorem exists_dyadic_scale (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ j : ℕ, ∃ M : ℕ, 3 ≤ M ∧
      (1 + (M : ℝ)) ^ ((n : ℝ) / 2) * (2 : ℝ) ^ (-decayExponent n * (j : ℝ)) +
        (2 : ℝ) ^ (-(M : ℤ)) * (2 : ℝ) ^ (2 * (j : ℝ)) ≤
          C * (1 + (j : ℝ)) ^ ((n : ℝ) / 2) *
            (2 : ℝ) ^ (-decayExponent n * (j : ℝ)) :=
  ⟨dyadicConstant n, dyadicConstant_pos n, dyadic_scale_bound n⟩

end StrongSpherical.LogarithmicScales
