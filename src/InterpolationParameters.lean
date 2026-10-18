import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-! # Actual interpolation parameters in the sharp subquadratic range -/
noncomputable section
namespace StrongSpherical.InterpolationParameters

def a (n : ℕ) : ℝ := ((n : ℝ) - 3) / 4

def critical (n : ℕ) : ℝ := ((n : ℝ) + 1) / ((n : ℝ) - 1)

def theta (p q : ℝ) : ℝ := (1 / q - 1 / p) / (1 / q - 1 / 2)

lemma theta_formula (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hq2 : q < 2) :
    theta p q = 2 * (p - q) / (p * (2 - q)) := by
  have hnum : 1 / q - 1 / p = (p - q) / (q * p) := by
    field_simp [hp.ne', hq.ne']
  have hden : 1 / q - 1 / 2 = (2 - q) / (2 * q) := by
    field_simp [hq.ne']
  rw [theta, hnum, hden]
  field_simp [hp.ne', hq.ne', (sub_pos.mpr hq2).ne']

lemma theta_pos (p q : ℝ) (hq : 0 < q) (hqp : q < p) (hp2 : p < 2) :
    0 < theta p q := by
  rw [theta_formula p q (hq.trans hqp) hq (hqp.trans hp2)]
  exact div_pos (mul_pos (by norm_num) (sub_pos.mpr hqp))
    (mul_pos (hq.trans hqp) (sub_pos.mpr (hqp.trans hp2)))

lemma theta_lt_one (p q : ℝ) (hq : 0 < q) (hqp : q < p) (hp2 : p < 2) :
    theta p q < 1 := by
  rw [theta_formula p q (hq.trans hqp) hq (hqp.trans hp2)]
  apply (div_lt_one (mul_pos (hq.trans hqp) (sub_pos.mpr (hqp.trans hp2)))).mpr
  nlinarith [mul_pos hq (sub_pos.mpr hp2)]

lemma interpolation_identity (p q : ℝ) (hp : 0 < p) (hq : 0 < q) (hq2 : q < 2) :
    1 / p = (1 - theta p q) / q + theta p q / 2 := by
  rw [theta_formula p q hp hq hq2]
  field_simp [hp.ne', hq.ne', (sub_pos.mpr hq2).ne']
  ring

/-- The sharp lower endpoint admits an actual q>1 with strictly negative
interpolated dyadic exponent. The witness is a rational expression in n and p. -/
theorem exists_below_two_parameters (n : ℕ) (hn : 4 ≤ n) (p : ℝ)
    (hcritical : critical n < p) (hp2 : p < 2) :
    ∃ q θ : ℝ, 1 < q ∧ q < p ∧ 0 < θ ∧ θ < 1 ∧
      1 / p = (1 - θ) / q + θ / 2 ∧ 1 - (1 + a n) * θ < 0 := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : 0 < (n : ℝ) - 1 := by linarith
  have hcrit1 : 1 < critical n := by
    unfold critical
    apply (one_lt_div hn1).mpr
    linarith
  have hp1 : 1 < p := hcrit1.trans hcritical
  have hp : 0 < p := zero_lt_one.trans hp1
  have hden : 0 < (n : ℝ) + 1 - 2 * p := by linarith
  let Q : ℝ := ((n : ℝ) - 3) * p / ((n : ℝ) + 1 - 2 * p)
  have hQ1 : 1 < Q := by
    dsimp [Q]
    apply (one_lt_div hden).mpr
    have h := (div_lt_iff₀ hn1).mp hcritical
    nlinarith [h]
  have hQp : Q < p := by
    dsimp [Q]
    apply (div_lt_iff₀ hden).mpr
    nlinarith [mul_pos hp (sub_pos.mpr hp2)]
  let q : ℝ := (1 + Q) / 2
  have hq1 : 1 < q := by dsimp [q]; linarith
  have hqQ : q < Q := by dsimp [q]; linarith
  have hqp : q < p := hqQ.trans hQp
  have hq : 0 < q := zero_lt_one.trans hq1
  have hq2 : q < 2 := hqp.trans hp2
  have hneg : 1 - (1 + a n) * theta p q < 0 := by
    rw [theta_formula p q hp hq hq2]
    have hcross : q * ((n : ℝ) + 1 - 2 * p) < ((n : ℝ) - 3) * p :=
      (lt_div_iff₀ hden).mp hqQ
    have hratio : 1 < (((n : ℝ) + 1) / 2 * (p - q)) / (p * (2 - q)) := by
      apply (one_lt_div (mul_pos hp (sub_pos.mpr hq2))).mpr
      nlinarith [hcross]
    have heq : (1 + a n) * (2 * (p - q) / (p * (2 - q))) =
        (((n : ℝ) + 1) / 2 * (p - q)) / (p * (2 - q)) := by
      unfold a
      ring
    rw [heq]
    linarith
  exact ⟨q, theta p q, hq1, hqp, theta_pos p q hq hqp hp2,
    theta_lt_one p q hq hqp hp2, interpolation_identity p q hp hq hq2, hneg⟩

lemma above_two_weight (p : ℝ) (hp : 2 < p) : 0 < 2 / p ∧ 2 / p < 1 := by
  have hp0 : 0 < p := lt_trans (by norm_num) hp
  exact ⟨div_pos (by norm_num) hp0, (div_lt_one hp0).mpr hp⟩

/-- Exact frequency-factor algebra for interpolation below two. The
natural dyadic power on the first endpoint is converted to a real power. -/
theorem below_two_frequency_coefficient (n j : ℕ) (Cq C2 θ : ℝ)
    (hCq : 0 ≤ Cq) (hC2 : 0 ≤ C2) :
    (Cq * (2 : ℝ) ^ j) ^ (1 - θ) *
        (C2 * (1 + (j : ℝ)) ^ ((n : ℝ) / 2) * (2 : ℝ) ^ (-a n * (j : ℝ))) ^ θ =
      (Cq ^ (1 - θ) * C2 ^ θ) * (1 + (j : ℝ)) ^ ((n : ℝ) * θ / 2) *
        (2 : ℝ) ^ ((j : ℝ) * (1 - (1 + a n) * θ)) := by
  have hw : 0 ≤ 1 + (j : ℝ) := by positivity
  have hlow : (Cq * (2 : ℝ) ^ j) ^ (1 - θ) =
      Cq ^ (1 - θ) * (2 : ℝ) ^ ((j : ℝ) * (1 - θ)) := by
    rw [Real.mul_rpow hCq (pow_nonneg (by norm_num) j),
      ← Real.rpow_natCast (2 : ℝ) j, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hhigh :
      (C2 * (1 + (j : ℝ)) ^ ((n : ℝ) / 2) * (2 : ℝ) ^ (-a n * (j : ℝ))) ^ θ =
        C2 ^ θ * (1 + (j : ℝ)) ^ ((n : ℝ) * θ / 2) *
          (2 : ℝ) ^ (-a n * (j : ℝ) * θ) := by
    rw [Real.mul_rpow (mul_nonneg hC2 (Real.rpow_nonneg hw _))
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _),
      Real.mul_rpow hC2 (Real.rpow_nonneg hw _),
      ← Real.rpow_mul hw, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      show (n : ℝ) / 2 * θ = (n : ℝ) * θ / 2 by ring]
  rw [hlow, hhigh]
  calc
    _ = (Cq ^ (1 - θ) * C2 ^ θ) * (1 + (j : ℝ)) ^ ((n : ℝ) * θ / 2) *
        ((2 : ℝ) ^ ((j : ℝ) * (1 - θ)) * (2 : ℝ) ^ (-a n * (j : ℝ) * θ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
        show (j : ℝ) * (1 - θ) + -a n * (j : ℝ) * θ =
          (j : ℝ) * (1 - (1 + a n) * θ) by ring]

/-- Exact frequency-factor algebra for interpolation with the L-infinity
endpoint. This gives the decay exponent appearing in (6.20). -/
theorem above_two_frequency_coefficient (n j : ℕ) (C2 Cinf p : ℝ) (hC2 : 0 ≤ C2) :
    (C2 * (1 + (j : ℝ)) ^ ((n : ℝ) / 2) * (2 : ℝ) ^ (-a n * (j : ℝ))) ^ (2 / p) *
        Cinf ^ (1 - 2 / p) =
      (C2 ^ (2 / p) * Cinf ^ (1 - 2 / p)) * (1 + (j : ℝ)) ^ ((n : ℝ) / p) *
        (2 : ℝ) ^ (-2 * a n * (j : ℝ) / p) := by
  have hw : 0 ≤ 1 + (j : ℝ) := by positivity
  rw [Real.mul_rpow (mul_nonneg hC2 (Real.rpow_nonneg hw _))
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _),
    Real.mul_rpow hC2 (Real.rpow_nonneg hw _),
    ← Real.rpow_mul hw, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    show (n : ℝ) / 2 * (2 / p) = (n : ℝ) / p by ring,
    show -a n * (j : ℝ) * (2 / p) = -2 * a n * (j : ℝ) / p by ring]
  ring

end StrongSpherical.InterpolationParameters
