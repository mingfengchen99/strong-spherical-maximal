import SmoothingGeometry
import MarginalLocalEstimate
import SmoothingError

/-! # Product Schwartz tails outside the support box -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace StrongSpherical.ProductTail
open ProductSmoothing ScalarSmoothing SmoothingGeometry
variable {n : ℕ}

theorem norm_convolution_le_box_product (K : Space n → ℂ) (hK : Continuous K)
    (R B : ℝ) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R)
    (hb : ∀ x, ‖K x‖ ≤ B) (r : Radii n) (w : Space n) :
    ‖kernelConvolution K (productPhi r) w‖ ≤ B * ∏ i, boxScalar R (r.1 i) (w i) := by
  have he : (∫ y in MarginalEnergy.coordinateBox n R, K y * productPhi r (w - y)) =
      kernelConvolution K (productPhi r) w := by
    rw [kernelConvolution_eq_integral]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hzero : K y = 0 := by
      by_contra hn
      exact hy (hs hn)
    rw [hzero, zero_mul]
  have hc := GenericKernelRegularity.isCompact_coordinateBox n R
  have hPhi : Continuous (fun y : Space n => productPhi r (w - y)) :=
    (continuous_productPhi r).comp (continuous_const.sub continuous_id)
  rw [← he]
  calc
    _ ≤ ∫ y in MarginalEnergy.coordinateBox n R, ‖K y * productPhi r (w - y)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y in MarginalEnergy.coordinateBox n R, B * ‖productPhi r (w - y)‖ := by
      apply integral_mono ((hK.mul hPhi).norm.continuousOn.integrableOn_compact hc)
        ((continuous_const.mul hPhi.norm).continuousOn.integrableOn_compact hc)
      intro y
      change ‖K y * productPhi r (w - y)‖ ≤ B * ‖productPhi r (w - y)‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hb y) (norm_nonneg _)
    _ = _ := by
      rw [integral_const_mul]
      congr 1
      simp_rw [norm_productPhi]
      exact integral_product_box R (fun i t => ‖FourierCutoff.scaledPhi (r.1 i) (w i - t)‖)

theorem box_product_small_tail (R epsilon : ℝ) (hR : 1 ≤ R) (heps : epsilon ≤ 1)
    (r : Radii n) (hsmall : ∀ i, r.1 i ≤ epsilon) (w : Space n)
    (i : Fin n) (hi : 2 * R + 2 < |w i|) :
    (∏ j, boxScalar R (r.1 j) (w j)) ≤
      epsilon * scalarConstant R ^ n * ∏ j, unitWeight (w j) := by
  classical
  have hC : 0 ≤ scalarConstant R := (scalarConstant_pos R hR).le
  have heps0 : 0 ≤ epsilon := (r.2 i).le.trans (hsmall i)
  have hp : ∀ j : Fin n,
      boxScalar R (r.1 j) (w j) ≤
        (if j = i then epsilon else 1) * scalarConstant R * unitWeight (w j) := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [ite_true] using
        boxScalar_small_tail R _ epsilon _ hR (r.2 i) (hsmall i) heps hi
    · simp only [if_neg hji, one_mul]
      exact boxScalar_uniform R _ epsilon _ hR (r.2 j) (hsmall j) heps
  calc
    _ ≤ ∏ j, (if j = i then epsilon else 1) * scalarConstant R * unitWeight (w j) :=
      Finset.prod_le_prod (fun _ _ => boxScalar_nonneg _ _ _) (fun j _ => hp j)
    _ = _ := by
      simp_rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [Fintype.prod_ite_eq' i (fun _ => epsilon)]

/-- The far-box half of (5.20), with its complete product weight. -/
theorem norm_sub_convolution_far (K : Space n → ℂ) (hK : Continuous K)
    (R B epsilon : ℝ) (hR : 1 ≤ R)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R) (hb : ∀ x, ‖K x‖ ≤ B)
    (r : Radii n) (heps : epsilon ≤ 1) (hsmall : ∀ i, r.1 i ≤ epsilon)
    (w : Space n) (i : Fin n) (hi : 2 * R + 2 < |w i|) :
    ‖K w - kernelConvolution K (productPhi r) w‖ ≤
      scalarConstant R ^ n * epsilon * B * ∏ j, unitWeight (w j) := by
  have hzero : K w = 0 := by
    by_contra hn
    have hh := abs_le.mpr (hs hn i)
    linarith
  have hB : 0 ≤ B := (norm_nonneg (K 0)).trans (hb 0)
  rw [hzero, zero_sub, norm_neg]
  calc
    _ ≤ B * ∏ j, boxScalar R (r.1 j) (w j) := norm_convolution_le_box_product K hK R B hs hb r w
    _ ≤ B * (epsilon * scalarConstant R ^ n * ∏ j, unitWeight (w j)) :=
      mul_le_mul_of_nonneg_left (box_product_small_tail R epsilon hR heps r hsmall w i hi) hB
    _ = _ := by ring

theorem near_box_weight_lower (R : ℝ) (w : Space n)
    (hw : ∀ i, |w i| ≤ 2 * R + 2) :
    1 ≤ ((2 * R + 3) ^ 3) ^ n * ∏ i, unitWeight (w i) := by
  have hpoint : ∀ i : Fin n, 1 ≤ (2 * R + 3) ^ 3 * unitWeight (w i) := by
    intro i
    rw [unitWeight_eq, ← div_eq_mul_inv]
    apply (one_le_div₀ (by positivity : 0 < (1 + |w i|) ^ 3)).mpr
    exact pow_le_pow_left₀ (by positivity) (by linarith [hw i] : 1 + |w i| ≤ 2 * R + 3) 3
  calc
    (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ ∏ i : Fin n, (2 * R + 3) ^ 3 * unitWeight (w i) :=
      Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => hpoint i)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp

def nearConstant (n : ℕ) (R : ℝ) : ℝ :=
  (n : ℝ) * momentBase ^ (n + 1) * ((2 * R + 3) ^ 3) ^ n

def errorConstant (n : ℕ) (R : ℝ) : ℝ :=
  1 + nearConstant n R + scalarConstant R ^ n

theorem nearConstant_nonneg (n : ℕ) (R : ℝ) (hR : 1 ≤ R) : 0 ≤ nearConstant n R := by
  have hm : 0 ≤ momentBase := zero_le_one.trans one_le_momentBase
  dsimp [nearConstant]
  positivity

theorem errorConstant_pos (n : ℕ) (R : ℝ) (hR : 1 ≤ R) : 0 < errorConstant n R := by
  have hn := nearConstant_nonneg n R hR
  have hs := scalarConstant_pos R hR
  dsimp [errorConstant]
  positivity

theorem norm_sub_convolution_near (K : Space n → ℂ) (hK : Differentiable ℝ K)
    (R B epsilon : ℝ) (_hR : 1 ≤ R) (heps : 0 ≤ epsilon)
    (hb : ∀ x, ‖K x‖ ≤ B) (hd : ∀ x, ‖fderiv ℝ K x‖ ≤ B)
    (r : Radii n) (hsmall : ∀ i, r.1 i ≤ epsilon)
    (w : Space n) (hw : ∀ i, |w i| ≤ 2 * R + 2) :
    ‖K w - kernelConvolution K (productPhi r) w‖ ≤
      nearConstant n R * epsilon * B * ∏ i, unitWeight (w i) := by
  have hB : 0 ≤ B := (norm_nonneg (K 0)).trans (hb 0)
  have hm : 0 ≤ momentBase := zero_le_one.trans one_le_momentBase
  have hcoef : 0 ≤ (n : ℝ) * momentBase ^ (n + 1) * epsilon * B := by positivity
  calc
    _ ≤ (n : ℝ) * momentBase ^ (n + 1) * epsilon * B :=
      SmoothingError.norm_sub_convolution_le_small_scale K hK B hb hd r epsilon hsmall w
    _ ≤ ((n : ℝ) * momentBase ^ (n + 1) * epsilon * B) *
        (((2 * R + 3) ^ 3) ^ n * ∏ i, unitWeight (w i)) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (near_box_weight_lower R w hw) hcoef
    _ = _ := by unfold nearConstant; ring

/-- The complete rescaled (5.20), before restoring the physical radii. -/
theorem norm_sub_convolution_weighted (K : Space n → ℂ) (hK : Differentiable ℝ K)
    (R B epsilon : ℝ) (hR : 1 ≤ R) (heps0 : 0 ≤ epsilon) (heps : epsilon ≤ 1)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R)
    (hb : ∀ x, ‖K x‖ ≤ B) (hd : ∀ x, ‖fderiv ℝ K x‖ ≤ B)
    (r : Radii n) (hsmall : ∀ i, r.1 i ≤ epsilon) (w : Space n) :
    ‖K w - kernelConvolution K (productPhi r) w‖ ≤
      errorConstant n R * epsilon * B * ∏ i, unitWeight (w i) := by
  have hB : 0 ≤ B := (norm_nonneg (K 0)).trans (hb 0)
  have hW : 0 ≤ ∏ i, unitWeight (w i) := Finset.prod_nonneg (fun _ _ => unitWeight_nonneg _)
  have hnear := nearConstant_nonneg n R hR
  have hscalar := scalarConstant_pos R hR
  by_cases hfar : ∃ i : Fin n, 2 * R + 2 < |w i|
  · obtain ⟨i, hi⟩ := hfar
    refine (norm_sub_convolution_far K hK.continuous R B epsilon hR hs hb r heps hsmall w i hi).trans ?_
    have hC : scalarConstant R ^ n ≤ errorConstant n R := by unfold errorConstant; linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC heps0) hB) hW
  · have hnearW : ∀ i : Fin n, |w i| ≤ 2 * R + 2 := by
      simpa only [not_exists, not_lt] using hfar
    refine (norm_sub_convolution_near K hK R B epsilon hR heps0 hb hd r hsmall w hnearW).trans ?_
    have hC : nearConstant n R ≤ errorConstant n R := by
      unfold errorConstant
      have hp : 0 ≤ scalarConstant R ^ n := pow_nonneg hscalar.le n
      linarith
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC heps0) hB) hW

end StrongSpherical.ProductTail
