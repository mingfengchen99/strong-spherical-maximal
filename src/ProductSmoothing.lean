import FourierCutoff
import DilationL2
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.Calculus.MeanValue

/-! # The actual normalized product smoothing kernels -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators SchwartzMap

namespace StrongSpherical.ProductSmoothing
open FourierCutoff
variable {n : ℕ}

def phiL1 : ℝ := ∫ t : ℝ, ‖phi t‖
def phiMoment : ℝ := ∫ t : ℝ, |t| * ‖phi t‖

theorem phiL1_nonneg : 0 ≤ phiL1 := integral_nonneg (fun _ => norm_nonneg _)
theorem phiMoment_nonneg : 0 ≤ phiMoment :=
  integral_nonneg (fun _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))

theorem integrable_phiMoment : Integrable (fun t : ℝ => |t| * ‖phi t‖) := by
  simpa only [Real.norm_eq_abs, pow_one] using phi.integrable_pow_mul volume 1

theorem continuous_scaledPhi (v : ℝ) : Continuous (scaledPhi v) :=
  continuous_const.mul (phi.continuous.comp (continuous_const.mul continuous_id))

theorem norm_scaledPhi (v : ℝ) (hv : 0 < v) (t : ℝ) :
    ‖scaledPhi v t‖ = v⁻¹ * ‖phi (v⁻¹ * t)‖ := by
  simp [scaledPhi, abs_of_pos hv]

theorem integral_norm_scaledPhi (v : ℝ) (hv : 0 < v) :
    (∫ t : ℝ, ‖scaledPhi v t‖) = phiL1 := by
  simp_rw [norm_scaledPhi v hv]
  rw [integral_const_mul, Measure.integral_comp_inv_mul_left (fun t : ℝ => ‖phi t‖) v,
    abs_of_pos hv]
  change v⁻¹ * (v * phiL1) = phiL1
  rw [← mul_assoc, inv_mul_cancel₀ hv.ne', one_mul]

theorem scaledPhi_moment_integrand (v : ℝ) (hv : 0 < v) (t : ℝ) :
    |t| * ‖scaledPhi v t‖ = |v⁻¹ * t| * ‖phi (v⁻¹ * t)‖ := by
  rw [norm_scaledPhi v hv, abs_mul, abs_of_pos (inv_pos.mpr hv)]
  ring

theorem integrable_scaledPhi_moment (v : ℝ) (hv : 0 < v) :
    Integrable (fun t : ℝ => |t| * ‖scaledPhi v t‖) := by
  simp_rw [scaledPhi_moment_integrand v hv]
  exact integrable_phiMoment.comp_smul (inv_ne_zero hv.ne')

theorem integral_scaledPhi_moment (v : ℝ) (hv : 0 < v) :
    (∫ t : ℝ, |t| * ‖scaledPhi v t‖) = v * phiMoment := by
  simp_rw [scaledPhi_moment_integrand v hv]
  rw [Measure.integral_comp_inv_mul_left (fun t : ℝ => |t| * ‖phi t‖) v, abs_of_pos hv]
  rfl

def productPhi (r : Radii n) (x : Space n) : ℂ :=
  ∏ i, scaledPhi (r.1 i) (x i)

def productWeight (r : Radii n) (x : Space n) : ℝ :=
  ∏ i, (r.1 i)⁻¹ * (1 + |x i| / r.1 i) ^ (-(3 : ℤ))

theorem productWeight_nonneg (r : Radii n) (x : Space n) : 0 ≤ productWeight r x := by
  apply Finset.prod_nonneg
  intro i _
  exact mul_nonneg (inv_nonneg.mpr (r.2 i).le)
    (zpow_nonneg (add_nonneg zero_le_one (div_nonneg (abs_nonneg _) (r.2 i).le)) _)

theorem continuous_productPhi (r : Radii n) : Continuous (productPhi r) := by
  apply continuous_finsetProd
  intro i _
  exact (continuous_scaledPhi _).comp (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i)

theorem norm_productPhi (r : Radii n) (x : Space n) :
    ‖productPhi r x‖ = ∏ i, ‖scaledPhi (r.1 i) (x i)‖ :=
  norm_prod _ _

theorem integrable_product_functions {𝕜 : Type*} [RCLike 𝕜]
    (F : Fin n → ℝ → 𝕜) (hF : ∀ i, Integrable (F i)) :
    Integrable (fun x : Space n => ∏ i, F i (x i)) := by
  exact ((PiLp.volume_preserving_ofLp (Fin n)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding).2
      (Integrable.fintype_prod hF)

theorem integral_product_functions {𝕜 : Type*} [RCLike 𝕜]
    (F : Fin n → ℝ → 𝕜) :
    (∫ x : Space n, ∏ i, F i (x i)) = ∏ i, ∫ t : ℝ, F i t := by
  calc
    _ = ∫ x : Fin n → ℝ, ∏ i, F i (x i) :=
      (PiLp.volume_preserving_ofLp (Fin n)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding _
    _ = _ := integral_fin_nat_prod_volume_eq_prod F

theorem integrable_productPhi (r : Radii n) : Integrable (productPhi r) :=
  integrable_product_functions _ (fun i => integrable_scaledPhi _ (r.2 i))

theorem integral_productPhi (r : Radii n) : (∫ x, productPhi r x) = 1 := by
  change (∫ x : Space n, ∏ i, scaledPhi (r.1 i) (x i)) = 1
  rw [integral_product_functions (fun i t => scaledPhi (r.1 i) t)]
  simp only [integral_scaledPhi _ (r.2 _), Finset.prod_const_one]

theorem integral_norm_productPhi (r : Radii n) :
    (∫ x, ‖productPhi r x‖) = phiL1 ^ n := by
  simp_rw [norm_productPhi]
  rw [integral_product_functions (fun i t => ‖scaledPhi (r.1 i) t‖)]
  simp only [integral_norm_scaledPhi _ (r.2 _), Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem norm_le_coordinate_sum (x : Space n) : ‖x‖ ≤ ∑ i, |x i| := by
  have he : x = ∑ i : Fin n, PiLp.single 2 i (x i) := by
    ext i
    simp
  calc
    _ = ‖∑ i : Fin n, PiLp.single 2 i (x i)‖ := congrArg norm he
    _ ≤ ∑ i : Fin n, ‖(PiLp.single 2 i (x i) : Space n)‖ :=
      norm_sum_le Finset.univ (fun i => (PiLp.single 2 i (x i) : Space n))
    _ = _ := by simp only [PiLp.norm_single, Real.norm_eq_abs]

def momentBase : ℝ := 1 + phiL1 + phiMoment

theorem one_le_momentBase : 1 ≤ momentBase := by
  unfold momentBase
  linarith [phiL1_nonneg, phiMoment_nonneg]

theorem phiL1_le_momentBase : phiL1 ≤ momentBase := by
  unfold momentBase
  linarith [phiMoment_nonneg]

theorem phiMoment_le_momentBase : phiMoment ≤ momentBase := by
  unfold momentBase
  linarith [phiL1_nonneg]

def momentFamily (r : Radii n) (i j : Fin n) (t : ℝ) : ℝ :=
  if j = i then |t| * ‖scaledPhi (r.1 j) t‖ else ‖scaledPhi (r.1 j) t‖

theorem momentFamily_product (r : Radii n) (i : Fin n) (x : Space n) :
    (∏ j, momentFamily r i j (x j)) = |x i| * ‖productPhi r x‖ := by
  have he : ∀ j : Fin n, momentFamily r i j (x j) =
      (if j = i then |x j| else 1) * ‖scaledPhi (r.1 j) (x j)‖ := by
    intro j
    by_cases h : j = i <;> simp [momentFamily, h]
  simp_rw [he]
  rw [Finset.prod_mul_distrib, Fintype.prod_ite_eq', norm_productPhi]

theorem integrable_coordinateMoment (r : Radii n) (i : Fin n) :
    Integrable (fun x : Space n => |x i| * ‖productPhi r x‖) := by
  have h : ∀ j : Fin n, Integrable (momentFamily r i j) := by
    intro j
    change Integrable (fun t : ℝ => momentFamily r i j t)
    by_cases h : j = i
    · simpa only [momentFamily, if_pos h] using integrable_scaledPhi_moment _ (r.2 j)
    · simpa only [momentFamily, if_neg h] using (integrable_scaledPhi _ (r.2 j)).norm
  simpa only [momentFamily_product] using integrable_product_functions _ h

theorem integral_coordinateMoment (r : Radii n) (i : Fin n) :
    (∫ x : Space n, |x i| * ‖productPhi r x‖) =
      (r.1 i * phiMoment) * ∏ _j ∈ Finset.univ.erase i, phiL1 := by
  classical
  calc
    _ = ∫ x : Space n, ∏ j, momentFamily r i j (x j) := by
      simp_rw [momentFamily_product]
    _ = ∏ j, ∫ t, momentFamily r i j t := integral_product_functions _
    _ = _ := by
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      have hi : momentFamily r i i = fun t : ℝ => |t| * ‖scaledPhi (r.1 i) t‖ := by
        funext t
        simp [momentFamily]
      rw [hi, integral_scaledPhi_moment _ (r.2 i)]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp only [momentFamily, if_neg hji]
      exact integral_norm_scaledPhi _ (r.2 j)

theorem coordinateMoment_le (r : Radii n) (epsilon : ℝ)
    (hscale : ∀ i, r.1 i ≤ epsilon) (i : Fin n) :
    (∫ x : Space n, |x i| * ‖productPhi r x‖) ≤ epsilon * momentBase ^ (n + 1) := by
  have heps : 0 ≤ epsilon := (r.2 i).le.trans (hscale i)
  have hbase : 0 ≤ momentBase := zero_le_one.trans one_le_momentBase
  have hp : (∏ _j ∈ Finset.univ.erase i, phiL1) ≤ momentBase ^ n := by
    calc
      _ ≤ ∏ _j ∈ Finset.univ.erase i, momentBase :=
        Finset.prod_le_prod (fun _ _ => phiL1_nonneg) (fun _ _ => phiL1_le_momentBase)
      _ = momentBase ^ (Finset.univ.erase i).card := by simp
      _ ≤ momentBase ^ n := by
        apply pow_le_pow_right₀ one_le_momentBase
        exact (Finset.card_le_card (Finset.erase_subset i Finset.univ)).trans (by simp)
  rw [integral_coordinateMoment]
  calc
    _ ≤ (epsilon * momentBase) * momentBase ^ n :=
      mul_le_mul (mul_le_mul (hscale i) phiMoment_le_momentBase phiMoment_nonneg heps)
        hp (Finset.prod_nonneg (fun _ _ => phiL1_nonneg)) (mul_nonneg heps hbase)
    _ = _ := by rw [pow_succ]; ring

theorem integrable_normMoment (r : Radii n) :
    Integrable (fun x : Space n => ‖x‖ * ‖productPhi r x‖) := by
  have h := integrable_finsetSum Finset.univ (fun i _ => integrable_coordinateMoment r i)
  apply h.mono'
  · exact (continuous_norm.mul (continuous_productPhi r).norm).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    simpa only [Finset.sum_mul] using
      mul_le_mul_of_nonneg_right (norm_le_coordinate_sum x) (norm_nonneg (productPhi r x))

theorem integral_normMoment_le (r : Radii n) (epsilon : ℝ) (hscale : ∀ i, r.1 i ≤ epsilon) :
    (∫ x : Space n, ‖x‖ * ‖productPhi r x‖) ≤ (n : ℝ) * epsilon * momentBase ^ (n + 1) := by
  calc
    _ ≤ ∫ x : Space n, ∑ i : Fin n, |x i| * ‖productPhi r x‖ := by
      apply integral_mono (integrable_normMoment r)
        (integrable_finsetSum Finset.univ (fun i _ => integrable_coordinateMoment r i))
      intro x
      simpa only [Finset.sum_mul] using
        mul_le_mul_of_nonneg_right (norm_le_coordinate_sum x) (norm_nonneg (productPhi r x))
    _ = ∑ i : Fin n, ∫ x : Space n, |x i| * ‖productPhi r x‖ :=
      integral_finsetSum Finset.univ (fun i _ => integrable_coordinateMoment r i)
    _ ≤ ∑ _i : Fin n, epsilon * momentBase ^ (n + 1) :=
      Finset.sum_le_sum (fun i _ => coordinateMoment_le r epsilon hscale i)
    _ = _ := by simp; ring

end StrongSpherical.ProductSmoothing
