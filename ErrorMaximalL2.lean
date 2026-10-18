import RectangularMaximal
import ScalarSmoothing

/-! # Product-weight envelopes for actual error kernels and partial smoothing -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StrongSpherical.ErrorMaximalL2
open RectangularMaximal ProductSmoothing MaximalWeight ScalarSmoothing FourierCutoff
variable {d : ℕ}

/-- A pointwise positive envelope gives a genuine L² norm estimate. The output
may be complex or extended nonnegative; its norm is handled uniformly. -/
theorem eLpNorm_le_of_enorm_envelope {E : Type*} [ENorm E]
    (B : Space d → E) (f : Space d → ℂ) (hf : Measurable f) (c : ℝ≥0∞)
    (hB : ∀ x, ‖B x‖ₑ ≤ c * controllingMaximal d (fun y => ‖f y‖ₑ) x) :
    eLpNorm B 2 volume ≤ c * (8 : ℝ≥0∞) ^ d * eLpNorm f 2 volume := by
  apply (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [DilationL2.eLpNorm_two_sq]
  have hN := pow_le_pow_left'
    (eLpNorm_controllingMaximal_le d (fun y => ‖f y‖ₑ) hf.enorm) 2
  rw [eLpNorm_two_sq_ennreal, eLpNorm_enorm, mul_pow] at hN
  calc
    _ ≤ ∫⁻ x, c ^ 2 * controllingMaximal d (fun y => ‖f y‖ₑ) x ^ 2 := by
      apply lintegral_mono
      intro x
      simpa only [mul_pow] using pow_le_pow_left' (hB x) 2
    _ = c ^ 2 * ∫⁻ x, controllingMaximal d (fun y => ‖f y‖ₑ) x ^ 2 :=
      lintegral_const_mul _ ((measurable_controllingMaximal d _ hf.enorm).pow_const 2)
    _ ≤ c ^ 2 * (((8 : ℝ≥0∞) ^ d) ^ 2 * eLpNorm f 2 volume ^ 2) :=
      mul_le_mul' le_rfl hN
    _ = _ := by rw [mul_pow, mul_pow]; ring

/-- This estimates the actual Bochner convolution, not an abstract operator. -/
theorem kernelConvolution_le_weight (H : Space d → ℂ) (r : Radii d)
    (C : ℝ) (hC : 0 ≤ C)
    (hH : ∀ y, ‖H y‖ ≤ C * productWeight r y)
    (f : Space d → ℂ) (hf : Measurable f) (x : Space d) :
    ‖kernelConvolution H f x‖ₑ ≤
      ENNReal.ofReal (C * (16 : ℝ) ^ d) * controllingMaximal d (fun y => ‖f y‖ₑ) x := by
  have hkernel : ∀ y, ‖H y‖ₑ ≤ ENNReal.ofReal C * ENNReal.ofReal (productWeight r y) := by
    intro y
    rw [← ofReal_norm, ← ENNReal.ofReal_mul hC]
    exact ENNReal.ofReal_le_ofReal (hH y)
  have hw : Measurable (fun y => ENNReal.ofReal (productWeight r y) * ‖f (x - y)‖ₑ) :=
    (ENNReal.measurable_ofReal.comp (continuous_productWeight r).measurable).mul
      (hf.enorm.comp (measurable_const.sub measurable_id))
  calc
    _ ≤ ∫⁻ y, ‖H y‖ₑ * ‖f (x - y)‖ₑ := by
      rw [kernelConvolution_eq_integral]
      simpa only [enorm_mul] using enorm_integral_le_lintegral_enorm (fun y => H y * f (x - y))
    _ ≤ ∫⁻ y, ENNReal.ofReal C *
        (ENNReal.ofReal (productWeight r y) * ‖f (x - y)‖ₑ) := by
      apply lintegral_mono
      intro y
      simpa only [mul_assoc] using mul_le_mul' (hkernel y) (le_rfl : ‖f (x - y)‖ₑ ≤ _)
    _ = ENNReal.ofReal C * ∫⁻ y, ENNReal.ofReal (productWeight r y) * ‖f (x - y)‖ₑ :=
      lintegral_const_mul _ hw
    _ ≤ ENNReal.ofReal C * ((16 : ℝ≥0∞) ^ d * controllingMaximal d (fun y => ‖f y‖ₑ) x) :=
      mul_le_mul' le_rfl (lintegral_productWeight_le d r _ hf.enorm x)
    _ = _ := by
      rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 16)]
      norm_num
      ring

/-- Uniform product-weight control handles even an uncountable kernel family.
Output measurability, when needed, follows separately from the concrete family. -/
theorem iSup_kernelConvolution_le_weight {ι : Type*} (H : ι → Space d → ℂ)
    (rho : ι → Radii d) (C : ℝ) (hC : 0 ≤ C)
    (hH : ∀ i y, ‖H i y‖ ≤ C * productWeight (rho i) y)
    (f : Space d → ℂ) (hf : Measurable f) (x : Space d) :
    (⨆ i, ‖kernelConvolution (H i) f x‖ₑ) ≤
      ENNReal.ofReal (C * (16 : ℝ) ^ d) * controllingMaximal d (fun y => ‖f y‖ₑ) x :=
  iSup_le fun i => kernelConvolution_le_weight (H i) (rho i) C hC (hH i) f hf x

theorem eLpNorm_iSup_kernelConvolution_le_weight {ι : Type*} (H : ι → Space d → ℂ)
    (rho : ι → Radii d) (C : ℝ) (hC : 0 ≤ C)
    (hH : ∀ i y, ‖H i y‖ ≤ C * productWeight (rho i) y)
    (f : Space d → ℂ) (hf : Measurable f) :
    eLpNorm (fun x => ⨆ i, ‖kernelConvolution (H i) f x‖ₑ) 2 volume ≤
      ENNReal.ofReal (C * (16 : ℝ) ^ d) * (8 : ℝ≥0∞) ^ d * eLpNorm f 2 volume := by
  apply eLpNorm_le_of_enorm_envelope _ f hf
  intro x
  simpa only [enorm_eq_self] using iSup_kernelConvolution_le_weight H rho C hC hH f hf x

theorem eLpNorm_le_of_partial_envelope {E : Type*} [ENorm E]
    (m j : ℕ) (B : Space (m + j) → E) (g : Space (m + j) → ℂ)
    (hg : Measurable g) (c : ℝ≥0∞)
    (hB : ∀ x, ‖B x‖ₑ ≤ c * partialBlockMaximal m j (fun y => ‖g y‖ₑ) x) :
    eLpNorm B 2 volume ≤ c * (8 : ℝ≥0∞) ^ m * eLpNorm g 2 volume := by
  apply (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [DilationL2.eLpNorm_two_sq]
  have hN := pow_le_pow_left'
    (eLpNorm_partialBlockMaximal_le m j (fun y => ‖g y‖ₑ) hg.enorm) 2
  rw [eLpNorm_two_sq_ennreal, eLpNorm_enorm, mul_pow] at hN
  calc
    _ ≤ ∫⁻ x, c ^ 2 * partialBlockMaximal m j (fun y => ‖g y‖ₑ) x ^ 2 := by
      apply lintegral_mono
      intro x
      simpa only [mul_pow] using pow_le_pow_left' (hB x) 2
    _ = c ^ 2 * ∫⁻ x, partialBlockMaximal m j (fun y => ‖g y‖ₑ) x ^ 2 :=
      lintegral_const_mul _ ((measurable_partialBlockMaximal m j _ hg.enorm).pow_const 2)
    _ ≤ c ^ 2 * (((8 : ℝ≥0∞) ^ m) ^ 2 * eLpNorm g 2 volume ^ 2) := mul_le_mul' le_rfl hN
    _ = _ := by rw [mul_pow, mul_pow]; ring

theorem norm_scaledPhi_le_weight (v : ℝ) (hv : 0 < v) (t : ℝ) :
    ‖scaledPhi v t‖ ≤ tailConstant * oneDimWeight v t := by
  have hp := phi_tail (v⁻¹ * t)
  have habs : |v⁻¹ * t| = |t| / v := by
    rw [abs_mul, abs_inv, abs_of_pos hv, div_eq_mul_inv, mul_comm]
  rw [habs] at hp
  have hpos : (0 : ℝ) < 1 + |t| / v := by positivity
  have hdiv : ‖phi (v⁻¹ * t)‖ ≤ tailConstant / (1 + |t| / v) ^ 3 :=
    (le_div_iff₀ (pow_pos hpos 3)).mpr (by simpa only [mul_comm] using hp)
  rw [norm_scaledPhi v hv]
  calc
    _ ≤ v⁻¹ * (tailConstant / (1 + |t| / v) ^ 3) :=
      mul_le_mul_of_nonneg_left hdiv (inv_nonneg.mpr hv.le)
    _ = _ := by simp only [oneDimWeight, zpow_neg, zpow_ofNat, div_eq_mul_inv]; ring

theorem norm_productPhi_le_weight (r : Radii d) (y : Space d) :
    ‖productPhi r y‖ ≤ tailConstant ^ d * productWeight r y := by
  rw [norm_productPhi]
  calc
    _ ≤ ∏ i : Fin d, tailConstant * oneDimWeight (r.1 i) (y i) := by
      apply Finset.prod_le_prod
      · intro i _; exact norm_nonneg _
      · intro i _; exact norm_scaledPhi_le_weight _ (r.2 i) _
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp [productWeight, oneDimWeight]

/-- Actual smoothing in a coordinate block, leaving the complementary coordinates fixed. -/
def partialBlockSmoothing (m j : ℕ) (b : Radii m) (g : Space (m + j) → ℂ)
    (x : Space (m + j)) : ℂ :=
  ∫ u : Space m, productPhi b u * g ((ProductCoordinates.split m j).symm
    ((ProductCoordinates.split m j x).1 - u, (ProductCoordinates.split m j x).2))

theorem measurable_partialBlockSmoothing (m j : ℕ) (b : Radii m)
    (g : Space (m + j) → ℂ) (hg : Measurable g) :
    Measurable (partialBlockSmoothing m j b g) := by
  let H : Space (m + j) × Space m → ℂ := fun p => productPhi b p.2 *
    g ((ProductCoordinates.split m j).symm
      ((ProductCoordinates.split m j p.1).1 - p.2, (ProductCoordinates.split m j p.1).2))
  have hmap : Measurable (fun p : Space (m + j) × Space m =>
      (ProductCoordinates.split m j).symm
        ((ProductCoordinates.split m j p.1).1 - p.2, (ProductCoordinates.split m j p.1).2)) :=
    (ProductCoordinates.split m j).symm.measurable.comp
      ((((ProductCoordinates.split m j).measurable.comp measurable_fst).fst.sub measurable_snd).prodMk
        ((ProductCoordinates.split m j).measurable.comp measurable_fst).snd)
  have hH : Measurable H := ((continuous_productPhi b).measurable.comp measurable_snd).mul
    (hg.comp hmap)
  change Measurable (fun x => ∫ u : Space m, H (x, u))
  exact hH.stronglyMeasurable.integral_prod_right'.measurable

theorem partialBlockSmoothing_le (m j : ℕ) (b : Radii m)
    (g : Space (m + j) → ℂ) (hg : Measurable g) (x : Space (m + j)) :
    ‖partialBlockSmoothing m j b g x‖ₑ ≤
      ENNReal.ofReal (tailConstant ^ m * (16 : ℝ) ^ m) *
        partialBlockMaximal m j (fun y => ‖g y‖ₑ) x := by
  let G : Space m → ℂ := fun u => g ((ProductCoordinates.split m j).symm
    (u, (ProductCoordinates.split m j x).2))
  have hG : Measurable G := hg.comp ((ProductCoordinates.split m j).symm.measurable.comp
    (measurable_id.prodMk measurable_const))
  exact kernelConvolution_le_weight (productPhi b) b (tailConstant ^ m)
    (pow_nonneg tailConstant_pos.le m) (norm_productPhi_le_weight b) G hG
      (ProductCoordinates.split m j x).1

theorem eLpNorm_partialBlockSmoothing_le (m j : ℕ) (b : Radii m)
    (g : Space (m + j) → ℂ) (hg : Measurable g) :
    eLpNorm (partialBlockSmoothing m j b g) 2 volume ≤
      ENNReal.ofReal (tailConstant ^ m * (16 : ℝ) ^ m) *
        (8 : ℝ≥0∞) ^ m * eLpNorm g 2 volume := by
  apply (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [DilationL2.eLpNorm_two_sq]
  have hN := pow_le_pow_left'
    (eLpNorm_partialBlockMaximal_le m j (fun y => ‖g y‖ₑ) hg.enorm) 2
  rw [eLpNorm_two_sq_ennreal, eLpNorm_enorm, mul_pow] at hN
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (tailConstant ^ m * (16 : ℝ) ^ m) ^ 2 *
        partialBlockMaximal m j (fun y => ‖g y‖ₑ) x ^ 2 := by
      apply lintegral_mono
      intro x
      simpa only [mul_pow] using pow_le_pow_left' (partialBlockSmoothing_le m j b g hg x) 2
    _ = ENNReal.ofReal (tailConstant ^ m * (16 : ℝ) ^ m) ^ 2 *
        ∫⁻ x, partialBlockMaximal m j (fun y => ‖g y‖ₑ) x ^ 2 :=
      lintegral_const_mul _ ((measurable_partialBlockMaximal m j _ hg.enorm).pow_const 2)
    _ ≤ ENNReal.ofReal (tailConstant ^ m * (16 : ℝ) ^ m) ^ 2 *
        (((8 : ℝ≥0∞) ^ m) ^ 2 * eLpNorm g 2 volume ^ 2) := mul_le_mul' le_rfl hN
    _ = _ := by rw [mul_pow, mul_pow]; ring

theorem iSup_partialBlockSmoothing_le {ι : Type*} (m j : ℕ) (b : ι → Radii m)
    (g : Space (m + j) → ℂ) (hg : Measurable g) (x : Space (m + j)) :
    (⨆ i, ‖partialBlockSmoothing m j (b i) g x‖ₑ) ≤
      ENNReal.ofReal (tailConstant ^ m * (16 : ℝ) ^ m) *
        partialBlockMaximal m j (fun y => ‖g y‖ₑ) x :=
  iSup_le fun i => partialBlockSmoothing_le m j (b i) g hg x

theorem measurable_iSup_partialBlockSmoothing {ι : Type*} [Countable ι]
    (m j : ℕ) (b : ι → Radii m) (g : Space (m + j) → ℂ) (hg : Measurable g) :
    Measurable (fun x => ⨆ i, ‖partialBlockSmoothing m j (b i) g x‖ₑ) :=
  Measurable.iSup fun i => (measurable_partialBlockSmoothing m j (b i) g hg).enorm

theorem eLpNorm_iSup_partialBlockSmoothing_le {ι : Type*}
    (m j : ℕ) (b : ι → Radii m) (g : Space (m + j) → ℂ) (hg : Measurable g) :
    eLpNorm (fun x => ⨆ i, ‖partialBlockSmoothing m j (b i) g x‖ₑ) 2 volume ≤
      ENNReal.ofReal (tailConstant ^ m * (16 : ℝ) ^ m) *
        (8 : ℝ≥0∞) ^ m * eLpNorm g 2 volume := by
  apply eLpNorm_le_of_partial_envelope m j _ g hg
  intro x
  simpa only [enorm_eq_self] using iSup_partialBlockSmoothing_le m j b g hg x

end StrongSpherical.ErrorMaximalL2
