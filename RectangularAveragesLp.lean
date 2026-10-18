import RectangularAverages

/-! # Finite Lᑫ bounds for the actual centered rectangular maximal function

The normalized indicator of every genuine coordinate rectangle is controlled
by the product cubic weight.  All integrals remain extended nonnegative,
including infinite input and fiber energies.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Topology

namespace StrongSpherical.RectangularAveragesLp
open RectangularAverages RectangularMaximal ProductSmoothing MaximalWeight
variable {n : ℕ}

/-- The normalized interval density is bounded by four times the cubic weight
throughout its interval. -/
theorem scalar_box_weight (v t : ℝ) (hv : 0 < v) (ht : |t| ≤ v) :
    (2 * v)⁻¹ ≤ 4 * oneDimWeight v t := by
  have hb : 0 < 1 + |t| / v := by positivity
  have hden : (1 + |t| / v) ^ 3 ≤ (8 : ℝ) := by
    calc
      _ ≤ (2 : ℝ) ^ 3 := pow_le_pow_left₀ hb.le (by
        have := (div_le_one hv).mpr ht
        linarith) 3
      _ = _ := by norm_num
  have h := (one_le_div₀ (pow_pos hb 3)).mpr hden
  have hm := mul_le_mul_of_nonneg_left h
    (inv_nonneg.mpr (mul_pos (by norm_num : (0 : ℝ) < 2) hv).le)
  calc
    (2 * v)⁻¹ = (2 * v)⁻¹ * 1 := by ring
    _ ≤ (2 * v)⁻¹ * (8 / (1 + |t| / v) ^ 3) := hm
    _ = 4 * oneDimWeight v t := by
      unfold oneDimWeight
      simp only [zpow_neg, zpow_ofNat, div_eq_mul_inv]
      field_simp
      ring

/-- The actual reciprocal rectangle volume has a uniform product-weight
bound on its support, including dimension zero. -/
theorem rectangle_density_le_productWeight (r : Radii n) (y : Space n)
    (hy : y ∈ rectangle r) :
    (rectangleVolume r)⁻¹ ≤ (4 : ℝ) ^ n * productWeight r y := by
  rw [rectangleVolume, ← Finset.prod_inv_distrib]
  calc
    (∏ i : Fin n, (2 * r.1 i)⁻¹) ≤ ∏ i : Fin n, 4 * oneDimWeight (r.1 i) (y i) :=
      Finset.prod_le_prod
        (fun i _ => inv_nonneg.mpr (mul_pos (by norm_num) (r.2 i)).le)
        (fun i _ => scalar_box_weight _ _ (r.2 i) (abs_le.mpr (hy i)))
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        productWeight, oneDimWeight]

/-- Each actual centered rectangular average is controlled pointwise by the
iterated coordinate maximal operator, without any finite-energy assumption. -/
theorem rectangularAverage_le_controlling (r : Radii n) (F : Space n → ℝ≥0∞)
    (hF : Measurable F) (x : Space n) :
    rectangularAverage r F x ≤ ENNReal.ofReal ((64 : ℝ) ^ n) * controllingMaximal n F x := by
  have hshift : Measurable (fun y : Space n => F (x - y)) :=
    hF.comp (measurable_const.sub measurable_id)
  have hw : Measurable (fun y : Space n => ENNReal.ofReal (productWeight r y) * F (x - y)) :=
    (ENNReal.measurable_ofReal.comp (continuous_productWeight r).measurable).mul hshift
  have hdensity : ∀ y ∈ rectangle r, (ENNReal.ofReal (rectangleVolume r))⁻¹ ≤
      ENNReal.ofReal ((4 : ℝ) ^ n) * ENNReal.ofReal (productWeight r y) := by
    intro y hy
    rw [← ENNReal.ofReal_inv_of_pos (rectangleVolume_pos r),
      ← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 4) n)]
    exact ENNReal.ofReal_le_ofReal (rectangle_density_le_productWeight r y hy)
  have hconstant : ENNReal.ofReal ((4 : ℝ) ^ n) * (16 : ℝ≥0∞) ^ n =
      ENNReal.ofReal ((64 : ℝ) ^ n) := by
    simp only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 4),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 64), ENNReal.ofReal_ofNat]
    rw [← mul_pow]
    norm_num
  calc
    _ = ∫⁻ y in rectangle r, (ENNReal.ofReal (rectangleVolume r))⁻¹ * F (x - y) :=
      (lintegral_const_mul _ hshift).symm
    _ ≤ ∫⁻ y in rectangle r, ENNReal.ofReal ((4 : ℝ) ^ n) *
        (ENNReal.ofReal (productWeight r y) * F (x - y)) := by
      apply setLIntegral_mono' (measurableSet_rectangle r)
      intro y hy
      simpa only [mul_assoc] using mul_le_mul' (hdensity y hy) (le_rfl : F (x - y) ≤ _)
    _ ≤ ∫⁻ y, ENNReal.ofReal ((4 : ℝ) ^ n) *
        (ENNReal.ofReal (productWeight r y) * F (x - y)) := setLIntegral_le_lintegral _ _
    _ = ENNReal.ofReal ((4 : ℝ) ^ n) *
        ∫⁻ y, ENNReal.ofReal (productWeight r y) * F (x - y) := lintegral_const_mul _ hw
    _ ≤ ENNReal.ofReal ((4 : ℝ) ^ n) *
        ((16 : ℝ≥0∞) ^ n * controllingMaximal n F x) :=
      mul_le_mul' le_rfl (lintegral_productWeight_le n r F hF x)
    _ = _ := by rw [← mul_assoc, hconstant]

/-- The literal full centered rectangular maximal function has pointwise
control by the already constructed coordinate maximal operator. -/
theorem rectangularMaximal_le_controlling (F : Space n → ℝ≥0∞) (hF : Measurable F)
    (x : Space n) :
    rectangularMaximal F x ≤ ENNReal.ofReal ((64 : ℝ) ^ n) * controllingMaximal n F x :=
  iSup_le fun r => rectangularAverage_le_controlling r F hF x

/-- The actual M_rec satisfies the finite Lᑫ estimate for every q > 1.
The positive constant is chosen before the measurable extended-valued input. -/
theorem exists_rectangularMaximal_Lp (n : ℕ) (q : ℝ) (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : Space n → ℝ≥0∞, Measurable F →
      eLpNorm (rectangularMaximal F) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal q) volume := by
  obtain ⟨Cq, hCq, hmax⟩ := RectangularMaximalLp.exists_controllingMaximal_Lp n q hq
  refine ⟨(64 : ℝ) ^ n * Cq, mul_pos (pow_pos (by norm_num) n) hCq, ?_⟩
  intro F hF
  have hM := measurable_controllingMaximal n F hF
  have h : eLpNorm (rectangularMaximal F) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal ((64 : ℝ) ^ n) *
        eLpNorm (controllingMaximal n F) (ENNReal.ofReal q) volume := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' (ENNReal.ofReal q) hM.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simpa only [enorm_eq_self] using rectangularMaximal_le_controlling F hF x
  calc
    _ ≤ ENNReal.ofReal ((64 : ℝ) ^ n) *
        (ENNReal.ofReal Cq * eLpNorm F (ENNReal.ofReal q) volume) :=
      h.trans (mul_le_mul' le_rfl (hmax F hF))
    _ = _ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg (by norm_num : (0 : ℝ) ≤ 64) n)]

end StrongSpherical.RectangularAveragesLp
