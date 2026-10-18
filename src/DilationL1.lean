import DilationL2

/-! # Exact L¹ preservation by normalized positive diagonal dilations -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace StrongSpherical.DilationL1
open DilationL2
variable {n : ℕ}

/-- The Jacobian is finite and positive, so this change of variables also
holds for arbitrary extended nonnegative functions. -/
theorem lintegral_eq_dilation (r : Radii n) (F : Space n → ℝ≥0∞) :
    (∫⁻ y, F y) = ENNReal.ofReal (dilationJacobian r) *
      ∫⁻ y, F (diagonalDilation r.1 y) := by
  rw [lintegral_comp_dilation, ← mul_assoc,
    ← ENNReal.ofReal_mul (dilationJacobian_pos r).le,
    mul_inv_cancel₀ (dilationJacobian_pos r).ne', ENNReal.ofReal_one, one_mul]

theorem norm_dilatedKernel (K : Space n → ℂ) (r : Radii n) (y : Space n) :
    ‖dilatedKernel K r y‖ = (dilationJacobian r)⁻¹ * ‖K (inverseDilation r y)‖ := by
  simp only [dilatedKernel, norm_mul, norm_inv, Complex.norm_real,
    Real.norm_of_nonneg (dilationJacobian_pos r).le]

theorem enorm_dilatedKernel (K : Space n → ℂ) (r : Radii n) (y : Space n) :
    ‖dilatedKernel K r y‖ₑ = ENNReal.ofReal ((dilationJacobian r)⁻¹) *
      ‖K (inverseDilation r y)‖ₑ := by
  rw [← ofReal_norm, norm_dilatedKernel,
    ENNReal.ofReal_mul (inv_nonneg.mpr (dilationJacobian_pos r).le), ofReal_norm]

/-- Exact real L¹ mass, with no measurability or integrability hypothesis.
The Bochner change of variables is unconditional. -/
theorem integral_norm_dilatedKernel (K : Space n → ℂ) (r : Radii n) :
    (∫ y, ‖dilatedKernel K r y‖) = ∫ y, ‖K y‖ := by
  rw [integral_eq_dilation r (fun y => ‖dilatedKernel K r y‖)]
  simp_rw [norm_dilatedKernel, inverseDilation_diagonalDilation]
  rw [integral_const_mul]
  change dilationJacobian r * ((dilationJacobian r)⁻¹ * ∫ y, ‖K y‖) = _
  rw [← mul_assoc, mul_inv_cancel₀ (dilationJacobian_pos r).ne', one_mul]

/-- Unlike the real integral, this equality also records the infinite L¹ mass. -/
theorem lintegral_enorm_dilatedKernel (K : Space n → ℂ) (r : Radii n) :
    (∫⁻ y, ‖dilatedKernel K r y‖ₑ) = ∫⁻ y, ‖K y‖ₑ := by
  rw [lintegral_eq_dilation r (fun y => ‖dilatedKernel K r y‖ₑ)]
  simp_rw [enorm_dilatedKernel, inverseDilation_diagonalDilation]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
    ← ENNReal.ofReal_mul (dilationJacobian_pos r).le,
    mul_inv_cancel₀ (dilationJacobian_pos r).ne', ENNReal.ofReal_one, one_mul]

theorem eLpNorm_dilatedKernel_one (K : Space n → ℂ) (r : Radii n) :
    eLpNorm (dilatedKernel K r) 1 volume = eLpNorm K 1 volume := by
  rw [eLpNorm_one_eq_lintegral_enorm, eLpNorm_one_eq_lintegral_enorm,
    lintegral_enorm_dilatedKernel]

/-- Raw integrability is preserved, including its almost-everywhere
measurability component. -/
theorem integrable_dilatedKernel (K : Space n → ℂ) (hK : Integrable K) (r : Radii n) :
    Integrable (dilatedKernel K r) := by
  let s : Radii n := ⟨fun i => (r.1 i)⁻¹, fun i => inv_pos.mpr (r.2 i)⟩
  have hm : AEStronglyMeasurable K
      (Measure.map (diagonalDilation s.1) (volume : Measure (Space n))) := by
    rw [map_diagonalDilation_volume]
    exact hK.aestronglyMeasurable.smul_measure _
  apply memLp_one_iff_integrable.mp
  refine ⟨?_, ?_⟩
  · change AEStronglyMeasurable
      (fun y : Space n => (dilationJacobian r : ℂ)⁻¹ * K (inverseDilation r y)) volume
    exact (hm.comp_measurable (continuous_diagonalDilation _).measurable).const_mul _
  · rw [eLpNorm_dilatedKernel_one]
    exact (memLp_one_iff_integrable.mpr hK).eLpNorm_lt_top

/-- The complex integral itself is also unchanged by the normalization. -/
theorem integral_dilatedKernel (K : Space n → ℂ) (r : Radii n) :
    (∫ y, dilatedKernel K r y) = ∫ y, K y := by
  rw [integral_eq_dilation r (fun y => dilatedKernel K r y)]
  simp_rw [dilatedKernel, inverseDilation_diagonalDilation]
  rw [integral_const_mul, Complex.real_smul, ← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (dilationJacobian_pos r).ne'), one_mul]

theorem norm_dilatedKernel_le (K : Space n → ℂ) (r : Radii n) (B : ℝ)
    (hB : ∀ y, ‖K y‖ ≤ B) (y : Space n) :
    ‖dilatedKernel K r y‖ ≤ (dilationJacobian r)⁻¹ * B := by
  rw [norm_dilatedKernel]
  exact mul_le_mul_of_nonneg_left (hB _) (inv_nonneg.mpr (dilationJacobian_pos r).le)

theorem eLpNorm_dilatedKernel_top_le_of_bound (K : Space n → ℂ) (r : Radii n) (B : ℝ)
    (hB : ∀ y, ‖K y‖ ≤ B) :
    eLpNorm (dilatedKernel K r) ∞ volume ≤
      ENNReal.ofReal ((dilationJacobian r)⁻¹ * B) := by
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall (norm_dilatedKernel_le K r B hB))

end StrongSpherical.DilationL1
