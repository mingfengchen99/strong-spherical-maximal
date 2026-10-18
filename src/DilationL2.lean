import DyadicRadii
import SchurTest
import GenericKernelRegularity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Change of variables and L² scaling for diagonal dilations -/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StrongSpherical.DilationL2
variable {n : ℕ}

/-- Positive diagonal dilations are homeomorphisms of the original Euclidean space. -/
def dilationHomeomorph (r : Radii n) : Space n ≃ₜ Space n where
  toFun := diagonalDilation r.1
  invFun := inverseDilation r
  left_inv := inverseDilation_diagonalDilation r
  right_inv := diagonalDilation_inverseDilation r
  continuous_toFun := continuous_diagonalDilation _
  continuous_invFun := continuous_diagonalDilation _

def dilationEquiv (r : Radii n) : Space n ≃ᵐ Space n :=
  (dilationHomeomorph r).toMeasurableEquiv

/-- The exact Jacobian applies to canonical Euclidean volume, including dimension zero. -/
theorem map_diagonalDilation_volume (r : Radii n) :
    Measure.map (diagonalDilation r.1) (volume : Measure (Space n)) =
      ENNReal.ofReal (dilationJacobian r)⁻¹ • volume := by
  let D : (Fin n → ℝ) → (Fin n → ℝ) := fun u i => r.1 i * u i
  have hDm : Measurable D := by
    exact (continuous_pi fun i => continuous_const.mul (continuous_apply i)).measurable
  have hdet : Matrix.det (Matrix.diagonal r.1) ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => ne_of_gt (r.2 i))
  have hmatrix := Real.map_matrix_volume_pi_eq_smul_volume_pi hdet
  have hfun : (Matrix.toLin' (Matrix.diagonal r.1) : (Fin n → ℝ) → Fin n → ℝ) = D := by
    funext u
    ext i
    simp [D, Matrix.diagonal_toLin']
  have hD : Measure.map D (volume : Measure (Fin n → ℝ)) =
      ENNReal.ofReal (dilationJacobian r)⁻¹ • volume := by
    rw [hfun, Matrix.det_diagonal] at hmatrix
    change Measure.map D (volume : Measure (Fin n → ℝ)) =
      ENNReal.ofReal |(dilationJacobian r)⁻¹| • volume at hmatrix
    simpa only [abs_inv, abs_of_pos (dilationJacobian_pos r)] using hmatrix
  calc
    _ = Measure.map (WithLp.toLp 2) (Measure.map D
        (Measure.map (@WithLp.ofLp 2 (Fin n → ℝ)) (volume : Measure (Space n)))) := by
      rw [Measure.map_map (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).measurable hDm,
        Measure.map_map
          ((PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).measurable.comp hDm)
          (PiLp.volume_preserving_ofLp (Fin n)).measurable]
      rfl
    _ = Measure.map (WithLp.toLp 2) (Measure.map D (volume : Measure (Fin n → ℝ))) := by
      rw [(PiLp.volume_preserving_ofLp (Fin n)).map_eq]
    _ = _ := by
      rw [hD, Measure.map_smul, (PiLp.volume_preserving_toLp (Fin n)).map_eq]

theorem lintegral_comp_dilation (r : Radii n) (F : Space n → ℝ≥0∞) :
    (∫⁻ y, F (diagonalDilation r.1 y)) =
      ENNReal.ofReal (dilationJacobian r)⁻¹ * ∫⁻ y, F y := by
  change (∫⁻ y, F (dilationEquiv r y)) = _
  rw [← (dilationEquiv r).measurableEmbedding.lintegral_map F]
  change (∫⁻ y, F y ∂Measure.map (diagonalDilation r.1) volume) = _
  rw [map_diagonalDilation_volume, lintegral_smul_measure]
  rfl

theorem integral_comp_dilation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : Radii n) (F : Space n → E) :
    (∫ y, F (diagonalDilation r.1 y)) =
      (dilationJacobian r)⁻¹ • ∫ y, F y := by
  change (∫ y, F (dilationEquiv r y)) = _
  rw [← (dilationEquiv r).measurableEmbedding.integral_map F]
  change (∫ y, F y ∂Measure.map (diagonalDilation r.1) volume) = _
  rw [map_diagonalDilation_volume, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (dilationJacobian_pos r).le)]

theorem eLpNorm_comp_dilation_sq (r : Radii n) (f : Space n → ℂ) :
    eLpNorm (f ∘ diagonalDilation r.1) 2 volume ^ 2 =
      ENNReal.ofReal (dilationJacobian r)⁻¹ * eLpNorm f 2 volume ^ 2 := by
  rw [SchurTest.eLpNorm_two_sq, SchurTest.eLpNorm_two_sq]
  exact lintegral_comp_dilation r (fun y => ‖f y‖ₑ ^ 2)

theorem eLpNorm_two_sq {α E : Type*} [MeasurableSpace α] [ENorm E]
    (f : α → E) (μ : Measure α) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μ := by
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] using
    (eLpNorm_nnreal_pow_eq_lintegral (f := f) (μ := μ) (p := (2 : ℝ≥0)) (by norm_num))

theorem eLpNorm_comp_dilation_sq_general {E : Type*} [ENorm E]
    (r : Radii n) (f : Space n → E) :
    eLpNorm (f ∘ diagonalDilation r.1) 2 volume ^ 2 =
      ENNReal.ofReal (dilationJacobian r)⁻¹ * eLpNorm f 2 volume ^ 2 := by
  rw [eLpNorm_two_sq, eLpNorm_two_sq]
  exact lintegral_comp_dilation r (fun y => ‖f y‖ₑ ^ 2)

theorem memLp_comp_dilation (r : Radii n) (f : Space n → ℂ) (hf : MemLp f 2 volume) :
    MemLp (f ∘ diagonalDilation r.1) 2 volume := by
  have hEq : eLpNorm (f ∘ diagonalDilation r.1) 2 volume ^ 2 < ∞ := by
    rw [eLpNorm_comp_dilation_sq]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top hf.eLpNorm_lt_top)
  refine ⟨?_, ?_⟩
  · have hMeas : AEStronglyMeasurable f
        (Measure.map (diagonalDilation r.1) (volume : Measure (Space n))) := by
      rw [map_diagonalDilation_volume]
      exact hf.aestronglyMeasurable.smul_measure _
    exact hMeas.comp_measurable (continuous_diagonalDilation _).measurable
  · simpa only [ENNReal.pow_lt_top_iff, OfNat.ofNat_ne_zero, or_false] using hEq

theorem integral_eq_dilation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : Radii n) (F : Space n → E) :
    (∫ y, F y) = dilationJacobian r • ∫ y, F (diagonalDilation r.1 y) := by
  rw [integral_comp_dilation, smul_smul, mul_inv_cancel₀ (ne_of_gt (dilationJacobian_pos r)), one_smul]

theorem diagonalDilation_sub (r : Radii n) (x y : Space n) :
    diagonalDilation r.1 (x - y) = diagonalDilation r.1 x - diagonalDilation r.1 y := by
  ext i
  simp [mul_sub]

theorem dilatedKernel_multiply_dilation (K : Space n → ℂ) (r t : Radii n) (y : Space n) :
    dilatedKernel K (DyadicRadii.multiply r t) (diagonalDilation r.1 y) =
      (dilationJacobian r : ℂ)⁻¹ * dilatedKernel K t y := by
  rw [DyadicRadii.dilatedKernel_multiply]
  simp only [dilatedKernel, inverseDilation_diagonalDilation]

/-- Convolution on each dyadic rectangle is exactly a rescaled local convolution. -/
theorem kernelConvolution_multiply_dilation (K f : Space n → ℂ) (r t : Radii n)
    (x : Space n) :
    kernelConvolution (dilatedKernel K (DyadicRadii.multiply r t)) f (diagonalDilation r.1 x) =
      kernelConvolution (dilatedKernel K t) (f ∘ diagonalDilation r.1) x := by
  rw [kernelConvolution_eq_integral,
    integral_eq_dilation r (fun y => dilatedKernel K (DyadicRadii.multiply r t) y *
      f (diagonalDilation r.1 x - y))]
  simp_rw [dilatedKernel_multiply_dilation, ← diagonalDilation_sub, mul_assoc]
  rw [integral_const_mul]
  change (dilationJacobian r : ℂ) * ((dilationJacobian r : ℂ)⁻¹ * _) = _
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (dilationJacobian_pos r))), one_mul]
  rfl

/-- The maximal function on a fixed scaled local rectangle of radii. -/
def rectangleMaximal (K : Space n → ℂ) (r : Radii n) (f : Space n → ℂ)
    (x : Space n) : ℝ≥0∞ :=
  ⨆ t ∈ localRadii n, ‖kernelConvolution (dilatedKernel K (DyadicRadii.multiply r t)) f x‖ₑ

theorem rectangleMaximal_comp_dilation (K f : Space n → ℂ) (r : Radii n) :
    rectangleMaximal K r f ∘ diagonalDilation r.1 =
      localKernelMaximal K (f ∘ diagonalDilation r.1) := by
  funext x
  simp only [rectangleMaximal, localKernelMaximal, maximalOver, Function.comp_apply,
    kernelConvolution_multiply_dilation]

theorem rectangleMaximal_eq_local (K f : Space n → ℂ) (r : Radii n) (x : Space n) :
    rectangleMaximal K r f x =
      localKernelMaximal K (f ∘ diagonalDilation r.1) (inverseDilation r x) := by
  have h := congrFun (rectangleMaximal_comp_dilation K f r) (inverseDilation r x)
  simpa only [Function.comp_apply, diagonalDilation_inverseDilation] using h

theorem measurable_rectangleMaximal (K : Space n → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R)
    (r : Radii n) (f : Space n → ℂ) (hf : MemLp f 2 volume) :
    Measurable (rectangleMaximal K r f) := by
  have h := (GenericKernelRegularity.localKernelMaximal_measurable_and_finite
    K hK R hR hs _ (memLp_comp_dilation r f hf)).1
  have hi : Measurable (inverseDilation r) := (continuous_diagonalDilation _).measurable
  have hh := h.comp hi
  change Measurable (fun x => localKernelMaximal K (f ∘ diagonalDilation r.1) (inverseDilation r x)) at hh
  convert hh using 1
  funext x
  exact rectangleMaximal_eq_local K f r x

/-- The same local constant applies to every positive rescaling of the local rectangle. -/
theorem rectangle_local_bound (K : Space n → ℂ) (A : ℝ≥0∞)
    (hlocal : ∀ f : Space n → ℂ, MemLp f 2 volume →
      eLpNorm (localKernelMaximal K f) 2 volume ≤ A * eLpNorm f 2 volume)
    (r : Radii n) (f : Space n → ℂ) (hf : MemLp f 2 volume) :
    eLpNorm (rectangleMaximal K r f) 2 volume ≤ A * eLpNorm f 2 volume := by
  have h := pow_le_pow_left' (hlocal _ (memLp_comp_dilation r f hf)) 2
  rw [← rectangleMaximal_comp_dilation, eLpNorm_comp_dilation_sq_general,
    mul_pow, eLpNorm_comp_dilation_sq] at h
  have h0 : ENNReal.ofReal (dilationJacobian r)⁻¹ ≠ 0 := by
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr (dilationJacobian_pos r)))
  have hc := (ENNReal.mul_le_mul_iff_right h0 ENNReal.ofReal_ne_top).mp
    (show ENNReal.ofReal (dilationJacobian r)⁻¹ * eLpNorm (rectangleMaximal K r f) 2 volume ^ 2 ≤
      ENNReal.ofReal (dilationJacobian r)⁻¹ * (A ^ 2 * eLpNorm f 2 volume ^ 2) by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h)
  rw [← mul_pow] at hc
  exact (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hc

theorem strongKernelMaximal_measurable (K : Space n → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R)
    (f : Space n → ℂ) (hf : MemLp f 2 volume) : Measurable (strongKernelMaximal K f) := by
  have h := Measurable.iSup (fun k : Fin n → ℤ =>
    measurable_rectangleMaximal K hK R hR hs (DyadicRadii.scales k) f hf)
  have he : strongKernelMaximal K f = fun x =>
      ⨆ k : Fin n → ℤ, rectangleMaximal K (DyadicRadii.scales k) f x := by
    funext x
    simpa only [rectangleMaximal, DyadicRadii.rectangle] using
      DyadicRadii.strongKernelMaximal_eq_dyadic K f x
  rw [he]
  exact h

end StrongSpherical.DilationL2
