import KernelLInfinity
import ErrorMaximalL2
import SmoothingGeometry
import MaximalAssembly
import RectangularMaximalLp

/-! # Cube-supported kernels and the full maximal operator on Lᵖ

A bounded kernel supported in a fixed coordinate cube is dominated by the
actual product weight after every positive diagonal dilation.  This gives a
pointwise controlling-maximal estimate.  Measurable representatives transfer
the norm estimate to every raw Lᵖ input without altering any convolution point.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Topology

namespace StrongSpherical.KernelMaximalLp
open ProductSmoothing ScalarSmoothing SmoothingGeometry RectangularMaximal
variable {n : ℕ}

def boxWeightConstant (n : ℕ) (R : ℝ) : ℝ := ((1 + R) ^ 3) ^ n

def boxMaximalConstant (n : ℕ) (R : ℝ) : ℝ := boxWeightConstant n R * (16 : ℝ) ^ n

theorem boxWeightConstant_pos (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    0 < boxWeightConstant n R := by unfold boxWeightConstant; positivity

theorem boxMaximalConstant_pos (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    0 < boxMaximalConstant n R :=
  mul_pos (boxWeightConstant_pos n R hR) (pow_pos (by norm_num) n)

/-- On the support cube the reciprocal cubic product weight has a uniform
positive lower bound, including the empty product in dimension zero. -/
theorem box_weight_lower (R : ℝ) (w : Space n) (hw : ∀ i, |w i| ≤ R) :
    1 ≤ boxWeightConstant n R * ∏ i, unitWeight (w i) := by
  have hi : ∀ i : Fin n, 1 ≤ (1 + R) ^ 3 * unitWeight (w i) := by
    intro i
    rw [unitWeight_eq, ← div_eq_mul_inv]
    apply (one_le_div₀ (by positivity : 0 < (1 + |w i|) ^ 3)).mpr
    exact pow_le_pow_left₀ (by positivity) (by linarith [hw i]) 3
  calc
    (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
    _ ≤ ∏ i : Fin n, (1 + R) ^ 3 * unitWeight (w i) :=
      Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => hi i)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp [boxWeightConstant]

/-- The undilated bounded kernel is dominated by a product of cubic tails. -/
theorem norm_kernel_le_unitWeight (K : Space n → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R)
    (B : ℝ) (hB : ∀ u, ‖K u‖ ≤ B) (w : Space n) :
    ‖K w‖ ≤ boxWeightConstant n R * B * ∏ i, unitWeight (w i) := by
  have hB0 : 0 ≤ B := (norm_nonneg (K 0)).trans (hB 0)
  have hW : 0 ≤ ∏ i, unitWeight (w i) :=
    Finset.prod_nonneg (fun _ _ => unitWeight_nonneg _)
  by_cases hz : K w = 0
  · rw [hz, norm_zero]
    exact mul_nonneg (mul_nonneg (boxWeightConstant_pos n R hR).le hB0) hW
  · have hw : ∀ i, |w i| ≤ R := fun i => abs_le.mpr (hs hz i)
    have hl := mul_le_mul_of_nonneg_left (box_weight_lower R w hw) hB0
    exact (hB w).trans (by simpa only [mul_one, mul_assoc, mul_left_comm, mul_comm] using hl)

/-- The product-weight bound has the same constant at every positive radius. -/
theorem norm_dilatedKernel_le_productWeight (K : Space n → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R)
    (B : ℝ) (hB : ∀ u, ‖K u‖ ≤ B) (r : Radii n) (y : Space n) :
    ‖dilatedKernel K r y‖ ≤ boxWeightConstant n R * B * productWeight r y := by
  let w := inverseDilation r y
  have hw : diagonalDilation r.1 w = y := diagonalDilation_inverseDilation r y
  have hweight : productWeight r y = (dilationJacobian r)⁻¹ * ∏ i, unitWeight (w i) := by
    simpa only [hw] using productWeight_dilation r w
  rw [DilationL1.norm_dilatedKernel]
  calc
    _ ≤ (dilationJacobian r)⁻¹ *
        (boxWeightConstant n R * B * ∏ i, unitWeight (w i)) :=
      mul_le_mul_of_nonneg_left (norm_kernel_le_unitWeight K R hR hs B hB w)
        (inv_nonneg.mpr (dilationJacobian_pos r).le)
    _ = _ := by rw [hweight]; ring

/-- Pointwise full-radius control for every measurable complex input. -/
theorem strongKernelMaximal_le_controlling (K : Space n → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R)
    (B : ℝ) (hB : ∀ u, ‖K u‖ ≤ B) (f : Space n → ℂ) (hf : Measurable f) (x : Space n) :
    strongKernelMaximal K f x ≤ ENNReal.ofReal (boxMaximalConstant n R * B) *
      controllingMaximal n (fun y => ‖f y‖ₑ) x := by
  have hB0 : 0 ≤ B := (norm_nonneg (K 0)).trans (hB 0)
  have hc : 0 ≤ boxWeightConstant n R * B :=
    mul_nonneg (boxWeightConstant_pos n R hR).le hB0
  unfold strongKernelMaximal maximalOver
  refine iSup_le fun r => iSup_le fun _ => ?_
  have h := ErrorMaximalL2.kernelConvolution_le_weight (dilatedKernel K r) r
    (boxWeightConstant n R * B) hc (norm_dilatedKernel_le_productWeight K R hR hs B hB r) f hf x
  simpa only [show (boxWeightConstant n R * B) * (16 : ℝ) ^ n =
    boxMaximalConstant n R * B by unfold boxMaximalConstant; ring] using h

/-- Continuity uses local integrability, so it applies to every raw Lᵖ input
with p ≥ 1 and requires no choice of representative. -/
theorem continuous_dilated_convolution (K : Space n → ℂ) (hK : Continuous K)
    (hc : HasCompactSupport K) (r : Radii n) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f : Space n → ℂ) (hf : MemLp f p volume) :
    Continuous (kernelConvolution (dilatedKernel K r) f) := by
  have hcr : HasCompactSupport (dilatedKernel K r) :=
    (hc.comp_homeomorph (CoordinateMarginals.inverseDilationHomeomorph r)).mul_left
  exact hcr.continuous_convolution_left (ContinuousLinearMap.mul ℂ ℂ)
    (GenericKernelRegularity.continuous_fixed_kernel K hK r) (hf.locallyIntegrable hp)

theorem lowerSemicontinuous_strongKernelMaximal (K : Space n → ℂ) (hK : Continuous K)
    (hc : HasCompactSupport K) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f : Space n → ℂ) (hf : MemLp f p volume) :
    LowerSemicontinuous (strongKernelMaximal K f) := by
  unfold strongKernelMaximal maximalOver
  exact lowerSemicontinuous_biSup fun r _ =>
    (continuous_dilated_convolution K hK hc r hp f hf).enorm.lowerSemicontinuous

theorem measurable_strongKernelMaximal (K : Space n → ℂ) (hK : Continuous K)
    (hc : HasCompactSupport K) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (f : Space n → ℂ) (hf : MemLp f p volume) :
    Measurable (strongKernelMaximal K f) :=
  (lowerSemicontinuous_strongKernelMaximal K hK hc hp f hf).measurable

/-- A controlling-maximal norm bound transfers to the original raw input.
Almost-everywhere replacement preserves the actual convolution at every point
and every radius, rather than just the resulting maximal function a.e. -/
theorem strongKernelMaximal_Lp_of_controlling (K : Space n → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R)
    (B : ℝ) (hB : ∀ u, ‖K u‖ ≤ B) (p : ℝ≥0∞) (hp : 1 ≤ p) (C : ℝ≥0∞)
    (hmax : ∀ F : Space n → ℝ≥0∞, Measurable F →
      eLpNorm (controllingMaximal n F) p volume ≤ C * eLpNorm F p volume)
    (f : Space n → ℂ) (hf : MemLp f p volume) :
    Measurable (strongKernelMaximal K f) ∧
      eLpNorm (strongKernelMaximal K f) p volume ≤
        ENNReal.ofReal (boxMaximalConstant n R * B) * C * eLpNorm f p volume := by
  have hc : HasCompactSupport K :=
    (GenericKernelRegularity.isCompact_coordinateBox n R).of_isClosed_subset
      (isClosed_tsupport _) (closure_minimal hs
        (GenericKernelRegularity.isCompact_coordinateBox n R).isClosed)
  refine ⟨measurable_strongKernelMaximal K hK hc hp f hf, ?_⟩
  let g := hf.aestronglyMeasurable.mk f
  have hg : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  have hM : Measurable (controllingMaximal n (fun y => ‖g y‖ₑ)) :=
    measurable_controllingMaximal n _ hg.enorm
  have hnorm : eLpNorm (strongKernelMaximal K g) p volume ≤
      ENNReal.ofReal (boxMaximalConstant n R * B) *
        eLpNorm (controllingMaximal n (fun y => ‖g y‖ₑ)) p volume := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' p hM.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun x => by
      simpa only [enorm_eq_self] using strongKernelMaximal_le_controlling K R hR hs B hB g hg x
  have h := hnorm.trans (mul_le_mul' le_rfl (hmax _ hg.enorm))
  rw [eLpNorm_enorm, ← MaximalAssembly.strongKernelMaximal_congr_ae K f g hfg,
    ← eLpNorm_congr_ae hfg] at h
  simpa only [mul_assoc] using h

/-- The finite Lᵠ estimate with no auxiliary maximal-operator hypothesis.
The constant depends only on dimension, support radius, and q, and is chosen
before the kernel, its amplitude bound, and the raw input. -/
theorem exists_strongKernelMaximal_Lp (n : ℕ) (R : ℝ) (hR : 0 ≤ R) (q : ℝ) (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : Space n → ℂ, Continuous K →
      Function.support K ⊆ MarginalEnergy.coordinateBox n R →
      ∀ B : ℝ, (∀ u, ‖K u‖ ≤ B) → ∀ f : Space n → ℂ,
      MemLp f (ENNReal.ofReal q) volume →
        Measurable (strongKernelMaximal K f) ∧
          eLpNorm (strongKernelMaximal K f) (ENNReal.ofReal q) volume ≤
            ENNReal.ofReal (C * B) * eLpNorm f (ENNReal.ofReal q) volume := by
  obtain ⟨Cq, hCq, hmax⟩ := RectangularMaximalLp.exists_controllingMaximal_Lp n q hq
  refine ⟨boxMaximalConstant n R * Cq, mul_pos (boxMaximalConstant_pos n R hR) hCq, ?_⟩
  intro K hK hs B hB f hf
  have hp : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq.le
  have h := strongKernelMaximal_Lp_of_controlling K hK R hR hs B hB
    (ENNReal.ofReal q) hp (ENNReal.ofReal Cq) hmax f hf
  refine ⟨h.1, h.2.trans_eq ?_⟩
  have hB0 : 0 ≤ B := (norm_nonneg (K 0)).trans (hB 0)
  rw [← ENNReal.ofReal_mul (mul_nonneg (boxMaximalConstant_pos n R hR).le hB0)]
  congr 2
  ring

end StrongSpherical.KernelMaximalLp
