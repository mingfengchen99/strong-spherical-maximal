import GenericKernelRegularity
import CoordinateMarginals
import DilationL1
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Semicontinuity.Basic

/-! # The full maximal convolution operator on raw L∞ inputs

For every output point, translation preserves the exceptional set in the
essential bound of the input.  The L¹ norm of the kernel therefore controls
all radii simultaneously.  Continuity in the output variable gives lower
semicontinuity of the arbitrary-radius supremum and hence measurability.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology

namespace StrongSpherical.KernelLInfinity
variable {n : ℕ}

/-- The essential bound of a raw input controls every actual convolution point.
The input need not be assigned a preferred almost-everywhere representative. -/
theorem kernelConvolution_enorm_le (H : Space n → ℂ) (hH : Integrable H)
    (f : Space n → ℂ) (x : Space n) :
    ‖kernelConvolution H f x‖ₑ ≤
      ENNReal.ofReal (∫ y, ‖H y‖) * eLpNorm f ∞ volume := by
  have hess : ∀ᵐ y ∂(volume : Measure (Space n)), ‖f y‖ₑ ≤ eLpNorm f ∞ volume := by
    simpa only [eLpNorm_exponent_top] using enorm_ae_le_eLpNormEssSup f volume
  have hshift : ∀ᵐ y ∂(volume : Measure (Space n)),
      ‖f (x - y)‖ₑ ≤ eLpNorm f ∞ volume :=
    (volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae hess
  calc
    _ ≤ ∫⁻ y, ‖H y‖ₑ * ‖f (x - y)‖ₑ := by
      rw [kernelConvolution_eq_integral]
      simpa only [enorm_mul] using
        enorm_integral_le_lintegral_enorm (fun y => H y * f (x - y))
    _ ≤ ∫⁻ y, ‖H y‖ₑ * eLpNorm f ∞ volume := by
      apply lintegral_mono_ae
      filter_upwards [hshift] with y hy
      exact mul_le_mul' le_rfl hy
    _ = (∫⁻ y, ‖H y‖ₑ) * eLpNorm f ∞ volume :=
      lintegral_mul_const'' _ hH.aestronglyMeasurable.enorm
    _ = _ := by rw [ofReal_integral_norm_eq_lintegral_enorm hH]

/-- Continuous compact kernels produce continuous convolutions with raw L∞ inputs. -/
theorem continuous_dilated_convolution (K : Space n → ℂ) (hK : Continuous K)
    (hc : HasCompactSupport K) (r : Radii n)
    (f : Space n → ℂ) (hf : MemLp f ∞ volume) :
    Continuous (kernelConvolution (dilatedKernel K r) f) := by
  have hcr : HasCompactSupport (dilatedKernel K r) :=
    (hc.comp_homeomorph (CoordinateMarginals.inverseDilationHomeomorph r)).mul_left
  exact hcr.continuous_convolution_left (ContinuousLinearMap.mul ℂ ℂ)
    (GenericKernelRegularity.continuous_fixed_kernel K hK r)
    (hf.locallyIntegrable le_top)

/-- No countability restriction on the radius family is needed: its supremum is
lower semicontinuous as a function of the output point. -/
theorem lowerSemicontinuous_strongKernelMaximal (K : Space n → ℂ) (hK : Continuous K)
    (hc : HasCompactSupport K) (f : Space n → ℂ) (hf : MemLp f ∞ volume) :
    LowerSemicontinuous (strongKernelMaximal K f) := by
  unfold strongKernelMaximal maximalOver
  exact lowerSemicontinuous_biSup fun r _ =>
    (continuous_dilated_convolution K hK hc r f hf).enorm.lowerSemicontinuous

theorem measurable_strongKernelMaximal (K : Space n → ℂ) (hK : Continuous K)
    (hc : HasCompactSupport K) (f : Space n → ℂ) (hf : MemLp f ∞ volume) :
    Measurable (strongKernelMaximal K f) :=
  (lowerSemicontinuous_strongKernelMaximal K hK hc f hf).measurable

/-- All positive dilations obey the same pointwise bound, with exactly the
L¹ norm of the original kernel as the constant. -/
theorem strongKernelMaximal_le (K : Space n → ℂ) (hK : Continuous K)
    (hc : HasCompactSupport K) (f : Space n → ℂ) (x : Space n) :
    strongKernelMaximal K f x ≤
      ENNReal.ofReal (∫ y, ‖K y‖) * eLpNorm f ∞ volume := by
  have hKi : Integrable K (volume : Measure (Space n)) :=
    hK.integrable_of_hasCompactSupport hc
  unfold strongKernelMaximal maximalOver
  refine iSup_le fun r => iSup_le fun _ => ?_
  have h := kernelConvolution_enorm_le (dilatedKernel K r)
    (DilationL1.integrable_dilatedKernel K hKi r) f x
  simpa only [DilationL1.integral_norm_dilatedKernel] using h

/-- The endpoint estimate applies to the actual raw L∞ input and actual
uncountable maximal function. -/
theorem strongKernelMaximal_LInfinity (K : Space n → ℂ) (hK : Continuous K)
    (hc : HasCompactSupport K) (f : Space n → ℂ) (hf : MemLp f ∞ volume) :
    Measurable (strongKernelMaximal K f) ∧
      eLpNorm (strongKernelMaximal K f) ∞ volume ≤
        ENNReal.ofReal (∫ y, ‖K y‖) * eLpNorm f ∞ volume := by
  refine ⟨measurable_strongKernelMaximal K hK hc f hf, ?_⟩
  rw [eLpNorm_exponent_top]
  apply eLpNormEssSup_le_of_ae_enorm_bound
  exact Filter.Eventually.of_forall fun x => by
    simpa only [enorm_eq_self] using strongKernelMaximal_le K hK hc f x

end StrongSpherical.KernelLInfinity
