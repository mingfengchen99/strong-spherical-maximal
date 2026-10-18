import NormalKernelRegularity
import MaximalLinearization
import MarginalEnergy

/-!
# Regularity of local maximal convolution for continuous box-supported kernels

Local radii lie in a compact parameter space. A continuous kernel with a
fixed coordinate-box support therefore has a jointly continuous convolution
with every L² input, including raw almost-everywhere representatives. This
gives measurability and pointwise finiteness of its actual local maximal
function. No operator norm bound is asserted here.
-/

noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators Topology

namespace StrongSpherical.GenericKernelRegularity
open NormalKernelRegularity MarginalEnergy
variable {n : ℕ}

theorem isCompact_coordinateBox (n : ℕ) (R : ℝ) :
    IsCompact (coordinateBox n R) := by
  have heq : coordinateBox n R =
      WithLp.ofLp ⁻¹' (Set.pi univ fun _ : Fin n => Icc (-R) R) := by
    ext v
    simp only [coordinateBox, mem_preimage, mem_setOf_eq, Set.mem_pi,
      mem_univ, true_implies]
  rw [heq]
  exact (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isCompact_preimage.2
    (isCompact_univ_pi fun _ => isCompact_Icc)

theorem continuous_fixed_kernel (K : Space n → ℂ) (hK : Continuous K) (r : Radii n) :
    Continuous (dilatedKernel K r) :=
  continuous_const.mul (hK.comp (continuous_diagonalDilation _))

/-- The actual dilated kernel is jointly continuous in local radii and displacement. -/
theorem continuous_parameter_kernel (K : Space n → ℂ) (hK : Continuous K) :
    Continuous (fun p : LocalParameters n × Space n =>
      dilatedKernel K (parameterRadii p.1) p.2) := by
  have hd : Continuous (fun p : LocalParameters n × Space n =>
      dilationJacobian (parameterRadii p.1)) := by
    unfold dilationJacobian parameterRadii
    fun_prop
  have hdc := Complex.ofRealCLM.continuous.comp hd
  change Continuous (fun p : LocalParameters n × Space n =>
    (dilationJacobian (parameterRadii p.1) : ℂ)⁻¹ *
      K (inverseDilation (parameterRadii p.1) p.2))
  exact (hdc.inv₀ (fun p =>
    Complex.ofReal_ne_zero.mpr (ne_of_gt (dilationJacobian_pos _)))).mul
    (hK.comp continuous_parameter_inverseDilation)

/-- A box of radius R dilates into the uniform box of radius 2R for local radii. -/
theorem parameter_kernel_support (K : Space n → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support K ⊆ coordinateBox n R) (p : LocalParameters n) :
    Function.support (dilatedKernel K (parameterRadii p)) ⊆ coordinateBox n (2 * R) := by
  intro y hy
  have hne : K (inverseDilation (parameterRadii p) y) ≠ 0 := by
    intro hz
    apply hy
    simp [dilatedKernel, hz]
  intro j
  have hh : |inverseDilation (parameterRadii p) y j| ≤ R := abs_le.mpr (hs hne j)
  change |((parameterRadii p).1 j)⁻¹ * y j| ≤ R at hh
  rw [abs_mul, abs_inv, abs_of_pos ((parameterRadii p).2 j)] at hh
  have hm := mul_le_mul_of_nonneg_left hh ((parameterRadii p).2 j).le
  have he : (parameterRadii p).1 j * (((parameterRadii p).1 j)⁻¹ * |y j|) = |y j| := by
    field_simp [ne_of_gt ((parameterRadii p).2 j)]
  rw [he] at hm
  exact abs_le.mp (hm.trans (mul_le_mul_of_nonneg_right (parameterRadii_local p j).2 hR))

theorem hasCompactSupport_local_kernel (K : Space n → ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support K ⊆ coordinateBox n R)
    (r : Radii n) (hr : r ∈ localRadii n) :
    HasCompactSupport (dilatedKernel K r) := by
  obtain ⟨p, hp⟩ := exists_parameter_of_local r hr
  rw [← hp]
  exact (isCompact_coordinateBox n (2 * R)).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (parameter_kernel_support K R hR hs p)
      (isCompact_coordinateBox n (2 * R)).isClosed)

/-- Centered kernel rows can be paired with any L² input using Hölder. -/
theorem memLp_centered_kernel (K : Space n → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ coordinateBox n R)
    (r : Radii n) (hr : r ∈ localRadii n) (x : Space n) :
    MemLp (fun y => dilatedKernel K r (x - y)) 2 volume := by
  have hc := hasCompactSupport_local_kernel K R hR hs r hr
  exact ((continuous_fixed_kernel K hK r).comp
    (continuous_const.sub continuous_id)).memLp_of_hasCompactSupport
      (hc.comp_homeomorph (Homeomorph.subLeft x))

/-- Joint continuity in the compact local-radius parameter and the output point. -/
theorem continuous_parameter_convolution_L2 (K : Space n → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ coordinateBox n R)
    (f : Space n → ℂ) (hf : MemLp f 2 volume) :
    Continuous (fun p : LocalParameters n × Space n =>
      kernelConvolution (dilatedKernel K (parameterRadii p.1)) f p.2) := by
  have hker := continuous_parameter_kernel K hK
  have h : ContinuousOn (fun p : LocalParameters n × Space n =>
      convolution f (dilatedKernel K (parameterRadii p.1))
        (ContinuousLinearMap.mul ℂ ℂ).flip volume p.2) (univ ×ˢ univ) :=
    continuousOn_convolution_right_with_param (f := f)
      (g := fun p => dilatedKernel K (parameterRadii p))
      (μ := (volume : Measure (Space n))) (ContinuousLinearMap.mul ℂ ℂ).flip
      (isCompact_coordinateBox n (2 * R)) (fun p y _ hy => by
        by_contra hn
        exact hy (parameter_kernel_support K R hR hs p hn))
      (hf.locallyIntegrable (by norm_num)) hker.continuousOn
  have he : ∀ p : LocalParameters n, convolution f
      (dilatedKernel K (parameterRadii p))
      (ContinuousLinearMap.mul ℂ ℂ).flip volume =
        kernelConvolution (dilatedKernel K (parameterRadii p)) f :=
    fun p => by
      change convolution f (dilatedKernel K (parameterRadii p))
        (ContinuousLinearMap.mul ℂ ℂ).flip volume = convolution
          (dilatedKernel K (parameterRadii p)) f (ContinuousLinearMap.mul ℂ ℂ) volume
      exact convolution_flip (ContinuousLinearMap.mul ℂ ℂ)
  have hh : Continuous (fun p : LocalParameters n × Space n => convolution f
      (dilatedKernel K (parameterRadii p.1))
      (ContinuousLinearMap.mul ℂ ℂ).flip volume p.2) :=
    continuousOn_univ.mp (by simpa only [univ_prod_univ] using h)
  have heq : (fun p : LocalParameters n × Space n => convolution f
      (dilatedKernel K (parameterRadii p.1))
      (ContinuousLinearMap.mul ℂ ℂ).flip volume p.2) =
      (fun p : LocalParameters n × Space n => kernelConvolution
        (dilatedKernel K (parameterRadii p.1)) f p.2) := by
    funext p
    exact congrFun (he p.1) p.2
  rw [heq] at hh
  exact hh

/-- This is the original supremum over all local positive radii. -/
theorem localKernelMaximal_eq_parameter_iSup (K f : Space n → ℂ) (x : Space n) :
    localKernelMaximal K f x = ⨆ p : LocalParameters n,
      ‖kernelConvolution (dilatedKernel K (parameterRadii p)) f x‖ₑ := by
  unfold localKernelMaximal maximalOver
  apply le_antisymm
  · apply iSup_le
    intro r
    apply iSup_le
    intro hr
    obtain ⟨p, hp⟩ := exists_parameter_of_local r hr
    rw [← hp]
    exact le_iSup (fun p : LocalParameters n =>
      ‖kernelConvolution (dilatedKernel K (parameterRadii p)) f x‖ₑ) p
  · apply iSup_le
    intro p
    exact le_iSup_of_le (parameterRadii p)
      (le_iSup_of_le (parameterRadii_local p) le_rfl)

/-- Measurability and pointwise finiteness for arbitrary raw L² inputs. -/
theorem localKernelMaximal_measurable_and_finite (K : Space n → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ coordinateBox n R)
    (f : Space n → ℂ) (hf : MemLp f 2 volume) :
    Measurable (localKernelMaximal K f) ∧ ∀ x, localKernelMaximal K f x ≠ ∞ := by
  let A : LocalParameters n → Space n → ℂ := fun p x =>
    kernelConvolution (dilatedKernel K (parameterRadii p)) f x
  have hjoint := continuous_parameter_convolution_L2 K hK R hR hs f hf
  have hAm : ∀ p, Measurable (A p) := by
    intro p
    have hmap : Measurable (fun x : Space n => (p, x)) :=
      measurable_const.prodMk measurable_id
    simpa only [Function.comp_def, A] using hjoint.measurable.comp hmap
  have hAc : ∀ x, Continuous (fun p => A p x) := by
    intro x
    have hmap : Continuous (fun p : LocalParameters n => (p, x)) :=
      continuous_id.prodMk continuous_const
    simpa only [Function.comp_def, A] using hjoint.comp hmap
  obtain ⟨d, _, heq, hm, hfin⟩ :=
    MaximalLinearization.exists_dense_maximal_representation A hAm hAc
  refine ⟨?_, ?_⟩
  · simpa only [A, ← localKernelMaximal_eq_parameter_iSup] using hm
  · intro x
    rw [localKernelMaximal_eq_parameter_iSup]
    change (⨆ p : LocalParameters n, ‖A p x‖ₑ) ≠ ∞
    rw [heq x]
    exact hfin x

end StrongSpherical.GenericKernelRegularity
