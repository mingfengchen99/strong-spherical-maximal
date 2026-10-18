import CoordinateMarginals
import ProductCoordinates
import GenericKernelRegularity

/-! # Coordinate marginals inherit the local L² bound

The box test is performed on the actual original Euclidean convolution,
using the measure-preserving coordinate splitting.  Taking the box radius
to infinity preserves the constant exactly.  The final statement accepts
all L² inputs, including nonmeasurable representatives of measurable
almost-everywhere classes.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StrongSpherical.MarginalLocalEstimate
open ProductCoordinates CoordinateMarginals
variable {m j : ℕ}

/-- The first-block marginal of a kernel in the original Euclidean space. -/
def marginalKernel (K : Space (m + j) → ℂ) : Space m → ℂ :=
  marginal (K ∘ (split m j).symm)

theorem hasCompactSupport_of_box (K : Space (m + j) → ℂ) (R : ℝ)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox (m + j) R) :
    HasCompactSupport K :=
  (GenericKernelRegularity.isCompact_coordinateBox (m + j) R).of_isClosed_subset
    (isClosed_tsupport _)
    (closure_minimal hs (GenericKernelRegularity.isCompact_coordinateBox (m + j) R).isClosed)

theorem continuous_product_kernel (K : Space (m + j) → ℂ) (hK : Continuous K) :
    Continuous (K ∘ (split m j).symm) :=
  hK.comp (continuous_split_symm m j)

theorem hasCompactSupport_product_kernel (K : Space (m + j) → ℂ)
    (hc : HasCompactSupport K) : HasCompactSupport (K ∘ (split m j).symm) :=
  hc.comp_homeomorph
    (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := j)).symm.toHomeomorph

theorem product_kernel_support (K : Space (m + j) → ℂ) (R : ℝ)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox (m + j) R) :
    Function.support (K ∘ (split m j).symm) ⊆ coordinateCube m R ×ˢ coordinateCube j R := by
  intro p hp
  have hbound := hs hp
  constructor
  · intro i
    exact abs_le.mpr (by simpa only [split_symm_castAdd, mem_Icc] using hbound (Fin.castAdd j i))
  · intro i
    exact abs_le.mpr (by simpa only [split_symm_natAdd, mem_Icc] using hbound (Fin.natAdd m i))

theorem continuous_marginalKernel (K : Space (m + j) → ℂ) (hK : Continuous K)
    (R : ℝ) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox (m + j) R) :
    Continuous (marginalKernel K) :=
  continuous_marginal _ (continuous_product_kernel K hK)
    (hasCompactSupport_product_kernel K (hasCompactSupport_of_box K R hs))

theorem marginalKernel_support (K : Space (m + j) → ℂ) (R : ℝ)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox (m + j) R) :
    Function.support (marginalKernel K) ⊆ MarginalEnergy.coordinateBox m R := by
  rw [← coordinateCube_eq_coordinateBox]
  exact support_marginal_subset_cube _ R (product_kernel_support K R hs)

/-- Pull the genuine product box input back to the original Euclidean space. -/
def euclideanBoxInput (L : ℝ) (g : Space m → ℂ) : Space (m + j) → ℂ :=
  boxLift (j := j) L g ∘ split m j

theorem memLp_euclideanBoxInput (L : ℝ) (g : Space m → ℂ)
    (hg : Measurable g) (hgLp : MemLp g 2 volume) :
    MemLp (euclideanBoxInput (j := j) L g) 2 volume := by
  have h := MarginalEnergy.memLp_cutoffInput (j := j) L g hg hgLp
  rw [← boxLift_eq_cutoffInput] at h
  exact h.comp_measurePreserving (measurePreserving_split m j)

theorem euclideanBoxInput_energy (L : ℝ) (g : Space m → ℂ)
    (hg : Measurable g) (hgLp : MemLp g 2 volume) :
    eLpNorm (euclideanBoxInput (j := j) L g) 2 volume ^ 2 =
      ENNReal.ofReal (2 * L) ^ j * eLpNorm g 2 volume ^ 2 := by
  have h := MarginalEnergy.memLp_cutoffInput (j := j) L g hg hgLp
  unfold euclideanBoxInput
  rw [boxLift_eq_cutoffInput,
    eLpNorm_comp_measurePreserving h.aestronglyMeasurable (measurePreserving_split m j),
    SchurTest.eLpNorm_two_sq, MarginalEnergy.lintegral_cutoffInput_sq L g hg,
    SchurTest.eLpNorm_two_sq]

/-- Unit radii in the integrated coordinates match the partial convolution exactly. -/
theorem convolution_join_unit (K : Space (m + j) → ℂ) (r : Radii m)
    (L : ℝ) (g : Space m → ℂ) (p : Space m × Space j) :
    kernelConvolution (dilatedKernel K (joinRadii r (unitRadii j)))
      (euclideanBoxInput L g) ((split m j).symm p) =
        productConvolution (partialDilatedKernel (K ∘ (split m j).symm) r) (boxLift L g) p := by
  rw [kernelConvolution_eq_product]
  simp only [MeasurableEquiv.apply_symm_apply, dilatedKernel_join_unit,
    euclideanBoxInput, Function.comp_apply, productConvolution, partialDilatedKernel]

/-- The actual full local maximal function dominates the marginal maximal
function on the smaller output box, for every L² test input. -/
theorem localMaximal_box_dominates (K : Space (m + j) → ℂ) (hK : Continuous K)
    (R L : ℝ) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox (m + j) R)
    (g : Space m → ℂ) (hg : Measurable g) (hgLp : MemLp g 2 volume)
    (x : Space m) (z : Space j) (hz : z ∈ coordinateCube j (L - R)) :
    localKernelMaximal (marginalKernel K) g x ≤
      localKernelMaximal K (euclideanBoxInput L g) ((split m j).symm (x, z)) := by
  unfold localKernelMaximal maximalOver
  refine iSup_le fun r => iSup_le fun hr => ?_
  have hp := product_kernel_support K R hs
  have hs' : Function.support (K ∘ (split m j).symm) ⊆ univ ×ˢ coordinateCube j R :=
    fun p h => ⟨mem_univ _, (hp h).2⟩
  have he := partialDilatedConvolution_boxLift_eq_L2 _ (continuous_product_kernel K hK)
    (hasCompactSupport_product_kernel K (hasCompactSupport_of_box K R hs))
    R L hs' r g hg hgLp x z hz
  change productConvolution (partialDilatedKernel (K ∘ (split m j).symm) r) (boxLift L g) (x, z) =
    kernelConvolution (dilatedKernel (marginalKernel K) r) g x at he
  change ‖kernelConvolution (dilatedKernel (marginalKernel K) r) g x‖ₑ ≤ _
  rw [← he, ← convolution_join_unit]
  exact le_iSup_of_le (joinRadii r (unitRadii j))
    (le_iSup_of_le (joinRadii_local r (unitRadii j) hr unitRadii_mem_localRadii) le_rfl)

theorem eLpNorm_two_sq_ennreal {α : Type*} [MeasurableSpace α]
    (F : α → ℝ≥0∞) (μ : Measure α) :
    eLpNorm F 2 μ ^ 2 = ∫⁻ x, F x ^ 2 ∂μ := by
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two, enorm_eq_self] using
    (eLpNorm_nnreal_pow_eq_lintegral (f := F) (μ := μ) (p := (2 : ℝ≥0)) (by norm_num))

/-- The box test and the exact limiting volume ratio preserve the constant A. -/
theorem marginal_local_bound_measurable (K : Space (m + j) → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox (m + j) R)
    (A : ℝ≥0∞)
    (hlocal : ∀ f : Space (m + j) → ℂ, MemLp f 2 volume →
      eLpNorm (localKernelMaximal K f) 2 volume ≤ A * eLpNorm f 2 volume)
    (g : Space m → ℂ) (hg : Measurable g) (hgLp : MemLp g 2 volume) :
    Measurable (localKernelMaximal (marginalKernel K) g) ∧
      eLpNorm (localKernelMaximal (marginalKernel K) g) 2 volume ≤ A * eLpNorm g 2 volume := by
  have hm := (GenericKernelRegularity.localKernelMaximal_measurable_and_finite
    (marginalKernel K) (continuous_marginalKernel K hK R hs) R hR
    (marginalKernel_support K R hs) g hgLp).1
  refine ⟨hm, ?_⟩
  apply (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [mul_pow]
  apply MarginalEnergy.large_box_transfer R hR j
  intro L _hL
  let f := euclideanBoxInput (j := j) L g
  have hf : MemLp f 2 volume := memLp_euclideanBoxInput L g hg hgLp
  have hMf := (GenericKernelRegularity.localKernelMaximal_measurable_and_finite
    K hK R hR hs f hf).1
  let B : Space m × Space j → ℝ≥0∞ := fun p =>
    (MarginalEnergy.coordinateBox j (L - R)).indicator
      (fun _ => localKernelMaximal (marginalKernel K) g p.1 ^ 2) p.2
  have hB : (∫⁻ p : Space m × Space j, B p ∂(volume : Measure (Space m)).prod volume) =
      ENNReal.ofReal (2 * L - 2 * R) ^ j *
        eLpNorm (localKernelMaximal (marginalKernel K) g) 2 volume ^ 2 := by
    rw [eLpNorm_two_sq_ennreal]
    simpa only [B, show 2 * (L - R) = 2 * L - 2 * R by ring] using
      MarginalEnergy.lintegral_coordinateBox_product (j := j) (L - R)
        (fun x => localKernelMaximal (marginalKernel K) g x ^ 2) (hm.pow_const 2)
  rw [← hB]
  calc
    _ ≤ ∫⁻ p : Space m × Space j,
        localKernelMaximal K f ((split m j).symm p) ^ 2
        ∂(volume : Measure (Space m)).prod volume := by
      apply lintegral_mono
      intro p
      by_cases hp : p.2 ∈ MarginalEnergy.coordinateBox j (L - R)
      · simp only [B, indicator_of_mem hp]
        apply pow_le_pow_left'
        apply localMaximal_box_dominates K hK R L hs g hg hgLp p.1 p.2
        simpa only [coordinateCube_eq_coordinateBox] using hp
      · simp only [B, indicator_of_notMem hp]
        exact zero_le
    _ = eLpNorm (localKernelMaximal K f) 2 volume ^ 2 := by
      rw [eLpNorm_two_sq_ennreal]
      exact (measurePreserving_split m j).symm.lintegral_comp
        (hMf.pow_const 2)
    _ ≤ (A * eLpNorm f 2 volume) ^ 2 := pow_le_pow_left' (hlocal f hf) 2
    _ = ENNReal.ofReal (2 * L) ^ j * (A ^ 2 * eLpNorm g 2 volume ^ 2) := by
      rw [mul_pow, euclideanBoxInput_energy L g hg hgLp]
      ac_rfl

/-- Centering the input works in every dimension, including dimension zero. -/
theorem convolution_eq_centered_integral {n : ℕ} (K f : Space n → ℂ) (x : Space n) :
    kernelConvolution K f x = ∫ y, K (x - y) * f y := by
  rw [kernelConvolution_eq_integral]
  have h := integral_sub_left_eq_self (fun y => K (x - y) * f y) volume x
  simpa only [sub_sub_cancel] using h

/-- Equation (5.3) with the limiting boundary loss removed: every first-block
marginal inherits the original local L² constant for arbitrary raw inputs. -/
theorem marginal_local_bound (K : Space (m + j) → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox (m + j) R)
    (A : ℝ≥0∞)
    (hlocal : ∀ f : Space (m + j) → ℂ, MemLp f 2 volume →
      eLpNorm (localKernelMaximal K f) 2 volume ≤ A * eLpNorm f 2 volume)
    (g : Space m → ℂ) (hgLp : MemLp g 2 volume) :
    Measurable (localKernelMaximal (marginalKernel K) g) ∧
      eLpNorm (localKernelMaximal (marginalKernel K) g) 2 volume ≤ A * eLpNorm g 2 volume := by
  let g' := hgLp.aestronglyMeasurable.mk g
  have hg' : Measurable g' := hgLp.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hgg' : g =ᵐ[volume] g' := hgLp.aestronglyMeasurable.ae_eq_mk
  have hg'Lp : MemLp g' 2 volume := (memLp_congr_ae hgg').mp hgLp
  have hconv : ∀ (r : Radii m) (x : Space m),
      kernelConvolution (dilatedKernel (marginalKernel K) r) g x =
        kernelConvolution (dilatedKernel (marginalKernel K) r) g' x := by
    intro r x
    rw [convolution_eq_centered_integral, convolution_eq_centered_integral]
    apply integral_congr_ae
    filter_upwards [hgg'] with y hy
    rw [hy]
  have hmax : localKernelMaximal (marginalKernel K) g = localKernelMaximal (marginalKernel K) g' := by
    funext x
    simp only [localKernelMaximal, maximalOver, hconv]
  have h := marginal_local_bound_measurable K hK R hR hs A hlocal g' hg' hg'Lp
  rw [← hmax, ← eLpNorm_congr_ae hgg'] at h
  exact h

end StrongSpherical.MarginalLocalEstimate
