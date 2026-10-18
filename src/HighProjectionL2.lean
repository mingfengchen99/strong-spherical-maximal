import HighMaximalL2
import DyadicKernelScales
import FourierKernel
import FourierProjectionBridges

/-! # Dyadic high-frequency projection maximal estimates -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators SchwartzMap

namespace StrongSpherical.HighProjectionL2
open HighMaximalL2 CoordinateSubsets NormalKernelRegularity FourierKernel FourierMiddle
open DilationL2 DyadicKernelScales
attribute [local instance] Classical.propDecidable

variable {d : ℕ}

abbrev HighParameter (d : ℕ) := (Fin d → ℤ) × LocalParameters d

def setDimension (I : Set (Fin d)) : ℕ := Fintype.card I
def setComplementDimension (I : Set (Fin d)) : ℕ := Fintype.card (↥(Iᶜ))

def blockDimension (J : Finset (Fin d)) : ℕ := setDimension (J : Set (Fin d))
def complementDimension (J : Finset (Fin d)) : ℕ := setComplementDimension (J : Set (Fin d))
def blockPermutation (J : Finset (Fin d)) :
    Fin (blockDimension J + complementDimension J) ≃ Fin d :=
  subsetEnumeration (J : Set (Fin d))

def blockEmbedding (J : Finset (Fin d)) : Fin (blockDimension J) ↪ Fin d :=
  (Fin.castAddEmb (complementDimension J)).trans (blockPermutation J).toEmbedding

def blockSmoothingRadii (M : ℕ) (J : Finset (Fin d)) (i : HighParameter d) :
    Radii (blockDimension J) := subsetRadii M i.1 (blockEmbedding J)

def kernelRadii (i : HighParameter d) : Radii d :=
  DyadicRadii.rectangle i.1 (parameterRadii i.2)

def physicalHighMaximal (K : Space d → ℂ) (M : ℕ) (f : Space d → ℂ) (x : Space d) : ℝ≥0∞ :=
  ⨆ i : HighParameter d, ‖physicalHighFamily Finset.univ.powerset blockDimension complementDimension
    blockPermutation (blockSmoothingRadii M) (fun J => (-1 : ℂ) ^ J.card)
    (fun i => kernelConvolution (smallScaleErrorKernel K (kernelRadii i) (smallRadii M i.1)) f) i x‖ₑ

def errorProjectionMaximal (K : Space d → ℂ) (M : ℕ) (f : L2 d) (x : Space d) : ℝ≥0∞ :=
  ⨆ k : Fin d → ℤ, rectangleMaximal K (DyadicRadii.scales k) (errorOperator M k f) x

theorem measurable_errorProjectionMaximal (K : Space d → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox d R)
    (M : ℕ) (f : L2 d) : Measurable (errorProjectionMaximal K M f) :=
  Measurable.iSup fun k => measurable_rectangleMaximal K hK R hR hs
    (DyadicRadii.scales k) (errorOperator M k f) (Lp.memLp _)

set_option maxHeartbeats 1000000 in
theorem exists_physicalHighMaximal_bound (d : ℕ) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : Space d → ℂ, Differentiable ℝ K →
      Function.support K ⊆ MarginalEnergy.coordinateBox d R →
      ∀ B : ℝ, (∀ x, ‖K x‖ ≤ B) → (∀ x, ‖fderiv ℝ K x‖ ≤ B) →
      ∀ M : ℕ, ∀ f : Space d → ℂ, Measurable f →
        eLpNorm (physicalHighMaximal K M f) 2 volume ≤
          ENNReal.ofReal (C * epsilon M * B) * eLpNorm f 2 volume := by
  have hsign : ∀ J ∈ (Finset.univ.powerset : Finset (Finset (Fin d))),
      ‖(-1 : ℂ) ^ J.card‖ ≤ 1 := by intro J _; simp
  obtain ⟨C, hC, hbound⟩ := exists_physicalHigh_smallScale_L2 (κ := HighParameter d) d R hR
    Finset.univ.powerset blockDimension complementDimension blockPermutation
    (fun J => (-1 : ℂ) ^ J.card) hsign
  refine ⟨C, hC, ?_⟩
  intro K hK hs B hb hd M f hf
  exact hbound K hK hs B hb hd kernelRadii (fun i => smallRadii M i.1)
    (blockSmoothingRadii M) (epsilon M) (epsilon_pos M).le (epsilon_le_one M)
    (fun i q => (small_relative_bounds M i.1 (parameterRadii i.2) (parameterRadii_local i.2) q).2)
    f hf

theorem blockEmbedding_eq_subsetEmbedding (J : Finset (Fin d)) :
    blockEmbedding J = FourierProjectionBridges.subsetEmbedding J := by
  exact (FourierProjectionBridges.subsetEmbedding_eq_firstBlock J).symm

theorem highRadii_eq_smallRadii (M : ℕ) (k : Fin d → ℤ) :
    FourierKernel.highRadii M k = smallRadii M k := rfl

theorem integrable_dilatedKernel_of_box (K : Space d → ℂ) (hK : Continuous K)
    (R : ℝ) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox d R) (r : Radii d) :
    Integrable (dilatedKernel K r) := by
  have hc : HasCompactSupport K :=
    (GenericKernelRegularity.isCompact_coordinateBox d R).of_isClosed_subset
      (isClosed_tsupport _) (closure_minimal hs
        (GenericKernelRegularity.isCompact_coordinateBox d R).isClosed)
  exact (GenericKernelRegularity.continuous_fixed_kernel K hK r).integrable_of_hasCompactSupport
    ((hc.comp_homeomorph (CoordinateMarginals.inverseDilationHomeomorph r)).mul_left)

set_option maxHeartbeats 1000000 in
/-- The actual L² high projection has exactly the physical finite signed-sum
representation, for every local radius parameter and every output point. -/
theorem error_projection_eq_physicalHigh (K : Space d → ℂ) (hK : Continuous K)
    (R : ℝ) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox d R)
    (M : ℕ) (f : 𝓢(Space d, ℂ)) (i : HighParameter d) (x : Space d) :
    kernelConvolution (dilatedKernel K (kernelRadii i))
      (errorOperator M i.1 (f.toLp 2 volume)) x =
      physicalHighFamily Finset.univ.powerset blockDimension complementDimension
        blockPermutation (blockSmoothingRadii M) (fun J => (-1 : ℂ) ^ J.card)
        (fun i => kernelConvolution
          (smallScaleErrorKernel K (kernelRadii i) (smallRadii M i.1)) f) i x := by
  rw [FourierProjectionBridges.error_projection_convolution _
    (GenericKernelRegularity.continuous_fixed_kernel K hK (kernelRadii i))
    (integrable_dilatedKernel_of_box K hK R hs (kernelRadii i))]
  have hk : FourierProjectionBridges.highKernel (dilatedKernel K (kernelRadii i)) M i.1 =
      smallScaleErrorKernel K (kernelRadii i) (smallRadii M i.1) := rfl
  unfold physicalHighFamily
  apply Finset.sum_congr rfl
  intro J _
  congr 1
  rw [FourierProjectionBridges.partialConvolution_subset_eq_block]
  simp only [blockDimension, complementDimension, blockPermutation,
    blockSmoothingRadii, blockEmbedding_eq_subsetEmbedding,
    hk, setDimension, setComplementDimension, FourierProjectionBridges.setDimension,
    FourierProjectionBridges.setComplementDimension]
  rfl

/-- Taking the dyadic rectangles preserves the physical high-piece envelope. -/
theorem errorProjectionMaximal_le_physicalHighMaximal (K : Space d → ℂ)
    (hK : Continuous K) (R : ℝ)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox d R)
    (M : ℕ) (f : 𝓢(Space d, ℂ)) (x : Space d) :
    errorProjectionMaximal K M (f.toLp 2 volume) x ≤ physicalHighMaximal K M f x := by
  unfold errorProjectionMaximal rectangleMaximal
  apply iSup_le
  intro k
  apply iSup_le
  intro t
  apply iSup_le
  intro ht
  obtain ⟨p, hp⟩ := exists_parameter_of_local t ht
  rw [← hp]
  have h := error_projection_eq_physicalHigh K hK R hs M f (k, p) x
  change kernelConvolution (dilatedKernel K
    (DyadicRadii.multiply (DyadicRadii.scales k) (parameterRadii p)))
      (errorOperator M k (f.toLp 2 volume)) x = _ at h
  rw [h]
  exact le_iSup (fun i : HighParameter d =>
    ‖physicalHighFamily Finset.univ.powerset blockDimension complementDimension
      blockPermutation (blockSmoothingRadii M) (fun J => (-1 : ℂ) ^ J.card)
      (fun i => kernelConvolution
        (smallScaleErrorKernel K (kernelRadii i) (smallRadii M i.1)) f) i x‖ₑ) (k, p)

set_option maxHeartbeats 1000000 in
/-- Equations (5.31)--(5.33), for the genuine Fourier high projection.
The constant is chosen before the kernel, derivative bound, dyadic separation,
and Schwartz input; it depends only on dimension and the support box. -/
theorem exists_errorProjectionMaximal_L2 (d : ℕ) (R : ℝ) (hR : 1 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : Space d → ℂ, Differentiable ℝ K →
      Function.support K ⊆ MarginalEnergy.coordinateBox d R →
      ∀ B : ℝ, (∀ x, ‖K x‖ ≤ B) → (∀ x, ‖fderiv ℝ K x‖ ≤ B) →
      ∀ M : ℕ, ∀ f : 𝓢(Space d, ℂ),
        eLpNorm (errorProjectionMaximal K M (f.toLp 2 volume)) 2 volume ≤
          ENNReal.ofReal (C * epsilon M * B) * eLpNorm f 2 volume := by
  obtain ⟨C, hC, hb⟩ := exists_physicalHighMaximal_bound d R hR
  refine ⟨C, hC, ?_⟩
  intro K hK hs B hB hd M f
  calc
    _ ≤ eLpNorm (physicalHighMaximal K M f) 2 volume := by
      apply eLpNorm_mono_enorm
      intro x
      simpa only [enorm_eq_self] using
        errorProjectionMaximal_le_physicalHighMaximal K hK.continuous R hs M f x
    _ ≤ _ := hb K hK hs B hB hd M f f.continuous.measurable

end StrongSpherical.HighProjectionL2
