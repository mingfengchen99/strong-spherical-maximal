import FourierKernel
import ConvolutionSmoothing
import CoordinateSubsets
import ErrorMaximalL2

/-! # Pointwise physical realizations of the low and high L² projections -/
noncomputable section
open MeasureTheory Set FourierTransform
open scoped FourierTransform SchwartzMap BigOperators BoundedContinuousFunction
attribute [local instance] Classical.propDecidable

namespace StrongSpherical.FourierProjectionBridges
set_option maxHeartbeats 1000000
open FourierKernel FourierMiddle ProductSmoothing ConvolutionSmoothing
variable {d j : ℕ}

theorem convolution_congr_ae (K f g : Space d → ℂ) (hfg : f =ᵐ[volume] g) (x : Space d) :
    kernelConvolution K f x = kernelConvolution K g x := by
  rw [MarginalLocalEstimate.convolution_eq_centered_integral,
    MarginalLocalEstimate.convolution_eq_centered_integral]
  apply integral_congr_ae
  filter_upwards [hfg] with y hy
  rw [hy]

theorem low_projection_convolution (K : Space d → ℂ) (M : ℕ) (k : Fin d → ℤ)
    (e : Fin j ↪ Fin d) (f : 𝓢(Space d, ℂ)) (x : Space d) :
    kernelConvolution K (lowSubsetOperator M k (Finset.univ.image e) (f.toLp 2 volume)) x =
      kernelConvolution K (partialConvolution (coordinateInclusion e) (subsetRadii M k e) f) x := by
  rw [← lowSubsetSchwartz_toLp]
  calc
    _ = kernelConvolution K (lowSubsetSchwartz M k e f) x :=
      convolution_congr_ae K _ _ ((lowSubsetSchwartz M k e f).coeFn_toLp 2 volume) x
    _ = _ := by
      congr 1
      funext z
      exact lowSubsetSchwartz_apply M k e f z

theorem low_projection_smoothed_kernel (K : Space d → ℂ) (hK : Continuous K)
    (hKi : Integrable K) (M : ℕ) (k : Fin d → ℤ) (e : Fin j ↪ Fin d)
    (f : 𝓢(Space d, ℂ)) (x : Space d) :
    kernelConvolution K (lowSubsetOperator M k (Finset.univ.image e) (f.toLp 2 volume)) x =
      kernelConvolution (partialConvolution (coordinateInclusion e) (subsetRadii M k e) K) f x := by
  rw [low_projection_convolution]
  exact convolution_partial_kernel K hK hKi _ _ f x

/-- Fix the subtype instance before specializing a set to a finset. -/
def setDimension (I : Set (Fin d)) : ℕ := Fintype.card I

def setComplementDimension (I : Set (Fin d)) : ℕ := Fintype.card (↥Iᶜ)

def setEmbedding (I : Set (Fin d)) : Fin (setDimension I) ↪ Fin d :=
  ⟨fun i => ((Fintype.equivFin I).symm i).1, by
    intro i l h
    apply (Fintype.equivFin I).symm.injective
    exact Subtype.ext h⟩

theorem setEmbedding_mem (I : Set (Fin d)) (i : Fin (setDimension I)) :
    setEmbedding I i ∈ I := ((Fintype.equivFin I).symm i).2

theorem setEmbedding_surjective (I : Set (Fin d)) (x : I) :
    ∃ i, setEmbedding I i = x.1 := by
  refine ⟨Fintype.equivFin I x, ?_⟩
  change (((Fintype.equivFin I).symm ((Fintype.equivFin I) x)).1) = x.1
  rw [Equiv.symm_apply_apply]

/-- The same coordinate enumeration used by `CoordinateSubsets.subsetEnumeration`. -/
def subsetEmbedding (J : Finset (Fin d)) : Fin (setDimension (J : Set (Fin d))) ↪ Fin d :=
  setEmbedding (J : Set (Fin d))

@[simp] theorem subsetEmbedding_image (J : Finset (Fin d)) :
    Finset.univ.image (subsetEmbedding J) = J := by
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    exact setEmbedding_mem (J : Set (Fin d)) a
  · intro hi
    exact setEmbedding_surjective (J : Set (Fin d)) ⟨i, hi⟩

theorem setEmbedding_eq_firstBlock (I : Set (Fin d)) :
    setEmbedding I = (Fin.castAddEmb (setComplementDimension I)).trans
      (CoordinateSubsets.subsetEnumeration I).toEmbedding := by
  apply Function.Embedding.ext
  intro i
  change ((Fintype.equivFin I).symm i).1 =
    (CoordinateSubsets.subsetEnumeration I) (Fin.castAdd (setComplementDimension I) i)
  simp [CoordinateSubsets.subsetEnumeration, setComplementDimension]

theorem subsetEmbedding_eq_firstBlock (J : Finset (Fin d)) :
    subsetEmbedding J = (Fin.castAddEmb (setComplementDimension (J : Set (Fin d)))).trans
      (CoordinateSubsets.subsetEnumeration (J : Set (Fin d))).toEmbedding :=
  setEmbedding_eq_firstBlock (J : Set (Fin d))

theorem coordinateInclusion_permutation {n : ℕ} (q : Fin n ≃ Fin d)
    (e : Fin j ↪ Fin n) (u : Space j) :
    coordinateInclusion (e.trans q.toEmbedding) u =
      CoordinateSubsets.coordinatePermutation q (coordinateInclusion e u) := by
  apply ext_inner_right ℝ
  intro z
  rw [coordinateInclusion, ContinuousLinearMap.adjoint_inner_left]
  have hp : coordinateProjection (e.trans q.toEmbedding) z =
      coordinateProjection e ((CoordinateSubsets.coordinatePermutation q).symm z) := by
    ext i
    simp [coordinateProjection_apply, CoordinateSubsets.coordinatePermutation_symm,
      CoordinateSubsets.coordinatePermutation_apply]
  rw [hp, ← ContinuousLinearMap.adjoint_inner_left]
  have h := (CoordinateSubsets.coordinatePermutation q).inner_map_map
    (coordinateInclusion e u) ((CoordinateSubsets.coordinatePermutation q).symm z)
  simpa only [coordinateInclusion, LinearIsometryEquiv.apply_symm_apply] using h.symm

theorem partialConvolution_permutation {n : ℕ} (q : Fin n ≃ Fin d)
    (e : Fin j ↪ Fin n) (r : Radii j) (g : Space d → ℂ) (x : Space n) :
    partialConvolution (coordinateInclusion (e.trans q.toEmbedding)) r g
      (CoordinateSubsets.coordinatePermutation q x) =
        partialConvolution (coordinateInclusion e) r
          (g ∘ CoordinateSubsets.coordinatePermutation q) x := by
  unfold partialConvolution
  apply integral_congr_ae
  filter_upwards with y
  simp only [coordinateInclusion_permutation, Function.comp_apply, map_sub]

theorem kernelConvolution_permutation {n : ℕ} (q : Fin n ≃ Fin d)
    (K f : Space d → ℂ) (x : Space n) :
    kernelConvolution K f (CoordinateSubsets.coordinatePermutation q x) =
      kernelConvolution (K ∘ CoordinateSubsets.coordinatePermutation q)
        (f ∘ CoordinateSubsets.coordinatePermutation q) x := by
  rw [kernelConvolution_eq_integral, kernelConvolution_eq_integral]
  have h := (CoordinateSubsets.coordinatePermutation q).measurePreserving.integral_comp
    (CoordinateSubsets.coordinatePermutation q).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun y : Space d => K y * f (CoordinateSubsets.coordinatePermutation q x - y))
  simpa only [Function.comp_apply, map_sub] using h.symm

theorem partialConvolution_firstBlock_covariance {m l : ℕ} (q : Fin (m + l) ≃ Fin d)
    (r : Radii m) (g : Space d → ℂ) (x : Space d) :
    partialConvolution (coordinateInclusion ((Fin.castAddEmb l).trans q.toEmbedding)) r g x =
      ErrorMaximalL2.partialBlockSmoothing m l r
        (g ∘ CoordinateSubsets.coordinatePermutation q) ((CoordinateSubsets.coordinatePermutation q).symm x) := by
  unfold partialConvolution ErrorMaximalL2.partialBlockSmoothing
  apply integral_congr_ae
  filter_upwards with y
  congr 2
  rw [coordinateInclusion_permutation]
  have hs := congrArg (CoordinateSubsets.coordinatePermutation q)
    (sub_coordinateInclusion_castAdd m l ((CoordinateSubsets.coordinatePermutation q).symm x) y)
  simpa only [map_sub, LinearIsometryEquiv.apply_symm_apply] using hs

theorem partialConvolution_subset_eq_block (J : Finset (Fin d))
    (r : Radii (setDimension (J : Set (Fin d)))) (g : Space d → ℂ) (x : Space d) :
    partialConvolution (coordinateInclusion (subsetEmbedding J)) r g x =
      ErrorMaximalL2.partialBlockSmoothing (setDimension (J : Set (Fin d)))
        (setComplementDimension (J : Set (Fin d))) r
        (g ∘ CoordinateSubsets.coordinatePermutation (CoordinateSubsets.subsetEnumeration (J : Set (Fin d))))
        ((CoordinateSubsets.coordinatePermutation (CoordinateSubsets.subsetEnumeration (J : Set (Fin d)))).symm x) := by
  rw [subsetEmbedding_eq_firstBlock]
  exact partialConvolution_firstBlock_covariance _ _ _ _

theorem coordinateInclusion_natAdd (m l : ℕ) (u : Space l) :
    coordinateInclusion (Fin.natAddEmb m) u = (ProductCoordinates.split m l).symm (0, u) := by
  apply ext_inner_right ℝ
  intro z
  rw [coordinateInclusion, ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply, Real.inner_apply, coordinateProjection_apply,
    Fin.natAddEmb_apply]
  rw [Fin.sum_univ_add]
  simp only [ProductCoordinates.split_symm_castAdd, ProductCoordinates.split_symm_natAdd,
    WithLp.ofLp_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add]

theorem sub_coordinateInclusion_natAdd (m l : ℕ) (x : Space (m + l)) (u : Space l) :
    x - coordinateInclusion (Fin.natAddEmb m) u =
      (ProductCoordinates.split m l).symm ((ProductCoordinates.split m l x).1,
        (ProductCoordinates.split m l x).2 - u) := by
  rw [coordinateInclusion_natAdd]
  apply (ProductCoordinates.split m l).injective
  simp only [ProductCoordinates.split_sub, MeasurableEquiv.apply_symm_apply,
    Prod.sub_def, sub_zero]

theorem partialConvolution_lastBlock_covariance {m l : ℕ} (q : Fin (m + l) ≃ Fin d)
    (r : Radii l) (g : Space d → ℂ) (x : Space d) :
    partialConvolution (coordinateInclusion ((Fin.natAddEmb m).trans q.toEmbedding)) r g x =
      ∫ y, productPhi r y *
        (g ∘ CoordinateSubsets.coordinatePermutation q)
          ((ProductCoordinates.split m l).symm
            ((ProductCoordinates.split m l ((CoordinateSubsets.coordinatePermutation q).symm x)).1,
             (ProductCoordinates.split m l ((CoordinateSubsets.coordinatePermutation q).symm x)).2 - y)) := by
  unfold partialConvolution
  apply integral_congr_ae
  filter_upwards with y
  congr 2
  rw [coordinateInclusion_permutation]
  have hs := congrArg (CoordinateSubsets.coordinatePermutation q)
    (sub_coordinateInclusion_natAdd m l ((CoordinateSubsets.coordinatePermutation q).symm x) y)
  simpa only [map_sub, LinearIsometryEquiv.apply_symm_apply] using hs

def canonicalLowSchwartz (M : ℕ) (k : Fin d → ℤ) (J : Finset (Fin d))
    (f : 𝓢(Space d, ℂ)) : 𝓢(Space d, ℂ) :=
  lowSubsetSchwartz M k (subsetEmbedding J) f

theorem canonicalLowSchwartz_toLp (M : ℕ) (k : Fin d → ℤ) (J : Finset (Fin d))
    (f : 𝓢(Space d, ℂ)) :
    (canonicalLowSchwartz M k J f).toLp 2 volume = lowSubsetOperator M k J (f.toLp 2 volume) := by
  unfold canonicalLowSchwartz
  rw [lowSubsetSchwartz_toLp, subsetEmbedding_image]

def errorSchwartz (M : ℕ) (k : Fin d → ℤ) (f : 𝓢(Space d, ℂ)) : 𝓢(Space d, ℂ) :=
  ∑ J ∈ Finset.univ.powerset, (-1 : ℂ) ^ J.card •
    canonicalLowSchwartz M k J (highRemainderSchwartz M k f)

theorem errorSchwartz_toLp (M : ℕ) (k : Fin d → ℤ) (f : 𝓢(Space d, ℂ)) :
    (errorSchwartz M k f).toLp 2 volume = errorOperator M k (f.toLp 2 volume) := by
  change (SchwartzMap.toLpCLM ℂ (E := Space d) ℂ 2 volume)
    (∑ J ∈ Finset.univ.powerset, (-1 : ℂ) ^ J.card •
      canonicalLowSchwartz M k J (highRemainderSchwartz M k f)) = _
  rw [map_sum]
  simp_rw [map_smul]
  change (∑ J ∈ Finset.univ.powerset, (-1 : ℂ) ^ J.card •
    (canonicalLowSchwartz M k J (highRemainderSchwartz M k f)).toLp 2 volume) = _
  simp_rw [canonicalLowSchwartz_toLp, highRemainderSchwartz_toLp]
  exact (error_operator_expansion M k (f.toLp 2 volume)).symm

def schwartzConvolutionLinear (K : Space d → ℂ) (hKi : Integrable K) :
    𝓢(Space d, ℂ) →ₗ[ℂ] (Space d → ℂ) where
  toFun f := kernelConvolution K f
  map_add' f g := by
    funext x
    change (∫ y, K y * (f (x - y) + g (x - y))) =
      (∫ y, K y * f (x - y)) + ∫ y, K y * g (x - y)
    simp_rw [mul_add]
    exact integral_add (integrable_convolution_schwartz K hKi f x)
      (integrable_convolution_schwartz K hKi g x)
  map_smul' c f := by
    funext x
    change (∫ y, K y * (c * f (x - y))) = c * ∫ y, K y * f (x - y)
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with y
    ring

def highKernel (K : Space d → ℂ) (M : ℕ) (k : Fin d → ℤ) (y : Space d) : ℂ :=
  K y - kernelConvolution K (productPhi (highRadii M k)) y

/-- The high Schwartz remainder is the actual kernel difference after outer convolution. -/
theorem highRemainder_convolution (K : Space d → ℂ) (hK : Continuous K)
    (hKi : Integrable K) (M : ℕ) (k : Fin d → ℤ) (f : 𝓢(Space d, ℂ)) (x : Space d) :
    kernelConvolution K (highRemainderSchwartz M k f) x = kernelConvolution (highKernel K M k) f x := by
  let r := highRadii M k
  let g := productPhiSchwartz r
  have hAssoc : kernelConvolution K (fullSmoothSchwartz r f) x =
      kernelConvolution (kernelConvolution K (productPhi r)) f x := by
    have hc : (fullSmoothSchwartz r f : Space d → ℂ) = kernelConvolution g f := by
      funext z
      exact SchwartzMap.convolution_apply (ContinuousLinearMap.mul ℂ ℂ) g f z
    rw [hc, ← convolution_assoc_schwartz K hK hKi g f x, productPhiSchwartz_eq]
  have hL : Integrable (kernelConvolution K (productPhi r)) :=
    hKi.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) (integrable_productPhi r)
  have hsub := congrArg (fun g : Space d → ℂ => g x)
    ((schwartzConvolutionLinear K hKi).map_sub f (fullSmoothSchwartz r f))
  change kernelConvolution K (highRemainderSchwartz M k f) x =
    kernelConvolution K f x - kernelConvolution K (fullSmoothSchwartz r f) x at hsub
  rw [hsub, hAssoc, kernelConvolution_eq_integral, kernelConvolution_eq_integral,
    kernelConvolution_eq_integral]
  simp only [highKernel, sub_mul]
  exact (integral_sub (integrable_convolution_schwartz K hKi f x)
    (integrable_convolution_schwartz _ hL f x)).symm

/-- Exact pointwise high-error bridge for every outer convolution point.
The signed sum consists of the physical partial smoothings controlled in Section 5. -/
theorem error_projection_convolution (K : Space d → ℂ) (hK : Continuous K)
    (hKi : Integrable K) (M : ℕ) (k : Fin d → ℤ) (f : 𝓢(Space d, ℂ)) (x : Space d) :
    kernelConvolution K (errorOperator M k (f.toLp 2 volume)) x =
      ∑ J ∈ Finset.univ.powerset, (-1 : ℂ) ^ J.card *
        partialConvolution (coordinateInclusion (subsetEmbedding J))
          (subsetRadii M k (subsetEmbedding J)) (kernelConvolution (highKernel K M k) f) x := by
  rw [← errorSchwartz_toLp]
  rw [convolution_congr_ae K _ _ ((errorSchwartz M k f).coeFn_toLp 2 volume) x]
  have hs := congrArg (fun g : Space d → ℂ => g x)
    (map_sum (schwartzConvolutionLinear K hKi)
      (fun J : Finset (Fin d) => (-1 : ℂ) ^ J.card •
        canonicalLowSchwartz M k J (highRemainderSchwartz M k f)) Finset.univ.powerset)
  change kernelConvolution K (errorSchwartz M k f) x = _ at hs
  rw [hs]
  simp only [map_smul, schwartzConvolutionLinear, LinearMap.coe_mk, AddHom.coe_mk,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  have hlow : (canonicalLowSchwartz M k J (highRemainderSchwartz M k f) : Space d → ℂ) =
      partialConvolution (coordinateInclusion (subsetEmbedding J))
        (subsetRadii M k (subsetEmbedding J)) (highRemainderSchwartz M k f) := by
    funext z
    exact lowSubsetSchwartz_apply M k _ _ z
  rw [hlow, convolution_partial_commute K hK hKi]
  congr 1
  funext z
  exact highRemainder_convolution K hK hKi M k f z

end StrongSpherical.FourierProjectionBridges
