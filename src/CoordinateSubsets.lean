import MarginalC1
import Mathlib.Logic.Equiv.Set

/-! # Arbitrary coordinate subsets, exact covariance, and the empty marginal -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace StrongSpherical.CoordinateSubsets
open ProductCoordinates CoordinateMarginals MarginalLocalEstimate
variable {n k m j : ℕ}

def coordinatePermutation (e : Fin k ≃ Fin n) : Space k ≃ₗᵢ[ℝ] Space n :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ e

@[simp] theorem coordinatePermutation_apply (e : Fin k ≃ Fin n) (x : Space k) (i : Fin n) :
    coordinatePermutation e x i = x (e.symm i) := rfl

@[simp] theorem coordinatePermutation_symm (e : Fin k ≃ Fin n) :
    (coordinatePermutation e).symm = coordinatePermutation e.symm := by
  exact LinearIsometryEquiv.piLpCongrLeft_symm e

def reindexRadii (e : Fin k ≃ Fin n) (r : Radii n) : Radii k :=
  ⟨fun i => r.1 (e i), fun i => r.2 (e i)⟩

theorem reindexRadii_local (e : Fin k ≃ Fin n) (r : Radii n) (hr : r ∈ localRadii n) :
    reindexRadii e r ∈ localRadii k := fun i => hr (e i)

@[simp] theorem reindexRadii_symm (e : Fin k ≃ Fin n) (r : Radii k) :
    reindexRadii e (reindexRadii e.symm r) = r := by
  apply Subtype.ext
  funext i
  simp [reindexRadii]

theorem dilationJacobian_reindex (e : Fin k ≃ Fin n) (r : Radii n) :
    dilationJacobian (reindexRadii e r) = dilationJacobian r := e.prod_comp r.1

theorem inverseDilation_reindex (e : Fin k ≃ Fin n) (r : Radii n) (x : Space k) :
    coordinatePermutation e (inverseDilation (reindexRadii e r) x) =
      inverseDilation r (coordinatePermutation e x) := by
  ext i
  simp [inverseDilation, reindexRadii]

def reorderedKernel (e : Fin k ≃ Fin n) (K : Space n → ℂ) : Space k → ℂ :=
  K ∘ coordinatePermutation e

theorem dilatedKernel_reindex (e : Fin k ≃ Fin n) (K : Space n → ℂ) (r : Radii n)
    (x : Space k) :
    dilatedKernel (reorderedKernel e K) (reindexRadii e r) x =
      dilatedKernel K r (coordinatePermutation e x) := by
  simp only [dilatedKernel, reorderedKernel, Function.comp_apply, dilationJacobian_reindex]
  rw [inverseDilation_reindex]

theorem convolution_reindex (e : Fin k ≃ Fin n) (K f : Space n → ℂ)
    (r : Radii n) (x : Space k) :
    kernelConvolution (dilatedKernel (reorderedKernel e K) (reindexRadii e r))
      (f ∘ coordinatePermutation e) x =
      kernelConvolution (dilatedKernel K r) f (coordinatePermutation e x) := by
  rw [kernelConvolution_eq_integral, kernelConvolution_eq_integral]
  simp_rw [dilatedKernel_reindex]
  have he : (fun y : Space k => dilatedKernel K r (coordinatePermutation e y) *
      (f ∘ coordinatePermutation e) (x - y)) =
      (fun y => dilatedKernel K r y * f (coordinatePermutation e x - y)) ∘
        coordinatePermutation e := by
    funext y
    simp only [Function.comp_apply, map_sub]
  rw [he]
  convert (coordinatePermutation e).measurePreserving.integral_comp
    (coordinatePermutation e).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun y : Space n => dilatedKernel K r y * f (coordinatePermutation e x - y)) using 1
  rfl

theorem localKernelMaximal_reindex (e : Fin k ≃ Fin n) (K f : Space n → ℂ)
    (x : Space k) :
    localKernelMaximal (reorderedKernel e K) (f ∘ coordinatePermutation e) x =
      localKernelMaximal K f (coordinatePermutation e x) := by
  apply le_antisymm
  · apply iSup_le
    intro r
    apply iSup_le
    intro hr
    have hrr := reindexRadii_symm e r
    change ‖kernelConvolution (dilatedKernel (reorderedKernel e K) r)
      (f ∘ coordinatePermutation e) x‖ₑ ≤ _
    rw [← hrr, convolution_reindex]
    exact le_maximalOver _ _ _ (reindexRadii_local e.symm r hr)
  · apply iSup_le
    intro r
    apply iSup_le
    intro hr
    change ‖kernelConvolution (dilatedKernel K r) f (coordinatePermutation e x)‖ₑ ≤ _
    rw [← convolution_reindex e K f r x]
    exact le_maximalOver _ _ _ (reindexRadii_local e r hr)

theorem eLpNorm_comp_permutation (e : Fin k ≃ Fin n) (f : Space n → ℂ) :
    eLpNorm (f ∘ coordinatePermutation e) 2 volume = eLpNorm f 2 volume := by
  apply (ENNReal.rpow_left_injective (by norm_num : (2 : ℝ) ≠ 0))
  simp only [ENNReal.rpow_two, SchurTest.eLpNorm_two_sq]
  convert (coordinatePermutation e).measurePreserving.lintegral_comp_emb
    (coordinatePermutation e).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun y : Space n => ‖f y‖ₑ ^ 2) using 1
  rfl

theorem eLpNorm_ennreal_comp_permutation (e : Fin k ≃ Fin n) (F : Space n → ℝ≥0∞) :
    eLpNorm (F ∘ coordinatePermutation e) 2 volume = eLpNorm F 2 volume := by
  apply (ENNReal.rpow_left_injective (by norm_num : (2 : ℝ) ≠ 0))
  simp only [ENNReal.rpow_two, eLpNorm_two_sq_ennreal]
  convert (coordinatePermutation e).measurePreserving.lintegral_comp_emb
    (coordinatePermutation e).toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun y : Space n => F y ^ 2) using 1
  rfl

theorem reorderedKernel_support (e : Fin k ≃ Fin n) (K : Space n → ℂ) (R : ℝ)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R) :
    Function.support (reorderedKernel e K) ⊆ MarginalEnergy.coordinateBox k R := by
  intro x hx i
  simpa only [coordinatePermutation_apply, Equiv.symm_apply_apply] using hs hx (e i)

theorem contDiff_reorderedKernel (e : Fin k ≃ Fin n) (K : Space n → ℂ)
    (hK : ContDiff ℝ 1 K) : ContDiff ℝ 1 (reorderedKernel e K) :=
  hK.comp (coordinatePermutation e).contDiff

theorem norm_fderiv_reorderedKernel_le (e : Fin k ≃ Fin n) (K : Space n → ℂ)
    (hK : ContDiff ℝ 1 K) (B : ℝ) (hB : ∀ x, ‖fderiv ℝ K x‖ ≤ B) (x : Space k) :
    ‖fderiv ℝ (reorderedKernel e K) x‖ ≤ B := by
  have hd := (hK.differentiable one_ne_zero (coordinatePermutation e x)).hasFDerivAt.comp x
    (coordinatePermutation e).hasFDerivAt
  change ‖fderiv ℝ (K ∘ coordinatePermutation e) x‖ ≤ B
  rw [hd.fderiv]
  calc
    _ ≤ ‖fderiv ℝ K (coordinatePermutation e x)‖ *
        ‖(coordinatePermutation e).toContinuousLinearEquiv.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ K (coordinatePermutation e x)‖ * 1 :=
      mul_le_mul_of_nonneg_left
        (coordinatePermutation e).toLinearIsometry.norm_toContinuousLinearMap_le (norm_nonneg _)
    _ ≤ B := by simpa using hB (coordinatePermutation e x)

/-- Arbitrary coordinate permutations preserve the given original local constant exactly. -/
theorem reordered_local_bound (e : Fin k ≃ Fin n) (K : Space n → ℂ) (A : ℝ≥0∞)
    (hlocal : ∀ f : Space n → ℂ, MemLp f 2 volume →
      eLpNorm (localKernelMaximal K f) 2 volume ≤ A * eLpNorm f 2 volume)
    (g : Space k → ℂ) (hg : MemLp g 2 volume) :
    eLpNorm (localKernelMaximal (reorderedKernel e K) g) 2 volume ≤ A * eLpNorm g 2 volume := by
  let f := g ∘ (coordinatePermutation e).symm
  have hf : MemLp f 2 volume := hg.comp_measurePreserving (coordinatePermutation e).symm.measurePreserving
  have he : f ∘ coordinatePermutation e = g := by
    funext x
    exact congrArg g ((coordinatePermutation e).symm_apply_apply x)
  have hm : localKernelMaximal (reorderedKernel e K) g =
      localKernelMaximal K f ∘ coordinatePermutation e := by
    rw [← he]
    funext x
    exact localKernelMaximal_reindex e K f x
  rw [hm, eLpNorm_ennreal_comp_permutation]
  have hin : eLpNorm f 2 volume = eLpNorm g 2 volume := by
    simpa only [f, coordinatePermutation_symm] using eLpNorm_comp_permutation e.symm g
  simpa only [hin] using hlocal f hf

/-- A concrete enumeration: selected coordinates first, complementary coordinates second. -/
def subsetEnumeration (I : Set (Fin n)) :
    Fin (Fintype.card I + Fintype.card (↥(Iᶜ : Set (Fin n)))) ≃ Fin n := by
  classical
  exact finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (Fintype.equivFin I).symm (Fintype.equivFin (↥(Iᶜ : Set (Fin n)))).symm).trans
      (Equiv.Set.sumCompl I))

def subsetMarginal (I : Set (Fin n)) (K : Space n → ℂ) :
    Space (Fintype.card I) → ℂ :=
  marginalKernel (reorderedKernel (subsetEnumeration I) K)

theorem subset_marginal_local_bound (I : Set (Fin n)) (K : Space n → ℂ)
    (hK : Continuous K) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R) (A : ℝ≥0∞)
    (hlocal : ∀ f : Space n → ℂ, MemLp f 2 volume →
      eLpNorm (localKernelMaximal K f) 2 volume ≤ A * eLpNorm f 2 volume)
    (g : Space (Fintype.card I) → ℂ) (hg : MemLp g 2 volume) :
    Measurable (localKernelMaximal (subsetMarginal I K) g) ∧
      eLpNorm (localKernelMaximal (subsetMarginal I K) g) 2 volume ≤ A * eLpNorm g 2 volume :=
  marginal_local_bound _ (hK.comp (coordinatePermutation (subsetEnumeration I)).continuous)
    R hR (reorderedKernel_support _ K R hs) A
    (reordered_local_bound (subsetEnumeration I) K A hlocal) g hg

theorem contDiff_subsetMarginal (I : Set (Fin n)) (K : Space n → ℂ)
    (hK : ContDiff ℝ 1 K) (R : ℝ)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R) :
    ContDiff ℝ 1 (subsetMarginal I K) :=
  MarginalC1.contDiff_marginalKernel _ (contDiff_reorderedKernel _ K hK)
    R (reorderedKernel_support _ K R hs)

theorem subsetMarginal_support (I : Set (Fin n)) (K : Space n → ℂ) (R : ℝ)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R) :
    Function.support (subsetMarginal I K) ⊆ MarginalEnergy.coordinateBox (Fintype.card I) R :=
  marginalKernel_support _ R (reorderedKernel_support _ K R hs)

theorem norm_subsetMarginal_le (I : Set (Fin n)) (K : Space n → ℂ)
    (hK : ContDiff ℝ 1 K) (R B : ℝ)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R)
    (hB : ∀ x, ‖K x‖ ≤ B) (u : Space (Fintype.card I)) :
    ‖subsetMarginal I K u‖ ≤
      (volume : Measure (Space (Fintype.card (↥(Iᶜ : Set (Fin n)))))).real
        (coordinateCube (Fintype.card (↥(Iᶜ : Set (Fin n)))) R) * B :=
  MarginalC1.norm_marginalKernel_le _
    (contDiff_reorderedKernel _ K hK).continuous R B
    (reorderedKernel_support _ K R hs) (fun _ => hB _) u

theorem norm_fderiv_subsetMarginal_le (I : Set (Fin n)) (K : Space n → ℂ)
    (hK : ContDiff ℝ 1 K) (R B : ℝ)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R)
    (hB : ∀ x, ‖fderiv ℝ K x‖ ≤ B) (u : Space (Fintype.card I)) :
    ‖fderiv ℝ (subsetMarginal I K) u‖ ≤
      (volume : Measure (Space (Fintype.card (↥(Iᶜ : Set (Fin n)))))).real
        (coordinateCube (Fintype.card (↥(Iᶜ : Set (Fin n)))) R) * B :=
  MarginalC1.norm_fderiv_marginalKernel_le _
    (contDiff_reorderedKernel _ K hK) R B
    (reorderedKernel_support _ K R hs)
    (norm_fderiv_reorderedKernel_le _ K hK B hB) u

theorem kernelConvolution_empty (H g : Space 0 → ℂ) (x : Space 0) :
    kernelConvolution H g x = H 0 * g 0 := by
  rw [kernelConvolution_eq_integral]
  have he : (fun y : Space 0 => H y * g (x - y)) = fun _ => H 0 * g 0 := by
    funext y
    rw [show y = 0 from Subsingleton.elim _ _, show x = 0 from Subsingleton.elim _ _]
    simp
  rw [he, integral_const, measureReal_def, volume_space_zero, ENNReal.toReal_one, one_smul]

theorem localKernelMaximal_empty (H g : Space 0 → ℂ) (x : Space 0) :
    localKernelMaximal H g x = ‖H 0 * g 0‖ₑ := by
  have hd : ∀ r : Radii 0, dilatedKernel H r 0 = H 0 := by
    intro r
    simp [dilatedKernel, dilationJacobian,
      show inverseDilation r (0 : Space 0) = 0 from Subsingleton.elim _ _]
  have he : ∀ r : Radii 0,
      kernelConvolution (dilatedKernel H r) g x = H 0 * g 0 := by
    intro r
    rw [kernelConvolution_empty, hd]
  apply le_antisymm
  · apply iSup_le
    intro r
    apply iSup_le
    intro _hr
    simp only [he, le_refl]
  · have h := le_maximalOver (localRadii 0)
      (fun r => kernelConvolution (dilatedKernel H r) g) x unitRadii_mem_localRadii
    simp only [he] at h
    convert h using 1 <;> rfl

theorem marginalKernel_empty_mass (K : Space (0 + j) → ℂ) (hK : Continuous K)
    (R : ℝ) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox (0 + j) R) :
    marginalKernel (m := 0) (j := j) K 0 = ∫ x, K x := by
  have h := integral_split K (hK.integrable_of_hasCompactSupport (hasCompactSupport_of_box K R hs))
  have he : (fun u : Space 0 => ∫ v : Space j, K ((split 0 j).symm (u, v))) =
      fun _ => marginalKernel (m := 0) (j := j) K 0 := by
    funext u
    rw [show u = 0 from Subsingleton.elim _ _]
    rfl
  rw [he, integral_const, measureReal_def, volume_space_zero, ENNReal.toReal_one, one_smul] at h
  exact h.symm

theorem integral_enorm_le_local_bound_first_empty (K : Space (0 + j) → ℂ)
    (hK : Continuous K) (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox (0 + j) R) (A : ℝ≥0∞)
    (hlocal : ∀ f : Space (0 + j) → ℂ, MemLp f 2 volume →
      eLpNorm (localKernelMaximal K f) 2 volume ≤ A * eLpNorm f 2 volume) :
    ‖∫ x, K x‖ₑ ≤ A := by
  letI : IsProbabilityMeasure (volume : Measure (Space 0)) := ⟨volume_space_zero⟩
  have h := (marginal_local_bound (m := 0) (j := j) K hK R hR hs A hlocal
    (fun _ : Space 0 => (1 : ℂ)) (memLp_const 1)).2
  have he : localKernelMaximal (marginalKernel K) (fun _ : Space 0 => (1 : ℂ)) =
      fun _ => ‖marginalKernel K 0‖ₑ := by
    funext x
    simp only [localKernelMaximal_empty, mul_one]
  rw [he] at h
  have h' : ‖marginalKernel K 0‖ₑ ≤ A := by
    simpa [eLpNorm_const', enorm_eq_self] using h
  rw [marginalKernel_empty_mass K hK R hs] at h'
  exact h'

/-- The scalar empty marginal has modulus at most the original local L² constant. -/
theorem integral_enorm_le_local_bound (K : Space n → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R)
    (A : ℝ≥0∞)
    (hlocal : ∀ f : Space n → ℂ, MemLp f 2 volume →
      eLpNorm (localKernelMaximal K f) 2 volume ≤ A * eLpNorm f 2 volume) :
    ‖∫ x, K x‖ₑ ≤ A := by
  let e : Fin (0 + n) ≃ Fin n := finCongr (Nat.zero_add n)
  have h := integral_enorm_le_local_bound_first_empty
    (reorderedKernel e K) (hK.comp (coordinatePermutation e).continuous)
    R hR (reorderedKernel_support e K R hs) A (reordered_local_bound e K A hlocal)
  have he : (∫ x, reorderedKernel e K x) = ∫ x, K x :=
    (coordinatePermutation e).measurePreserving.integral_comp
      (coordinatePermutation e).toHomeomorph.toMeasurableEquiv.measurableEmbedding K
  rwa [he] at h

theorem norm_integral_le_local_bound (K : Space n → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R)
    (A : ℝ) (hA : 0 ≤ A)
    (hlocal : ∀ f : Space n → ℂ, MemLp f 2 volume →
      eLpNorm (localKernelMaximal K f) 2 volume ≤ ENNReal.ofReal A * eLpNorm f 2 volume) :
    ‖∫ x, K x‖ ≤ A := by
  have h := integral_enorm_le_local_bound K hK R hR hs (ENNReal.ofReal A) hlocal
  rw [← ofReal_norm] at h
  exact (ENNReal.ofReal_le_ofReal_iff hA).mp h

end StrongSpherical.CoordinateSubsets
