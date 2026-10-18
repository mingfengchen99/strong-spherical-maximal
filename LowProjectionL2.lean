import LowMaximalL2
import FourierProjectionBridges
import MaximalAssembly
import DyadicKernelScales

/-! # Actual low coordinate projections and the lower-dimensional maximal estimate -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators SchwartzMap
namespace StrongSpherical.LowProjectionL2
set_option maxHeartbeats 1000000
open ProductCoordinates CoordinateSubsets LowMaximalL2 FourierKernel FourierProjectionBridges
open FourierMiddle DyadicKernelScales MarginalLocalEstimate
attribute [local instance] Classical.propDecidable
variable {d m j : ℕ}

def firstRadii (r : Radii (m + j)) : Radii m :=
  ⟨fun i => r.1 (Fin.castAdd j i), fun _ => r.2 _⟩
def lastRadii (r : Radii (m + j)) : Radii j :=
  ⟨fun i => r.1 (Fin.natAdd m i), fun _ => r.2 _⟩

@[simp] theorem join_first_last (r : Radii (m + j)) :
    joinRadii (firstRadii r) (lastRadii r) = r := by
  apply Subtype.ext
  funext i
  refine Fin.addCases ?_ ?_ i <;> intro a
  · simp only [joinRadii_castAdd, firstRadii]
  · simp only [joinRadii_natAdd, lastRadii]

def reorderedSchwartz (q : Fin (m + j) ≃ Fin d) (f : 𝓢(Space d, ℂ)) :
    𝓢(Space (m + j), ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (coordinatePermutation q).toContinuousLinearEquiv f

@[simp] theorem reorderedSchwartz_apply (q : Fin (m + j) ≃ Fin d)
    (f : 𝓢(Space d, ℂ)) (x : Space (m + j)) :
    reorderedSchwartz q f x = f (coordinatePermutation q x) := rfl

theorem low_projection_le_physical (q : Fin (m + j) ≃ Fin d)
    (K : Space d → ℂ) (hK : Continuous K) (hc : HasCompactSupport K)
    (M : ℕ) (k : Fin d → ℤ) (t : Radii d) (ht : t ∈ localRadii d)
    (f : 𝓢(Space d, ℂ)) (x : Space d) :
    ‖kernelConvolution (dilatedKernel K (DyadicRadii.rectangle k t))
      (lowSubsetOperator M k (Finset.univ.image ((Fin.natAddEmb m).trans q.toEmbedding))
        (f.toLp 2 volume)) x‖ₑ ≤
      lowMaximal (reorderedKernel q K) (epsilon M) (reorderedSchwartz q f)
        ((coordinatePermutation q).symm x) := by
  let r0 := DyadicRadii.rectangle k t
  let rp := reindexRadii q r0
  let r : Radii m := firstRadii rp
  let s : Radii j := lastRadii rp
  let e : Fin j ↪ Fin d := (Fin.natAddEmb m).trans q.toEmbedding
  let b := subsetRadii M k e
  have hratio : ∀ i, s.1 i / b.1 i ≤ 2 * epsilon M := by
    intro i
    have hh := large_relative_le M k t ht (e i)
    simpa only [s, lastRadii, rp, reindexRadii, r0, b, subsetRadii,
      largeRadii, DyadicRadii.scales_apply, e, Function.Embedding.trans_apply,
      Equiv.toEmbedding_apply, Fin.natAddEmb_apply] using hh
  let p : LowParameters m j (epsilon M) := ⟨(r, (s, b)), hratio⟩
  have hKr := GenericKernelRegularity.continuous_fixed_kernel K hK r0
  have hKi := integrable_dilatedKernel K hK hc r0
  rw [low_projection_smoothed_kernel _ hKr hKi]
  rw [show kernelConvolution
    (ConvolutionSmoothing.partialConvolution (coordinateInclusion e) b (dilatedKernel K r0)) f x =
      kernelConvolution
        ((ConvolutionSmoothing.partialConvolution (coordinateInclusion e) b (dilatedKernel K r0))
          ∘ coordinatePermutation q) (f ∘ coordinatePermutation q)
          ((coordinatePermutation q).symm x) from by
      simpa only [LinearIsometryEquiv.apply_symm_apply] using
        kernelConvolution_permutation q
          (ConvolutionSmoothing.partialConvolution (coordinateInclusion e) b (dilatedKernel K r0)) f
          ((coordinatePermutation q).symm x)]
  have hker : ConvolutionSmoothing.partialConvolution (coordinateInclusion e) b
        (dilatedKernel K r0) ∘ coordinatePermutation q =
      smoothedKernel (reorderedKernel q K) r s b := by
    funext y
    rw [Function.comp_apply, partialConvolution_permutation]
    have hinc : coordinateInclusion (Fin.natAddEmb m) = lastInclusion m j := by
      ext z i
      rw [coordinateInclusion_natAdd, lastInclusion_apply]
    have hd : dilatedKernel K r0 ∘ coordinatePermutation q =
        dilatedKernel (reorderedKernel q K) (joinRadii r s) := by
      change dilatedKernel K r0 ∘ coordinatePermutation q =
        dilatedKernel (reorderedKernel q K) (joinRadii (firstRadii rp) (lastRadii rp))
      rw [join_first_last]
      funext z
      exact (dilatedKernel_reindex q K r0 z).symm
    rw [hinc, hd, ← smoothedKernel_eq_partialConvolution]
  rw [hker]
  change ‖kernelConvolution (smoothedKernel (reorderedKernel q K) r s b)
    (reorderedSchwartz q f) ((coordinatePermutation q).symm x)‖ₑ ≤ _
  exact le_iSup (fun p : LowParameters m j (epsilon M) =>
    ‖kernelConvolution (smoothedKernel (reorderedKernel q K) p.1.1 p.1.2.1 p.1.2.2)
      (reorderedSchwartz q f) ((coordinatePermutation q).symm x)‖ₑ) p

def retainedSet (J : Finset (Fin d)) : Set (Fin d) := (J : Set (Fin d))ᶜ

def complementEmbedding (J : Finset (Fin d)) :
    Fin (Fintype.card (↥((retainedSet J)ᶜ))) ↪ Fin d :=
  (Fin.natAddEmb (Fintype.card (retainedSet J))).trans
    (subsetEnumeration (retainedSet J)).toEmbedding

theorem complementEmbedding_apply (J : Finset (Fin d))
    (a : Fin (Fintype.card (↥((retainedSet J)ᶜ)))) :
    complementEmbedding J a = ((Fintype.equivFin (↥((retainedSet J)ᶜ))).symm a).1 := by
  change subsetEnumeration (retainedSet J)
    (Fin.natAdd (Fintype.card (retainedSet J)) a) = _
  simp only [subsetEnumeration, Equiv.trans_apply, finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inr, Equiv.Set.sumCompl_apply_inr]

theorem complementEmbedding_image (J : Finset (Fin d)) :
    Finset.univ.image (complementEmbedding J) = J := by
  ext i
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩
    rw [complementEmbedding_apply]
    have h := ((Fintype.equivFin (↥((retainedSet J)ᶜ))).symm a).2
    simpa only [retainedSet, compl_compl, Finset.mem_coe] using h
  · intro hi
    have hh : i ∈ (retainedSet J)ᶜ := by simpa [retainedSet] using hi
    refine ⟨Fintype.equivFin (↥((retainedSet J)ᶜ)) ⟨i, hh⟩, ?_⟩
    rw [complementEmbedding_apply, Equiv.symm_apply_apply]

theorem retainedSet_card_lt (J : Finset (Fin d)) (hJ : J.Nonempty) :
    Fintype.card (retainedSet J) < d := by
  have hc := Fintype.card_congr (subsetEnumeration (retainedSet J))
  simp only [Fintype.card_fin] at hc
  have hj : 0 < Fintype.card (↥((retainedSet J)ᶜ)) := by
    apply Fintype.card_pos_iff.mpr
    obtain ⟨i, hi⟩ := hJ
    exact ⟨⟨i, by simpa [retainedSet] using hi⟩⟩
  omega

theorem projectionMaximal_le_physical (q : Fin (m + j) ≃ Fin d)
    (K : Space d → ℂ) (hK : Continuous K) (hc : HasCompactSupport K)
    (M : ℕ) (f : 𝓢(Space d, ℂ)) (x : Space d) :
    MaximalAssembly.projectionMaximal K
      (fun k => lowSubsetOperator M k
        (Finset.univ.image ((Fin.natAddEmb m).trans q.toEmbedding))) (f.toLp 2 volume) x ≤
      lowMaximal (reorderedKernel q K) (epsilon M) (reorderedSchwartz q f)
        ((coordinatePermutation q).symm x) := by
  unfold MaximalAssembly.projectionMaximal DilationL2.rectangleMaximal
  refine iSup_le fun k => iSup_le fun t => iSup_le fun ht => ?_
  exact low_projection_le_physical q K hK hc M k t ht f x

/-- Each nonempty low coordinate projection is controlled by the actual strong
maximal operator of its complementary coordinate marginal. -/
theorem exists_lowProjection_bound (J : Finset (Fin d)) (_hJ : J.Nonempty)
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Space d → ℂ), Continuous K →
      Function.support K ⊆ MarginalEnergy.coordinateBox d R →
      ∀ B : ℝ, (∀ x, ‖K x‖ ≤ B) → ∀ M : ℕ, ∀ D : ℝ≥0∞,
      (∀ g : Space (Fintype.card (retainedSet J)) → ℂ, MemLp g 2 volume →
        eLpNorm (strongKernelMaximal (subsetMarginal (retainedSet J) K) g) 2 volume ≤
          D * eLpNorm g 2 volume) →
      ∀ f : 𝓢(Space d, ℂ),
      eLpNorm (MaximalAssembly.projectionMaximal K
        (fun k => lowSubsetOperator M k J) (f.toLp 2 volume)) 2 volume ≤
        ENNReal.ofReal C * (D + ENNReal.ofReal (epsilon M * B)) * eLpNorm f 2 volume := by
  let I := retainedSet J
  let m := Fintype.card I
  let j := Fintype.card (↥(Iᶜ))
  let q := subsetEnumeration I
  obtain ⟨C, hC, hbound⟩ := exists_lowMaximal_bound m j R hR
  refine ⟨C, hC, ?_⟩
  intro K hK hs B hB M D hIH f
  have hKq : Continuous (reorderedKernel q K) := hK.comp (coordinatePermutation q).continuous
  have hsq := reorderedKernel_support q K R hs
  have hc : HasCompactSupport K :=
    (GenericKernelRegularity.isCompact_coordinateBox d R).of_isClosed_subset
      (isClosed_tsupport _) (closure_minimal hs
        (GenericKernelRegularity.isCompact_coordinateBox d R).isClosed)
  have hPoint : ∀ x, MaximalAssembly.projectionMaximal K
      (fun k => lowSubsetOperator M k J) (f.toLp 2 volume) x ≤
        lowMaximal (reorderedKernel q K) (epsilon M) (reorderedSchwartz q f)
          ((coordinatePermutation q).symm x) := by
    intro x
    have hh := projectionMaximal_le_physical q K hK hc M f x
    have hImage : Finset.univ.image ((Fin.natAddEmb m).trans q.toEmbedding) = J :=
      complementEmbedding_image J
    rw [hImage] at hh
    exact hh
  have hNorm := hbound (reorderedKernel q K) hKq hsq B (fun _ => hB _)
    (epsilon M) (epsilon_pos M).le (epsilon_le_one M) D hIH (reorderedSchwartz q f)
  calc
    _ ≤ eLpNorm (fun x => lowMaximal (reorderedKernel q K) (epsilon M)
        (reorderedSchwartz q f) ((coordinatePermutation q).symm x)) 2 volume := by
      apply eLpNorm_mono_enorm
      intro x
      simpa only [enorm_eq_self] using hPoint x
    _ = eLpNorm (lowMaximal (reorderedKernel q K) (epsilon M) (reorderedSchwartz q f))
        2 volume := by
      rw [coordinatePermutation_symm]
      change eLpNorm (lowMaximal (reorderedKernel q K) (epsilon M) (reorderedSchwartz q f)
        ∘ coordinatePermutation q.symm) 2 volume = _
      exact eLpNorm_ennreal_comp_permutation q.symm
        (lowMaximal (reorderedKernel q K) (epsilon M) (reorderedSchwartz q f))
    _ ≤ _ := by
      simpa only [show (reorderedSchwartz q f : Space (m + j) → ℂ) =
        f ∘ coordinatePermutation q from rfl, eLpNorm_comp_permutation] using hNorm

/-- The finite sum of all nonempty low projections.  The constant is chosen
before the kernel, the scale gap, and the marginal induction bound. -/
theorem exists_lowProjection_sum_bound (d : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Space d → ℂ), Continuous K →
      Function.support K ⊆ MarginalEnergy.coordinateBox d R →
      ∀ B : ℝ, (∀ x, ‖K x‖ ≤ B) → ∀ M : ℕ, ∀ D : ℝ≥0∞,
      (∀ I : Set (Fin d), Fintype.card I < d →
        ∀ g : Space (Fintype.card I) → ℂ, MemLp g 2 volume →
          eLpNorm (strongKernelMaximal (subsetMarginal I K) g) 2 volume ≤
            D * eLpNorm g 2 volume) →
      ∀ f : 𝓢(Space d, ℂ),
      (∑ J ∈ Finset.univ.powerset.erase ∅,
        eLpNorm (MaximalAssembly.projectionMaximal K
          (fun k => lowSubsetOperator M k J) (f.toLp 2 volume)) 2 volume) ≤
        ENNReal.ofReal C * (D + ENNReal.ofReal (epsilon M * B)) * eLpNorm f 2 volume := by
  classical
  let S : Finset (Finset (Fin d)) := Finset.univ.powerset.erase ∅
  have hex : ∀ J : Finset (Fin d), J.Nonempty → ∃ C : ℝ, 0 < C ∧
      ∀ (K : Space d → ℂ), Continuous K →
      Function.support K ⊆ MarginalEnergy.coordinateBox d R →
      ∀ B : ℝ, (∀ x, ‖K x‖ ≤ B) → ∀ M : ℕ, ∀ D : ℝ≥0∞,
      (∀ g : Space (Fintype.card (retainedSet J)) → ℂ, MemLp g 2 volume →
        eLpNorm (strongKernelMaximal (subsetMarginal (retainedSet J) K) g) 2 volume ≤
          D * eLpNorm g 2 volume) →
      ∀ f : 𝓢(Space d, ℂ),
      eLpNorm (MaximalAssembly.projectionMaximal K
        (fun k => lowSubsetOperator M k J) (f.toLp 2 volume)) 2 volume ≤
        ENNReal.ofReal C * (D + ENNReal.ofReal (epsilon M * B)) * eLpNorm f 2 volume :=
    fun J hJ => exists_lowProjection_bound J hJ R hR
  let c : Finset (Fin d) → ℝ := fun J => if h : J.Nonempty then Classical.choose (hex J h) else 1
  have hc : ∀ J, 0 < c J := by
    intro J
    dsimp [c]
    split_ifs with h
    · exact (Classical.choose_spec (hex J h)).1
    · norm_num
  let C := (∑ J ∈ S, c J) + 1
  have hC : 0 < C := by
    have hh : 0 ≤ ∑ J ∈ S, c J := Finset.sum_nonneg fun J _ => (hc J).le
    dsimp [C]
    linarith
  refine ⟨C, hC, ?_⟩
  intro K hK hs B hB M D hIH f
  have hJbound : ∀ J ∈ S,
      eLpNorm (MaximalAssembly.projectionMaximal K
        (fun k => lowSubsetOperator M k J) (f.toLp 2 volume)) 2 volume ≤
        ENNReal.ofReal (c J) * (D + ENNReal.ofReal (epsilon M * B)) * eLpNorm f 2 volume := by
    intro J hJS
    have hJ : J.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hJS).1
    have hh := (Classical.choose_spec (hex J hJ)).2 K hK hs B hB M D
      (hIH (retainedSet J) (retainedSet_card_lt J hJ)) f
    simpa only [c, dif_pos hJ] using hh
  calc
    _ ≤ ∑ J ∈ S, ENNReal.ofReal (c J) *
        (D + ENNReal.ofReal (epsilon M * B)) * eLpNorm f 2 volume :=
      Finset.sum_le_sum hJbound
    _ = (∑ J ∈ S, ENNReal.ofReal (c J)) *
        (D + ENNReal.ofReal (epsilon M * B)) * eLpNorm f 2 volume := by
      rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ _ := by
      apply mul_le_mul' (mul_le_mul' ?_ le_rfl) le_rfl
      rw [← ENNReal.ofReal_sum_of_nonneg (fun J _ => (hc J).le)]
      exact ENNReal.ofReal_le_ofReal (by dsimp [C]; linarith)

end StrongSpherical.LowProjectionL2
