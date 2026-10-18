import Definitions

/-! # Splitting Euclidean coordinates and Lebesgue measure

This interface identifies the ambient Euclidean space with two blocks of
coordinates.  The target measure is the explicit product of the two
Euclidean Lebesgue measures, as used for coordinate marginals.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StrongSpherical.ProductCoordinates

variable {m j : ℕ}

/-- Split the first `m` coordinates from the last `j` coordinates. -/
def split (m j : ℕ) : Space (m + j) ≃ᵐ Space m × Space j :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := j)).toHomeomorph.toMeasurableEquiv

@[simp] theorem split_fst (v : Space (m + j)) (i : Fin m) :
    (split m j v).1 i = v (Fin.castAdd j i) := rfl

@[simp] theorem split_snd (v : Space (m + j)) (i : Fin j) :
    (split m j v).2 i = v (Fin.natAdd m i) := rfl

@[simp] theorem split_symm_castAdd (u : Space m × Space j) (i : Fin m) :
    (split m j).symm u (Fin.castAdd j i) = u.1 i := by
  have h := congrArg (fun p : Space m × Space j => p.1 i)
    ((split m j).apply_symm_apply u)
  exact h

@[simp] theorem split_symm_natAdd (u : Space m × Space j) (i : Fin j) :
    (split m j).symm u (Fin.natAdd m i) = u.2 i := by
  have h := congrArg (fun p : Space m × Space j => p.2 i)
    ((split m j).apply_symm_apply u)
  exact h

theorem continuous_split (m j : ℕ) : Continuous (split m j) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := j)).continuous

theorem continuous_split_symm (m j : ℕ) : Continuous (split m j).symm :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := j)).symm.continuous

/-- The splitting has Jacobian one for the canonical Euclidean volume. -/
theorem measurePreserving_split (m j : ℕ) :
    MeasurePreserving (split m j) (volume : Measure (Space (m + j)))
      ((volume : Measure (Space m)).prod (volume : Measure (Space j))) := by
  have h := (WithLp.volume_preserving_ofLp (Space m) (Space j)).comp
    ((PiLp.sumPiLpEquivProdLpPiLp 2 (fun _ : Fin m ⊕ Fin j => ℝ)).measurePreserving.comp
      ((LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
        (finSumFinEquiv.symm : Fin (m + j) ≃ Fin m ⊕ Fin j)).measurePreserving))
  convert h using 1 <;>
    try (borelize (Space (m + j)) (Space m) (Space j) (Space m × Space j); rfl)

theorem lintegral_split (F : Space (m + j) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, F v) = ∫⁻ u, ∫⁻ w, F ((split m j).symm (u, w)) := by
  rw [← (measurePreserving_split m j).symm.lintegral_comp_emb
    (split m j).symm.measurableEmbedding F]
  exact lintegral_prod _ ((hF.comp (split m j).symm.measurable).aemeasurable)

theorem integral_split {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Space (m + j) → E) (hF : Integrable F) :
    (∫ v, F v) = ∫ u, ∫ w, F ((split m j).symm (u, w)) := by
  calc
    _ = ∫ p : Space m × Space j, F ((split m j).symm p)
        ∂((volume : Measure (Space m)).prod (volume : Measure (Space j))) :=
      ((measurePreserving_split m j).symm.integral_comp' F).symm
    _ = _ := integral_prod _ ((measurePreserving_split m j).symm.integrable_comp_emb
      (split m j).symm.measurableEmbedding |>.2 hF)

theorem eLpNorm_comp_split_symm {E : Type*} [NormedAddCommGroup E]
    (f : Space (m + j) → E) (p : ℝ≥0∞) (hf : AEStronglyMeasurable f volume) :
    eLpNorm (f ∘ (split m j).symm) p
      ((volume : Measure (Space m)).prod (volume : Measure (Space j))) =
        eLpNorm f p volume :=
  eLpNorm_comp_measurePreserving hf (measurePreserving_split m j).symm

@[simp] theorem split_sub (u v : Space (m + j)) :
    split m j (u - v) = split m j u - split m j v :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := j)).map_sub u v

@[simp] theorem split_symm_sub (u v : Space m × Space j) :
    (split m j).symm (u - v) = (split m j).symm u - (split m j).symm v :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := j)).symm.map_sub u v

/-- Convolution is unchanged when the Euclidean coordinates are split into blocks. -/
theorem kernelConvolution_eq_product (K f : Space (m + j) → ℂ) (x : Space (m + j)) :
    kernelConvolution K f x =
      ∫ p : Space m × Space j,
        K ((split m j).symm p) * f ((split m j).symm (split m j x - p))
        ∂((volume : Measure (Space m)).prod (volume : Measure (Space j))) := by
  rw [kernelConvolution_eq_integral]
  have h := ((measurePreserving_split m j).symm.integral_comp'
    (fun y : Space (m + j) => K y * f (x - y))).symm
  simpa only [split_symm_sub, MeasurableEquiv.symm_apply_apply] using h

/-- Join two positive radius blocks in the original coordinate order. -/
def joinRadii (r : Radii m) (s : Radii j) : Radii (m + j) :=
  ⟨Fin.addCases r.1 s.1, by
    intro i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i
    · simpa using r.2 a
    · simpa using s.2 b⟩

@[simp] theorem joinRadii_castAdd (r : Radii m) (s : Radii j) (i : Fin m) :
    (joinRadii r s).1 (Fin.castAdd j i) = r.1 i := by simp [joinRadii]

@[simp] theorem joinRadii_natAdd (r : Radii m) (s : Radii j) (i : Fin j) :
    (joinRadii r s).1 (Fin.natAdd m i) = s.1 i := by simp [joinRadii]

theorem dilationJacobian_joinRadii (r : Radii m) (s : Radii j) :
    dilationJacobian (joinRadii r s) = dilationJacobian r * dilationJacobian s := by
  unfold dilationJacobian
  rw [Fin.prod_univ_add]
  simp only [joinRadii_castAdd, joinRadii_natAdd]

theorem joinRadii_local (r : Radii m) (s : Radii j)
    (hr : r ∈ localRadii m) (hs : s ∈ localRadii j) :
    joinRadii r s ∈ localRadii (m + j) := by
  intro i
  refine Fin.addCases (fun a => ?_) (fun b => ?_) i
  · simpa only [joinRadii_castAdd] using hr a
  · simpa only [joinRadii_natAdd] using hs b

theorem split_inverseDilation (r : Radii m) (s : Radii j) (v : Space (m + j)) :
    split m j (inverseDilation (joinRadii r s) v) =
      (inverseDilation r (split m j v).1, inverseDilation s (split m j v).2) := by
  apply Prod.ext
  · ext i
    simp [inverseDilation]
  · ext i
    simp [inverseDilation]

/-- Unit radii in the integrated block give precisely partial kernel dilation. -/
theorem dilatedKernel_join_unit (K : Space (m + j) → ℂ) (r : Radii m)
    (p : Space m × Space j) :
    dilatedKernel K (joinRadii r (unitRadii j)) ((split m j).symm p) =
      (dilationJacobian r : ℂ)⁻¹ *
        K ((split m j).symm (inverseDilation r p.1, p.2)) := by
  have hInv : inverseDilation (joinRadii r (unitRadii j)) ((split m j).symm p) =
      (split m j).symm (inverseDilation r p.1, p.2) := by
    apply (split m j).injective
    rw [split_inverseDilation]
    simp [inverseDilation, unitRadii]
  unfold dilatedKernel
  rw [hInv, dilationJacobian_joinRadii]
  have hunit : dilationJacobian (unitRadii j) = 1 := by
    simp [dilationJacobian, unitRadii]
  rw [hunit, mul_one]

end StrongSpherical.ProductCoordinates
