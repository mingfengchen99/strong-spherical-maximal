import MarginalLocalEstimate
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-! # C¹ regularity and derivative bounds for actual coordinate marginals -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology ContDiff
namespace StrongSpherical.MarginalC1
open ProductCoordinates CoordinateMarginals MarginalLocalEstimate
variable {m j : ℕ}

/-- The first coordinate block, inserted into the original Euclidean space. -/
def joinFirst (m j : ℕ) : Space m →L[ℝ] Space (m + j) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := j)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inl ℝ (Space m) (Space j))

theorem joinFirst_apply (u : Space m) :
    joinFirst m j u = (split m j).symm (u, 0) := rfl

theorem norm_joinFirst_apply (u : Space m) : ‖joinFirst m j u‖ = ‖u‖ := by
  have he : ‖joinFirst m j u‖ ^ 2 = ‖u‖ ^ 2 := by
    rw [norm_sq_eq_sum_coordinates, norm_sq_eq_sum_coordinates, Fin.sum_univ_add]
    simp [joinFirst_apply, split_symm_castAdd, split_symm_natAdd]
  nlinarith [norm_nonneg (joinFirst m j u), norm_nonneg u]

theorem norm_joinFirst_le_one : ‖joinFirst m j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simp only [norm_joinFirst_apply, one_mul, le_refl]

theorem hasFDerivAt_join (u : Space m) (v : Space j) :
    HasFDerivAt (fun w : Space m => (split m j).symm (w, v)) (joinFirst m j) u := by
  have h := (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := j)).symm.hasFDerivAt.comp u
    ((hasFDerivAt_id u).prodMk (hasFDerivAt_const v u))
  convert h using 1 <;> rfl

/-- The retained-coordinate derivative of the actual kernel, before integration. -/
def marginalDerivativeIntegrand (K : Space (m + j) → ℂ)
    (p : Space m × Space j) : Space m →L[ℝ] ℂ :=
  (fderiv ℝ K ((split m j).symm p)).comp (joinFirst m j)

def marginalDerivative (K : Space (m + j) → ℂ) (u : Space m) : Space m →L[ℝ] ℂ :=
  ∫ v, marginalDerivativeIntegrand K (u, v)

theorem continuous_marginalDerivativeIntegrand (K : Space (m + j) → ℂ)
    (hK : ContDiff ℝ 1 K) : Continuous (marginalDerivativeIntegrand K) := by
  exact ((hK.continuous_fderiv one_ne_zero).comp (continuous_split_symm m j)).clm_comp
    continuous_const

theorem norm_marginalDerivativeIntegrand_le (K : Space (m + j) → ℂ) (B : ℝ)
    (hB : ∀ x, ‖fderiv ℝ K x‖ ≤ B) (p : Space m × Space j) :
    ‖marginalDerivativeIntegrand K p‖ ≤ B := by
  calc
    _ ≤ ‖fderiv ℝ K ((split m j).symm p)‖ * ‖joinFirst m j‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ K ((split m j).symm p)‖ * 1 :=
      mul_le_mul_of_nonneg_left norm_joinFirst_le_one (norm_nonneg _)
    _ ≤ B := by simpa using hB ((split m j).symm p)

theorem marginalDerivativeIntegrand_eq_zero (K : Space (m + j) → ℂ) (R : ℝ)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox (m + j) R)
    (u : Space m) (v : Space j) (hv : v ∉ coordinateCube j R) :
    marginalDerivativeIntegrand K (u, v) = 0 := by
  have hts : tsupport K ⊆ MarginalEnergy.coordinateBox (m + j) R :=
    closure_minimal hs (GenericKernelRegularity.isCompact_coordinateBox (m + j) R).isClosed
  have hn : (split m j).symm (u, v) ∉ tsupport K := by
    intro hp
    apply hv
    intro i
    apply abs_le.mpr
    simpa only [split_symm_natAdd, mem_Icc] using hts hp (Fin.natAdd m i)
  simp [marginalDerivativeIntegrand, fderiv_of_notMem_tsupport ℝ hn]

theorem continuous_marginalDerivative (K : Space (m + j) → ℂ)
    (hK : ContDiff ℝ 1 K) (R : ℝ)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox (m + j) R) :
    Continuous (marginalDerivative K) := by
  exact continuousOn_univ.mp
    (continuousOn_integral_of_compact_support
      (f := fun u v => marginalDerivativeIntegrand K (u, v)) (s := univ)
      (isCompact_coordinateCube j R)
      (continuous_marginalDerivativeIntegrand K hK).continuousOn
      (fun u v _ hv => marginalDerivativeIntegrand_eq_zero K R hs u v hv))

theorem hasFDerivAt_marginalKernel_of_bound (K : Space (m + j) → ℂ)
    (hK : ContDiff ℝ 1 K) (R B : ℝ)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox (m + j) R)
    (hB : ∀ x, ‖fderiv ℝ K x‖ ≤ B) (u : Space m) :
    HasFDerivAt (marginalKernel K) (marginalDerivative K u) u := by
  let C := coordinateCube j R
  have hc : IsCompact C := isCompact_coordinateCube j R
  have hF : ∀ w : Space m, Continuous (fun v : Space j => K ((split m j).symm (w, v))) :=
    fun w => hK.continuous.comp ((continuous_split_symm m j).comp
      (continuous_const.prodMk continuous_id))
  have hD : ∀ w : Space m, Continuous
      (fun v : Space j => marginalDerivativeIntegrand K (w, v)) :=
    fun w => (continuous_marginalDerivativeIntegrand K hK).comp
      (continuous_const.prodMk continuous_id)
  have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := (volume : Measure (Space j)).restrict C)
    (F := fun w v => K ((split m j).symm (w, v)))
    (F' := fun w v => marginalDerivativeIntegrand K (w, v))
    (s := univ) (bound := fun _ => B) (x₀ := u) (by simp)
    (Eventually.of_forall fun w => (hF w).aestronglyMeasurable)
    ((hF u).continuousOn.integrableOn_compact hc)
    (hD u).aestronglyMeasurable
    (Eventually.of_forall fun v w _ => norm_marginalDerivativeIntegrand_le K B hB (w, v))
    (integrableOn_const hc.measure_ne_top)
    (Eventually.of_forall fun v w _ =>
      (hK.differentiable one_ne_zero ((split m j).symm (w, v))).hasFDerivAt.comp w
        (hasFDerivAt_join w v))
  have heF : (fun w : Space m => ∫ v in C, K ((split m j).symm (w, v))) =
      marginalKernel K := by
    funext w
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    by_contra hne
    exact hv (product_kernel_support K R hs hne).2
  have heD : (∫ v in C, marginalDerivativeIntegrand K (u, v)) = marginalDerivative K u := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    exact marginalDerivativeIntegrand_eq_zero K R hs u
  rw [heF, heD] at hd
  exact hd

theorem hasFDerivAt_marginalKernel (K : Space (m + j) → ℂ)
    (hK : ContDiff ℝ 1 K) (R : ℝ)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox (m + j) R) (u : Space m) :
    HasFDerivAt (marginalKernel K) (marginalDerivative K u) u := by
  obtain ⟨B, hB⟩ := ((hasCompactSupport_of_box K R hs).fderiv ℝ).exists_bound_of_continuous
    (hK.continuous_fderiv one_ne_zero)
  exact hasFDerivAt_marginalKernel_of_bound K hK R B hs hB u

theorem contDiff_marginalKernel (K : Space (m + j) → ℂ)
    (hK : ContDiff ℝ 1 K) (R : ℝ)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox (m + j) R) :
    ContDiff ℝ 1 (marginalKernel K) :=
  contDiff_one_iff_hasFDerivAt.mpr ⟨marginalDerivative K,
    continuous_marginalDerivative K hK R hs, hasFDerivAt_marginalKernel K hK R hs⟩

/-- The differentiated integral formula is an equality with the actual fderiv. -/
theorem fderiv_marginalKernel (K : Space (m + j) → ℂ)
    (hK : ContDiff ℝ 1 K) (R : ℝ)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox (m + j) R) (u : Space m) :
    fderiv ℝ (marginalKernel K) u =
      ∫ v, (fderiv ℝ K ((split m j).symm (u, v))).comp (joinFirst m j) :=
  (hasFDerivAt_marginalKernel K hK R hs u).fderiv

theorem norm_marginalKernel_le (K : Space (m + j) → ℂ) (hK : Continuous K)
    (R B : ℝ) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox (m + j) R)
    (hB : ∀ x, ‖K x‖ ≤ B) (u : Space m) :
    ‖marginalKernel K u‖ ≤ (volume : Measure (Space j)).real (coordinateCube j R) * B :=
  norm_marginal_le _ (continuous_product_kernel K hK) R B
    (fun _ hp => ⟨mem_univ _, (product_kernel_support K R hs hp).2⟩)
    (fun _ => hB _) u

theorem norm_fderiv_marginalKernel_le (K : Space (m + j) → ℂ)
    (hK : ContDiff ℝ 1 K) (R B : ℝ)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox (m + j) R)
    (hB : ∀ x, ‖fderiv ℝ K x‖ ≤ B) (u : Space m) :
    ‖fderiv ℝ (marginalKernel K) u‖ ≤
      (volume : Measure (Space j)).real (coordinateCube j R) * B := by
  rw [(hasFDerivAt_marginalKernel K hK R hs u).fderiv]
  have he : (∫ v in coordinateCube j R, marginalDerivativeIntegrand K (u, v)) =
      marginalDerivative K u := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    exact marginalDerivativeIntegrand_eq_zero K R hs u
  rw [← he]
  have hc := isCompact_coordinateCube j R
  have hcont : Continuous (fun v : Space j => marginalDerivativeIntegrand K (u, v)) :=
    (continuous_marginalDerivativeIntegrand K hK).comp (continuous_const.prodMk continuous_id)
  calc
    _ ≤ ∫ v in coordinateCube j R, ‖marginalDerivativeIntegrand K (u, v)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ _v in coordinateCube j R, B := integral_mono_ae
      (hcont.norm.continuousOn.integrableOn_compact hc)
      (integrableOn_const hc.measure_ne_top)
      (Eventually.of_forall fun v => norm_marginalDerivativeIntegrand_le K B hB (u, v))
    _ = _ := by
      simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]

end StrongSpherical.MarginalC1
