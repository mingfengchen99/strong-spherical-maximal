import CoordinateSubsets
import DilationL2

/-! # Lifting a lower-dimensional maximal estimate to coordinate fibers -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology
namespace StrongSpherical.MarginalFiberL2
open NormalKernelRegularity ProductCoordinates
variable {m j : ℕ}

def fiberInput (f : Space m × Space j → ℂ) (z : Space j) (u : Space m) : ℂ := f (u, z)

def fiberLocalMaximal (K : Space m → ℂ) (f : Space m × Space j → ℂ)
    (p : Space m × Space j) : ℝ≥0∞ := localKernelMaximal K (fiberInput f p.2) p.1

def fiberStrongMaximal (K : Space m → ℂ) (f : Space m × Space j → ℂ)
    (p : Space m × Space j) : ℝ≥0∞ := strongKernelMaximal K (fiberInput f p.2) p.1

theorem continuous_parameter_fiber_convolution (K : Space m → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox m R)
    (f : Space m × Space j → ℂ) (hf : Continuous f) :
    Continuous (fun q : LocalParameters m × (Space m × Space j) =>
      kernelConvolution (dilatedKernel K (parameterRadii q.1)) (fiberInput f q.2.2) q.2.1) := by
  let F : (LocalParameters m × (Space m × Space j)) → Space m → ℂ := fun q u =>
    dilatedKernel K (parameterRadii q.1) u * f (q.2.1 - u, q.2.2)
  have hmapK : Continuous (fun q : (LocalParameters m × (Space m × Space j)) × Space m =>
      (q.1.1, q.2)) := by fun_prop
  have hmapF : Continuous (fun q : (LocalParameters m × (Space m × Space j)) × Space m =>
      (q.1.2.1 - q.2, q.1.2.2)) := by fun_prop
  have hF : Continuous F.uncurry :=
    ((GenericKernelRegularity.continuous_parameter_kernel K hK).comp hmapK).mul (hf.comp hmapF)
  have hc := GenericKernelRegularity.isCompact_coordinateBox m (2 * R)
  have hz : ∀ q u, q ∈ (univ : Set (LocalParameters m × (Space m × Space j))) →
      u ∉ MarginalEnergy.coordinateBox m (2 * R) → F q u = 0 := by
    intro q u _ hu
    have hzero : dilatedKernel K (parameterRadii q.1) u = 0 := by
      by_contra hn
      exact hu (GenericKernelRegularity.parameter_kernel_support K R hR hs q.1 hn)
    simp only [F, hzero, zero_mul]
  exact continuousOn_univ.mp
    (continuousOn_integral_of_compact_support (f := F) (s := univ) hc hF.continuousOn hz)

theorem measurable_fiberLocalMaximal (K : Space m → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox m R)
    (f : Space m × Space j → ℂ) (hf : Continuous f) : Measurable (fiberLocalMaximal K f) := by
  let A : LocalParameters m → (Space m × Space j) → ℂ := fun t p =>
    kernelConvolution (dilatedKernel K (parameterRadii t)) (fiberInput f p.2) p.1
  have hj := continuous_parameter_fiber_convolution K hK R hR hs f hf
  have hm : ∀ t, Measurable (A t) := by
    intro t
    have hmap : Continuous (fun p : Space m × Space j => (t, p)) :=
      continuous_const.prodMk continuous_id
    simpa only [Function.comp_def, A] using (hj.comp hmap).measurable
  have ht : ∀ p, Continuous (fun t => A t p) := by
    intro p
    have hmap : Continuous (fun t : LocalParameters m => (t, p)) :=
      continuous_id.prodMk continuous_const
    simpa only [Function.comp_def, A] using hj.comp hmap
  obtain ⟨_, _, _, hmeas, _⟩ := MaximalLinearization.exists_dense_maximal_representation A hm ht
  have he : fiberLocalMaximal K f = fun p => ⨆ t, ‖A t p‖ₑ := by
    funext p
    exact GenericKernelRegularity.localKernelMaximal_eq_parameter_iSup K (fiberInput f p.2) p.1
  rwa [he]

theorem measurable_fiberStrongMaximal (K : Space m → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox m R)
    (f : Space m × Space j → ℂ) (hf : Continuous f) : Measurable (fiberStrongMaximal K f) := by
  let F : (Fin m → ℤ) → (Space m × Space j) → ℂ := fun k p =>
    f (diagonalDilation (DyadicRadii.scales k).1 p.1, p.2)
  let T : (Fin m → ℤ) → (Space m × Space j) → (Space m × Space j) := fun k p =>
    (inverseDilation (DyadicRadii.scales k) p.1, p.2)
  have hF : ∀ k, Continuous (F k) := by
    intro k
    exact hf.comp (((continuous_diagonalDilation _).comp continuous_fst).prodMk continuous_snd)
  have hT : ∀ k, Continuous (T k) := by
    intro k
    exact ((continuous_diagonalDilation _).comp continuous_fst).prodMk continuous_snd
  have hm : Measurable (fun p => ⨆ k, fiberLocalMaximal K (F k) (T k p)) :=
    Measurable.iSup fun k =>
      (measurable_fiberLocalMaximal K hK R hR hs (F k) (hF k)).comp (hT k).measurable
  have he : fiberStrongMaximal K f = fun p => ⨆ k, fiberLocalMaximal K (F k) (T k p) := by
    funext p
    rw [fiberStrongMaximal, DyadicRadii.strongKernelMaximal_eq_dyadic]
    apply iSup_congr
    intro k
    exact DilationL2.rectangleMaximal_eq_local K (fiberInput f p.2) (DyadicRadii.scales k) p.1
  rwa [he]

theorem memLp_fiber_ae (f : Space m × Space j → ℂ) (hf : Continuous f)
    (hLp : MemLp f 2 ((volume : Measure (Space m)).prod (volume : Measure (Space j)))) :
    ∀ᵐ z : Space j, MemLp (fiberInput f z) 2 volume := by
  have hmeas : Measurable (fun p : Space m × Space j => ‖f p‖ₑ ^ 2) := hf.measurable.enorm.pow_const 2
  have hi : (∫⁻ z : Space j, ∫⁻ u : Space m, ‖f (u, z)‖ₑ ^ 2) < ∞ := by
    rw [← lintegral_prod_symm _ hmeas.aemeasurable, ← DilationL2.eLpNorm_two_sq]
    exact ENNReal.pow_lt_top hLp.eLpNorm_lt_top
  have hinner : Measurable (fun z : Space j => ∫⁻ u : Space m, ‖f (u, z)‖ₑ ^ 2) :=
    hmeas.lintegral_prod_left
  filter_upwards [ae_lt_top hinner hi.ne] with z hz
  refine ⟨((hf.comp (continuous_id.prodMk continuous_const)).measurable).aestronglyMeasurable, ?_⟩
  have hp : eLpNorm (fiberInput f z) 2 volume ^ 2 < ∞ := by
    rw [DilationL2.eLpNorm_two_sq]
    exact hz
  simpa only [ENNReal.pow_lt_top_iff, OfNat.ofNat_ne_zero, or_false] using hp

/-- The original lower-dimensional strong maximal estimate lifts to all
coordinate fibers with exactly the same constant. -/
theorem fiberStrongMaximal_L2 (K : Space m → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox m R)
    (D : ℝ≥0∞)
    (hIH : ∀ g : Space m → ℂ, MemLp g 2 volume →
      eLpNorm (strongKernelMaximal K g) 2 volume ≤ D * eLpNorm g 2 volume)
    (f : Space m × Space j → ℂ) (hf : Continuous f)
    (hLp : MemLp f 2 ((volume : Measure (Space m)).prod volume)) :
    Measurable (fiberStrongMaximal K f) ∧
      eLpNorm (fiberStrongMaximal K f) 2 ((volume : Measure (Space m)).prod volume) ≤
        D * eLpNorm f 2 ((volume : Measure (Space m)).prod volume) := by
  have hm := measurable_fiberStrongMaximal K hK R hR hs f hf
  refine ⟨hm, ?_⟩
  apply (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [mul_pow, MarginalLocalEstimate.eLpNorm_two_sq_ennreal,
    DilationL2.eLpNorm_two_sq]
  rw [lintegral_prod_symm _ (hm.pow_const 2).aemeasurable]
  have hmeas : Measurable (fun p : Space m × Space j => ‖f p‖ₑ ^ 2) := hf.measurable.enorm.pow_const 2
  rw [lintegral_prod_symm _ hmeas.aemeasurable, ← lintegral_const_mul _ hmeas.lintegral_prod_left]
  apply lintegral_mono_ae
  filter_upwards [memLp_fiber_ae f hf hLp] with z hz
  have h := pow_le_pow_left' (hIH (fiberInput f z) hz) 2
  simpa only [mul_pow, MarginalLocalEstimate.eLpNorm_two_sq_ennreal,
    DilationL2.eLpNorm_two_sq, enorm_eq_self, fiberStrongMaximal, fiberInput] using h

def coordinateFiberMaximal (K : Space m → ℂ) (f : Space (m + j) → ℂ)
    (x : Space (m + j)) : ℝ≥0∞ :=
  fiberStrongMaximal K (f ∘ (split m j).symm) (split m j x)

/-- Fiber lifting in the original Euclidean coordinates and canonical volume. -/
theorem coordinateFiberMaximal_L2 (K : Space m → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox m R)
    (D : ℝ≥0∞)
    (hIH : ∀ g : Space m → ℂ, MemLp g 2 volume →
      eLpNorm (strongKernelMaximal K g) 2 volume ≤ D * eLpNorm g 2 volume)
    (f : Space (m + j) → ℂ) (hf : Continuous f) (hLp : MemLp f 2 volume) :
    Measurable (coordinateFiberMaximal K f) ∧
      eLpNorm (coordinateFiberMaximal K f) 2 volume ≤ D * eLpNorm f 2 volume := by
  have hF : Continuous (f ∘ (split m j).symm) := hf.comp (continuous_split_symm m j)
  have hFLp := hLp.comp_measurePreserving (measurePreserving_split m j).symm
  obtain ⟨hM, hbound⟩ := fiberStrongMaximal_L2 K hK R hR hs D hIH
    (f ∘ (split m j).symm) hF hFLp
  refine ⟨hM.comp (split m j).measurable, ?_⟩
  change eLpNorm (fiberStrongMaximal K (f ∘ (split m j).symm) ∘ split m j) 2 volume ≤ _
  rw [eLpNorm_comp_measurePreserving hM.aestronglyMeasurable (measurePreserving_split m j)]
  rw [eLpNorm_comp_split_symm f 2 hLp.aestronglyMeasurable] at hbound
  exact hbound

end StrongSpherical.MarginalFiberL2
