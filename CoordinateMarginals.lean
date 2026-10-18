import Definitions
import MarginalEnergy
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Coordinate marginals and the box test in §5.1

We use `Space m × Space j` with the explicit product of Euclidean Lebesgue
measures. Thus the following identities apply equally when either coordinate
block is empty. Identifying an arbitrary coordinate split of `Space (m+j)`
with this product is a separate measure-preserving coordinate change.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace StrongSpherical.CoordinateMarginals

variable {m j : ℕ}

/-- A closed coordinate cube, including the singleton cube in dimension zero. -/
def coordinateCube (n : ℕ) (R : ℝ) : Set (Space n) := {x | ∀ i, |x i| ≤ R}

theorem isCompact_coordinateCube (n : ℕ) (R : ℝ) :
    IsCompact (coordinateCube n R) := by
  have h : coordinateCube n R =
      (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)) ⁻¹'
        (Set.pi univ (fun _ : Fin n => Icc (-R) R)) := by
    ext x
    simp only [coordinateCube, mem_setOf_eq, mem_preimage, mem_pi, mem_univ,
      forall_true_left, mem_Icc, abs_le]
    rfl
  rw [h]
  exact (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isCompact_preimage.2
    (isCompact_univ_pi fun _ => isCompact_Icc)

theorem measurableSet_coordinateCube (n : ℕ) (R : ℝ) :
    MeasurableSet (coordinateCube n R) :=
  (isCompact_coordinateCube n R).isClosed.measurableSet

theorem coordinateCube_eq_coordinateBox (n : ℕ) (R : ℝ) :
    coordinateCube n R = MarginalEnergy.coordinateBox n R := by
  ext x
  simp only [coordinateCube, MarginalEnergy.coordinateBox, mem_setOf_eq, mem_Icc, abs_le]

/-- Integrating the second coordinate block defines the first marginal. -/
def marginal (K : Space m × Space j → ℂ) (u : Space m) : ℂ := ∫ v, K (u, v)

/-- The canonical zero-dimensional Lebesgue measure has total mass one. -/
theorem volume_space_zero : (volume : Measure (Space 0)) univ = 1 := by
  calc
    _ = (volume : Measure (Fin 0 → ℝ)) univ := by
      simpa only [preimage_univ] using
        (PiLp.volume_preserving_ofLp (Fin 0)).measure_preimage
          (MeasurableSet.univ.nullMeasurableSet)
    _ = 1 := Measure.pi_empty_univ _

/-- Integrating an empty coordinate block performs no averaging or renormalization. -/
theorem marginal_empty_integrated (K : Space m × Space 0 → ℂ) (u : Space m) :
    marginal K u = K (u, 0) := by
  have he : (fun v : Space 0 => K (u, v)) = fun _ => K (u, 0) := by
    funext v
    rw [show v = 0 from Subsingleton.elim _ _]
  rw [marginal, he, integral_const, measureReal_def, volume_space_zero,
    ENNReal.toReal_one, one_smul]

/-- When the retained block is empty, the marginal is the total kernel mass. -/
theorem marginal_empty_retained (K : Space 0 × Space j → ℂ) (u : Space 0) :
    marginal K u = ∫ v, K (0, v) := by
  rw [show u = 0 from Subsingleton.elim _ _]
  rfl

theorem continuous_marginal (K : Space m × Space j → ℂ)
    (hK : Continuous K) (hc : HasCompactSupport K) : Continuous (marginal K) := by
  have hp : IsCompact (Prod.snd '' tsupport K) := hc.image continuous_snd
  have hs : ∀ u v, u ∈ (univ : Set (Space m)) →
      v ∉ Prod.snd '' tsupport K → K (u, v) = 0 := by
    intro u v _ hv
    by_contra hne
    exact hv ⟨(u, v), subset_tsupport K hne, rfl⟩
  exact continuousOn_univ.mp
    (continuousOn_integral_of_compact_support hp hK.continuousOn hs)

theorem support_marginal_subset_projection (K : Space m × Space j → ℂ) :
    Function.support (marginal K) ⊆ Prod.fst '' tsupport K := by
  intro u hu
  by_contra hout
  apply hu
  apply integral_eq_zero_of_ae
  filter_upwards with v
  by_contra hne
  exact hout ⟨(u, v), subset_tsupport K hne, rfl⟩

theorem hasCompactSupport_marginal (K : Space m × Space j → ℂ)
    (hc : HasCompactSupport K) : HasCompactSupport (marginal K) := by
  have hp : IsCompact (Prod.fst '' tsupport K) := hc.image continuous_fst
  exact hp.of_isClosed_subset (isClosed_tsupport _) 
    (closure_minimal (support_marginal_subset_projection K) hp.isClosed)

theorem integrable_marginal (K : Space m × Space j → ℂ)
    (hK : Continuous K) (hc : HasCompactSupport K) : Integrable (marginal K) :=
  (continuous_marginal K hK hc).integrable_of_hasCompactSupport
    (hasCompactSupport_marginal K hc)

theorem integral_marginal (K : Space m × Space j → ℂ)
    (hK : Continuous K) (hc : HasCompactSupport K) :
    (∫ u, marginal K u) =
      ∫ p, K p ∂((volume : Measure (Space m)).prod volume) :=
  (integral_prod _ (hK.integrable_of_hasCompactSupport hc)).symm

theorem support_marginal_subset_cube (K : Space m × Space j → ℂ) (R : ℝ)
    (hs : Function.support K ⊆ coordinateCube m R ×ˢ coordinateCube j R) :
    Function.support (marginal K) ⊆ coordinateCube m R := by
  intro u hu
  by_contra hout
  apply hu
  apply integral_eq_zero_of_ae
  filter_upwards with v
  by_contra hne
  exact hout (hs hne).1

theorem tsupport_marginal_subset_cube (K : Space m × Space j → ℂ) (R : ℝ)
    (hs : Function.support K ⊆ coordinateCube m R ×ˢ coordinateCube j R) :
    tsupport (marginal K) ⊆ coordinateCube m R :=
  closure_minimal (support_marginal_subset_cube K R hs)
    (isCompact_coordinateCube m R).isClosed

/-- The marginal sup-norm loses only the volume of the integrated coordinate cube. -/
theorem norm_marginal_le (K : Space m × Space j → ℂ) (hK : Continuous K)
    (R B : ℝ) (hs : Function.support K ⊆ univ ×ˢ coordinateCube j R)
    (hb : ∀ p, ‖K p‖ ≤ B) (u : Space m) :
    ‖marginal K u‖ ≤ (volume : Measure (Space j)).real (coordinateCube j R) * B := by
  have hc := isCompact_coordinateCube j R
  have hcont : Continuous (fun v : Space j => K (u, v)) :=
    hK.comp (continuous_const.prodMk continuous_id)
  have he : (∫ v in coordinateCube j R, K (u, v)) = marginal K u := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro v hv
    by_contra hne
    exact hv (hs hne).2
  rw [← he]
  calc
    _ ≤ ∫ v in coordinateCube j R, ‖K (u, v)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ _v in coordinateCube j R, B := integral_mono_ae
      (hcont.norm.continuousOn.integrableOn_compact hc)
      (integrableOn_const hc.measure_ne_top)
      (Filter.Eventually.of_forall fun v => hb (u, v))
    _ = _ := by
      simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul]

/-- Convolution on the coordinate product, with its product Lebesgue measure. -/
def productConvolution (K f : Space m × Space j → ℂ)
    (p : Space m × Space j) : ℂ :=
  ∫ q, K q * f (p - q) ∂((volume : Measure (Space m)).prod volume)

/-- The test input `g(u) 1_{[-L,L]^j}(v)` used in the marginal argument. -/
def boxLift (L : ℝ) (g : Space m → ℂ) (p : Space m × Space j) : ℂ :=
  g p.1 * (coordinateCube j L).indicator (fun _ => (1 : ℂ)) p.2

theorem boxLift_eq_cutoffInput (L : ℝ) (g : Space m → ℂ) :
    boxLift (j := j) L g = MarginalEnergy.cutoffInput L g := by
  unfold boxLift MarginalEnergy.cutoffInput
  rw [coordinateCube_eq_coordinateBox]

theorem measurable_boxLift (L : ℝ) (g : Space m → ℂ) (hg : Measurable g) :
    Measurable (boxLift (j := j) L g) :=
  (hg.comp measurable_fst).mul
    ((measurable_const.indicator (measurableSet_coordinateCube j L)).comp measurable_snd)

theorem box_sub_mem (R L : ℝ) (v z : Space j)
    (hv : v ∈ coordinateCube j R) (hz : z ∈ coordinateCube j (L - R)) :
    z - v ∈ coordinateCube j L := by
  intro i
  calc
    |(z - v) i| = |z i - v i| := rfl
    _ ≤ |z i| + |v i| := abs_sub _ _
    _ ≤ (L - R) + R := add_le_add (hz i) (hv i)
    _ = L := sub_add_cancel L R

/-- On the smaller output cube the cutoff disappears throughout kernel support. -/
theorem kernel_mul_boxLift (K : Space m × Space j → ℂ) (R L : ℝ)
    (hs : Function.support K ⊆ univ ×ˢ coordinateCube j R)
    (g : Space m → ℂ) (x : Space m) (z : Space j)
    (hz : z ∈ coordinateCube j (L - R)) (q : Space m × Space j) :
    K q * boxLift L g ((x, z) - q) = K q * g (x - q.1) := by
  by_cases hq : K q = 0
  · simp [hq]
  · have hmem := box_sub_mem R L q.2 z (hs hq).2 hz
    simp [boxLift, hmem]

/-- Exact Fubini reduction; the assumed integrability concerns the actual
untruncated product integrand, rather than the desired conclusion. -/
theorem productConvolution_boxLift_eq (K : Space m × Space j → ℂ) (R L : ℝ)
    (hs : Function.support K ⊆ univ ×ˢ coordinateCube j R)
    (g : Space m → ℂ) (x : Space m) (z : Space j)
    (hz : z ∈ coordinateCube j (L - R))
    (hi : Integrable (fun q : Space m × Space j => K q * g (x - q.1))
      ((volume : Measure (Space m)).prod volume)) :
    productConvolution K (boxLift L g) (x, z) =
      kernelConvolution (marginal K) g x := by
  rw [productConvolution, kernelConvolution_eq_integral]
  simp_rw [kernel_mul_boxLift K R L hs g x z hz]
  rw [integral_prod _ hi]
  congr 1
  funext u
  exact integral_mul_const (g (x - u)) (fun v => K (u, v))

theorem integrable_product_kernel_mul (K : Space m × Space j → ℂ)
    (hK : Continuous K) (hc : HasCompactSupport K)
    (g : Space m → ℂ) (hg : Continuous g) (x : Space m) :
    Integrable (fun q : Space m × Space j => K q * g (x - q.1))
      ((volume : Measure (Space m)).prod volume) := by
  have hcont : Continuous (fun q : Space m × Space j => K q * g (x - q.1)) :=
    hK.mul (hg.comp (continuous_const.sub continuous_fst))
  exact hcont.integrable_of_hasCompactSupport hc.mul_right

/-- A genuine L² test input also gives an integrable product integrand.
The finite cutoff supplies L² integrability in the otherwise unbounded
second block; on kernel support it is identically one. -/
theorem integrable_product_kernel_mul_L2 (K : Space m × Space j → ℂ)
    (hK : Continuous K) (hc : HasCompactSupport K) (R : ℝ)
    (hs : Function.support K ⊆ univ ×ˢ coordinateCube j R)
    (g : Space m → ℂ) (hg : Measurable g) (hLp : MemLp g 2 volume) (x : Space m) :
    Integrable (fun q : Space m × Space j => K q * g (x - q.1))
      ((volume : Measure (Space m)).prod volume) := by
  have hKLp : MemLp K 2 ((volume : Measure (Space m)).prod volume) :=
    hK.memLp_of_hasCompactSupport hc
  have hb : MemLp (boxLift (j := j) R g) 2
      ((volume : Measure (Space m)).prod volume) := by
    rw [boxLift_eq_cutoffInput]
    exact MarginalEnergy.memLp_cutoffInput R g hg hLp
  have hmp : MeasurePreserving
      (fun q : Space m × Space j => (x, (0 : Space j)) - q)
      ((volume : Measure (Space m)).prod volume)
      ((volume : Measure (Space m)).prod volume) := by
    exact (Measure.measurePreserving_sub_left (volume : Measure (Space m)) x).prod
      (Measure.measurePreserving_sub_left (volume : Measure (Space j)) 0)
  have hi := hKLp.integrable_mul (hb.comp_measurePreserving hmp)
  have hz : (0 : Space j) ∈ coordinateCube j (R - R) := by
    intro i
    simp
  convert hi using 1
  funext q
  exact (kernel_mul_boxLift K R R hs g x 0 hz q).symm

theorem productConvolution_boxLift_eq_L2 (K : Space m × Space j → ℂ)
    (hK : Continuous K) (hc : HasCompactSupport K) (R L : ℝ)
    (hs : Function.support K ⊆ univ ×ˢ coordinateCube j R)
    (g : Space m → ℂ) (hg : Measurable g) (hLp : MemLp g 2 volume)
    (x : Space m) (z : Space j) (hz : z ∈ coordinateCube j (L - R)) :
    productConvolution K (boxLift L g) (x, z) =
      kernelConvolution (marginal K) g x :=
  productConvolution_boxLift_eq K R L hs g x z hz
    (integrable_product_kernel_mul_L2 K hK hc R hs g hg hLp x)

/-- The concrete compact-kernel identity needs no additional Fubini hypothesis. -/
theorem productConvolution_boxLift_eq_of_continuous (K : Space m × Space j → ℂ)
    (hK : Continuous K) (hc : HasCompactSupport K) (R L : ℝ)
    (hs : Function.support K ⊆ univ ×ˢ coordinateCube j R)
    (g : Space m → ℂ) (hg : Continuous g) (x : Space m) (z : Space j)
    (hz : z ∈ coordinateCube j (L - R)) :
    productConvolution K (boxLift L g) (x, z) =
      kernelConvolution (marginal K) g x :=
  productConvolution_boxLift_eq K R L hs g x z hz
    (integrable_product_kernel_mul K hK hc g hg x)

/-- Dilation only in the retained coordinates; the other radii are one. -/
def partialDilatedKernel (K : Space m × Space j → ℂ) (r : Radii m)
    (p : Space m × Space j) : ℂ :=
  (dilationJacobian r : ℂ)⁻¹ * K (inverseDilation r p.1, p.2)

theorem marginal_partialDilatedKernel (K : Space m × Space j → ℂ) (r : Radii m) :
    marginal (partialDilatedKernel K r) = dilatedKernel (marginal K) r := by
  funext u
  exact integral_const_mul (dilationJacobian r : ℂ)⁻¹
    (fun v => K (inverseDilation r u, v))

/-- The inverse dilation is a homeomorphism, also for the empty tuple of radii. -/
def inverseDilationHomeomorph (r : Radii m) : Space m ≃ₜ Space m where
  toFun := inverseDilation r
  invFun := diagonalDilation r.1
  left_inv := diagonalDilation_inverseDilation r
  right_inv := inverseDilation_diagonalDilation r
  continuous_toFun := continuous_diagonalDilation _
  continuous_invFun := continuous_diagonalDilation _

theorem continuous_partialDilatedKernel (K : Space m × Space j → ℂ)
    (hK : Continuous K) (r : Radii m) : Continuous (partialDilatedKernel K r) := by
  exact continuous_const.mul (hK.comp
    (((inverseDilationHomeomorph r).continuous.comp continuous_fst).prodMk continuous_snd))

theorem hasCompactSupport_partialDilatedKernel (K : Space m × Space j → ℂ)
    (hc : HasCompactSupport K) (r : Radii m) :
    HasCompactSupport (partialDilatedKernel K r) := by
  exact (hc.comp_homeomorph
    ((inverseDilationHomeomorph r).prodCongr (Homeomorph.refl (Space j)))).mul_left

theorem support_partialDilatedKernel_second (K : Space m × Space j → ℂ) (R : ℝ)
    (hs : Function.support K ⊆ univ ×ˢ coordinateCube j R) (r : Radii m) :
    Function.support (partialDilatedKernel K r) ⊆ univ ×ˢ coordinateCube j R := by
  intro p hp
  have hne : K (inverseDilation r p.1, p.2) ≠ 0 := by
    intro he
    exact hp (by simp [partialDilatedKernel, he])
  exact ⟨mem_univ _, (hs hne).2⟩

/-- Equation (5.3)'s pointwise convolution reduction, with arbitrary positive
retained radii, a genuine compact kernel, and a continuous test function. -/
theorem partialDilatedConvolution_boxLift_eq (K : Space m × Space j → ℂ)
    (hK : Continuous K) (hc : HasCompactSupport K) (R L : ℝ)
    (hs : Function.support K ⊆ univ ×ˢ coordinateCube j R)
    (r : Radii m) (g : Space m → ℂ) (hg : Continuous g)
    (x : Space m) (z : Space j) (hz : z ∈ coordinateCube j (L - R)) :
    productConvolution (partialDilatedKernel K r) (boxLift L g) (x, z) =
      kernelConvolution (dilatedKernel (marginal K) r) g x := by
  rw [productConvolution_boxLift_eq_of_continuous _
    (continuous_partialDilatedKernel K hK r) (hasCompactSupport_partialDilatedKernel K hc r)
    R L (support_partialDilatedKernel_second K R hs r) g hg x z hz]
  rw [marginal_partialDilatedKernel]

theorem partialDilatedConvolution_boxLift_eq_L2 (K : Space m × Space j → ℂ)
    (hK : Continuous K) (hc : HasCompactSupport K) (R L : ℝ)
    (hs : Function.support K ⊆ univ ×ˢ coordinateCube j R)
    (r : Radii m) (g : Space m → ℂ) (hg : Measurable g) (hLp : MemLp g 2 volume)
    (x : Space m) (z : Space j) (hz : z ∈ coordinateCube j (L - R)) :
    productConvolution (partialDilatedKernel K r) (boxLift L g) (x, z) =
      kernelConvolution (dilatedKernel (marginal K) r) g x := by
  rw [productConvolution_boxLift_eq_L2 _
    (continuous_partialDilatedKernel K hK r) (hasCompactSupport_partialDilatedKernel K hc r)
    R L (support_partialDilatedKernel_second K R hs r) g hg hLp x z hz]
  rw [marginal_partialDilatedKernel]

/-- Local maximal function with only the retained coordinate radii varying. -/
def partialLocalMaximal (K f : Space m × Space j → ℂ)
    (p : Space m × Space j) : ℝ≥0∞ :=
  ⨆ r ∈ localRadii m, ‖productConvolution (partialDilatedKernel K r) f p‖ₑ

/-- The pointwise identity holds for the whole uncountable local supremum. -/
theorem partialLocalMaximal_boxLift_eq (K : Space m × Space j → ℂ)
    (hK : Continuous K) (hc : HasCompactSupport K) (R L : ℝ)
    (hs : Function.support K ⊆ univ ×ˢ coordinateCube j R)
    (g : Space m → ℂ) (hg : Continuous g)
    (x : Space m) (z : Space j) (hz : z ∈ coordinateCube j (L - R)) :
    partialLocalMaximal K (boxLift L g) (x, z) = localKernelMaximal (marginal K) g x := by
  unfold partialLocalMaximal localKernelMaximal maximalOver
  simp_rw [partialDilatedConvolution_boxLift_eq K hK hc R L hs _ g hg x z hz]

theorem partialLocalMaximal_boxLift_eq_L2 (K : Space m × Space j → ℂ)
    (hK : Continuous K) (hc : HasCompactSupport K) (R L : ℝ)
    (hs : Function.support K ⊆ univ ×ˢ coordinateCube j R)
    (g : Space m → ℂ) (hg : Measurable g) (hLp : MemLp g 2 volume)
    (x : Space m) (z : Space j) (hz : z ∈ coordinateCube j (L - R)) :
    partialLocalMaximal K (boxLift L g) (x, z) = localKernelMaximal (marginal K) g x := by
  unfold partialLocalMaximal localKernelMaximal maximalOver
  simp_rw [partialDilatedConvolution_boxLift_eq_L2 K hK hc R L hs _ g hg hLp x z hz]

end StrongSpherical.CoordinateMarginals
