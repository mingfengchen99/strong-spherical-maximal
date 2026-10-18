import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Tactic.FunProp

/-!
# Definitions for the strong spherical maximal operator

This is the definitions milestone for Mingfeng Chen,
*Sharp L^p estimates for the strong spherical maximal operator*,
arXiv:2609.32421v2 (5 October 2026).

The ambient space is genuinely Euclidean, rather than the sup-norm function
space `Fin n → ℝ`. Spherical measure is obtained from Lebesgue measure using
`Measure.toSphere`, normalized to mass one, and pushed forward by diagonal
dilations. Maximal functions take values in `ℝ≥0∞`, so an unbounded supremum
is not silently replaced by a real-valued conditional supremum.

`MainTheorem` at the end is a proposition recording the precise target of the
project. This file does not assert or assume that proposition as a theorem.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators FourierTransform CompactlySupported

namespace StrongSpherical

/-- The Euclidean space `ℝⁿ`, with its canonical Lebesgue measure. -/
abbrev Space (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The unit sphere, as a measurable subtype of Euclidean space. -/
abbrev UnitSphere (n : ℕ) := Metric.sphere (0 : Space n) 1

/-- Coordinatewise strictly positive radii. The empty tuple is allowed in dimension zero. -/
abbrev Radii (n : ℕ) := {r : Fin n → ℝ // ∀ i, 0 < r i}

variable {n : ℕ}

/-- The radius tuple `(1, …, 1)`. -/
def unitRadii (n : ℕ) : Radii n := ⟨fun _ => 1, fun _ => zero_lt_one⟩

/-- The local range of radii in (1.4). -/
def localRadii (n : ℕ) : Set (Radii n) := {r | ∀ i, r.1 i ∈ Icc (1 : ℝ) 2}

@[simp] theorem unitRadii_mem_localRadii : unitRadii n ∈ localRadii n := by
  simp [unitRadii, localRadii]

/-- The diagonal map `δᵣ u = (rᵢ uᵢ)ᵢ`. This map is defined for all real tuples. -/
def diagonalDilation (r : Fin n → ℝ) (u : Space n) : Space n :=
  WithLp.toLp 2 (fun i => r i * u i)

@[simp] theorem diagonalDilation_apply (r : Fin n → ℝ) (u : Space n) (i : Fin n) :
    diagonalDilation r u i = r i * u i := rfl

theorem continuous_diagonalDilation (r : Fin n → ℝ) : Continuous (diagonalDilation r) := by
  unfold diagonalDilation
  fun_prop

@[simp] theorem diagonalDilation_one (u : Space n) :
    diagonalDilation (fun _ => 1) u = u := by
  ext i
  simp

/-- The inverse diagonal map, with positivity carried by `r`. -/
def inverseDilation (r : Radii n) : Space n → Space n :=
  diagonalDilation (fun i => (r.1 i)⁻¹)

@[simp] theorem inverseDilation_diagonalDilation (r : Radii n) (u : Space n) :
    inverseDilation r (diagonalDilation r.1 u) = u := by
  ext i
  simp [inverseDilation, ne_of_gt (r.2 i)]

@[simp] theorem diagonalDilation_inverseDilation (r : Radii n) (u : Space n) :
    diagonalDilation r.1 (inverseDilation r u) = u := by
  ext i
  simp [inverseDilation, ne_of_gt (r.2 i)]

/-- The Jacobian factor `∏ᵢ rᵢ`. -/
def dilationJacobian (r : Radii n) : ℝ := ∏ i, r.1 i

theorem dilationJacobian_pos (r : Radii n) : 0 < dilationJacobian r :=
  Finset.prod_pos fun i _ => r.2 i

/-- The defining function `Fₓ,ᵣ` from (1.3). -/
def ellipsoidForm (x : Space n) (r : Radii n) (y : Space n) : ℝ :=
  (∑ i, (y i - x i) ^ 2 / (r.1 i) ^ 2) - 1

/-- The ellipsoid `E(x; r)` from (1.3). -/
def ellipsoid (x : Space n) (r : Radii n) : Set (Space n) :=
  {y | ellipsoidForm x r y = 0}

theorem norm_sq_eq_sum_coordinates (u : Space n) : ‖u‖ ^ 2 = ∑ i, (u i) ^ 2 :=
  EuclideanSpace.real_norm_sq_eq u

theorem ellipsoidForm_eq_norm_sq (x y : Space n) (r : Radii n) :
    ellipsoidForm x r y = ‖inverseDilation r (y - x)‖ ^ 2 - 1 := by
  simp [ellipsoidForm, inverseDilation, norm_sq_eq_sum_coordinates,
    mul_pow, div_eq_mul_inv, mul_comm]

theorem continuous_ellipsoidForm (x : Space n) (r : Radii n) :
    Continuous (ellipsoidForm x r) := by
  unfold ellipsoidForm
  fun_prop

theorem measurableSet_ellipsoid (x : Space n) (r : Radii n) :
    MeasurableSet (ellipsoid x r) :=
  (isClosed_eq (continuous_ellipsoidForm x r) continuous_const).measurableSet

theorem diagonalDilation_mem_ellipsoid (x : Space n) (r : Radii n)
    (ω : UnitSphere n) : x + diagonalDilation r.1 ω ∈ ellipsoid x r := by
  have hnorm : ‖(ω : Space n)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using ω.2
  change ellipsoidForm x r (x + diagonalDilation r.1 ω) = 0
  simp [ellipsoidForm_eq_norm_sq, hnorm]

/-- Unnormalized Euclidean surface measure on the sphere, supplied by mathlib. -/
def surfaceMeasure (n : ℕ) : Measure (UnitSphere n) :=
  (volume : Measure (Space n)).toSphere

instance surfaceMeasure_isFiniteMeasure (n : ℕ) : IsFiniteMeasure (surfaceMeasure n) := by
  unfold surfaceMeasure
  infer_instance

theorem surfaceMeasure_ne_zero (n : ℕ) [NeZero n] : surfaceMeasure n ≠ 0 := by
  exact Measure.toSphere_ne_zero (volume : Measure (Space n))

/-- Normalized surface measure on the sphere. It has mass one for `n > 0`.
In dimension zero the sphere is empty and this measure is zero. -/
def sphereMeasure (n : ℕ) : Measure (UnitSphere n) :=
  (surfaceMeasure n univ)⁻¹ • surfaceMeasure n

instance sphereMeasure_isProbabilityMeasure (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (sphereMeasure n) := by
  letI : NeZero (surfaceMeasure n) := ⟨surfaceMeasure_ne_zero n⟩
  unfold sphereMeasure
  infer_instance

/-- The same normalized spherical measure, viewed on the ambient Euclidean space. -/
def sphericalMeasure (n : ℕ) : Measure (Space n) :=
  (sphereMeasure n).map (fun ω : UnitSphere n => (ω : Space n))

instance sphericalMeasure_isProbabilityMeasure (n : ℕ) [NeZero n] :
    IsProbabilityMeasure (sphericalMeasure n) := by
  exact Measure.isProbabilityMeasure_map measurable_subtype_coe.aemeasurable

/-- The measure `σᵣ = (δᵣ)₊ σ` from (1.1).
This is the pushforward of normalized spherical measure used in the paper. -/
def ellipsoidMeasure (r : Radii n) : Measure (Space n) :=
  (sphericalMeasure n).map (diagonalDilation r.1)

instance ellipsoidMeasure_isProbabilityMeasure [NeZero n] (r : Radii n) :
    IsProbabilityMeasure (ellipsoidMeasure r) := by
  exact Measure.isProbabilityMeasure_map
    (continuous_diagonalDilation r.1).measurable.aemeasurable

theorem ellipsoidMeasure_eq_map_sphere (r : Radii n) :
    ellipsoidMeasure r = (sphereMeasure n).map
      (fun ω : UnitSphere n => diagonalDilation r.1 ω) := by
  rw [ellipsoidMeasure, sphericalMeasure,
    Measure.map_map (continuous_diagonalDilation r.1).measurable measurable_subtype_coe]
  rfl

/-- The pushed-forward measure is concentrated on `E(0; r)`. -/
theorem ellipsoidMeasure_compl_ellipsoid (r : Radii n) :
    ellipsoidMeasure r (ellipsoid 0 r)ᶜ = 0 := by
  have hmap : Measurable (fun ω : UnitSphere n => diagonalDilation r.1 ω) :=
    ((continuous_diagonalDilation r.1).comp continuous_subtype_val).measurable
  rw [ellipsoidMeasure_eq_map_sphere,
    Measure.map_apply hmap (measurableSet_ellipsoid 0 r).compl]
  have hempty : (fun ω : UnitSphere n => diagonalDilation r.1 ω) ⁻¹'
      (ellipsoid 0 r)ᶜ = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro ω
    simpa only [mem_preimage, mem_compl_iff, not_not, zero_add] using
      diagonalDilation_mem_ellipsoid (0 : Space n) r ω
  rw [hempty, measure_empty]

/-- Integration against `σᵣ` in the sphere coordinates of (1.1). -/
theorem integral_ellipsoidMeasure (r : Radii n) (f : Space n → ℂ) (hf : Continuous f) :
    ∫ y, f y ∂ellipsoidMeasure r =
      ∫ ω : UnitSphere n, f (diagonalDilation r.1 ω) ∂sphereMeasure n := by
  rw [ellipsoidMeasure, integral_map_of_stronglyMeasurable
    (continuous_diagonalDilation r.1).measurable hf.stronglyMeasurable]
  exact integral_map_of_stronglyMeasurable measurable_subtype_coe
    (hf.comp (continuous_diagonalDilation r.1)).stronglyMeasurable

/-- Convolution with a finite surface measure, with the `f(x - y)` convention. -/
def measureConvolution (μ : Measure (Space n)) (f : Space n → ℂ) (x : Space n) : ℂ :=
  ∫ y, f (x - y) ∂μ

/-- The spherical/ellipsoidal average `f * σᵣ`. -/
def sphericalAverage (f : Space n → ℂ) (r : Radii n) : Space n → ℂ :=
  measureConvolution (ellipsoidMeasure r) f

theorem sphericalAverage_eq_sphere_integral (f : Space n → ℂ) (hf : Continuous f)
    (r : Radii n) (x : Space n) :
    sphericalAverage f r x =
      ∫ ω : UnitSphere n, f (x - diagonalDilation r.1 ω) ∂sphereMeasure n := by
  exact integral_ellipsoidMeasure r (fun y => f (x - y))
    (hf.comp (continuous_const.sub continuous_id))

/-- Supremum over an arbitrary set of parameters. Finite and countable sets
can be used before proving the passage to the full supremum. -/
def maximalOver {ι : Type*} (R : Set ι) (A : ι → Space n → ℂ) (x : Space n) : ℝ≥0∞ :=
  ⨆ r ∈ R, ‖A r x‖ₑ

theorem le_maximalOver {ι : Type*} (R : Set ι) (A : ι → Space n → ℂ)
    (x : Space n) {r : ι} (hr : r ∈ R) : ‖A r x‖ₑ ≤ maximalOver R A x :=
  le_iSup_of_le r (le_iSup_of_le hr le_rfl)

theorem maximalOver_mono {ι : Type*} {R S : Set ι} (hRS : R ⊆ S)
    (A : ι → Space n → ℂ) (x : Space n) : maximalOver R A x ≤ maximalOver S A x := by
  refine iSup_le fun r => iSup_le fun hr => ?_
  exact le_maximalOver S A x (hRS hr)

/-- The full strong spherical maximal function `M_st` in (1.2). -/
def strongSphericalMaximal (f : Space n → ℂ) : Space n → ℝ≥0∞ :=
  maximalOver univ (sphericalAverage f)

/-- The full supremum in precisely the sphere-coordinate form of (1.2). -/
theorem strongSphericalMaximal_eq_sphere_integral (f : Space n → ℂ)
    (hf : Continuous f) (x : Space n) :
    strongSphericalMaximal f x =
      ⨆ r : Radii n,
        ‖∫ ω : UnitSphere n, f (x - diagonalDilation r.1 ω) ∂sphereMeasure n‖ₑ := by
  simp only [strongSphericalMaximal, maximalOver, sphericalAverage_eq_sphere_integral f hf,
    mem_univ, iSup_pos]

/-- The local spherical maximal function `M_loc` in (1.4). -/
def localSphericalMaximal (f : Space n → ℂ) : Space n → ℝ≥0∞ :=
  maximalOver (localRadii n) (sphericalAverage f)

theorem localSphericalMaximal_le_strong (f : Space n → ℂ) (x : Space n) :
    localSphericalMaximal f x ≤ strongSphericalMaximal f x :=
  maximalOver_mono (subset_univ _) _ x

/-- Dilation of a convolution kernel, including the reciprocal Jacobian. -/
def dilatedKernel (K : Space n → ℂ) (r : Radii n) (y : Space n) : ℂ :=
  (dilationJacobian r : ℂ)⁻¹ * K (inverseDilation r y)

/-- Kernel convolution `K * f`, compatible with mathlib's convolution API. -/
def kernelConvolution (K f : Space n → ℂ) : Space n → ℂ :=
  MeasureTheory.convolution K f (ContinuousLinearMap.mul ℂ ℂ) volume

theorem kernelConvolution_eq_integral (K f : Space n → ℂ) (x : Space n) :
    kernelConvolution K f x = ∫ y, K y * f (x - y) := rfl

/-- The local maximal convolution operator in Proposition 1.3 / (1.12). -/
def localKernelMaximal (K f : Space n → ℂ) : Space n → ℝ≥0∞ :=
  maximalOver (localRadii n) (fun r => kernelConvolution (dilatedKernel K r) f)

/-- The full maximal convolution operator in Lemma 1.4 / (1.13). -/
def strongKernelMaximal (K f : Space n → ℂ) : Space n → ℝ≥0∞ :=
  maximalOver univ (fun r => kernelConvolution (dilatedKernel K r) f)

/-- The oscillatory kernel `K_λ` in (1.7). `𝓕⁻` uses the paper's `+2πi` convention.
Smoothness, support and `1 ≤ λ` are hypotheses for later estimates, rather than
restrictions needed to form this expression. -/
def normalKernel (χ : Space n → ℂ) (β : ℝ → ℂ) (lambda : ℝ) (u : Space n) : ℂ :=
  χ u * (lambda : ℂ) * (𝓕⁻ β) (lambda * (‖u‖ ^ 2 - 1))

/-- The corresponding dilated kernel `K_{λ,r}`. -/
def dilatedNormalKernel (χ : Space n → ℂ) (β : ℝ → ℂ) (lambda : ℝ)
    (r : Radii n) : Space n → ℂ :=
  dilatedKernel (normalKernel χ β lambda) r

/-- The sharp lower endpoint `(n + 1)/(n - 1)`.
The subtraction is in `ℝ`, before conversion to an extended nonnegative real. -/
def criticalExponent (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((n : ℝ) + 1) / ((n : ℝ) - 1))

/-- The conclusion of Theorem 1.1 for fixed dimension and exponent.
`C : ℝ≥0` is finite and independent of the compactly supported continuous
complex-valued input. `p = ∞` is included by the definition of `eLpNorm`.
Measurability is recorded explicitly for the extended-valued output. -/
def StrongSphericalBound (n : ℕ) (p : ℝ≥0∞) : Prop :=
  ∃ C : ℝ≥0, ∀ f : C_c(Space n, ℂ),
    AEMeasurable (strongSphericalMaximal (f : Space n → ℂ)) volume ∧
      eLpNorm (strongSphericalMaximal (f : Space n → ℂ)) p volume ≤
        (C : ℝ≥0∞) * eLpNorm (f : Space n → ℂ) p volume

/-- The exact target of the project: Theorem 1.1 of arXiv:2609.32421v2.
This is a statement to prove in `Main.lean`, not an axiom or an admitted theorem. -/
def MainTheorem : Prop :=
  ∀ (n : ℕ), 4 ≤ n → ∀ (p : ℝ≥0∞), criticalExponent n < p →
    StrongSphericalBound n p

end StrongSpherical
