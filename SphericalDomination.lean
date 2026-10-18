import NormalSphereLimit
import DilationL2
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-! # Domination of the actual spherical maximal function by the normal pieces

The finite normal-frequency convolutions converge to the actual normalized
spherical average at every radius and every output point. Taking their norms
gives the extended-valued pointwise series bound without any summability
assumption on the series of maximal functions.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators CompactlySupported

namespace StrongSpherical.SphericalDomination
variable {n : ℕ}

/-- The reciprocal Jacobian in the actual dilated kernel cancels exactly
under the positive diagonal change of variables. This identity is unconditional. -/
theorem kernelConvolution_dilated_eq_pairing (K f : Space n → ℂ)
    (r : Radii n) (x : Space n) :
    kernelConvolution (dilatedKernel K r) f x =
      ∫ u, K u * f (x - diagonalDilation r.1 u) := by
  rw [kernelConvolution_eq_integral,
    DilationL2.integral_eq_dilation r (fun y => dilatedKernel K r y * f (x - y))]
  simp_rw [dilatedKernel, inverseDilation_diagonalDilation, mul_assoc]
  rw [integral_const_mul, Complex.real_smul, ← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (dilationJacobian_pos r).ne'), one_mul]

/-- The same test function paired with the normalized spherical measure is
the actual spherical average from Definitions. -/
theorem sphericalAverage_eq_pairing (f : Space n → ℂ) (hf : Continuous f)
    (r : Radii n) (x : Space n) :
    sphericalAverage f r x =
      ∫ u, f (x - diagonalDilation r.1 u) ∂sphericalMeasure n := by
  rw [sphericalAverage, measureConvolution, ellipsoidMeasure]
  have hg : StronglyMeasurable (fun y : Space n => f (x - y)) :=
    (hf.comp (continuous_const.sub continuous_id)).stronglyMeasurable
  exact integral_map_of_stronglyMeasurable (continuous_diagonalDilation r.1).measurable hg

/-- The actual finite sums, including K₀, converge pointwise to the normalized
spherical average. Continuity suffices because the kernels have a common
compact spatial support. -/
theorem tendsto_partial_convolution (n : ℕ) (hn : 2 ≤ n)
    (f : Space n → ℂ) (hf : Continuous f) (r : Radii n) (x : Space n) :
    Tendsto (fun J : ℕ => ∑ j ∈ Finset.range (J + 1),
      kernelConvolution (dilatedKernel (NormalDecomposition.kernelPiece n j) r) f x)
      atTop (𝓝 (sphericalAverage f r x)) := by
  have ht : Continuous (fun u : Space n => f (x - diagonalDilation r.1 u)) :=
    hf.comp (continuous_const.sub (continuous_diagonalDilation r.1))
  rw [sphericalAverage_eq_pairing f hf r x]
  simpa only [kernelConvolution_dilated_eq_pairing] using
    NormalSphereLimit.continuous_test_decomposition n hn _ ht

/-- Every finite convolution sum is controlled by the entire nonnegative
series of actual kernel maxima, whether that series is finite or infinite. -/
theorem partial_convolution_enorm_le_tsum (n : ℕ) (f : Space n → ℂ)
    (r : Radii n) (x : Space n) (J : ℕ) :
    ‖∑ j ∈ Finset.range (J + 1),
      kernelConvolution (dilatedKernel (NormalDecomposition.kernelPiece n j) r) f x‖ₑ ≤
      ∑' j : ℕ, strongKernelMaximal (NormalDecomposition.kernelPiece n j) f x := by
  calc
    _ ≤ ∑ j ∈ Finset.range (J + 1),
        ‖kernelConvolution (dilatedKernel (NormalDecomposition.kernelPiece n j) r) f x‖ₑ :=
      enorm_sum_le _ _
    _ ≤ ∑ j ∈ Finset.range (J + 1),
        strongKernelMaximal (NormalDecomposition.kernelPiece n j) f x := by
      apply Finset.sum_le_sum
      intro j _
      exact le_maximalOver univ
        (fun r => kernelConvolution (dilatedKernel (NormalDecomposition.kernelPiece n j) r) f)
        x (mem_univ r)
    _ ≤ _ := ENNReal.sum_le_tsum _

/-- Passing to the closed order interval retains the same extended-valued
series bound for the limiting spherical average. -/
theorem sphericalAverage_enorm_le_tsum (n : ℕ) (hn : 2 ≤ n)
    (f : Space n → ℂ) (hf : Continuous f) (r : Radii n) (x : Space n) :
    ‖sphericalAverage f r x‖ₑ ≤
      ∑' j : ℕ, strongKernelMaximal (NormalDecomposition.kernelPiece n j) f x :=
  le_of_tendsto' (tendsto_partial_convolution n hn f hf r x).enorm
    (fun J => partial_convolution_enorm_le_tsum n f r x J)

/-- Equation (6.22), for the actual strong spherical maximal function.
The series includes the low-frequency rho-piece at index zero, and no
pointwise or norm summability assumption is imposed. -/
theorem strongSphericalMaximal_le_tsum (n : ℕ) (hn : 2 ≤ n)
    (f : Space n → ℂ) (hf : Continuous f) (x : Space n) :
    strongSphericalMaximal f x ≤
      ∑' j : ℕ, strongKernelMaximal (NormalDecomposition.kernelPiece n j) f x := by
  unfold strongSphericalMaximal maximalOver
  exact iSup_le fun r => iSup_le fun _ => sphericalAverage_enorm_le_tsum n hn f hf r x

/-- The form used directly by the compact-test statement of MainTheorem. -/
theorem compact_strongSphericalMaximal_le_tsum (n : ℕ) (hn : 2 ≤ n)
    (f : C_c(Space n, ℂ)) (x : Space n) :
    strongSphericalMaximal (f : Space n → ℂ) x ≤
      ∑' j : ℕ, strongKernelMaximal (NormalDecomposition.kernelPiece n j)
        (f : Space n → ℂ) x :=
  strongSphericalMaximal_le_tsum n hn f f.continuous x

end StrongSpherical.SphericalDomination
