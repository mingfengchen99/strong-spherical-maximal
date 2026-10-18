import NormalDecomposition
import SpherePolar
import NormalRadialDensity
import ScalarApproximation
import QuadraticRadialChange

/-! # The weak spherical limit of the normal-frequency decomposition

Equation (6.6) is proved against every compactly supported continuous complex
test function. The series is expressed as convergence of its ordered finite
partial sums, with the original normalized spherical measure as the limit.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology FourierTransform BigOperators CompactlySupported
namespace StrongSpherical.NormalSphereLimit

/-- The coarea formula for the defining function ‖u‖²-1 and the actual annular
cutoff. The Jacobian is contained in the explicitly constructed density. -/
theorem quadratic_coarea (n : ℕ) (hn : 2 ≤ n) (k : ℝ → ℂ) (hk : Continuous k)
    (f : Space n → ℂ) (hf : Continuous f) :
    (∫ u, NormalCutoffs.chi n u * k (‖u‖ ^ 2 - 1) * f u) =
      ∫ t, k t * NormalRadialDensity.density n f t := by
  let G : Space n → ℂ := fun u => NormalCutoffs.chi n u * k (‖u‖ ^ 2 - 1) * f u
  have hG : Continuous G :=
    ((NormalCutoffs.contDiff_chi n).continuous.mul
      (hk.comp ((continuous_norm.pow 2).sub continuous_const))).mul hf
  have hcG : HasCompactSupport G :=
    ((NormalCutoffs.hasCompactSupport_chi n).mul_right
      (f' := fun u => k (‖u‖ ^ 2 - 1))).mul_right (f' := f)
  have hangle (r : ℝ) (hr : 0 < r) :
      (∫ omega : UnitSphere n, G (r • (omega : Space n)) ∂surfaceMeasure n) =
        k (r ^ 2 - 1) *
          NormalRadialDensity.angular n (fun u => NormalCutoffs.chi n u * f u) r := by
    rw [NormalRadialDensity.angular, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with omega
    dsimp only [G]
    rw [NormalRadialDensity.norm_smul_sphere, abs_of_pos hr]
    ring
  calc
    _ = ∫ r in Ioi (0 : ℝ), ((r ^ (n - 1) : ℝ) : ℂ) *
        (∫ omega : UnitSphere n, G (r • (omega : Space n)) ∂surfaceMeasure n) :=
      SpherePolar.integral_eq_polar n (by omega) G hG hcG
    _ = ∫ r in Ioi (0 : ℝ), ((r ^ (n - 1) : ℝ) : ℂ) * k (r ^ 2 - 1) *
        NormalRadialDensity.angular n (fun u => NormalCutoffs.chi n u * f u) r := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro r hr
      dsimp only
      rw [hangle r hr]
      ring
    _ = _ := QuadraticRadialChange.integral_quadratic n hn k
      (NormalRadialDensity.angular n (fun u => NormalCutoffs.chi n u * f u))
      (NormalRadialDensity.angular_cutoff_zero n f)

/-- The actual finite approximate kernel pairs with a scalar approximate
identity, with exactly the normalization c_n from (6.1). -/
theorem approximate_pairing (n : ℕ) (hn : 2 ≤ n) (f : Space n → ℂ)
    (hf : Continuous f) (J : ℕ) :
    (∫ u, NormalDecomposition.approximateKernel (NormalCutoffs.chi n)
      NormalCutoffs.rho J u * f u) =
      (NormalFrequencyPieces.normalization n : ℂ) *
        ∫ t, ((2 : ℝ) ^ J : ℂ) * (𝓕⁻ NormalCutoffs.rho) ((2 : ℝ) ^ J * t) *
          NormalRadialDensity.density n f t := by
  have hk : Continuous (fun t : ℝ =>
      ((2 : ℝ) ^ J : ℂ) * (𝓕⁻ NormalCutoffs.rho) ((2 : ℝ) ^ J * t)) :=
    continuous_const.mul
      ((NormalKernelC1.contDiff_inverseFourier NormalCutoffs.rho NormalCutoffs.contDiff_rho
        NormalCutoffs.hasCompactSupport_rho).continuous.comp
          (continuous_const.mul continuous_id))
  calc
    _ = (NormalFrequencyPieces.normalization n : ℂ) *
        ∫ u, NormalCutoffs.chi n u *
          (((2 : ℝ) ^ J : ℂ) * (𝓕⁻ NormalCutoffs.rho) ((2 : ℝ) ^ J * (‖u‖ ^ 2 - 1))) * f u := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with u
      dsimp only [NormalDecomposition.approximateKernel]
      ring
    _ = _ := by rw [quadratic_coarea n hn _ hk f hf]

/-- The radial Jacobian 1/2 cancels the numerator 2 of c_n, leaving precisely
the normalized surface measure defined at the start of the project. -/
theorem normalization_mul_density_zero (n : ℕ) (f : Space n → ℂ) (hf : Continuous f) :
    (NormalFrequencyPieces.normalization n : ℂ) * NormalRadialDensity.density n f 0 =
      ∫ u, f u ∂sphericalMeasure n := by
  rw [sphericalMeasure, integral_map_of_stronglyMeasurable measurable_subtype_coe
    hf.stronglyMeasurable, sphereMeasure, integral_smul_measure,
    NormalRadialDensity.density_zero]
  simp only [NormalFrequencyPieces.normalization, ENNReal.toReal_inv,
    Complex.real_smul, Complex.ofReal_div, Complex.ofReal_inv, Complex.ofReal_ofNat]
  ring

/-- The genuine coarea limit. Continuity alone is sufficient because the
spatial cutoff confines every integral to a fixed compact annulus. -/
theorem approximateKernel_tendsto (n : ℕ) (hn : 2 ≤ n)
    (f : Space n → ℂ) (hf : Continuous f) :
    Tendsto (fun J : ℕ => ∫ u,
      NormalDecomposition.approximateKernel (NormalCutoffs.chi n) NormalCutoffs.rho J u * f u)
      atTop (𝓝 (∫ u, f u ∂sphericalMeasure n)) := by
  have h := ScalarApproximation.dyadic_tendsto (𝓕⁻ NormalCutoffs.rho)
    NormalDecomposition.integrable_inverse_rho NormalDecomposition.integral_inverse_rho
    (NormalRadialDensity.density n f) (NormalRadialDensity.continuous_density n f hf)
    (NormalRadialDensity.hasCompactSupport_density n f)
  have hc := (tendsto_const_nhds
    (x := (NormalFrequencyPieces.normalization n : ℂ))).mul h
  rw [normalization_mul_density_zero n f hf] at hc
  simp only [Complex.ofReal_pow] at hc
  exact hc.congr' (Eventually.of_forall fun J => (approximate_pairing n hn f hf J).symm)

/-- Integrability needed to pass the finite sum through the pairing. -/
theorem integrable_piece_pairing (n j : ℕ) (f : Space n → ℂ) (hf : Continuous f) :
    Integrable (fun u => NormalDecomposition.kernelPiece n j u * f u) :=
  ((NormalDecomposition.contDiff_kernelPiece n j).continuous.mul hf).integrable_of_hasCompactSupport
      ((NormalDecomposition.hasCompactSupport_kernelPiece n j).mul_right (f' := f))

/-- The pointwise finite identity (6.5), integrated against a continuous test. -/
theorem finite_pairing (n J : ℕ) (f : Space n → ℂ) (hf : Continuous f) :
    (∑ j ∈ Finset.range (J + 1), ∫ u, NormalDecomposition.kernelPiece n j u * f u) =
      ∫ u, NormalDecomposition.approximateKernel (NormalCutoffs.chi n) NormalCutoffs.rho J u * f u := by
  rw [← integral_finsetSum _ (fun j _ => integrable_piece_pairing n j f hf)]
  apply integral_congr_ae
  filter_upwards with u
  rw [← Finset.sum_mul, NormalDecomposition.sum_kernelPiece]

/-- Equation (6.6) as convergence of the ordered finite kernel pairings.
The limiting measure is the actual normalized spherical measure. -/
theorem continuous_test_decomposition (n : ℕ) (hn : 2 ≤ n)
    (f : Space n → ℂ) (hf : Continuous f) :
    Tendsto (fun J : ℕ => ∑ j ∈ Finset.range (J + 1),
      ∫ u, NormalDecomposition.kernelPiece n j u * f u)
      atTop (𝓝 (∫ u, f u ∂sphericalMeasure n)) := by
  have h := approximateKernel_tendsto n hn f hf
  exact h.congr' (Eventually.of_forall fun J => (finite_pairing n J f hf).symm)

/-- In particular, (6.6) holds against every compactly supported continuous
complex test function, and hence against all smooth compactly supported tests. -/
theorem compact_test_decomposition (n : ℕ) (hn : 2 ≤ n) (f : C_c(Space n, ℂ)) :
    Tendsto (fun J : ℕ => ∑ j ∈ Finset.range (J + 1),
      ∫ u, NormalDecomposition.kernelPiece n j u * f u)
      atTop (𝓝 (∫ u, f u ∂sphericalMeasure n)) :=
  continuous_test_decomposition n hn f f.continuous

end StrongSpherical.NormalSphereLimit
