import NormalCutoffs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

/-! # The continuous scalar density for the quadratic radial variable -/
noncomputable section
open MeasureTheory Set

namespace StrongSpherical.NormalRadialDensity

/-- Angular integration uses the unnormalized surface measure from the paper. -/
def angular (n : ℕ) (g : Space n → ℂ) (r : ℝ) : ℂ :=
  ∫ omega : UnitSphere n, g (r • (omega : Space n)) ∂surfaceMeasure n

/-- The radial Jacobian density in the variable `t = r² - 1`.
The cutoff at the origin makes this a continuous zero extension on `t ≤ -1`. -/
def density (n : ℕ) (f : Space n → ℂ) (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) * (((Real.sqrt (t + 1)) ^ (n - 2) : ℝ) : ℂ) *
    angular n (fun u => NormalCutoffs.chi n u * f u) (Real.sqrt (t + 1))

lemma norm_coe_sphere (n : ℕ) (omega : UnitSphere n) : ‖(omega : Space n)‖ = 1 := by
  simpa only [Metric.mem_sphere, dist_zero_right] using omega.2

lemma norm_smul_sphere (n : ℕ) (r : ℝ) (omega : UnitSphere n) :
    ‖r • (omega : Space n)‖ = |r| := by
  rw [norm_smul, Real.norm_eq_abs, norm_coe_sphere, mul_one]

/-- Continuity holds for every continuous angular input, without a support assumption. -/
theorem continuous_angular (n : ℕ) (g : Space n → ℂ) (hg : Continuous g) :
    Continuous (angular n g) := by
  unfold angular
  have hjoint : Continuous (Function.uncurry
      (fun (r : ℝ) (omega : UnitSphere n) => g (r • (omega : Space n)))) := by
    exact hg.comp (continuous_fst.smul (continuous_subtype_val.comp continuous_snd))
  have h := continuous_parametric_integral_of_continuous
    (μ := surfaceMeasure n) hjoint (isCompact_univ : IsCompact (univ : Set (UnitSphere n)))
  simpa only [setIntegral_univ] using h

/-- Each sphere integral is an actual convergent Bochner integral. -/
theorem integrable_angular_integrand (n : ℕ) (g : Space n → ℂ)
    (hg : Continuous g) (r : ℝ) :
    Integrable (fun omega : UnitSphere n => g (r • (omega : Space n))) (surfaceMeasure n) := by
  have hc : Continuous (fun omega : UnitSphere n => g (r • (omega : Space n))) := by
    exact hg.comp (continuous_const.smul continuous_subtype_val)
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem continuous_density (n : ℕ) (f : Space n → ℂ) (hf : Continuous f) :
    Continuous (density n f) := by
  have hs : Continuous (fun t : ℝ => Real.sqrt (t + 1)) := by fun_prop
  have hp : Continuous (fun t : ℝ => (((Real.sqrt (t + 1)) ^ (n - 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (hs.pow (n - 2))
  have ha := continuous_angular n (fun u => NormalCutoffs.chi n u * f u)
    ((NormalCutoffs.contDiff_chi n).continuous.mul hf)
  exact (continuous_const.mul hp).mul (ha.comp hs)

/-- The annular spatial cutoff kills sufficiently small radii, including zero. -/
theorem angular_cutoff_eq_zero_of_small_radius (n : ℕ) (f : Space n → ℂ)
    (r : ℝ) (hr : |r| ≤ 5 / 8) :
    angular n (fun u => NormalCutoffs.chi n u * f u) r = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards with omega
  have hnorm : ‖r • (omega : Space n)‖ ≤ 5 / 8 := by
    simpa only [norm_smul_sphere] using hr
  simp only [NormalCutoffs.chi_eq_zero_of_norm_le n _ hnorm, zero_mul, Pi.zero_apply]

/-- The same cutoff kills all radii of absolute value at least `3/2`. -/
theorem angular_cutoff_eq_zero_of_large_radius (n : ℕ) (f : Space n → ℂ)
    (r : ℝ) (hr : (3 / 2 : ℝ) ≤ |r|) :
    angular n (fun u => NormalCutoffs.chi n u * f u) r = 0 := by
  apply integral_eq_zero_of_ae
  filter_upwards with omega
  have hnorm : (3 / 2 : ℝ) ≤ ‖r • (omega : Space n)‖ := by
    simpa only [norm_smul_sphere] using hr
  simp only [NormalCutoffs.chi_eq_zero_of_le_norm n _ hnorm, zero_mul, Pi.zero_apply]

@[simp] theorem angular_cutoff_zero (n : ℕ) (f : Space n → ℂ) :
    angular n (fun u => NormalCutoffs.chi n u * f u) 0 = 0 :=
  angular_cutoff_eq_zero_of_small_radius n f 0 (by norm_num)

theorem support_angular_cutoff_subset (n : ℕ) (f : Space n → ℂ) :
    Function.support (angular n (fun u => NormalCutoffs.chi n u * f u)) ⊆
      Icc (-(3 / 2 : ℝ)) (3 / 2) := by
  intro r hr
  apply abs_le.mp
  exact le_of_not_gt (fun h => hr (angular_cutoff_eq_zero_of_large_radius n f r h.le))

theorem hasCompactSupport_angular_cutoff (n : ℕ) (f : Space n → ℂ) :
    HasCompactSupport (angular n (fun u => NormalCutoffs.chi n u * f u)) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal (support_angular_cutoff_subset n f) isClosed_Icc)

theorem density_eq_zero_of_le_neg_one (n : ℕ) (f : Space n → ℂ)
    (t : ℝ) (ht : t ≤ -1) : density n f t = 0 := by
  have hs : Real.sqrt (t + 1) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
  simp only [density, hs, angular_cutoff_zero, mul_zero]

theorem density_eq_zero_of_two_le (n : ℕ) (f : Space n → ℂ)
    (t : ℝ) (ht : 2 ≤ t) : density n f t = 0 := by
  have hs : (3 / 2 : ℝ) ≤ |Real.sqrt (t + 1)| := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    have hsq := Real.sq_sqrt (show 0 ≤ t + 1 by linarith)
    have hn := Real.sqrt_nonneg (t + 1)
    nlinarith
  simp only [density, angular_cutoff_eq_zero_of_large_radius n f _ hs, mul_zero]

/-- A fixed compact interval contains the support, independently of the input function. -/
theorem support_density_subset (n : ℕ) (f : Space n → ℂ) :
    Function.support (density n f) ⊆ Icc (-2 : ℝ) 2 := by
  intro t ht
  constructor
  · exact le_of_not_gt (fun h => ht (density_eq_zero_of_le_neg_one n f t (by linarith)))
  · exact le_of_not_gt (fun h => ht (density_eq_zero_of_two_le n f t h.le))

theorem tsupport_density_subset (n : ℕ) (f : Space n → ℂ) :
    tsupport (density n f) ⊆ Icc (-2 : ℝ) 2 :=
  closure_minimal (support_density_subset n f) isClosed_Icc

/-- Compact support does not itself require continuity of the original input. -/
theorem hasCompactSupport_density (n : ℕ) (f : Space n → ℂ) :
    HasCompactSupport (density n f) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (tsupport_density_subset n f)

theorem integrable_density (n : ℕ) (f : Space n → ℂ) (hf : Continuous f) :
    Integrable (density n f) :=
  (continuous_density n f hf).integrable_of_hasCompactSupport (hasCompactSupport_density n f)

/-- At the unit sphere the spatial cutoff equals one and the radial Jacobian is `1/2`. -/
theorem density_zero (n : ℕ) (f : Space n → ℂ) :
    density n f 0 = (1 / 2 : ℂ) *
      ∫ omega : UnitSphere n, f (omega : Space n) ∂surfaceMeasure n := by
  have ha : angular n (fun u => NormalCutoffs.chi n u * f u) 1 =
      ∫ omega : UnitSphere n, f (omega : Space n) ∂surfaceMeasure n := by
    unfold angular
    simp only [one_smul]
    apply integral_congr_ae
    filter_upwards with omega
    rw [NormalCutoffs.chi_eq_one_on_sphere n _ (norm_coe_sphere n omega), one_mul]
  simp only [density, zero_add, Real.sqrt_one, one_pow, Complex.ofReal_one, mul_one, ha]

end StrongSpherical.NormalRadialDensity
