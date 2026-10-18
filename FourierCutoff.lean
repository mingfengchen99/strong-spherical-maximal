import FrequencyDecomposition
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # A concrete smooth Fourier cutoff and its normalized Schwartz kernels -/
noncomputable section
open MeasureTheory Set FourierTransform
open scoped FourierTransform SchwartzMap BigOperators ContDiff

namespace StrongSpherical.FourierCutoff

/-- The chosen even smooth bump, with inner radius one and outer radius two. -/
def bump : ContDiffBump (0 : ℝ) := ⟨1, 2, by norm_num, by norm_num⟩

def theta (t : ℝ) : ℝ := bump t

theorem theta_contDiff : ContDiff ℝ ∞ theta := bump.contDiff

theorem theta_compact : HasCompactSupport theta := bump.hasCompactSupport

theorem theta_even (t : ℝ) : theta (-t) = theta t := bump.neg t

theorem theta_control : FrequencyDecomposition.CutoffControl theta where
  nonneg := fun _ => bump.nonneg
  le_one := fun _ => bump.le_one
  eq_one := fun t ht => bump.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, bump] using ht)
  support_subset := by
    intro t ht
    have ht' : t ∈ Function.support bump := ht
    rw [bump.support_eq] at ht'
    have hmem : t ∈ Metric.ball (0 : ℝ) 2 := by simpa only [bump] using ht'
    have ha : |t| < 2 := by simpa using hmem
    exact abs_le.mp ha.le

@[simp] theorem theta_zero : theta 0 = 1 := theta_control.eq_one 0 (by norm_num)

/-- The real cutoff viewed as a complex Schwartz function. -/
def thetaSchwartz : 𝓢(ℝ, ℂ) :=
  (theta_compact.comp_left (g := Complex.ofRealCLM) rfl).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp theta_contDiff)

@[simp] theorem thetaSchwartz_apply (t : ℝ) : thetaSchwartz t = (theta t : ℂ) := rfl

/-- The actual inverse Fourier transform, using mathlib's `exp(2πixξ)` convention. -/
def phi : 𝓢(ℝ, ℂ) := 𝓕⁻ thetaSchwartz

@[simp] theorem fourier_phi : 𝓕 phi = thetaSchwartz := fourier_fourierInv_eq _

theorem phi_integrable : Integrable (phi : ℝ → ℂ) := phi.integrable

theorem integral_phi : (∫ t, phi t) = 1 := by
  have h := congrArg (fun f : 𝓢(ℝ, ℂ) => f 0) fourier_phi
  change (∫ t : ℝ, 𝐞 (-inner ℝ t 0) • phi t) = (theta 0 : ℂ) at h
  simpa only [inner_zero_right, neg_zero, AddChar.map_zero_eq_one,
    one_smul, theta_zero, Complex.ofReal_one] using h

/-- Every derivative has every polynomial decay, with a positive constant. -/
theorem phi_decay (N r : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      (1 + |t|) ^ N * ‖iteratedFDeriv ℝ r (phi : ℝ → ℂ) t‖ ≤ C := by
  let C := (2 : ℝ) ^ N * (Finset.Iic (N, r)).sup
    (fun p => SchwartzMap.seminorm ℝ p.1 p.2) phi
  refine ⟨C + 1, by positivity, ?_⟩
  intro t
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (N, r)) (k := N) (n := r) le_rfl le_rfl phi t
  have h' : (1 + |t|) ^ N * ‖iteratedFDeriv ℝ r (phi : ℝ → ℂ) t‖ ≤ C := by
    simpa only [Real.norm_eq_abs] using h
  exact h'.trans (by linarith)

/-- The normalized one-dimensional smoothing kernel at a positive scale. -/
def scaledPhi (v : ℝ) (t : ℝ) : ℂ := (v⁻¹ : ℂ) * phi (v⁻¹ * t)

theorem integral_scaledPhi (v : ℝ) (hv : 0 < v) : (∫ t, scaledPhi v t) = 1 := by
  simp only [scaledPhi]
  rw [integral_const_mul, Measure.integral_comp_inv_mul_left,
    abs_of_pos hv, integral_phi]
  simp only [Complex.real_smul, mul_one]
  norm_cast
  exact inv_mul_cancel₀ hv.ne'

theorem integrable_scaledPhi (v : ℝ) (hv : 0 < v) : Integrable (scaledPhi v) := by
  have h := phi_integrable.comp_smul (inv_ne_zero hv.ne')
  exact h.const_mul _

end StrongSpherical.FourierCutoff
