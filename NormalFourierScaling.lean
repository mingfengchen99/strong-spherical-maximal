import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Tactic

/-! # Exact inverse Fourier scaling for the normal-frequency decomposition -/
noncomputable section
open MeasureTheory
open scoped FourierTransform

namespace StrongSpherical.NormalFourierScaling

/-- The inverse Fourier integrand is genuinely integrable whenever its input is. -/
lemma integrable_inverseFourier_integrand (f : ℝ → ℂ) (hf : Integrable f) (t : ℝ) :
    Integrable (fun s : ℝ => 𝐞 (inner ℝ s t) • f s) := by
  have hc : Continuous (fun s : ℝ => 𝐞 (inner ℝ s t)) := by fun_prop
  apply (integrable_norm_iff (hc.aestronglyMeasurable.smul hf.aestronglyMeasurable)).mp
  simpa only [Circle.norm_smul] using hf.norm

/-- Actual inverse Fourier scaling, with the positive Jacobian `a⁻¹`.
The identity also holds for nonintegrable functions under the Bochner integral convention. -/
theorem inverseFourier_comp_mul (f : ℝ → ℂ) (a : ℝ) (ha : 0 < a) (t : ℝ) :
    (𝓕⁻ (fun s : ℝ => f (a * s))) t = (a : ℂ)⁻¹ * (𝓕⁻ f) (t / a) := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq]
  let G : ℝ → ℂ := fun s => 𝐞 (inner ℝ s (t / a)) • f s
  have heq : (fun s : ℝ => 𝐞 (inner ℝ s t) • f (a * s)) = fun s => G (a * s) := by
    funext s
    change 𝐞 (inner ℝ s t) • f (a * s) = 𝐞 (inner ℝ (a * s) (t / a)) • f (a * s)
    have harg : inner ℝ s t = inner ℝ (a * s) (t / a) := by
      simp only [Real.inner_apply]
      field_simp [ha.ne']
    rw [harg]
  rw [heq, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr ha), Complex.real_smul]
  simp only [Complex.ofReal_inv]
  rfl

/-- Subtraction under the actual inverse Fourier integral requires only L¹ inputs. -/
theorem inverseFourier_difference (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g)
    (t : ℝ) :
    (𝓕⁻ (fun s => f s - g s)) t = (𝓕⁻ f) t - (𝓕⁻ g) t := by
  rw [Real.fourierInv_eq, Real.fourierInv_eq, Real.fourierInv_eq]
  simp only [smul_sub]
  exact integral_sub (integrable_inverseFourier_integrand f hf t)
    (integrable_inverseFourier_integrand g hg t)

theorem inverseFourier_sub (f g : ℝ → ℂ) (hf : Integrable f) (hg : Integrable g) :
    (𝓕⁻ (f - g) : ℝ → ℂ) = 𝓕⁻ f - 𝓕⁻ g := by
  funext t
  exact inverseFourier_difference f g hf hg t

/-- For `β(s)=ρ(s)-ρ(2s)`, the second inverse Fourier term has scale `t/2`. -/
theorem inverseFourier_beta_difference (rho : ℝ → ℂ) (hrho : Integrable rho) (t : ℝ) :
    (𝓕⁻ (fun s => rho s - rho (2 * s))) t =
      (𝓕⁻ rho) t - (1 / 2 : ℂ) * (𝓕⁻ rho) (t / 2) := by
  rw [inverseFourier_difference rho (fun s => rho (2 * s)) hrho
    (hrho.comp_mul_left' (by norm_num : (2 : ℝ) ≠ 0))]
  rw [inverseFourier_comp_mul rho 2 (by norm_num)]
  norm_num

/-- The version directly applicable to a continuous compactly supported cutoff. -/
theorem inverseFourier_beta_difference_of_compact (rho : ℝ → ℂ)
    (hrho : Continuous rho) (hc : HasCompactSupport rho) (t : ℝ) :
    (𝓕⁻ (fun s => rho s - rho (2 * s))) t =
      (𝓕⁻ rho) t - (1 / 2 : ℂ) * (𝓕⁻ rho) (t / 2) :=
  inverseFourier_beta_difference rho (hrho.integrable_of_hasCompactSupport hc) t

/-- The exact dyadic difference used when summing the kernels in (6.5).
Both powers in the coefficients are casts of the actual real dilation factors. -/
theorem dyadic_inverse_beta_difference (rho : ℝ → ℂ) (hrho : Integrable rho)
    (j : ℕ) (t : ℝ) :
    (((2 : ℝ) ^ (j + 1) : ℝ) : ℂ) *
        (𝓕⁻ (fun s => rho s - rho (2 * s))) ((2 : ℝ) ^ (j + 1) * t) =
      (((2 : ℝ) ^ (j + 1) : ℝ) : ℂ) * (𝓕⁻ rho) ((2 : ℝ) ^ (j + 1) * t) -
        (((2 : ℝ) ^ j : ℝ) : ℂ) * (𝓕⁻ rho) ((2 : ℝ) ^ j * t) := by
  rw [inverseFourier_beta_difference rho hrho]
  have harg : (2 : ℝ) ^ (j + 1) * t / 2 = (2 : ℝ) ^ j * t := by
    rw [pow_succ]
    ring
  rw [harg]
  push_cast
  simp only [pow_succ]
  ring

end StrongSpherical.NormalFourierScaling
