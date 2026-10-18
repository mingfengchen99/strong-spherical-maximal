import FourierCutoff
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Concrete smooth cutoffs for the normal dyadic kernel decomposition -/
noncomputable section
open MeasureTheory Set
open scoped ContDiff
namespace StrongSpherical.NormalCutoffs
set_option maxHeartbeats 1000000

/-- Its outer radius is strictly smaller than two, so the closed support
lies in the open frequency interval required in §6.1. -/
def rhoBump : ContDiffBump (0 : ℝ) := ⟨1, 3 / 2, by norm_num, by norm_num⟩

/-- The fixed real even low-frequency bump, viewed as a complex function. -/
def rho (t : ℝ) : ℂ := (rhoBump t : ℂ)

/-- The annular frequency cutoff used in the dyadic difference. -/
def beta (t : ℝ) : ℂ := rho t - rho (2 * t)

theorem contDiff_rho : ContDiff ℝ ∞ rho :=
  Complex.ofRealCLM.contDiff.comp rhoBump.contDiff

theorem hasCompactSupport_rho : HasCompactSupport rho :=
  rhoBump.hasCompactSupport.comp_left (g := Complex.ofRealCLM) rfl

theorem integrable_rho : Integrable rho :=
  contDiff_rho.continuous.integrable_of_hasCompactSupport hasCompactSupport_rho

@[simp] theorem rho_even (t : ℝ) : rho (-t) = rho t := by
  simp only [rho, rhoBump.neg]

@[simp] theorem rho_im (t : ℝ) : (rho t).im = 0 := rfl
@[simp] theorem rho_re (t : ℝ) : (rho t).re = rhoBump t := rfl

theorem rho_eq_one_of_abs_le (t : ℝ) (ht : |t| ≤ 1) : rho t = 1 := by
  change (rhoBump t : ℂ) = 1
  have hh : rhoBump t = 1 := rhoBump.one_of_mem_closedBall (by
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, rhoBump] using ht)
  rw [hh, Complex.ofReal_one]

theorem rho_eq_one (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) : rho t = 1 :=
  rho_eq_one_of_abs_le t (abs_le.mpr ht)

@[simp] theorem rho_zero : rho 0 = 1 := rho_eq_one_of_abs_le 0 (by norm_num)

theorem rho_eq_zero_of_three_halves_le_abs (t : ℝ) (ht : (3 / 2 : ℝ) ≤ |t|) :
    rho t = 0 := by
  change (rhoBump t : ℂ) = 0
  have hh : rhoBump t = 0 := rhoBump.zero_of_le_dist (by
    simpa only [rhoBump, dist_zero_right, Real.norm_eq_abs] using ht)
  rw [hh, Complex.ofReal_zero]

theorem rho_eq_zero_of_two_le_abs (t : ℝ) (ht : 2 ≤ |t|) : rho t = 0 :=
  rho_eq_zero_of_three_halves_le_abs t (by linarith)

theorem support_rho_subset : Function.support rho ⊆ Ioo (-2 : ℝ) 2 := by
  intro t ht
  have h : |t| < 2 := lt_of_not_ge (fun h => ht (rho_eq_zero_of_two_le_abs t h))
  exact abs_lt.mp h

theorem tsupport_rho_subset_closed : tsupport rho ⊆ Icc (-(3 / 2 : ℝ)) (3 / 2) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  have h : |t| < (3 / 2 : ℝ) :=
    lt_of_not_ge (fun h => ht (rho_eq_zero_of_three_halves_le_abs t h))
  exact abs_le.mp h.le

theorem tsupport_rho_subset : tsupport rho ⊆ Ioo (-2 : ℝ) 2 := by
  intro t ht
  have hh := tsupport_rho_subset_closed ht
  constructor <;> linarith [hh.1, hh.2]

theorem contDiff_beta : ContDiff ℝ ∞ beta :=
  contDiff_rho.sub (contDiff_rho.comp (contDiff_const.mul contDiff_id))

@[simp] theorem beta_even (t : ℝ) : beta (-t) = beta t := by
  simp only [beta, mul_neg, rho_even]

@[simp] theorem beta_im (t : ℝ) : (beta t).im = 0 := by simp only [beta, Complex.sub_im, rho_im, sub_self]
@[simp] theorem beta_re (t : ℝ) : (beta t).re = rhoBump t - rhoBump (2 * t) := rfl
@[simp] theorem beta_zero : beta 0 = 0 := by simp only [beta, mul_zero, sub_self]

theorem beta_eq_zero_of_abs_lt_half (t : ℝ) (ht : |t| < 1 / 2) : beta t = 0 := by
  have h1 : |t| ≤ 1 := by linarith
  have h2 : |2 * t| ≤ 1 := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  rw [beta, rho_eq_one_of_abs_le t h1, rho_eq_one_of_abs_le (2 * t) h2, sub_self]

theorem beta_eq_zero_of_two_le_abs (t : ℝ) (ht : 2 ≤ |t|) : beta t = 0 := by
  have h2 : 2 ≤ |2 * t| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith
  rw [beta, rho_eq_zero_of_two_le_abs t ht, rho_eq_zero_of_two_le_abs (2 * t) h2, sub_self]

theorem support_beta_subset :
    Function.support beta ⊆ {t : ℝ | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2} := by
  intro t ht
  constructor
  · exact le_of_not_gt (fun h => ht (beta_eq_zero_of_abs_lt_half t h))
  · exact (lt_of_not_ge (fun h => ht (beta_eq_zero_of_two_le_abs t h))).le

theorem tsupport_beta_subset :
    tsupport beta ⊆ {t : ℝ | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2} :=
  closure_minimal support_beta_subset
    ((isClosed_le continuous_const continuous_abs).inter (isClosed_le continuous_abs continuous_const))

theorem hasCompactSupport_beta : HasCompactSupport beta :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport beta)
    (fun _ ht => abs_le.mp (tsupport_beta_subset ht).2)

theorem integrable_beta : Integrable beta :=
  contDiff_beta.continuous.integrable_of_hasCompactSupport hasCompactSupport_beta

/-- Scalar bumps applied to the squared norm make the spatial cutoff radial
without requiring any radiality choice for bump functions on Euclidean space. -/
def outer : ContDiffBump (0 : ℝ) := ⟨25 / 16, 9 / 4, by norm_num, by norm_num⟩
def inner : ContDiffBump (0 : ℝ) := ⟨25 / 64, 9 / 16, by norm_num, by norm_num⟩

def chi (n : ℕ) (u : Space n) : ℂ :=
  (outer (‖u‖ ^ 2) * (1 - inner (‖u‖ ^ 2)) : ℝ)

theorem contDiff_chi (n : ℕ) : ContDiff ℝ ∞ (chi n) :=
  Complex.ofRealCLM.contDiff.comp
    ((outer.contDiff.comp (contDiff_norm_sq ℝ)).mul
      (contDiff_const.sub (inner.contDiff.comp (contDiff_norm_sq ℝ))))

@[simp] theorem chi_im (n : ℕ) (u : Space n) : (chi n u).im = 0 := rfl

/-- The cutoff depends only on the Euclidean radius. -/
theorem chi_radial (n : ℕ) (u v : Space n) (h : ‖u‖ = ‖v‖) : chi n u = chi n v := by
  simp only [chi, h]

@[simp] theorem chi_even (n : ℕ) (u : Space n) : chi n (-u) = chi n u := by
  simp only [chi, norm_neg]

theorem outer_eq_one (n : ℕ) (u : Space n) (hu : ‖u‖ ≤ 5 / 4) : outer (‖u‖ ^ 2) = 1 := by
  apply outer.one_of_mem_closedBall
  have hh : ‖u‖ ^ 2 ≤ (25 / 16 : ℝ) := by nlinarith [norm_nonneg u]
  simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖u‖), outer] using hh

theorem inner_eq_zero (n : ℕ) (u : Space n) (hu : 3 / 4 ≤ ‖u‖) : inner (‖u‖ ^ 2) = 0 := by
  apply inner.zero_of_le_dist
  have hh : (9 / 16 : ℝ) ≤ ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖u‖), inner] using hh

theorem chi_eq_one (n : ℕ) (u : Space n) (hu : (3 / 4 : ℝ) ≤ ‖u‖ ∧ ‖u‖ ≤ 5 / 4) :
    chi n u = 1 := by
  simp only [chi, outer_eq_one n u hu.2, inner_eq_zero n u hu.1, sub_zero, mul_one, Complex.ofReal_one]

theorem chi_eq_one_of_near_sphere (n : ℕ) (u : Space n)
    (hu : (3 / 4 : ℝ) < ‖u‖ ∧ ‖u‖ < 5 / 4) : chi n u = 1 :=
  chi_eq_one n u ⟨hu.1.le, hu.2.le⟩

theorem chi_eq_zero_of_norm_le (n : ℕ) (u : Space n) (hu : ‖u‖ ≤ 5 / 8) : chi n u = 0 := by
  have hi : inner (‖u‖ ^ 2) = 1 := by
    apply inner.one_of_mem_closedBall
    have hh : ‖u‖ ^ 2 ≤ (25 / 64 : ℝ) := by nlinarith [norm_nonneg u]
    simpa only [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg ‖u‖), inner] using hh
  simp only [chi, hi, sub_self, mul_zero, Complex.ofReal_zero]

theorem chi_eq_zero_of_le_norm (n : ℕ) (u : Space n) (hu : 3 / 2 ≤ ‖u‖) : chi n u = 0 := by
  have ho : outer (‖u‖ ^ 2) = 0 := by
    apply outer.zero_of_le_dist
    have hh : (9 / 4 : ℝ) ≤ ‖u‖ ^ 2 := by nlinarith [norm_nonneg u]
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖u‖), outer] using hh
  simp only [chi, ho, zero_mul, Complex.ofReal_zero]

@[simp] theorem chi_zero (n : ℕ) : chi n 0 = 0 := chi_eq_zero_of_norm_le n 0 (by norm_num)

theorem support_chi_subset (n : ℕ) :
    Function.support (chi n) ⊆ {u | (5 / 8 : ℝ) ≤ ‖u‖ ∧ ‖u‖ ≤ 3 / 2} := by
  intro u hu
  constructor
  · exact le_of_not_gt (fun h => hu (chi_eq_zero_of_norm_le n u h.le))
  · exact le_of_not_gt (fun h => hu (chi_eq_zero_of_le_norm n u h.le))

theorem tsupport_chi_subset_closed (n : ℕ) :
    tsupport (chi n) ⊆ {u | (5 / 8 : ℝ) ≤ ‖u‖ ∧ ‖u‖ ≤ 3 / 2} :=
  closure_minimal (support_chi_subset n)
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))

theorem tsupport_chi_subset (n : ℕ) :
    tsupport (chi n) ⊆ {u | (1 / 2 : ℝ) < ‖u‖ ∧ ‖u‖ < 2} := by
  intro u hu
  obtain ⟨h1, h2⟩ := tsupport_chi_subset_closed n hu
  constructor <;> linarith

theorem hasCompactSupport_chi (n : ℕ) : HasCompactSupport (chi n) :=
  (isCompact_closedBall (0 : Space n) (3 / 2)).of_isClosed_subset (isClosed_tsupport _)
    (fun _ hu => by simpa only [Metric.mem_closedBall, dist_zero_right] using
      (tsupport_chi_subset_closed n hu).2)

theorem chi_eq_one_on_sphere (n : ℕ) (u : Space n) (hu : ‖u‖ = 1) : chi n u = 1 :=
  chi_eq_one n u (by rw [hu]; constructor <;> norm_num)

end StrongSpherical.NormalCutoffs
