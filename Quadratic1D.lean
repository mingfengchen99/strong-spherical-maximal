import Definitions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic

/-!
# One-dimensional quadratic oscillation

The one-dimensional estimate (3.5) used in Lemma 3.1 of
arXiv:2609.32421v2. All integrals are oriented interval integrals.
The analytic estimates below are proved directly by integration by parts.
-/

noncomputable section

open MeasureTheory Set
open scoped Interval

namespace StrongSpherical.Quadratic1D

/-- A real quadratic polynomial. -/
def phase (A B C t : ℝ) : ℝ := A * t ^ 2 + B * t + C

/-- Its derivative, kept separate for the nonstationary estimates. -/
def slope (A B t : ℝ) : ℝ := 2 * A * t + B

/-- The complex exponential with a real phase, without a `2π` normalization. -/
def wave (A B C t : ℝ) : ℂ := Complex.exp ((phase A B C t : ℂ) * Complex.I)

theorem hasDerivAt_phase (A B C t : ℝ) :
    HasDerivAt (phase A B C) (slope A B t) t := by
  unfold phase slope
  convert! (((hasDerivAt_id t).pow 2).const_mul A).add
    ((hasDerivAt_id t).const_mul B) |>.add_const C using 1
  simp only [id_eq, mul_one]
  ring

theorem hasDerivAt_slope (A B t : ℝ) : HasDerivAt (slope A B) (2 * A) t := by
  convert! ((hasDerivAt_id t).const_mul (2 * A)).add_const B using 1
  simp only [mul_one]

theorem hasDerivAt_wave (A B C t : ℝ) :
    HasDerivAt (wave A B C)
      (wave A B C t * ((slope A B t : ℂ) * Complex.I)) t := by
  exact (((hasDerivAt_phase A B C t).ofReal_comp).mul_const Complex.I).cexp

theorem continuous_wave (A B C : ℝ) : Continuous (wave A B C) :=
  continuous_iff_continuousAt.mpr fun t => (hasDerivAt_wave A B C t).continuousAt

@[simp] theorem norm_wave (A B C t : ℝ) : ‖wave A B C t‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

theorem intervalIntegrable_wave (A B C a b : ℝ) :
    IntervalIntegrable (wave A B C) volume a b :=
  (continuous_wave A B C).intervalIntegrable a b

/-- The elementary length estimate, also valid when the endpoints are reversed. -/
theorem norm_integral_wave_le_length (A B C a b : ℝ) :
    ‖∫ t in a..b, wave A B C t‖ ≤ |b - a| := by
  simpa only [one_mul] using
    (intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := 1) (fun t _ => (norm_wave A B C t).le))

private theorem integral_abs_eq_abs_integral_of_constant_sign
    {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hsign : (∀ t ∈ Icc a b, 0 ≤ f t) ∨ (∀ t ∈ Icc a b, f t ≤ 0)) :
    (∫ t in a..b, |f t|) = |∫ t in a..b, f t| := by
  rcases hsign with hpos | hneg
  · rw [abs_of_nonneg (intervalIntegral.integral_nonneg hab hpos)]
    apply intervalIntegral.integral_congr
    intro t ht
    exact abs_of_nonneg (hpos t (by simpa [uIcc_of_le hab] using ht))
  · have hnonpos : (∫ t in a..b, f t) ≤ 0 := by
      have := intervalIntegral.integral_nonneg (μ := volume) hab
        (fun t ht => neg_nonneg.mpr (hneg t ht))
      simpa only [intervalIntegral.integral_neg, neg_nonneg] using this
    rw [abs_of_nonpos hnonpos, ← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    exact abs_of_nonpos (hneg t (by simpa [uIcc_of_le hab] using ht))

/-- A first derivative test specialized to quadratic phases. The constant is
absolute, and there is no hypothesis on the length of the interval. -/
theorem norm_integral_wave_le_of_slope
    (A B C a b eta : ℝ) (hab : a ≤ b) (heta : 0 < eta)
    (hsep : ∀ t ∈ Icc a b, eta ≤ |slope A B t|) :
    ‖∫ t in a..b, wave A B C t‖ ≤ 4 / eta := by
  let q := slope A B
  let g : ℝ → ℝ := fun t => (q t)⁻¹
  let gp : ℝ → ℝ := fun t => -(2 * A) / (q t) ^ 2
  have hq : ∀ t ∈ Icc a b, q t ≠ 0 := by
    intro t ht hzero
    have := hsep t ht
    simp only [q, hzero, abs_zero] at this
    linarith
  have hg : ∀ t ∈ Icc a b, HasDerivAt g (gp t) t := by
    intro t ht
    convert! (hasDerivAt_slope A B t).inv (hq t ht) using 1
  have hgc : ContinuousOn g (Icc a b) := fun t ht => (hg t ht).continuousAt.continuousWithinAt
  have hgpc : ContinuousOn gp (Icc a b) := by
    apply ContinuousOn.div continuousOn_const
      (((show Continuous q from by unfold q slope; fun_prop).pow 2).continuousOn)
    intro t ht
    exact pow_ne_zero 2 (hq t ht)
  have hgpint : IntervalIntegrable gp volume a b := hgpc.intervalIntegrable_of_Icc hab
  have hFTC : (∫ t in a..b, gp t) = g b - g a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hg t (by simpa [uIcc_of_le hab] using ht)) hgpint
  have hvariation : (∫ t in a..b, |gp t|) = |g b - g a| := by
    rw [integral_abs_eq_abs_integral_of_constant_sign hab, hFTC]
    rcases le_total 0 A with hA | hA
    · right
      intro t _
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
    · left
      intro t _
      exact div_nonneg (by linarith) (sq_nonneg _)
  have hgbound : ∀ t ∈ Icc a b, |g t| ≤ eta⁻¹ := by
    intro t ht
    simpa [g, abs_inv] using (one_div_le_one_div_of_le heta (hsep t ht))
  let u := wave A B C
  let up : ℝ → ℂ := fun t => u t * ((q t : ℂ) * Complex.I)
  have hgpintC : IntervalIntegrable (fun t => (gp t : ℂ)) volume a b :=
    (Complex.continuous_ofReal.comp_continuousOn hgpc).intervalIntegrable_of_Icc hab
  have hparts := intervalIntegral.integral_deriv_mul_eq_sub (a := a) (b := b)
    (u := u) (v := fun t => (g t : ℂ)) (u' := up) (v' := fun t => (gp t : ℂ))
    (fun t _ => hasDerivAt_wave A B C t)
    (fun t ht => (hg t (by simpa [uIcc_of_le hab] using ht)).ofReal_comp)
    (by
      apply Continuous.intervalIntegrable
      exact (continuous_wave A B C).mul
        ((Complex.continuous_ofReal.comp (by unfold q slope; fun_prop)).mul continuous_const))
    hgpintC
  have hpoint : ∀ t ∈ Icc a b,
      up t * (g t : ℂ) + u t * (gp t : ℂ) =
        Complex.I * u t + u t * (gp t : ℂ) := by
    intro t ht
    dsimp [up, g]
    push_cast
    have hn : (q t : ℂ) ≠ 0 := by exact_mod_cast hq t ht
    field_simp
  have hi : (∫ t in a..b, Complex.I * u t + u t * (gp t : ℂ)) =
      u b * (g b : ℂ) - u a * (g a : ℂ) := by
    rw [← hparts]
    apply intervalIntegral.integral_congr
    intro t ht
    exact (hpoint t (by simpa [uIcc_of_le hab] using ht)).symm
  have huint := intervalIntegrable_wave A B C a b
  have hcorrint : IntervalIntegrable (fun t => u t * (gp t : ℂ)) volume a b :=
    hgpintC.continuousOn_mul (continuous_wave A B C).continuousOn
  rw [intervalIntegral.integral_add (huint.const_mul _) hcorrint,
    intervalIntegral.integral_const_mul] at hi
  have hc : ‖∫ t in a..b, u t * (gp t : ℂ)‖ ≤ |g b - g a| := by
    calc
      _ ≤ ∫ t in a..b, ‖u t * (gp t : ℂ)‖ :=
        intervalIntegral.norm_integral_le_integral_norm hab
      _ = ∫ t in a..b, |gp t| := by simp only [norm_mul, u, norm_wave, Complex.norm_real, one_mul, Real.norm_eq_abs]
      _ = _ := hvariation
  have he : ‖u b * (g b : ℂ) - u a * (g a : ℂ)‖ ≤ |g b| + |g a| := by
    simpa [u, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
      norm_sub_le (u b * (g b : ℂ)) (u a * (g a : ℂ))
  have hga := hgbound a (left_mem_Icc.mpr hab)
  have hgb := hgbound b (right_mem_Icc.mpr hab)
  have hv : |g b - g a| ≤ |g b| + |g a| := abs_sub _ _
  have hnorm := norm_sub_le (u b * (g b : ℂ) - u a * (g a : ℂ))
    (∫ t in a..b, u t * (gp t : ℂ))
  have hid : Complex.I * (∫ t in a..b, u t) =
      (u b * (g b : ℂ) - u a * (g a : ℂ)) -
        (∫ t in a..b, u t * (gp t : ℂ)) := by linear_combination hi
  rw [← hid, norm_mul, Complex.norm_I, one_mul] at hnorm
  dsimp [u] at hnorm
  rw [div_eq_mul_inv]
  linarith

/-- A second derivative test for a quadratic polynomial. Splitting at distance
`1 / sqrt |A|` from its stationary point gives the absolute constant `6`. -/
theorem norm_integral_wave_le_of_quadratic
    (A B C a b : ℝ) (hA : A ≠ 0) (hab : a ≤ b) :
    ‖∫ t in a..b, wave A B C t‖ ≤ 6 / Real.sqrt |A| := by
  let s := Real.sqrt |A|
  have hs : 0 < s := Real.sqrt_pos.mpr (abs_pos.mpr hA)
  have hss : s ^ 2 = |A| := Real.sq_sqrt (abs_nonneg A)
  let delta := s⁻¹
  have hd : 0 < delta := inv_pos.mpr hs
  let center := -B / (2 * A)
  let c := center - delta
  let d := center + delta
  have hcd : c ≤ d := by dsimp [c, d]; linarith
  let l := max (min c b) a
  let r := max (min d b) a
  have hal : a ≤ l := le_max_right _ _
  have hlb : l ≤ b := max_le (min_le_right _ _) hab
  have har : a ≤ r := le_max_right _ _
  have hrb : r ≤ b := max_le (min_le_right _ _) hab
  have hlr : l ≤ r := max_le_max (min_le_min_right b hcd) le_rfl
  have hmiddle : |r - l| ≤ 2 * delta := by
    have hmin : |min d b - min c b| ≤ |d - c| := by
      simpa using abs_min_sub_min_le_max d b c b
    have hmax := abs_max_sub_max_le_abs (min d b) (min c b) a
    have hdiff : |d - c| = 2 * delta := by
      rw [abs_of_nonneg (by linarith : 0 ≤ d - c)]
      dsimp [d, c]
      ring
    exact hmax.trans (hmin.trans_eq hdiff)
  have hsl : ∀ t, |slope A B t| = 2 * |A| * |t - center| := by
    intro t
    have heq : slope A B t = 2 * A * (t - center) := by
      dsimp [slope, center]
      field_simp
      ring
    rw [heq, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hscale : 2 * |A| * delta = 2 * s := by
    dsimp [delta]
    rw [← hss]
    field_simp
  have hleft : ‖∫ t in a..l, wave A B C t‖ ≤ 2 / s := by
    by_cases hac : a ≤ c
    · have hlc : l ≤ c := max_le (min_le_left _ _) hac
      have hsep : ∀ t ∈ Icc a l, 2 * s ≤ |slope A B t| := by
        intro t ht
        rw [hsl, ← hscale]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := neg_le_abs (t - center)
        dsimp [c] at hlc
        linarith [ht.2]
      have h := norm_integral_wave_le_of_slope A B C a l (2 * s) hal
        (by positivity) hsep
      have heq : 4 / (2 * s) = 2 / s := by ring
      simpa only [heq] using h
    · have hl : l = a := by
        have hca : c ≤ a := le_of_not_ge hac
        dsimp [l]
        rw [min_eq_left (hca.trans hab), max_eq_right hca]
      rw [hl, intervalIntegral.integral_same, norm_zero]
      positivity
  have hright : ‖∫ t in r..b, wave A B C t‖ ≤ 2 / s := by
    by_cases hdb : d ≤ b
    · have hdr : d ≤ r := by
        dsimp [r]
        rw [min_eq_left hdb]
        exact le_max_left _ _
      have hsep : ∀ t ∈ Icc r b, 2 * s ≤ |slope A B t| := by
        intro t ht
        rw [hsl, ← hscale]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := le_abs_self (t - center)
        dsimp [d] at hdr
        linarith [ht.1]
      have h := norm_integral_wave_le_of_slope A B C r b (2 * s) hrb
        (by positivity) hsep
      have heq : 4 / (2 * s) = 2 / s := by ring
      simpa only [heq] using h
    · have hr : r = b := by
        dsimp [r]
        rw [min_eq_right (le_of_not_ge hdb), max_eq_left hab]
      rw [hr, intervalIntegral.integral_same, norm_zero]
      positivity
  have hmid := (norm_integral_wave_le_length A B C l r).trans hmiddle
  have hsplit : (∫ t in a..l, wave A B C t) + (∫ t in l..r, wave A B C t) +
      (∫ t in r..b, wave A B C t) = ∫ t in a..b, wave A B C t := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_wave A B C a l) (intervalIntegrable_wave A B C l r),
      intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_wave A B C a r) (intervalIntegrable_wave A B C r b)]
  rw [← hsplit]
  calc
    _ ≤ ‖∫ t in a..l, wave A B C t‖ + ‖∫ t in l..r, wave A B C t‖ +
        ‖∫ t in r..b, wave A B C t‖ :=
      norm_add₃_le
    _ ≤ 6 / s := by
      dsimp [delta] at hmid
      simp only [div_eq_mul_inv] at hleft hright ⊢
      linarith

/-- The exponential of the difference of two centered quadratics, with the
paper's Fourier convention. Here `alpha = τ b` and `gamma = σ c`. -/
def centeredWave (alpha gamma x z : ℝ) : ℝ → ℂ :=
  wave (2 * Real.pi * (alpha - gamma))
    (2 * Real.pi * (-2 * alpha * x + 2 * gamma * z))
    (2 * Real.pi * (alpha * x ^ 2 - gamma * z ^ 2))

theorem centeredWave_eq_exp (alpha gamma x z t : ℝ) :
    centeredWave alpha gamma x z t =
      Complex.exp (((2 * Real.pi * (alpha * (t - x) ^ 2 - gamma * (t - z) ^ 2) : ℝ) : ℂ)
        * Complex.I) := by
  unfold centeredWave wave
  congr 3
  unfold phase
  ring

theorem centered_slope (alpha gamma x z t : ℝ) :
    slope (2 * Real.pi * (alpha - gamma))
      (2 * Real.pi * (-2 * alpha * x + 2 * gamma * z)) t =
        2 * Real.pi * (2 * (alpha - gamma) * (t - z) - 2 * alpha * (x - z)) := by
  unfold slope
  ring

/-- An explicit constant depending only on the size of the support interval
and the lower bound for `|τ b| / λ`. -/
def oscillationConstant (R m : ℝ) : ℝ :=
  4 * (R + 1) + 12 / Real.sqrt (m / (4 * (R + 1))) + 8 / m

theorem oscillationConstant_pos {R m : ℝ} (hR : 1 ≤ R) (hm : 0 < m) :
    0 < oscillationConstant R m := by
  unfold oscillationConstant
  positivity

/-- The uniform subinterval bound (3.5), in a slightly stronger form:
only the lower bound on `|τ b|` is needed. Neither coefficient has an upper
bound in this theorem. -/
theorem norm_integral_centeredWave_le
    (R m : ℝ) (hR : 1 ≤ R) (hm : 0 < m)
    (lambda alpha gamma x z a b : ℝ)
    (hlambda : 0 ≤ lambda) (halpha : m * lambda ≤ |alpha|)
    (hab : a ≤ b) (ha : z - R - 1 ≤ a) (hb : b ≤ z + R + 1) :
    ‖∫ t in a..b, centeredWave alpha gamma x z t‖ ≤
      oscillationConstant R m / Real.sqrt (1 + lambda * |x - z|) := by
  let L := lambda * |x - z|
  let k := m / (4 * (R + 1))
  let A := 2 * Real.pi * (alpha - gamma)
  let B := 2 * Real.pi * (-2 * alpha * x + 2 * gamma * z)
  let C := 2 * Real.pi * (alpha * x ^ 2 - gamma * z ^ 2)
  let N := ‖∫ t in a..b, centeredWave alpha gamma x z t‖
  have hL : 0 ≤ L := mul_nonneg hlambda (abs_nonneg _)
  have hk : 0 < k := by dsimp [k]; positivity
  have hkprod : k * (R + 1) = m / 4 := by
    dsimp [k]
    field_simp
  have hroot : 0 < Real.sqrt (1 + L) := Real.sqrt_pos.mpr (by linarith)
  have hroot_sq := Real.sq_sqrt (show 0 ≤ 1 + L by linarith)
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hnn : 0 ≤ N := norm_nonneg _
  have hKsmall : 4 * (R + 1) ≤ oscillationConstant R m := by
    unfold oscillationConstant
    linarith [show 0 ≤ 12 / Real.sqrt (m / (4 * (R + 1))) by positivity,
      show 0 ≤ 8 / m by positivity]
  have hKquad : 12 / Real.sqrt k ≤ oscillationConstant R m := by
    dsimp [oscillationConstant, k]
    linarith [show 0 ≤ 8 / m by positivity]
  have hKslope : 8 / m ≤ oscillationConstant R m := by
    unfold oscillationConstant
    linarith [show 0 ≤ 12 / Real.sqrt (m / (4 * (R + 1))) by positivity]
  apply (le_div_iff₀ hroot).mpr
  change N * Real.sqrt (1 + L) ≤ oscillationConstant R m
  by_cases hsmall : L ≤ 1
  · have hlen : |b - a| ≤ 2 * (R + 1) := by
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      linarith
    have hN : N ≤ 2 * (R + 1) :=
      (norm_integral_wave_le_length A B C a b).trans hlen
    have hsqrt : Real.sqrt (1 + L) ≤ 2 := by nlinarith [Real.sqrt_nonneg (1 + L)]
    have hmul := mul_le_mul hN hsqrt (Real.sqrt_nonneg _) (by linarith : 0 ≤ 2 * (R + 1))
    exact (by nlinarith : N * Real.sqrt (1 + L) ≤ 4 * (R + 1)).trans hKsmall
  · have hlarge : 1 < L := lt_of_not_ge hsmall
    have hsL : 0 < Real.sqrt L := Real.sqrt_pos.mpr (by linarith)
    have hsLsq := Real.sq_sqrt hL
    have hcompare : Real.sqrt (1 + L) ≤ 2 * Real.sqrt L := by
      nlinarith [Real.sqrt_nonneg (1 + L)]
    have hcompare' : Real.sqrt (1 + L) ≤ 2 * L := by
      nlinarith [Real.sqrt_nonneg (1 + L)]
    by_cases hquadratic : k * L ≤ |alpha - gamma|
    · have hAabs : k * L ≤ |A| := by
        dsimp [A]
        rw [abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
        exact hquadratic.trans (le_mul_of_one_le_left (abs_nonneg _) hpi)
      have hAnonzero : A ≠ 0 := by
        apply abs_pos.mp
        exact lt_of_lt_of_le (mul_pos hk (by linarith)) hAabs
      have hsA : 0 < Real.sqrt |A| := Real.sqrt_pos.mpr (abs_pos.mpr hAnonzero)
      have hsprod : Real.sqrt k * Real.sqrt L ≤ Real.sqrt |A| := by
        rw [← Real.sqrt_mul hk.le]
        exact Real.sqrt_le_sqrt hAabs
      have hN := norm_integral_wave_le_of_quadratic A B C a b hAnonzero hab
      have hNmul : N * Real.sqrt |A| ≤ 6 := (le_div_iff₀ hsA).mp hN
      have hNscale : N * (Real.sqrt k * Real.sqrt L) ≤ 6 :=
        (mul_le_mul_of_nonneg_left hsprod hnn).trans hNmul
      have hcomp := mul_le_mul_of_nonneg_left hcompare
        (mul_nonneg hnn (Real.sqrt_nonneg k))
      have hbound : N * Real.sqrt (1 + L) ≤ 12 / Real.sqrt k := by
        apply (le_div_iff₀ (Real.sqrt_pos.mpr hk)).mpr
        nlinarith
      exact hbound.trans hKquad
    · have hD : |alpha - gamma| ≤ k * L := (lt_of_not_ge hquadratic).le
      have hsep : ∀ t ∈ Icc a b, m * L ≤ |slope A B t| := by
        intro t ht
        have htz : |t - z| ≤ R + 1 := by
          apply abs_le.mpr
          constructor <;> linarith [ht.1, ht.2]
        have herror := mul_le_mul hD htz (abs_nonneg (t - z)) (by positivity : 0 ≤ k * L)
        have hkL : k * L * (R + 1) = m * L / 4 := by
          calc
            _ = (k * (R + 1)) * L := by ring
            _ = _ := by rw [hkprod]; ring
        rw [hkL] at herror
        have hmain : m * L ≤ |alpha| * |x - z| := by
          dsimp [L]
          nlinarith [mul_le_mul_of_nonneg_right halpha (abs_nonneg (x - z))]
        have hrev : 2 * |alpha| * |x - z| - 2 * |alpha - gamma| * |t - z| ≤
            |2 * (alpha - gamma) * (t - z) - 2 * alpha * (x - z)| := by
          have h := abs_sub_abs_le_abs_sub (2 * alpha * (x - z))
            (2 * (alpha - gamma) * (t - z))
          simpa only [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
            abs_sub_comm] using h
        have hfirst : m * L ≤
            |2 * (alpha - gamma) * (t - z) - 2 * alpha * (x - z)| := by
          nlinarith
        dsimp [A, B]
        rw [centered_slope, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
        exact hfirst.trans (le_mul_of_one_le_left (abs_nonneg _) hpi)
      have hN := norm_integral_wave_le_of_slope A B C a b (m * L) hab
        (mul_pos hm (by linarith)) hsep
      have hNm : N * (m * L) ≤ 4 := (le_div_iff₀ (mul_pos hm (by linarith))).mp hN
      have hcomp := mul_le_mul_of_nonneg_left hcompare' hnn
      have hbound : N * Real.sqrt (1 + L) ≤ 8 / m := by
        apply (le_div_iff₀ hm).mpr
        nlinarith [mul_le_mul_of_nonneg_right hcomp hm.le]
      exact hbound.trans hKslope

/-- The one-coordinate phase `Pᵢ(t)` in (3.4). -/
def quadraticPhase (tau sigma bcoef ccoef x z t : ℝ) : ℝ :=
  tau * bcoef * (t - x) ^ 2 - sigma * ccoef * (t - z) ^ 2

/-- Equation (3.5) with the paper's parameters and negative-half-power
notation. The omitted upper bounds from (3.1) are not needed in dimension one. -/
theorem norm_integral_quadraticPhase_le
    (R c0 bmin : ℝ) (hR : 1 ≤ R) (hc0 : 0 < c0) (hbmin : 0 < bmin)
    (lambda tau sigma bcoef ccoef x z a b : ℝ)
    (hlambda : 1 ≤ lambda) (htau : c0 * lambda ≤ |tau|) (hcoef : bmin ≤ bcoef)
    (hab : a ≤ b) (ha : z - R - 1 ≤ a) (hb : b ≤ z + R + 1) :
    ‖∫ t in a..b,
        Complex.exp (((2 * Real.pi * quadraticPhase tau sigma bcoef ccoef x z t : ℝ) : ℂ)
          * Complex.I)‖ ≤
      oscillationConstant R (c0 * bmin) *
        (1 + lambda * |x - z|) ^ (-(1 / 2 : ℝ)) := by
  have hbpos : 0 < bcoef := lt_of_lt_of_le hbmin hcoef
  have halpha : (c0 * bmin) * lambda ≤ |tau * bcoef| := by
    calc
      _ = (c0 * lambda) * bmin := by ring
      _ ≤ |tau| * bcoef := mul_le_mul htau hcoef hbmin.le (abs_nonneg tau)
      _ = _ := by rw [abs_mul, abs_of_pos hbpos]
  have h := norm_integral_centeredWave_le R (c0 * bmin) hR (mul_pos hc0 hbmin)
    lambda (tau * bcoef) (sigma * ccoef) x z a b (by linarith) halpha hab ha hb
  rw [Real.rpow_neg (by positivity : 0 ≤ 1 + lambda * |x - z|),
    ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
  simpa only [centeredWave_eq_exp, quadraticPhase] using h

/-- Quantifiers making the uniformity in (3.5) explicit. One constant works
for every frequency, every admissible coefficient and every subinterval. -/
theorem exists_uniform_subinterval_bound
    (R c0 bmin : ℝ) (hR : 1 ≤ R) (hc0 : 0 < c0) (hbmin : 0 < bmin) :
    ∃ K : ℝ, 0 < K ∧ ∀ (lambda tau sigma bcoef ccoef x z a b : ℝ),
      1 ≤ lambda → c0 * lambda ≤ |tau| → bmin ≤ bcoef →
      a ≤ b → z - R - 1 ≤ a → b ≤ z + R + 1 →
      ‖∫ t in a..b,
          Complex.exp (((2 * Real.pi * quadraticPhase tau sigma bcoef ccoef x z t : ℝ) : ℂ)
            * Complex.I)‖ ≤ K * (1 + lambda * |x - z|) ^ (-(1 / 2 : ℝ)) := by
  refine ⟨oscillationConstant R (c0 * bmin),
    oscillationConstant_pos hR (mul_pos hc0 hbmin), ?_⟩
  intro lambda tau sigma bcoef ccoef x z a b hlambda htau hcoef hab ha hb
  exact norm_integral_quadraticPhase_le R c0 bmin hR hc0 hbmin
    lambda tau sigma bcoef ccoef x z a b hlambda htau hcoef hab ha hb

/-- The primitive `Gᵢ` in (3.7), ready for integration by parts in the next module. -/
def quadraticPrimitive (R alpha gamma x z t : ℝ) : ℂ :=
  ∫ v in (z - R - 1)..t, centeredWave alpha gamma x z v

theorem hasDerivAt_quadraticPrimitive (R alpha gamma x z t : ℝ) :
    HasDerivAt (quadraticPrimitive R alpha gamma x z)
      (centeredWave alpha gamma x z t) t := by
  have hcont : Continuous (centeredWave alpha gamma x z) := continuous_wave _ _ _
  exact intervalIntegral.integral_hasDerivAt_right (hcont.intervalIntegrable _ _)
    hcont.aestronglyMeasurable.stronglyMeasurableAtFilter hcont.continuousAt

/-- Uniform bound for the primitive on the enlarged support interval. -/
theorem norm_quadraticPrimitive_le
    (R m : ℝ) (hR : 1 ≤ R) (hm : 0 < m)
    (lambda alpha gamma x z t : ℝ)
    (hlambda : 0 ≤ lambda) (halpha : m * lambda ≤ |alpha|)
    (ht : t ∈ Icc (z - R - 1) (z + R + 1)) :
    ‖quadraticPrimitive R alpha gamma x z t‖ ≤
      oscillationConstant R m / Real.sqrt (1 + lambda * |x - z|) :=
  norm_integral_centeredWave_le R m hR hm lambda alpha gamma x z
    (z - R - 1) t hlambda halpha ht.1 le_rfl ht.2

end StrongSpherical.Quadratic1D
