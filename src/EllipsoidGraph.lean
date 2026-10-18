import QuadraticGraphL2

/-!
# From local ellipsoid radii to quadratic graphs

This module starts the reduction in Section 4. It records the actual slice
coordinates, the defining-function identity, the uniform graph coefficients,
and the reparametrization of the normal-frequency kernel.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators FourierTransform ComplexConjugate

namespace StrongSpherical.EllipsoidGraph
open QuadraticGraph GramKernel AmplitudeBounds QuadraticGraphL2
variable {m : ℕ}

/-- Append the normal coordinate to a spatial point. -/
def slicePoint (x : Space m) (h : ℝ) : Space (m + 1) :=
  WithLp.toLp 2 (Fin.snoc (fun i => x i) h)

@[simp] theorem slicePoint_castSucc (x : Space m) (h : ℝ) (i : Fin m) :
    slicePoint x h i.castSucc = x i := by simp [slicePoint]

@[simp] theorem slicePoint_last (x : Space m) (h : ℝ) :
    slicePoint x h (Fin.last m) = h := by simp [slicePoint]

/-- The substitution y=(u,h+sqrt(s)) in (4.3). -/
def liftedInput (h : ℝ) (v : Space (m + 1)) : Space (m + 1) :=
  slicePoint (spatialInput v) (h + Real.sqrt (normalInput v))

/-- The displacement x-y after the substitution, independent of the slice height. -/
def patchOffset (x : Space m) (v : Space (m + 1)) : Space (m + 1) :=
  slicePoint (x - spatialInput v) (-Real.sqrt (normalInput v))

theorem slice_sub_liftedInput (x : Space m) (h : ℝ) (v : Space (m + 1)) :
    slicePoint x h - liftedInput h v = patchOffset x v := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [liftedInput, patchOffset]
  · simp [liftedInput, patchOffset]

/-- The graph coefficients in (4.4), with only coordinatewise measurability of the radii. -/
def coefficients (r : Space m → Radii (m + 1))
    (hr : ∀ j, Measurable (fun x => (r x).1 j)) : GraphCoefficients m where
  constant x := (r x).1 (Fin.last m) ^ 2
  quadratic x i := (r x).1 (Fin.last m) ^ 2 / (r x).1 i.castSucc ^ 2
  measurable_constant := (hr _).pow_const 2
  measurable_quadratic i := ((hr (Fin.last m)).pow_const 2).div ((hr i.castSucc).pow_const 2)

/-- The exact defining-function identity in (4.4). -/
theorem graphGap_eq_normal_sq_mul_form (r : Space m → Radii (m + 1))
    (hr : ∀ j, Measurable (fun x => (r x).1 j))
    (x : Space m) (h : ℝ) (v : Space (m + 1)) (hs : 0 ≤ normalInput v) :
    graphGap (coefficients r hr) x v =
      (r x).1 (Fin.last m) ^ 2 * ellipsoidForm (slicePoint x h) (r x) (liftedInput h v) := by
  unfold graphGap graph coefficients ellipsoidForm
  rw [Fin.sum_univ_castSucc]
  simp only [liftedInput, slicePoint_castSucc, slicePoint_last, add_sub_cancel_left, Real.sq_sqrt hs]
  rw [mul_sub, mul_add, Finset.mul_sum]
  have hnormal : (r x).1 (Fin.last m) ^ 2 * (normalInput v / (r x).1 (Fin.last m) ^ 2) = normalInput v := by
    field_simp [ne_of_gt ((r x).2 _)]
  rw [hnormal]
  have hsum : (∑ i : Fin m, (r x).1 (Fin.last m) ^ 2 *
      ((spatialInput v i - x i) ^ 2 / (r x).1 i.castSucc ^ 2)) =
      ∑ i : Fin m, (r x).1 (Fin.last m) ^ 2 / (r x).1 i.castSucc ^ 2 * (spatialInput v i - x i) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsum]
  ring

theorem ellipsoidForm_eq_graphGap_div (r : Space m → Radii (m + 1))
    (hr : ∀ j, Measurable (fun x => (r x).1 j))
    (x : Space m) (h : ℝ) (v : Space (m + 1)) (hs : 0 ≤ normalInput v) :
    ellipsoidForm (slicePoint x h) (r x) (liftedInput h v) =
      graphGap (coefficients r hr) x v / (r x).1 (Fin.last m) ^ 2 := by
  apply (eq_div_iff (pow_ne_zero _ (ne_of_gt ((r x).2 _)))).2
  simpa only [mul_comm] using (graphGap_eq_normal_sq_mul_form r hr x h v hs).symm

/-- The uniform coefficient bounds in (4.8). -/
theorem coefficients_bounds (r : Space m → Radii (m + 1))
    (hr : ∀ j, Measurable (fun x => (r x).1 j))
    (hlocal : ∀ x, r x ∈ localRadii (m + 1)) (x : Space m) (i : Fin m) :
    (1 / 4 : ℝ) ≤ (coefficients r hr).quadratic x i ∧
      (coefficients r hr).quadratic x i ≤ 4 := by
  have hn := hlocal x (Fin.last m)
  have hi := hlocal x i.castSucc
  rcases hn with ⟨hn1, hn2⟩
  rcases hi with ⟨hi1, hi2⟩
  have hnlo : 1 ≤ (r x).1 (Fin.last m) ^ 2 := by nlinarith [sq_nonneg ((r x).1 (Fin.last m) - 1)]
  have hnhi : (r x).1 (Fin.last m) ^ 2 ≤ 4 := by nlinarith
  have hilo : 1 ≤ (r x).1 i.castSucc ^ 2 := by nlinarith [sq_nonneg ((r x).1 i.castSucc - 1)]
  have hihi : (r x).1 i.castSucc ^ 2 ≤ 4 := by nlinarith
  have hipos : 0 < (r x).1 i.castSucc ^ 2 := sq_pos_of_pos ((r x).2 _)
  constructor
  · apply (le_div_iff₀ hipos).2
    nlinarith
  · apply (div_le_iff₀ hipos).2
    nlinarith

/-- The inverse Fourier integral uses the same positive exponential as `oscillation`. -/
theorem inverseFourier_eq_integral (beta : ℝ → ℂ) (t : ℝ) :
    (𝓕⁻ beta) t = ∫ tau, beta tau * oscillation (tau * t) := by
  rw [Real.fourierInv_eq']
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun tau => by
    simp only [Real.inner_apply, smul_eq_mul, oscillation]
    ring

/-- The exact normal-frequency change of variables in (4.5). -/
theorem frequency_reparametrization (beta : ℝ → ℂ) (lambda d t : ℝ)
    (hlambda : 0 < lambda) (hd : 0 < d) :
    (lambda : ℂ) * (𝓕⁻ beta) (lambda * t / d) =
      (d : ℂ) * ∫ tau, beta (d * tau / lambda) * oscillation (tau * t) := by
  let F : ℝ → ℂ := fun xi => beta xi * oscillation (xi * (lambda * t / d))
  have heq : (fun tau => F ((d / lambda) * tau)) =
      (fun tau => beta (d * tau / lambda) * oscillation (tau * t)) := by
    funext tau
    dsimp [F]
    congr 1
    · congr 1
      ring
    · congr 1
      field_simp
  have hscale := Measure.integral_comp_mul_left F (d / lambda)
  rw [heq, abs_of_pos (inv_pos.2 (div_pos hd hlambda))] at hscale
  rw [hscale, inverseFourier_eq_integral]
  change (lambda : ℂ) * (∫ xi, F xi) = (d : ℂ) * ((d / lambda)⁻¹ • ∫ xi, F xi)
  rw [Complex.real_smul]
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hd.ne']

end StrongSpherical.EllipsoidGraph

namespace StrongSpherical.EllipsoidGraph
open QuadraticGraph GramKernel AmplitudeBounds QuadraticGraphL2
variable {m : ℕ}

theorem local_radius_sq_bounds {n : ℕ} (r : Radii n) (hr : r ∈ localRadii n) (j : Fin n) :
    1 ≤ r.1 j ^ 2 ∧ r.1 j ^ 2 ≤ 4 := by
  obtain ⟨h1, h2⟩ := hr j
  constructor <;> nlinarith [sq_nonneg (r.1 j - 1)]

/-- The frequency amplitude q_x in (4.7). -/
def frequencyAmplitude (r : Space m → Radii (m + 1)) (beta : ℝ → ℂ)
    (lambda : ℝ) (x : Space m) (tau : ℝ) : ℂ :=
  beta ((r x).1 (Fin.last m) ^ 2 * tau / lambda)

theorem measurable_frequencyAmplitude (r : Space m → Radii (m + 1))
    (hr : ∀ j, Measurable (fun x => (r x).1 j))
    (beta : ℝ → ℂ) (hbeta : Measurable beta) (lambda : ℝ) :
    Measurable (fun p : Space m × ℝ => frequencyAmplitude r beta lambda p.1 p.2) :=
  hbeta.comp ((((hr (Fin.last m)).comp measurable_fst).pow_const 2).mul measurable_snd |>.div measurable_const)

/-- The frequency band λ/8≤|τ|≤2λ in (4.8), proved from the original beta support. -/
theorem frequencyAmplitude_band (r : Space m → Radii (m + 1))
    (hlocal : ∀ x, r x ∈ localRadii (m + 1)) (beta : ℝ → ℂ)
    (hsupport : Function.support beta ⊆ {t | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2})
    (lambda : ℝ) (hlambda : 0 < lambda) (x : Space m) (tau : ℝ)
    (htau : frequencyAmplitude r beta lambda x tau ≠ 0) :
    lambda / 8 ≤ |tau| ∧ |tau| ≤ 2 * lambda := by
  have hb := hsupport htau
  have hd := local_radius_sq_bounds (r x) (hlocal x) (Fin.last m)
  have heq : |(r x).1 (Fin.last m) ^ 2 * tau / lambda| =
      (r x).1 (Fin.last m) ^ 2 * |tau| / lambda := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos hlambda]
  change (1 / 2 : ℝ) ≤ |(r x).1 (Fin.last m) ^ 2 * tau / lambda| ∧
    |(r x).1 (Fin.last m) ^ 2 * tau / lambda| ≤ 2 at hb
  rw [heq] at hb
  have hlo := (le_div_iff₀ hlambda).mp hb.1
  have hhi := (div_le_iff₀ hlambda).mp hb.2
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hd.2) (abs_nonneg tau)]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hd.1) (abs_nonneg tau)]

/-- All frequency hypotheses of Lemma 3.2 follow uniformly from beta and local radii. -/
theorem frequencyAmplitude_control (r : Space m → Radii (m + 1))
    (hr : ∀ j, Measurable (fun x => (r x).1 j))
    (hlocal : ∀ x, r x ∈ localRadii (m + 1)) (beta : ℝ → ℂ) (hbeta : Measurable beta)
    (B : ℝ) (hbound : ∀ t, ‖beta t‖ ≤ B)
    (hsupport : Function.support beta ⊆ {t | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2})
    (lambda : ℝ) (hlambda : 0 < lambda) (x : Space m) :
    FrequencyControl (1 / 8) (max 2 B) lambda (frequencyAmplitude r beta lambda x) := by
  refine ⟨(measurable_frequencyAmplitude r hr beta hbeta lambda).comp
    (measurable_const.prodMk measurable_id), ?_, ?_⟩
  · intro tau
    exact (hbound _).trans (le_max_right _ _)
  · intro tau htau
    have h := frequencyAmplitude_band r hlocal beta hsupport lambda hlambda x tau htau
    constructor
    · linarith [h.1]
    · exact h.2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlambda.le)

theorem frequencyAmplitude_indicator_bound (r : Space m → Radii (m + 1))
    (hr : ∀ j, Measurable (fun x => (r x).1 j))
    (hlocal : ∀ x, r x ∈ localRadii (m + 1)) (beta : ℝ → ℂ) (hbeta : Measurable beta)
    (B : ℝ) (hbound : ∀ t, ‖beta t‖ ≤ B)
    (hsupport : Function.support beta ⊆ {t | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2})
    (lambda : ℝ) (hlambda : 0 < lambda) :
    ∀ x tau, ‖frequencyAmplitude r beta lambda x tau‖ ≤
      max 2 B * (frequencyAnnulus (1 / 8) (max 2 B) lambda).indicator (fun _ => 1) tau := by
  intro x tau
  have hqc := frequencyAmplitude_control r hr hlocal beta hbeta B hbound hsupport lambda hlambda x
  by_cases ht : tau ∈ frequencyAnnulus (1 / 8) (max 2 B) lambda
  · simpa only [indicator_of_mem ht, mul_one] using hqc.norm_le tau
  · have hz : frequencyAmplitude r beta lambda x tau = 0 := by
      by_contra hne
      exact ht (hqc.support_subset hne)
    simp only [hz, norm_zero, indicator_of_notMem ht, mul_zero, le_refl]

/-- Reparametrization (4.5) at the actual ellipsoid defining function. -/
theorem normalFrequency_eq_graphKernel (r : Space m → Radii (m + 1))
    (hr : ∀ j, Measurable (fun x => (r x).1 j)) (beta : ℝ → ℂ)
    (lambda : ℝ) (hlambda : 0 < lambda) (x : Space m) (h : ℝ)
    (v : Space (m + 1)) (hs : 0 ≤ normalInput v) :
    (lambda : ℂ) * (𝓕⁻ beta) (lambda * ellipsoidForm (slicePoint x h) (r x) (liftedInput h v)) =
      ((r x).1 (Fin.last m) ^ 2 : ℝ) *
        frequencyKernel (coefficients r hr) (frequencyAmplitude r beta lambda) x v := by
  rw [ellipsoidForm_eq_graphGap_div r hr x h v hs, ← mul_div_assoc]
  exact frequency_reparametrization beta lambda ((r x).1 (Fin.last m) ^ 2)
    (graphGap (coefficients r hr) x v) hlambda (sq_pos_of_pos ((r x).2 _))

/-- The derivative of the normal-coordinate substitution in (4.3). -/
theorem hasDerivAt_liftedNormal (h s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun t => h + Real.sqrt t) (1 / (2 * Real.sqrt s)) s :=
  (Real.hasDerivAt_sqrt hs.ne').const_add h

/-- The reciprocal Jacobian of y_n=h+sqrt(s). -/
def sqrtJacobian (v : Space (m + 1)) : ℂ := ((2 * Real.sqrt (normalInput v) : ℝ) : ℂ)⁻¹

/-- The genuine amplitude in (4.6), extended by zero when s≤0. -/
def graphAmplitude (chi : Space (m + 1) → ℂ) (r : Space m → Radii (m + 1))
    (x : Space m) (v : Space (m + 1)) : ℂ :=
  if 0 < normalInput v then
    (((r x).1 (Fin.last m) ^ 2 : ℝ) : ℂ) * sqrtJacobian v * (dilationJacobian (r x) : ℂ)⁻¹ *
      chi (inverseDilation (r x) (patchOffset x v))
  else 0

theorem inverseDilation_neg {n : ℕ} (r : Radii n) (v : Space n) :
    inverseDilation r (-v) = -inverseDilation r v := by
  ext j
  change (r.1 j)⁻¹ * (-v j) = -((r.1 j)⁻¹ * v j)
  ring

/-- The actual dilated kernel, with its substitution Jacobian, equals the
quadratic-graph input kernel. This is a pointwise identity before integration. -/
theorem inputKernel_eq_changed_kernel (chi : Space (m + 1) → ℂ)
    (r : Space m → Radii (m + 1)) (hr : ∀ j, Measurable (fun x => (r x).1 j))
    (beta : ℝ → ℂ) (lambda : ℝ) (hlambda : 0 < lambda)
    (x : Space m) (h : ℝ) (v : Space (m + 1)) (hs : 0 < normalInput v) :
    inputKernel (coefficients r hr) (graphAmplitude chi r) (frequencyAmplitude r beta lambda) x v =
      sqrtJacobian v * dilatedNormalKernel chi beta lambda (r x) (slicePoint x h - liftedInput h v) := by
  have harg : ‖inverseDilation (r x) (slicePoint x h - liftedInput h v)‖ ^ 2 - 1 =
      ellipsoidForm (slicePoint x h) (r x) (liftedInput h v) := by
    rw [ellipsoidForm_eq_norm_sq, ← neg_sub (slicePoint x h) (liftedInput h v), inverseDilation_neg, norm_neg]
  have hfrequency := normalFrequency_eq_graphKernel r hr beta lambda hlambda x h v hs.le
  rw [inputKernel, graphAmplitude, if_pos hs, dilatedNormalKernel, dilatedKernel, normalKernel, harg]
  simp only [slice_sub_liftedInput]
  calc
    _ = sqrtJacobian v * (dilationJacobian (r x) : ℂ)⁻¹ *
        chi (inverseDilation (r x) (patchOffset x v)) *
        ((((r x).1 (Fin.last m) ^ 2 : ℝ) : ℂ) *
          frequencyKernel (coefficients r hr) (frequencyAmplitude r beta lambda) x v) := by ring
    _ = _ := by rw [← hfrequency]; ring

set_option maxHeartbeats 1000000 in
/-- Apply the proved Lemma 3.2 with the actual ellipsoid graph coefficients and
frequency amplitudes. Input regularity and derivative bounds of the amplitude
remain explicit, for later verification for `graphAmplitude chi r`. -/
theorem exists_uniform_slice_bound (m : ℕ) (R M B : ℝ) (hR : 1 ≤ R) (hM : 0 ≤ M)
    (beta : ℝ → ℂ) (hbeta : Measurable beta) (hbound : ∀ t, ‖beta t‖ ≤ B)
    (hsupport : Function.support beta ⊆ {t | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ lambda : ℝ, 1 ≤ lambda →
      ∀ (r : Space m → Radii (m + 1)) (hr : ∀ j, Measurable (fun x => (r x).1 j)),
        (∀ x, r x ∈ localRadii (m + 1)) →
        ∀ a : Space m → Space (m + 1) → ℂ,
          (∀ x, ContDiff ℝ (m + 4 : ℕ) (a x)) →
          (∀ x, InputDerivativeBound (m + 4) M (a x)) →
          (∀ x, Function.support (a x) ⊆ inputSupport R x) →
          (∀ v, Measurable (fun x => a x v)) →
          ∀ g : Space (m + 1) → ℂ, MemLp g 2 volume →
            MemLp (graphOperator (coefficients r hr) a (frequencyAmplitude r beta lambda) g) 2 volume ∧
            eLpNorm (graphOperator (coefficients r hr) a (frequencyAmplitude r beta lambda) g) 2 volume ≤
              ENNReal.ofReal (C * lambda ^ (1 / 2 - (m : ℝ) / 4)) * eLpNorm g 2 volume := by
  have hC0 : 0 < max (2 : ℝ) B := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  obtain ⟨C, hC, hlemma⟩ := lemma_3_2 m R (1 / 8) (max 2 B) (1 / 4) M
    hR (by norm_num) hC0 (by norm_num) hM
  refine ⟨C, hC, ?_⟩
  intro lambda hlambda r hr hlocal a ha hDa hs hameas g hg
  exact hlemma lambda hlambda (coefficients r hr) a (frequencyAmplitude r beta lambda) ha hDa hs hameas
    (measurable_frequencyAmplitude r hr beta hbeta lambda)
    (frequencyAmplitude_indicator_bound r hr hlocal beta hbeta B hbound hsupport lambda (by linarith))
    (fun x i => (coefficients_bounds r hr hlocal x i).1) g hg

end StrongSpherical.EllipsoidGraph
