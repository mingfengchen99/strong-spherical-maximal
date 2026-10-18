import RectangularMaximal
import HardyLittlewoodLp

/-! # Finite Lᑫ bounds for the actual iterated coordinate maximal operator -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Topology

namespace StrongSpherical.RectangularMaximalLp
open HardyLittlewoodOneDim RectangularMaximal QuadraticGraph EllipsoidGraph

/-- The ENNReal power is measurable even when the input attains infinity. -/
lemma measurable_ennreal_rpow {X : Type*} [MeasurableSpace X]
    {F : X → ℝ≥0∞} (hF : Measurable F) (q : ℝ) :
    Measurable (fun x => F x ^ q) :=
  ENNReal.continuous_rpow_const.measurable.comp hF

set_option maxHeartbeats 1000000 in
/-- Tensorization of the genuine one-dimensional energy estimate. The argument
uses Tonelli only, so neither finite input energy nor finite fiber energy is required. -/
theorem controllingMaximal_rpow_of_oneDim (q : ℝ) (A : ℝ≥0∞)
    (hA : ∀ F : ℝ → ℝ≥0∞, Measurable F →
      (∫⁻ x, rationalMaximal F x ^ q) ≤ A * ∫⁻ x, F x ^ q)
    (n : ℕ) (F : Space n → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, controllingMaximal n F x ^ q) ≤ A ^ n * ∫⁻ x, F x ^ q := by
  induction n with
  | zero => simp [controllingMaximal]
  | succ n ih =>
    let G : ℝ × Space n → ℝ≥0∞ := fun p =>
      controllingMaximal n (fun u => F (slicePoint u p.1)) p.2
    have hFs : Measurable (fun p : ℝ × Space n => F (slicePoint p.2 p.1)) := by
      apply hF.comp
      unfold slicePoint
      fun_prop
    have hG : Measurable G := measurable_controllingMaximal_with_param n _ hFs
    have hQ := measurable_rationalMaximal_with_param
      (fun p : Space n × ℝ => G (p.2, p.1)) (hG.comp measurable_swap)
    have hQ' : Measurable (fun p : ℝ × Space n =>
        rationalMaximal (fun t => G (t, p.2)) p.1) := by
      have hm : Measurable (fun p : ℝ × Space n => (p.2, p.1)) := measurable_swap
      simpa only [Function.comp_def] using hQ.comp hm
    have hslices : (∫⁻ v, controllingMaximal (n + 1) F v ^ q) =
        ∫⁻ h, ∫⁻ u : Space n, rationalMaximal (fun t => G (t, u)) h ^ q := by
      simpa [controllingMaximal, normalInput, spatialInput, G] using
        (SliceMeasure.lintegral_slices
          (fun v => controllingMaximal (n + 1) F v ^ q)
          (measurable_ennreal_rpow (measurable_controllingMaximal (n + 1) F hF) q))
    calc
      _ = ∫⁻ h, ∫⁻ u : Space n, rationalMaximal (fun t => G (t, u)) h ^ q := hslices
      _ = ∫⁻ u : Space n, ∫⁻ h, rationalMaximal (fun t => G (t, u)) h ^ q :=
        lintegral_lintegral_swap (measurable_ennreal_rpow hQ' q).aemeasurable
      _ ≤ ∫⁻ u : Space n, A * ∫⁻ t, G (t, u) ^ q := by
        apply lintegral_mono
        intro u
        exact hA _ (hG.comp (measurable_id.prodMk measurable_const))
      _ = A * ∫⁻ u : Space n, ∫⁻ t, G (t, u) ^ q :=
        lintegral_const_mul _ (measurable_ennreal_rpow hG q).lintegral_prod_left'
      _ = A * ∫⁻ t, ∫⁻ u : Space n, G (t, u) ^ q := by
        have hh : (∫⁻ t, ∫⁻ u : Space n, G (t, u) ^ q) =
            ∫⁻ u : Space n, ∫⁻ t, G (t, u) ^ q :=
          lintegral_lintegral_swap (measurable_ennreal_rpow hG q).aemeasurable
        rw [← hh]
      _ ≤ A * ∫⁻ t, A ^ n * ∫⁻ u : Space n, F (slicePoint u t) ^ q := by
        gcongr with t
        exact ih _ (hFs.comp (measurable_const.prodMk measurable_id))
      _ = A ^ (n + 1) * ∫⁻ v, F v ^ q := by
        rw [lintegral_const_mul _ (measurable_ennreal_rpow hFs q).lintegral_prod_right,
          ← SliceMeasure.lintegral_slices _ (measurable_ennreal_rpow hF q), pow_succ]
        ring

/-- The finite positive-exponent norm identity needs no measurability or
finiteness assumption for an extended-valued input. -/
theorem eLpNorm_ofReal_rpow {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : X → ℝ≥0∞) (q : ℝ) (hq : 0 < q) :
    eLpNorm F (ENNReal.ofReal q) μ ^ q = ∫⁻ x, F x ^ q ∂μ := by
  rw [eLpNorm_eq_eLpNorm' (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq.le]
  simpa only [enorm_eq_self] using
    (lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := F) (μ := μ) hq).symm

/-- Taking the q-th root preserves the endpoint cases zero and infinity. -/
theorem eLpNorm_controllingMaximal_of_oneDim (q : ℝ) (hq : 0 < q)
    (A : ℝ) (hA : 0 < A)
    (henergy : ∀ F : ℝ → ℝ≥0∞, Measurable F →
      (∫⁻ x, rationalMaximal F x ^ q) ≤ ENNReal.ofReal A * ∫⁻ x, F x ^ q)
    (n : ℕ) (F : Space n → ℝ≥0∞) (hF : Measurable F) :
    eLpNorm (controllingMaximal n F) (ENNReal.ofReal q) volume ≤
      ENNReal.ofReal ((A ^ n) ^ (1 / q)) * eLpNorm F (ENNReal.ofReal q) volume := by
  have hcoefficient : ENNReal.ofReal ((A ^ n) ^ (1 / q)) ^ q = ENNReal.ofReal A ^ n := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (pow_nonneg hA.le n) (by positivity),
      ← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one,
      ENNReal.ofReal_pow hA.le]
  apply (ENNReal.rpow_le_rpow_iff hq).mp
  rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le, hcoefficient,
    eLpNorm_ofReal_rpow volume _ q hq, eLpNorm_ofReal_rpow volume _ q hq]
  exact controllingMaximal_rpow_of_oneDim q (ENNReal.ofReal A) henergy n F hF

/-- The actual iterated maximal operator has a uniform q-energy bound.
The constant is chosen before the measurable extended-valued input. -/
theorem exists_controllingMaximal_rpow (n : ℕ) (q : ℝ) (hq : 1 < q) :
    ∃ A : ℝ, 0 < A ∧ ∀ F : Space n → ℝ≥0∞, Measurable F →
      (∫⁻ x, controllingMaximal n F x ^ q) ≤ ENNReal.ofReal A * ∫⁻ x, F x ^ q := by
  obtain ⟨A, hA, henergy⟩ := HardyLittlewoodLp.exists_rationalMaximal_Lp q hq
  refine ⟨A ^ n, pow_pos hA n, ?_⟩
  intro F hF
  rw [ENNReal.ofReal_pow hA.le]
  exact controllingMaximal_rpow_of_oneDim q (ENNReal.ofReal A) henergy n F hF

/-- The genuine finite Lᑫ estimate for q > 1. Both sides may be infinite;
no integrability hypothesis on F or on any coordinate fiber is imposed. -/
theorem exists_controllingMaximal_Lp (n : ℕ) (q : ℝ) (hq : 1 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ F : Space n → ℝ≥0∞, Measurable F →
      eLpNorm (controllingMaximal n F) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal C * eLpNorm F (ENNReal.ofReal q) volume := by
  obtain ⟨A, hA, henergy⟩ := HardyLittlewoodLp.exists_rationalMaximal_Lp q hq
  refine ⟨(A ^ n) ^ (1 / q), Real.rpow_pos_of_pos (pow_pos hA n) _, ?_⟩
  intro F hF
  exact eLpNorm_controllingMaximal_of_oneDim q (lt_trans zero_lt_one hq) A hA henergy n F hF

end StrongSpherical.RectangularMaximalLp
