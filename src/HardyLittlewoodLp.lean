import HardyLittlewoodOneDim
import LayercakeLp

/-! # The genuine one-dimensional centered maximal estimate for every q>1 -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace StrongSpherical.HardyLittlewoodLp
open HardyLittlewoodOneDim
set_option maxHeartbeats 1000000

def boundConstant (q : ℝ) : ℝ := q * 10 * LayercakeLp.tailCoefficient q

theorem boundConstant_pos (q : ℝ) (hq : 1 < q) : 0 < boundConstant q :=
  mul_pos (mul_pos (by linarith) (by norm_num)) (LayercakeLp.tailCoefficient_pos q hq)

/-- First establish the estimate for finite, nonnegative inputs. The output
may still take the value infinity; monotone truncation retains that case. -/
theorem rationalMaximal_Lp_real (q : ℝ) (hq : 1 < q)
    (F : ℝ → ℝ) (hF : Measurable F) (hn : ∀ x, 0 ≤ F x) :
    (∫⁻ x, rationalMaximal (fun y => ENNReal.ofReal (F y)) x ^ q) ≤
      ENNReal.ofReal (boundConstant q) * ∫⁻ x, ENNReal.ofReal (F x) ^ q := by
  have hq0 : 0 < q := by linarith
  let M : ℝ → ℝ≥0∞ := rationalMaximal (fun y => ENNReal.ofReal (F y))
  have hM : Measurable M := measurable_rationalMaximal _ (ENNReal.measurable_ofReal.comp hF)
  let G : ℕ → ℝ → ℝ := fun N x => (min (M x) (N : ℝ≥0∞)).toReal
  have hcap : ∀ (N : ℕ) (x : ℝ), min (M x) (N : ℝ≥0∞) ≠ ∞ := fun N x =>
    ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  have hG : ∀ N : ℕ, Measurable (G N) := fun N => (hM.min measurable_const).ennreal_toReal
  have hnG : ∀ (N : ℕ) (x : ℝ), 0 ≤ G N x := fun N x => ENNReal.toReal_nonneg
  have hpow : ∀ (N : ℕ) (x : ℝ),
      ENNReal.ofReal (G N x) ^ q = min (M x) (N : ℝ≥0∞) ^ q := by
    intro N x
    change ENNReal.ofReal ((min (M x) (N : ℝ≥0∞)).toReal) ^ q = _
    rw [ENNReal.ofReal_toReal (hcap N x)]
  have hb : ∀ N : ℕ, (∫⁻ x, min (M x) (N : ℝ≥0∞) ^ q) ≤
      ENNReal.ofReal (boundConstant q) * ∫⁻ x, ENNReal.ofReal (F x) ^ q := by
    intro N
    have h := LayercakeLp.lintegral_rpow_le_of_high_tail F (G N) hF hn (hG N) (hnG N)
      q hq 10 (by norm_num) (fun t ht => by
        have hsub : {x | t < G N x} ⊆ {x | ENNReal.ofReal t < M x} := by
          intro x hx
          exact ((ENNReal.ofReal_lt_iff_lt_toReal ht.le (hcap N x)).2 hx).trans_le
            (min_le_left _ _)
        have hh := (mul_le_mul' le_rfl (measure_mono hsub)).trans
          (rationalMaximal_high_tail F hF t ht)
        simpa only [highInput, ENNReal.ofReal_ofNat] using hh)
    simpa only [hpow, boundConstant] using h
  have heq : ∀ x, M x ^ q = ⨆ N : ℕ, min (M x) (N : ℝ≥0∞) ^ q := by
    intro x
    have hs := (ENNReal.orderIsoRpow q hq0).map_iSup
      (fun N : ℕ => min (M x) (N : ℝ≥0∞))
    change (⨆ N : ℕ, min (M x) (N : ℝ≥0∞)) ^ q =
      ⨆ N : ℕ, min (M x) (N : ℝ≥0∞) ^ q at hs
    rw [← hs]
    congr 1
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  change (∫⁻ x, M x ^ q) ≤ _
  simp_rw [heq]
  rw [lintegral_iSup (fun N => (hM.min measurable_const).pow_const q)
    (fun i j hij x => ENNReal.rpow_le_rpow
      (min_le_min_left _ (by exact_mod_cast hij)) hq0.le)]
  exact iSup_le hb

/-- The same estimate for extended inputs. Infinite-energy fibers are kept;
finite energy only supplies the almost-everywhere finite representative. -/
theorem rationalMaximal_Lp_ennreal (q : ℝ) (hq : 1 < q)
    (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, rationalMaximal F x ^ q) ≤
      ENNReal.ofReal (boundConstant q) * ∫⁻ x, F x ^ q := by
  have hq0 : 0 < q := by linarith
  have hA0 : ENNReal.ofReal (boundConstant q) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (boundConstant_pos q hq))
  by_cases hfin : (∫⁻ x, F x ^ q) = ∞
  · simp [hfin, hA0]
  have hAE : ∀ᵐ x : ℝ, F x ≠ ∞ := by
    filter_upwards [ae_lt_top (hF.pow_const q) hfin] with x hx
    exact ((ENNReal.rpow_lt_top_iff_of_pos hq0).mp hx).ne
  have havg : ∀ (r x : ℝ), intervalAverage r F x =
      intervalAverage r (fun y => ENNReal.ofReal ((F y).toReal)) x := by
    intro r x
    unfold intervalAverage
    congr 1
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_of_ae hAE] with y hy
    exact (ENNReal.ofReal_toReal hy).symm
  have hmax : rationalMaximal F =
      rationalMaximal (fun y => ENNReal.ofReal ((F y).toReal)) := by
    ext x
    unfold rationalMaximal
    congr 1
    ext r
    exact havg r x
  have henergy : (∫⁻ x, ENNReal.ofReal ((F x).toReal) ^ q) = ∫⁻ x, F x ^ q := by
    apply lintegral_congr_ae
    filter_upwards [hAE] with x hx
    rw [ENNReal.ofReal_toReal hx]
  rw [hmax]
  have h := rationalMaximal_Lp_real q hq (fun y => (F y).toReal) hF.ennreal_toReal
    (fun _ => ENNReal.toReal_nonneg)
  rw [henergy] at h
  exact h

/-- The finite positive constant is chosen before the input function, with
no finite-energy hypothesis and the real rpow exponent appearing literally. -/
theorem exists_rationalMaximal_Lp (q : ℝ) (hq : 1 < q) :
    ∃ A : ℝ, 0 < A ∧ ∀ F : ℝ → ℝ≥0∞, Measurable F →
      (∫⁻ x, (HardyLittlewoodOneDim.rationalMaximal F x) ^ q) ≤
        ENNReal.ofReal A * ∫⁻ x, (F x) ^ q :=
  ⟨boundConstant q, boundConstant_pos q hq, rationalMaximal_Lp_ennreal q hq⟩

end StrongSpherical.HardyLittlewoodLp
