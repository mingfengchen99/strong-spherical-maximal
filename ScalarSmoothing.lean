import ProductSmoothing

/-! # Scalar Schwartz tails for the smoothing errors -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace StrongSpherical.ScalarSmoothing
open FourierCutoff ProductSmoothing

def tailConstant : ℝ := Classical.choose (phi_decay 3 0)

theorem tailConstant_pos : 0 < tailConstant := (Classical.choose_spec (phi_decay 3 0)).1

theorem phi_tail (t : ℝ) : (1 + |t|) ^ 3 * ‖phi t‖ ≤ tailConstant := by
  simpa only [norm_iteratedFDeriv_zero, tailConstant] using (Classical.choose_spec (phi_decay 3 0)).2 t

/-- Outside twice the support cube the scaled Schwartz tail gains a small scale. -/
theorem scaledPhi_tail_pointwise (R eta epsilon w z : ℝ)
    (hR : 1 ≤ R) (heta : 0 < eta) (hsmall : eta ≤ epsilon) (heps : epsilon ≤ 1)
    (hfar : 2 * R + 2 < |w|) (hz : |z| ≤ R) :
    ‖scaledPhi eta (w - z)‖ ≤ 64 * tailConstant * epsilon / (1 + |w|) ^ 3 := by
  let d : ℝ := eta + |w - z|
  let a : ℝ := 1 + |w|
  have hd : 0 < d := by dsimp [d]; positivity
  have ha : 0 < a := by dsimp [a]; positivity
  have habs : 1 + |eta⁻¹ * (w - z)| = d / eta := by
    rw [abs_mul, abs_inv, abs_of_pos heta]
    dsimp [d]
    field_simp
  have hphi := phi_tail (eta⁻¹ * (w - z))
  rw [habs] at hphi
  have hp : ‖phi (eta⁻¹ * (w - z))‖ ≤ tailConstant / (d / eta) ^ 3 :=
    (le_div_iff₀ (pow_pos (div_pos hd heta) 3)).mpr (by simpa only [mul_comm] using hphi)
  have hn : ‖scaledPhi eta (w - z)‖ ≤ tailConstant * eta ^ 2 / d ^ 3 := by
    rw [norm_scaledPhi eta heta]
    calc
      _ ≤ eta⁻¹ * (tailConstant / (d / eta) ^ 3) :=
        mul_le_mul_of_nonneg_left hp (inv_nonneg.mpr heta.le)
      _ = _ := by field_simp
  have hstep : a ≤ 4 * d := by
    have hdist := abs_sub_abs_le_abs_sub w z
    dsimp [a, d]
    linarith
  have hden : a ^ 3 ≤ 64 * d ^ 3 := by
    calc
      _ ≤ (4 * d) ^ 3 := by gcongr
      _ = _ := by ring
  have hrecip : 1 / d ^ 3 ≤ 64 / a ^ 3 := by
    apply (div_le_div_iff₀ (pow_pos hd 3) (pow_pos ha 3)).mpr
    simpa only [one_mul] using hden
  have heps0 : 0 ≤ epsilon := heta.le.trans hsmall
  have heta1 : eta ≤ 1 := hsmall.trans heps
  have hpows : eta ^ 2 ≤ epsilon := by
    calc
      _ = eta * eta := pow_two eta
      _ ≤ eta * 1 := mul_le_mul_of_nonneg_left heta1 heta.le
      _ ≤ epsilon := by simpa using hsmall
  calc
    _ ≤ tailConstant * eta ^ 2 / d ^ 3 := hn
    _ ≤ tailConstant * epsilon / d ^ 3 := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpows tailConstant_pos.le)
        (pow_nonneg hd.le 3)
    _ = (tailConstant * epsilon) * (1 / d ^ 3) := by ring
    _ ≤ (tailConstant * epsilon) * (64 / a ^ 3) :=
      mul_le_mul_of_nonneg_left hrecip (mul_nonneg tailConstant_pos.le heps0)
    _ = _ := by dsimp [a]; ring

def boxScalar (R eta w : ℝ) : ℝ := ∫ z in Icc (-R) R, ‖scaledPhi eta (w - z)‖

theorem boxScalar_nonneg (R eta w : ℝ) : 0 ≤ boxScalar R eta w :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem boxScalar_le_L1 (R eta w : ℝ) (heta : 0 < eta) :
    boxScalar R eta w ≤ phiL1 := by
  have hi := ((integrable_scaledPhi eta heta).comp_sub_left w).norm
  calc
    _ ≤ ∫ z, ‖scaledPhi eta (w - z)‖ := setIntegral_le_integral hi (Filter.Eventually.of_forall
      (fun _ => norm_nonneg _))
    _ = _ := by
      rw [integral_sub_left_eq_self (fun z => ‖scaledPhi eta z‖) volume w,
        integral_norm_scaledPhi eta heta]

theorem boxScalar_tail (R eta epsilon w : ℝ)
    (hR : 1 ≤ R) (heta : 0 < eta) (hsmall : eta ≤ epsilon) (heps : epsilon ≤ 1)
    (hfar : 2 * R + 2 < |w|) :
    boxScalar R eta w ≤ (128 * R * tailConstant) * epsilon / (1 + |w|) ^ 3 := by
  have hInt : IntegrableOn (fun z => ‖scaledPhi eta (w - z)‖) (Icc (-R) R) :=
    (((continuous_scaledPhi eta).comp (continuous_const.sub continuous_id)).norm).continuousOn.integrableOn_compact
      isCompact_Icc
  have hC : 0 ≤ 64 * tailConstant * epsilon / (1 + |w|) ^ 3 := by
    have heps0 : 0 ≤ epsilon := heta.le.trans hsmall
    have ht := tailConstant_pos
    positivity
  calc
    _ ≤ ∫ _z in Icc (-R) R, 64 * tailConstant * epsilon / (1 + |w|) ^ 3 := by
      apply integral_mono_ae hInt (integrableOn_const isCompact_Icc.measure_ne_top)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with z hz
      exact scaledPhi_tail_pointwise R eta epsilon w z hR heta hsmall heps hfar (abs_le.mpr hz)
    _ = _ := by
      rw [integral_const, measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith : 0 ≤ R - -R)]
      simp only [smul_eq_mul]
      ring

def unitWeight (w : ℝ) : ℝ := (1 + |w|) ^ (-(3 : ℤ))

theorem unitWeight_nonneg (w : ℝ) : 0 ≤ unitWeight w := by
  exact zpow_nonneg (by positivity) _

theorem unitWeight_pos (w : ℝ) : 0 < unitWeight w := by
  exact zpow_pos (by positivity) _

theorem unitWeight_eq (w : ℝ) : unitWeight w = ((1 + |w|) ^ 3)⁻¹ := rfl

def scalarConstant (R : ℝ) : ℝ :=
  1 + phiL1 * (2 * R + 3) ^ 3 + 128 * R * tailConstant

theorem scalarConstant_pos (R : ℝ) (hR : 1 ≤ R) : 0 < scalarConstant R := by
  dsimp [scalarConstant]
  have hp := phiL1_nonneg
  have ht := tailConstant_pos
  positivity

theorem boxScalar_near (R eta w : ℝ) (_hR : 1 ≤ R) (heta : 0 < eta)
    (hnear : |w| ≤ 2 * R + 2) :
    boxScalar R eta w ≤ (phiL1 * (2 * R + 3) ^ 3) * unitWeight w := by
  have hweight : 1 ≤ (2 * R + 3) ^ 3 * unitWeight w := by
    rw [unitWeight_eq, ← div_eq_mul_inv]
    apply (one_le_div₀ (by positivity : 0 < (1 + |w|) ^ 3)).mpr
    exact pow_le_pow_left₀ (by positivity) (by linarith : 1 + |w| ≤ 2 * R + 3) 3
  calc
    _ ≤ phiL1 := boxScalar_le_L1 R eta w heta
    _ ≤ phiL1 * ((2 * R + 3) ^ 3 * unitWeight w) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hweight phiL1_nonneg
    _ = _ := by ring

theorem boxScalar_uniform (R eta epsilon w : ℝ)
    (hR : 1 ≤ R) (heta : 0 < eta) (hsmall : eta ≤ epsilon) (heps : epsilon ≤ 1) :
    boxScalar R eta w ≤ scalarConstant R * unitWeight w := by
  have hfarC : 128 * R * tailConstant ≤ scalarConstant R := by
    dsimp [scalarConstant]
    have hp : 0 ≤ phiL1 * (2 * R + 3) ^ 3 := mul_nonneg phiL1_nonneg (by positivity)
    linarith
  have hnearC : phiL1 * (2 * R + 3) ^ 3 ≤ scalarConstant R := by
    dsimp [scalarConstant]
    have hp : 0 ≤ 128 * R * tailConstant := by have ht := tailConstant_pos; positivity
    linarith
  by_cases hfar : 2 * R + 2 < |w|
  · have h := boxScalar_tail R eta epsilon w hR heta hsmall heps hfar
    rw [div_eq_mul_inv, ← unitWeight_eq] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      ((mul_le_mul_of_nonneg_left heps (by have ht := tailConstant_pos; positivity)).trans
        (by simpa using hfarC)) (unitWeight_nonneg w))
  · exact (boxScalar_near R eta w hR heta (le_of_not_gt hfar)).trans
      (mul_le_mul_of_nonneg_right hnearC (unitWeight_nonneg w))

theorem boxScalar_small_tail (R eta epsilon w : ℝ)
    (hR : 1 ≤ R) (heta : 0 < eta) (hsmall : eta ≤ epsilon) (heps : epsilon ≤ 1)
    (hfar : 2 * R + 2 < |w|) :
    boxScalar R eta w ≤ epsilon * scalarConstant R * unitWeight w := by
  have heps0 : 0 ≤ epsilon := heta.le.trans hsmall
  have hfarC : 128 * R * tailConstant ≤ scalarConstant R := by
    dsimp [scalarConstant]
    have hp : 0 ≤ phiL1 * (2 * R + 3) ^ 3 := mul_nonneg phiL1_nonneg (by positivity)
    linarith
  have h := boxScalar_tail R eta epsilon w hR heta hsmall heps hfar
  rw [div_eq_mul_inv, ← unitWeight_eq] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (by nlinarith [mul_le_mul_of_nonneg_right hfarC heps0]) (unitWeight_nonneg w))

end StrongSpherical.ScalarSmoothing
