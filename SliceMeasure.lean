import EllipsoidGraph
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Euclidean slice measure and the squared-normal-coordinate substitution -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
namespace StrongSpherical.SliceMeasure
open QuadraticGraph EllipsoidGraph
variable {m : ℕ}

/-- Split off the last coordinate, keeping Euclidean measure on the other coordinates. -/
def splitEquiv (m : ℕ) : Space (m + 1) ≃ᵐ ℝ × Space m where
  toFun v := (normalInput v, spatialInput v)
  invFun p := slicePoint p.2 p.1
  left_inv v := by
    ext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [normalInput, spatialInput]
  right_inv p := by
    rcases p with ⟨h, u⟩
    apply Prod.ext
    · simp [normalInput]
    · ext i; simp [spatialInput]
  measurable_toFun := by
    apply Measurable.prodMk
    · unfold normalInput; fun_prop
    · unfold spatialInput; fun_prop
  measurable_invFun := by
    change Measurable (fun p : ℝ × Space m => slicePoint p.2 p.1)
    unfold slicePoint
    fun_prop

theorem measurePreserving_splitEquiv (m : ℕ) :
    MeasurePreserving (splitEquiv m) (volume : Measure (Space (m + 1)))
      ((volume : Measure ℝ).prod (volume : Measure (Space m))) := by
  have h := ((MeasurePreserving.id (μ := (volume : Measure ℝ))).prod
    (PiLp.volume_preserving_toLp (Fin m))).comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) (Fin.last m)).comp
      (PiLp.volume_preserving_ofLp (Fin (m + 1))))
  convert h using 1 <;> try (borelize (Space (m + 1)) (Space m) (ℝ × Space m); rfl)
  funext v
  apply Prod.ext
  · rfl
  · ext i
    simp [splitEquiv, spatialInput, MeasurableEquiv.piFinSuccAbove, Fin.init]

theorem lintegral_slices (F : Space (m + 1) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, F v) = ∫⁻ h, ∫⁻ u, F (slicePoint u h) := by
  rw [← (measurePreserving_splitEquiv m).symm.lintegral_comp_emb
    (splitEquiv m).symm.measurableEmbedding F]
  exact lintegral_prod _ ((hF.comp (splitEquiv m).symm.measurable).aemeasurable)

theorem integral_slices {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Space (m + 1) → E) (hF : Integrable F) :
    (∫ v, F v) = ∫ h, ∫ u, F (slicePoint u h) := by
  calc
    _ = ∫ p : ℝ × Space m, F ((splitEquiv m).symm p) :=
      ((measurePreserving_splitEquiv m).symm.integral_comp' F).symm
    _ = _ := integral_prod _ ((measurePreserving_splitEquiv m).symm.integrable_comp_emb
      (splitEquiv m).symm.measurableEmbedding |>.2 hF)

/-- The exact Jacobian for squaring the positive normal variable. This identity
is unconditional; no integrability convention is used to discard a term. -/
theorem integral_sqrt_substitution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) :
    (∫ s in Ioi (0 : ℝ), (1 / (2 * Real.sqrt s)) • F (Real.sqrt s)) =
      ∫ t in Ioi (0 : ℝ), F t := by
  have h := integral_comp_rpow_Ioi_of_pos (g := F) (by norm_num : (0 : ℝ) < 1 / 2)
  convert h using 1
  apply setIntegral_congr_fun measurableSet_Ioi
  intro s hs
  dsimp only
  rw [Real.sqrt_eq_rpow]
  congr 1
  rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.rpow_neg hs.le]
  ring

/-- An input cutoff in the squared normal variable. Lemma 3.2 accepts L²
inputs, so no smooth cutoff or additional differentiability of f is needed. -/
def sliceInput (L : ℝ) (f : Space (m + 1) → ℂ) (h : ℝ) (v : Space (m + 1)) : ℂ :=
  (Icc 0 L).indicator (fun _ => f (liftedInput h v)) (normalInput v)

theorem measurable_sliceInput (L : ℝ) (f : Space (m + 1) → ℂ) (hf : Measurable f) :
    Measurable (fun p : ℝ × Space (m + 1) => sliceInput L f p.1 p.2) := by
  unfold sliceInput
  have h := (hf.comp (by unfold liftedInput slicePoint spatialInput normalInput; fun_prop :
    Measurable (fun p : ℝ × Space (m + 1) => liftedInput p.1 p.2))).indicator
    ((by unfold normalInput; fun_prop : Measurable (fun p : ℝ × Space (m + 1) => normalInput p.2)) (measurableSet_Icc : MeasurableSet (Icc (0 : ℝ) L)))
  convert h using 1
  funext p
  by_cases hp : normalInput p.2 ∈ Icc 0 L <;> simp [hp]

end StrongSpherical.SliceMeasure

namespace StrongSpherical.SliceMeasure
open QuadraticGraph EllipsoidGraph
variable {m : ℕ}

/-- Height translation recovers the whole input energy on every fixed s. -/
theorem lintegral_lifted_height (F : Space (m + 1) → ℝ≥0∞) (hF : Measurable F) (s : ℝ) :
    (∫⁻ h, ∫⁻ u : Space m, F (slicePoint u (h + Real.sqrt s))) = ∫⁻ v, F v := by
  have hG : Measurable (fun h : ℝ => ∫⁻ u : Space m, F (slicePoint u h)) := by
    apply Measurable.lintegral_prod_right
    exact hF.comp (by unfold slicePoint; fun_prop)
  rw [(measurePreserving_add_right (volume : Measure ℝ) (Real.sqrt s)).lintegral_comp hG]
  exact (lintegral_slices F hF).symm

/-- Tonelli and height translation prove the exact cutoff energy identity. -/
theorem lintegral_slice_energy (L : ℝ) (F : Space (m + 1) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ h, ∫⁻ v : Space (m + 1),
      (Icc 0 L).indicator (fun _ => F (liftedInput h v)) (normalInput v)) =
        ENNReal.ofReal L * ∫⁻ v, F v := by
  let W : ℝ → ℝ≥0∞ := (Icc 0 L).indicator (fun _ => 1)
  have hW : Measurable W := measurable_const.indicator measurableSet_Icc
  have hEq : ∀ h v, (Icc 0 L).indicator (fun _ => F (liftedInput h v)) (normalInput v) =
      W (normalInput v) * F (liftedInput h v) := by
    intro h v
    by_cases hv : normalInput v ∈ Icc 0 L <;> simp [W, hv]
  simp_rw [hEq]
  have hmeas : Measurable (fun p : ℝ × Space (m + 1) =>
      W (normalInput p.2) * F (liftedInput p.1 p.2)) := by
    exact (hW.comp (by unfold normalInput; fun_prop)).mul
      (hF.comp (by unfold liftedInput slicePoint spatialInput normalInput; fun_prop))
  have heSlice : ∀ h : ℝ, (∫⁻ v, W (normalInput v) * F (liftedInput h v)) =
      ∫⁻ s, ∫⁻ u : Space m, W s * F (slicePoint u (h + Real.sqrt s)) := by
    intro h
    simpa [normalInput, liftedInput, spatialInput] using
      (lintegral_slices (fun v => W (normalInput v) * F (liftedInput h v)) (hmeas.comp (measurable_const.prodMk measurable_id)))
  simp_rw [heSlice]
  change (∫⁻ h, ∫⁻ s, ∫⁻ u : Space m, W s * F (slicePoint u (h + Real.sqrt s))) = _
  have h3 : Measurable (fun p : (ℝ × ℝ) × Space m =>
      W p.1.2 * F (slicePoint p.2 (p.1.1 + Real.sqrt p.1.2))) := by
    exact (hW.comp measurable_fst.snd).mul (hF.comp (by unfold slicePoint; fun_prop))
  rw [lintegral_lintegral_swap h3.lintegral_prod_right'.aemeasurable]
  have hinner : ∀ s, (∫⁻ h, ∫⁻ u : Space m, W s * F (slicePoint u (h + Real.sqrt s))) =
      W s * ∫⁻ v, F v := by
    intro s
    have hF2 : Measurable (fun p : ℝ × Space m => F (slicePoint p.2 (p.1 + Real.sqrt s))) :=
      hF.comp (by unfold slicePoint; fun_prop)
    calc
      _ = ∫⁻ h, W s * ∫⁻ u : Space m, F (slicePoint u (h + Real.sqrt s)) := by
        apply lintegral_congr
        intro h
        exact lintegral_const_mul _ (hF2.comp (measurable_const.prodMk measurable_id))
      _ = W s * (∫⁻ h, ∫⁻ u : Space m, F (slicePoint u (h + Real.sqrt s))) :=
        lintegral_const_mul _ hF2.lintegral_prod_right'
      _ = _ := by rw [lintegral_lifted_height F hF s]
  simp_rw [hinner]
  rw [lintegral_mul_const _ hW]
  simp [W, lintegral_indicator measurableSet_Icc, Real.volume_Icc]

theorem lintegral_sliceInput_sq (L : ℝ) (f : Space (m + 1) → ℂ) (hf : Measurable f) :
    (∫⁻ h, ∫⁻ v, ‖sliceInput L f h v‖ₑ ^ 2) =
      ENNReal.ofReal L * ∫⁻ v, ‖f v‖ₑ ^ 2 := by
  rw [← lintegral_slice_energy L (fun v => ‖f v‖ₑ ^ 2) (hf.enorm.pow_const 2)]
  apply lintegral_congr
  intro h
  apply lintegral_congr
  intro v
  by_cases hv : normalInput v ∈ Icc 0 L <;> simp [sliceInput, hv]

end StrongSpherical.SliceMeasure

namespace StrongSpherical.SliceMeasure
open QuadraticGraph EllipsoidGraph
variable {m : ℕ}

/-- Normal-variable change of variables on a negative-displacement patch. -/
theorem integral_normal_substitution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ℝ → E) (h : ℝ) (hzero : ∀ t, t ≤ h → F t = 0) :
    (∫ t, F t) = ∫ s, if 0 < s then (1 / (2 * Real.sqrt s)) • F (h + Real.sqrt s) else 0 := by
  calc
    _ = ∫ t, F (h + t) := (integral_add_left_eq_self F h).symm
    _ = ∫ t in Ioi (0 : ℝ), F (h + t) := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro t ht
      apply hzero
      have ht0 : t ≤ 0 := le_of_not_gt ht
      linarith
    _ = ∫ s in Ioi (0 : ℝ), (1 / (2 * Real.sqrt s)) • F (h + Real.sqrt s) :=
      (integral_sqrt_substitution (fun t => F (h + t))).symm
    _ = _ := by
      rw [← integral_indicator measurableSet_Ioi]
      rfl

/-- The cutoff energy is finite for L² inputs, hence almost every slice is L². -/
theorem memLp_sliceInput_ae (L : ℝ) (f : Space (m + 1) → ℂ) (hf : Measurable f)
    (hLp : MemLp f 2 volume) : ∀ᵐ h : ℝ, MemLp (sliceInput L f h) 2 volume := by
  have henergy : (∫⁻ h, ∫⁻ v, ‖sliceInput L f h v‖ₑ ^ 2) < ∞ := by
    rw [lintegral_sliceInput_sq L f hf, ← SchurTest.eLpNorm_two_sq]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top hLp.eLpNorm_lt_top)
  have hmeas := (measurable_sliceInput L f hf).enorm.pow_const 2
  have hfin := ae_lt_top hmeas.lintegral_prod_right' henergy.ne
  filter_upwards [hfin] with h hh
  refine ⟨((measurable_sliceInput L f hf).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable, ?_⟩
  apply (ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  simpa only [ENNReal.rpow_two, ENNReal.top_pow (by norm_num : 2 ≠ 0), SchurTest.eLpNorm_two_sq] using hh

end StrongSpherical.SliceMeasure

namespace StrongSpherical.SliceMeasure
open QuadraticGraph EllipsoidGraph
variable {m : ℕ}

theorem integral_slices_reverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : Space (m + 1) → E) (hF : Integrable F) :
    (∫ v, F v) = ∫ u : Space m, ∫ h, F (slicePoint u h) := by
  calc
    _ = ∫ p : ℝ × Space m, F ((splitEquiv m).symm p) :=
      ((measurePreserving_splitEquiv m).symm.integral_comp' F).symm
    _ = _ := integral_prod_symm _ ((measurePreserving_splitEquiv m).symm.integrable_comp_emb
      (splitEquiv m).symm.measurableEmbedding |>.2 hF)

end StrongSpherical.SliceMeasure
