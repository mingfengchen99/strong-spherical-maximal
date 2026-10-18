import QuadraticGraph

/-!
# Joint quadratic and normal oscillation

The oscillatory input integral underlying (3.19) of arXiv:2609.32421v2.
Spatial integration by parts transfers exactly one derivative in each of the
first `m` input coordinates. Two further derivatives in the last input
coordinate give frequency-difference decay. All amplitude derivatives below
are the actual coordinate Fréchet derivatives defined in ProductOscillation.

The main bound retains `amplitudeSeminorm` explicitly. Bounding it uniformly
for paired amplitudes from the paper's input derivative bounds, exchanging
input/frequency integrals in the Gram kernel, and the L² argument are subsequent steps.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace StrongSpherical.JointOscillation

open ProductOscillation QuadraticGraph

variable {n m : ℕ}

/-- A normal Fourier character with a continuous factor constant in that direction. -/
def weightedModulation (eta : ℝ) (i : Fin n) (H : Space n → ℂ) (v : Space n) : ℂ :=
  modulation eta i v * H v

theorem continuous_weightedModulation (eta : ℝ) (i : Fin n) {H : Space n → ℂ}
    (hH : Continuous H) : Continuous (weightedModulation eta i H) :=
  (continuous_modulation eta i).mul hH

theorem hasLineDerivAt_weightedModulation (eta : ℝ) (i : Fin n) (H : Space n → ℂ)
    (hinvariant : ∀ v (t : ℝ), H (v + t • coordinateVector i) = H v) (v : Space n) :
    HasLineDerivAt ℝ (weightedModulation eta i H)
      (weightedModulation eta i H v * frequencyFactor eta) v (coordinateVector i) := by
  have h := hasLineDerivAt_modulation eta i v
  unfold HasLineDerivAt at h ⊢
  simp_rw [weightedModulation, hinvariant]
  convert! h.mul_const (H v) using 1
  ring

/-- Integrate by parts in the normal direction without differentiating the spatial factor. -/
theorem weighted_integration_by_parts (eta : ℝ) (i : Fin n) {H a : Space n → ℂ}
    (hH : Continuous H) (hinvariant : ∀ v (t : ℝ), H (v + t • coordinateVector i) = H v)
    (ha : ContDiff ℝ 1 a) (hcompact : HasCompactSupport a) :
    frequencyFactor eta * (∫ v, weightedModulation eta i H v * a v) =
      -(∫ v, weightedModulation eta i H v * coordinateDerivative i a v) := by
  have hpa := contDiff_partial i (r := 0) ha
  have hd := ha.differentiable (by simp)
  have hc := continuous_weightedModulation eta i hH
  have hi : Integrable (fun v => weightedModulation eta i H v * a v) :=
    (hc.mul ha.continuous).integrable_of_hasCompactSupport hcompact.mul_left
  have hip : Integrable (fun v => weightedModulation eta i H v * coordinateDerivative i a v) :=
    (hc.mul hpa.continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_partial i hcompact).mul_left
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Space n))) (B := ContinuousLinearMap.mul ℝ ℂ)
    (f := a) (f' := coordinateDerivative i a)
    (g := weightedModulation eta i H)
    (g' := fun v => weightedModulation eta i H v * frequencyFactor eta)
    (v := coordinateVector i)
    (by simpa only [ContinuousLinearMap.mul_apply', mul_comm] using hip)
    (by simpa only [ContinuousLinearMap.mul_apply', mul_left_comm, mul_comm, mul_assoc]
      using hi.mul_const (frequencyFactor eta))
    (by simpa only [ContinuousLinearMap.mul_apply', mul_comm] using hi)
    (fun v _ => (hd v).hasFDerivAt.hasLineDerivAt (coordinateVector i))
    (fun v _ => hasLineDerivAt_weightedModulation eta i H hinvariant v)
  simp only [ContinuousLinearMap.mul_apply'] at h
  calc
    _ = ∫ v, a v * (weightedModulation eta i H v * frequencyFactor eta) := by
      rw [← integral_const_mul]
      congr 1
      ext v
      ring
    _ = _ := by simpa only [mul_comm] using h

theorem weighted_integration_by_parts_twice (eta : ℝ) (i : Fin n) {H a : Space n → ℂ}
    (hH : Continuous H) (hinvariant : ∀ v (t : ℝ), H (v + t • coordinateVector i) = H v)
    (ha : ContDiff ℝ 2 a) (hcompact : HasCompactSupport a) :
    frequencyFactor eta ^ 2 * (∫ v, weightedModulation eta i H v * a v) =
      ∫ v, weightedModulation eta i H v * coordinateDerivative i (coordinateDerivative i a) v := by
  have h1 := weighted_integration_by_parts eta i hH hinvariant
    (ha.of_le (by norm_num)) hcompact
  have h2 := weighted_integration_by_parts eta i hH hinvariant
    (contDiff_partial i (r := 1) ha) (hasCompactSupport_partial i hcompact)
  calc
    _ = frequencyFactor eta * (frequencyFactor eta *
      ∫ v, weightedModulation eta i H v * a v) := by ring
    _ = _ := by rw [h1, mul_neg, h2, neg_neg]

theorem norm_integral_weighted_le (eta : ℝ) (i : Fin n) (B : ℝ) {H a : Space n → ℂ}
    (ha : Continuous a) (hcompact : HasCompactSupport a)
    (hbound : ∀ v ∈ tsupport a, ‖H v‖ ≤ B) :
    ‖∫ v, weightedModulation eta i H v * a v‖ ≤ B * ∫ v, ‖a v‖ := by
  have hint := ha.integrable_of_hasCompactSupport (μ := volume) hcompact
  calc
    _ ≤ ∫ v, B * ‖a v‖ := by
      apply norm_integral_le_of_norm_le (hint.norm.const_mul B)
      apply Filter.Eventually.of_forall
      intro v
      simp only [weightedModulation, norm_mul, norm_modulation, one_mul]
      by_cases hz : a v = 0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_right
          (hbound v (subset_closure hz)) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

/-- Uniform normal-frequency decay with a factor that is merely continuous in the
other directions. Only derivatives of the amplitude enter the right-hand side. -/
theorem norm_integral_weighted_le_frequencyDecay
    (eta : ℝ) (i : Fin n) (B : ℝ) {H a : Space n → ℂ}
    (hH : Continuous H) (hinvariant : ∀ v (t : ℝ), H (v + t • coordinateVector i) = H v)
    (ha : ContDiff ℝ 2 a) (hcompact : HasCompactSupport a)
    (hbound : ∀ v ∈ tsupport a, ‖H v‖ ≤ B) :
    ‖∫ v, weightedModulation eta i H v * a v‖ ≤
      4 * B * ((∫ v, ‖a v‖) +
        ∫ v, ‖coordinateDerivative i (coordinateDerivative i a) v‖) * frequencyDecay eta := by
  have h0 := norm_integral_weighted_le eta i B ha.continuous hcompact hbound
  have hp := contDiff_partial i (r := 1) ha
  have hpp := contDiff_partial i (r := 0) hp
  have hcp := hasCompactSupport_partial i hcompact
  have hcpp := hasCompactSupport_partial i hcp
  have hbound2 : ∀ v ∈ tsupport (coordinateDerivative i (coordinateDerivative i a)), ‖H v‖ ≤ B := by
    intro v hv
    exact hbound v (tsupport_partial_subset i a (tsupport_partial_subset i _ hv))
  have hsecond := norm_integral_weighted_le eta i B hpp.continuous hcpp hbound2
  have hn := congrArg norm (weighted_integration_by_parts_twice eta i hH hinvariant ha hcompact)
  simp only [norm_mul, norm_pow] at hn
  have hq : |eta| ≤ ‖frequencyFactor eta‖ := by
    rw [norm_frequencyFactor]
    nlinarith [Real.pi_gt_three, abs_nonneg eta]
  have h2 : |eta| ^ 2 * ‖∫ v, weightedModulation eta i H v * a v‖ ≤
      B * ∫ v, ‖coordinateDerivative i (coordinateDerivative i a) v‖ := by
    calc
      _ ≤ ‖frequencyFactor eta‖ ^ 2 * ‖∫ v, weightedModulation eta i H v * a v‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg eta) hq 2) (norm_nonneg _)
      _ = _ := hn
      _ ≤ _ := hsecond
  have hN0 : 0 ≤ B * ∫ v, ‖a v‖ := (norm_nonneg _).trans h0
  have hN2 : 0 ≤ B * ∫ v, ‖coordinateDerivative i (coordinateDerivative i a) v‖ :=
    (norm_nonneg _).trans hsecond
  rw [frequencyDecay, Real.rpow_neg (by positivity : 0 ≤ 1 + |eta|),
    Real.rpow_two, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity : 0 < (1 + |eta|) ^ 2)).2
  rcases le_total |eta| 1 with he | he
  · have hd : (1 + |eta|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg eta]
    calc
      _ ≤ ‖∫ v, weightedModulation eta i H v * a v‖ * 4 :=
        mul_le_mul_of_nonneg_left hd (norm_nonneg _)
      _ ≤ _ := by nlinarith
  · have hd : (1 + |eta|) ^ 2 ≤ 4 * |eta| ^ 2 := by nlinarith
    calc
      _ ≤ ‖∫ v, weightedModulation eta i H v * a v‖ * (4 * |eta| ^ 2) :=
        mul_le_mul_of_nonneg_left hd (norm_nonneg _)
      _ ≤ _ := by nlinarith

end StrongSpherical.JointOscillation

namespace StrongSpherical.JointOscillation

open ProductOscillation QuadraticGraph
variable {m : ℕ}

/-- The ordered list of spatial input coordinates, excluding the last coordinate. -/
def spatialDerivativeList (m : ℕ) : List (Fin (m + 1)) :=
  (List.finRange m).map Fin.castSucc

@[simp] theorem length_spatialDerivativeList (m : ℕ) : (spatialDerivativeList m).length = m := by
  simp [spatialDerivativeList]

theorem nodup_spatialDerivativeList (m : ℕ) : (spatialDerivativeList m).Nodup :=
  (List.nodup_finRange m).map (Fin.castSucc_injective m)

@[simp] theorem castSucc_mem_spatialDerivativeList (i : Fin m) :
    i.castSucc ∈ spatialDerivativeList m := by simp [spatialDerivativeList]

@[simp] theorem last_not_mem_spatialDerivativeList (m : ℕ) :
    Fin.last m ∉ spatialDerivativeList m := by
  simp [spatialDerivativeList, Fin.castSucc_ne_last]

/-- Apply one derivative in each spatial input coordinate. -/
def spatialDerivatives (a : Space (m + 1) → ℂ) : Space (m + 1) → ℂ :=
  mixedDerivative (spatialDerivativeList m) a

/-- A factor depending on the first `m` input coordinates only. -/
def spatialFactor (G : Fin m → ℝ → ℂ) (v : Space (m + 1)) : ℂ :=
  ∏ i, G i (v i.castSucc)

theorem continuous_spatialFactor (G : Fin m → ℝ → ℂ) (hG : ∀ i, Continuous (G i)) :
    Continuous (spatialFactor G) := by
  apply continuous_finsetProd
  intro i _
  exact (hG i).comp (PiLp.continuous_apply 2 (fun _ : Fin (m + 1) => ℝ) i.castSucc)

theorem spatialFactor_normal_invariant (G : Fin m → ℝ → ℂ)
    (v : Space (m + 1)) (t : ℝ) :
    spatialFactor G (v + t • coordinateVector (Fin.last m)) = spatialFactor G v := by
  unfold spatialFactor
  apply Finset.prod_congr rfl
  intro i _
  simp [Fin.castSucc_ne_last]

/-- The full input character with an independent normal frequency. -/
def inputWave (w : Fin m → ℝ → ℂ) (eta : ℝ) (v : Space (m + 1)) : ℂ :=
  modulation eta (Fin.last m) v * spatialFactor w v

/-- A primitive in the normal coordinate; no norm bound for it will be needed. -/
def normalPrimitive (eta t : ℝ) : ℂ := ∫ s in 0..t, oscillation (eta * s)

theorem hasDerivAt_normalPrimitive (eta t : ℝ) :
    HasDerivAt (normalPrimitive eta) (oscillation (eta * t)) t := by
  have hc : Continuous (fun s => oscillation (eta * s)) :=
    continuous_oscillation.comp (continuous_const.mul continuous_id)
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- Append the normal character to the spatial characters. -/
def inputWaves (w : Fin m → ℝ → ℂ) (eta : ℝ) : Fin (m + 1) → ℝ → ℂ :=
  Fin.snoc w (fun s => oscillation (eta * s))

/-- Append a normal primitive to the spatial primitives. -/
def inputPrimitives (G : Fin m → ℝ → ℂ) (eta : ℝ) : Fin (m + 1) → ℝ → ℂ :=
  Fin.snoc G (normalPrimitive eta)

theorem continuous_inputWaves (w : Fin m → ℝ → ℂ) (eta : ℝ)
    (hw : ∀ i, Continuous (w i)) : ∀ j, Continuous (inputWaves w eta j) := by
  intro j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [inputWaves, Fin.snoc_last, Function.comp_def, Pi.mul_apply] using
      continuous_oscillation.comp (continuous_const.mul continuous_id : Continuous (fun s : ℝ => eta * s))
  · simpa only [inputWaves, Fin.snoc_castSucc] using hw i

theorem hasDerivAt_inputPrimitives (w G : Fin m → ℝ → ℂ) (eta : ℝ)
    (hG : ∀ i t, HasDerivAt (G i) (w i t) t) :
    ∀ j t, HasDerivAt (inputPrimitives G eta j) (inputWaves w eta j t) t := by
  intro j t
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa only [inputPrimitives, inputWaves, Fin.snoc_last] using hasDerivAt_normalPrimitive eta t
  · simpa only [inputPrimitives, inputWaves, Fin.snoc_castSucc] using hG i t

theorem weight_empty_eq_inputWave (w G : Fin m → ℝ → ℂ) (eta : ℝ) (v : Space (m + 1)) :
    weight (inputWaves w eta) (inputPrimitives G eta) ∅ v = inputWave w eta v := by
  simp only [weight, Finset.notMem_empty, if_false]
  rw [Fin.prod_univ_castSucc]
  simp only [inputWaves, Fin.snoc_castSucc, Fin.snoc_last, inputWave, spatialFactor,
    modulation_eq_oscillation]
  exact mul_comm _ _

theorem weight_spatial_eq_weightedModulation (w G : Fin m → ℝ → ℂ)
    (eta : ℝ) (v : Space (m + 1)) :
    weight (inputWaves w eta) (inputPrimitives G eta) (spatialDerivativeList m).toFinset v =
      weightedModulation eta (Fin.last m) (spatialFactor G) v := by
  unfold weight
  rw [Fin.prod_univ_castSucc]
  simp only [List.mem_toFinset, castSucc_mem_spatialDerivativeList,
    last_not_mem_spatialDerivativeList, if_true, if_false,
    inputPrimitives, inputWaves, Fin.snoc_castSucc, Fin.snoc_last,
    weightedModulation, spatialFactor, modulation_eq_oscillation]
  exact mul_comm _ _

/-- Spatial integration by parts preserves the normal character exactly. -/
theorem spatial_integration_by_parts (w G : Fin m → ℝ → ℂ) (eta : ℝ)
    (hw : ∀ i, Continuous (w i)) (hG : ∀ i t, HasDerivAt (G i) (w i t) t)
    {a : Space (m + 1) → ℂ} (ha : ContDiff ℝ m a) (hcompact : HasCompactSupport a) :
    (∫ v, inputWave w eta v * a v) = (-1 : ℂ) ^ m *
      ∫ v, weightedModulation eta (Fin.last m) (spatialFactor G) v * spatialDerivatives a v := by
  have hwi := continuous_inputWaves w eta hw
  have hGi := hasDerivAt_inputPrimitives w G eta hG
  have hGic : ∀ j, Continuous (inputPrimitives G eta j) := fun j =>
    continuous_iff_continuousAt.mpr fun t => (hGi j t).continuousAt
  have h := integral_weight_transfer (inputWaves w eta) (inputPrimitives G eta)
    hwi hGic hGi (spatialDerivativeList m) (nodup_spatialDerivativeList m) ∅
    (by simp) (by simpa only [length_spatialDerivativeList] using ha) hcompact
  simp only [Finset.empty_union, weight_empty_eq_inputWave,
    weight_spatial_eq_weightedModulation, length_spatialDerivativeList] at h
  exact h

end StrongSpherical.JointOscillation

namespace StrongSpherical.JointOscillation

open ProductOscillation QuadraticGraph
variable {m : ℕ}

/-- The two actual `L¹` derivative quantities needed for the joint estimate. -/
def amplitudeSeminorm (a : Space (m + 1) → ℂ) : ℝ :=
  (∫ v, ‖spatialDerivatives a v‖) +
    ∫ v, ‖coordinateDerivative (Fin.last m)
      (coordinateDerivative (Fin.last m) (spatialDerivatives a)) v‖

theorem amplitudeSeminorm_nonneg (a : Space (m + 1) → ℂ) : 0 ≤ amplitudeSeminorm a :=
  add_nonneg (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)

theorem contDiff_spatialDerivatives {a : Space (m + 1) → ℂ}
    (ha : ContDiff ℝ (m + 2 : ℕ) a) : ContDiff ℝ 2 (spatialDerivatives a) := by
  apply contDiff_mixedDerivative
  simpa only [length_spatialDerivativeList, Nat.add_comm] using ha

theorem integrable_spatialDerivatives {a : Space (m + 1) → ℂ}
    (ha : ContDiff ℝ (m + 2 : ℕ) a) (hcompact : HasCompactSupport a) :
    Integrable (spatialDerivatives a) :=
  (contDiff_spatialDerivatives ha).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_mixedDerivative _ hcompact)

theorem integrable_normalDerivatives_spatialDerivatives {a : Space (m + 1) → ℂ}
    (ha : ContDiff ℝ (m + 2 : ℕ) a) (hcompact : HasCompactSupport a) :
    Integrable (coordinateDerivative (Fin.last m)
      (coordinateDerivative (Fin.last m) (spatialDerivatives a))) := by
  have hc := contDiff_partial (Fin.last m) (r := 0)
    (contDiff_partial (Fin.last m) (r := 1) (contDiff_spatialDerivatives ha))
  exact hc.continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_partial _ (hasCompactSupport_partial _
      (hasCompactSupport_mixedDerivative _ hcompact)))

/-- Product of the spatial primitive bounds, on the original amplitude's support box. -/
theorem norm_spatialFactor_quadraticPrimitive_le
    (R c0 bmin : ℝ) (hR : 1 ≤ R) (hc0 : 0 < c0) (hbmin : 0 < bmin)
    (lambda tau sigma : ℝ) (b c : Fin m → ℝ) (x z : Space m)
    (hlambda : 1 ≤ lambda) (htau : c0 * lambda ≤ |tau|) (hb : ∀ i, bmin ≤ b i)
    (v : Space (m + 1)) (hv : ∀ i, |v i.castSucc - z i| ≤ R) :
    ‖spatialFactor (fun i => Quadratic1D.quadraticPrimitive R
      (tau * b i) (sigma * c i) (x i) (z i)) v‖ ≤
        Quadratic1D.oscillationConstant R (c0 * bmin) ^ m *
          ∏ i, spatialDecay lambda (x i - z i) := by
  let K := Quadratic1D.oscillationConstant R (c0 * bmin)
  have hbound : ∀ i : Fin m,
      ‖Quadratic1D.quadraticPrimitive R (tau * b i) (sigma * c i)
        (x i) (z i) (v i.castSucc)‖ ≤ K * spatialDecay lambda (x i - z i) := by
    intro i
    have hbpos : 0 < b i := lt_of_lt_of_le hbmin (hb i)
    have halpha : (c0 * bmin) * lambda ≤ |tau * b i| := by
      calc
        _ = (c0 * lambda) * bmin := by ring
        _ ≤ |tau| * b i := mul_le_mul htau (hb i) hbmin.le (abs_nonneg tau)
        _ = _ := by rw [abs_mul, abs_of_pos hbpos]
    have hvi := abs_le.mp (hv i)
    have ht : v i.castSucc ∈ Icc (z i - R - 1) (z i + R + 1) := by
      constructor <;> linarith [hvi.1, hvi.2]
    have h := Quadratic1D.norm_quadraticPrimitive_le R (c0 * bmin) hR (mul_pos hc0 hbmin)
      lambda (tau * b i) (sigma * c i) (x i) (z i) (v i.castSucc)
      (by linarith) halpha ht
    rw [spatialDecay, Real.rpow_neg (by positivity : 0 ≤ 1 + lambda * |x i - z i|),
      ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
    exact h
  unfold spatialFactor
  rw [norm_prod]
  calc
    _ ≤ ∏ i : Fin m, K * spatialDecay lambda (x i - z i) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hbound i)
    _ = _ := by rw [Finset.prod_mul_distrib]; simp [K]

/-- The joint spatial/normal oscillation bound for a general `C^(m+2)` compact
amplitude. Its constant is explicit and independent of the varying phase parameters. -/
theorem norm_integral_inputWave_le
    (R c0 bmin : ℝ) (hR : 1 ≤ R) (hc0 : 0 < c0) (hbmin : 0 < bmin)
    (lambda tau sigma eta : ℝ) (b c : Fin m → ℝ) (x z : Space m)
    (hlambda : 1 ≤ lambda) (htau : c0 * lambda ≤ |tau|) (hb : ∀ i, bmin ≤ b i)
    {a : Space (m + 1) → ℂ} (ha : ContDiff ℝ (m + 2 : ℕ) a)
    (hcompact : HasCompactSupport a) (hsupport : tsupport a ⊆ inputSupport R z) :
    ‖∫ v, inputWave (fun i => Quadratic1D.centeredWave (tau * b i) (sigma * c i)
        (x i) (z i)) eta v * a v‖ ≤
      4 * Quadratic1D.oscillationConstant R (c0 * bmin) ^ m * amplitudeSeminorm a *
        frequencyDecay eta * ∏ i, spatialDecay lambda (x i - z i) := by
  let w := fun i => Quadratic1D.centeredWave (tau * b i) (sigma * c i) (x i) (z i)
  let G := fun i => Quadratic1D.quadraticPrimitive R (tau * b i) (sigma * c i) (x i) (z i)
  let B := Quadratic1D.oscillationConstant R (c0 * bmin) ^ m *
    ∏ i, spatialDecay lambda (x i - z i)
  have hw : ∀ i, Continuous (w i) := fun _ => Quadratic1D.continuous_wave _ _ _
  have hG : ∀ i t, HasDerivAt (G i) (w i t) t := fun _ _ =>
    Quadratic1D.hasDerivAt_quadraticPrimitive _ _ _ _ _ _
  have hGc : ∀ i, Continuous (G i) := fun i =>
    continuous_iff_continuousAt.mpr fun t => (hG i t).continuousAt
  have hDa := contDiff_spatialDerivatives ha
  have hDcompact : HasCompactSupport (spatialDerivatives a) :=
    hasCompactSupport_mixedDerivative _ hcompact
  have hbound : ∀ v ∈ tsupport (spatialDerivatives a), ‖spatialFactor G v‖ ≤ B := by
    intro v hv
    have hav : v ∈ tsupport a := tsupport_mixedDerivative_subset _ a hv
    exact norm_spatialFactor_quadraticPrimitive_le R c0 bmin hR hc0 hbmin
      lambda tau sigma b c x z hlambda htau hb v (hsupport hav).1
  have h := norm_integral_weighted_le_frequencyDecay eta (Fin.last m) B
    (continuous_spatialFactor G hGc) (spatialFactor_normal_invariant G)
    hDa hDcompact hbound
  rw [spatial_integration_by_parts w G eta hw hG
    (ha.of_le (by norm_cast; omega)) hcompact, norm_mul, norm_pow]
  simp only [norm_neg, norm_one, one_pow, one_mul]
  calc
    _ ≤ 4 * B * amplitudeSeminorm a * frequencyDecay eta := h
    _ = _ := by dsimp [B]; ring

/-- Identify the input character with the original joint polynomial phase. -/
theorem inputWave_quadratic_eq_oscillation
    (tau sigma eta : ℝ) (b c : Fin m → ℝ) (x z : Space m) (v : Space (m + 1)) :
    inputWave (fun i => Quadratic1D.centeredWave (tau * b i) (sigma * c i)
      (x i) (z i)) eta v =
      oscillation (eta * normalInput v +
        productPhase tau sigma b c x z (spatialInput v)) := by
  rw [oscillation_add]
  unfold inputWave spatialFactor
  rw [modulation_eq_oscillation]
  congr 1
  simpa only [oscillation, spatialInput_apply] using
    product_centeredWave_eq_exp tau sigma b c x z (spatialInput v)

/-- The graph-pair phase differs from the joint input character by a constant of modulus one. -/
theorem graphPair_oscillation_eq (coeff : GraphCoefficients m)
    (tau sigma : ℝ) (x z : Space m) (v : Space (m + 1)) :
    oscillation (tau * graphGap coeff x v - sigma * graphGap coeff z v) =
      oscillation (sigma * coeff.constant z - tau * coeff.constant x) *
        inputWave (fun i => Quadratic1D.centeredWave
          (tau * coeff.quadratic x i) (sigma * coeff.quadratic z i) (x i) (z i))
          (tau - sigma) v := by
  rw [phase_difference]
  have hp : (tau - sigma) * normalInput v + sigma * coeff.constant z - tau * coeff.constant x +
      productPhase tau sigma (coeff.quadratic x) (coeff.quadratic z) x z (spatialInput v) =
      (sigma * coeff.constant z - tau * coeff.constant x) +
        ((tau - sigma) * normalInput v +
          productPhase tau sigma (coeff.quadratic x) (coeff.quadratic z) x z (spatialInput v)) := by ring
  rw [hp, oscillation_add, ← inputWave_quadratic_eq_oscillation]

/-- The oscillatory input-integral estimate underlying (3.19), retaining an explicit
amplitude seminorm. Coefficient functions are evaluated, never differentiated. -/
theorem norm_integral_graphPair_le
    (R c0 bmin : ℝ) (hR : 1 ≤ R) (hc0 : 0 < c0) (hbmin : 0 < bmin)
    (coeff : GraphCoefficients m) (lambda tau sigma : ℝ) (x z : Space m)
    (hlambda : 1 ≤ lambda) (htau : c0 * lambda ≤ |tau|)
    (hb : ∀ i, bmin ≤ coeff.quadratic x i)
    {a : Space (m + 1) → ℂ} (ha : ContDiff ℝ (m + 2 : ℕ) a)
    (hcompact : HasCompactSupport a) (hsupport : tsupport a ⊆ inputSupport R z) :
    ‖∫ v, oscillation (tau * graphGap coeff x v - sigma * graphGap coeff z v) * a v‖ ≤
      4 * Quadratic1D.oscillationConstant R (c0 * bmin) ^ m * amplitudeSeminorm a *
        frequencyDecay (tau - sigma) * ∏ i, spatialDecay lambda (x i - z i) := by
  have heq : (∫ v, oscillation (tau * graphGap coeff x v - sigma * graphGap coeff z v) * a v) =
      oscillation (sigma * coeff.constant z - tau * coeff.constant x) *
        ∫ v, inputWave (fun i => Quadratic1D.centeredWave
          (tau * coeff.quadratic x i) (sigma * coeff.quadratic z i) (x i) (z i))
          (tau - sigma) v * a v := by
    simp_rw [graphPair_oscillation_eq, mul_assoc]
    exact integral_const_mul _ _
  rw [heq, norm_mul, norm_oscillation, one_mul]
  exact norm_integral_inputWave_le R c0 bmin hR hc0 hbmin
    lambda tau sigma (tau - sigma) (coeff.quadratic x) (coeff.quadratic z) x z
    hlambda htau hb ha hcompact hsupport

/-- The constant is chosen before all varying coefficients, frequencies, points and amplitudes.
A bound for the displayed amplitude seminorm can be inserted without any further oscillatory hypothesis. -/
theorem exists_uniform_graphPair_bound (m : ℕ) (R c0 bmin : ℝ)
    (hR : 1 ≤ R) (hc0 : 0 < c0) (hbmin : 0 < bmin) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (coeff : GraphCoefficients m) (lambda tau sigma : ℝ) (x z : Space m)
        (a : Space (m + 1) → ℂ) (M : ℝ),
        1 ≤ lambda → c0 * lambda ≤ |tau| → (∀ i, bmin ≤ coeff.quadratic x i) →
        ContDiff ℝ (m + 2 : ℕ) a → HasCompactSupport a →
        tsupport a ⊆ inputSupport R z → amplitudeSeminorm a ≤ M →
        ‖∫ v, oscillation (tau * graphGap coeff x v - sigma * graphGap coeff z v) * a v‖ ≤
          C * M * frequencyDecay (tau - sigma) * ∏ i, spatialDecay lambda (x i - z i) := by
  have hK := Quadratic1D.oscillationConstant_pos hR (mul_pos hc0 hbmin)
  refine ⟨4 * Quadratic1D.oscillationConstant R (c0 * bmin) ^ m,
    mul_pos (by norm_num) (pow_pos hK m), ?_⟩
  intro coeff lambda tau sigma x z a M hlambda htau hb ha hcompact hsupport hM
  calc
    _ ≤ 4 * Quadratic1D.oscillationConstant R (c0 * bmin) ^ m * amplitudeSeminorm a *
        frequencyDecay (tau - sigma) * ∏ i, spatialDecay lambda (x i - z i) :=
      norm_integral_graphPair_le R c0 bmin hR hc0 hbmin coeff lambda tau sigma x z
        hlambda htau hb ha hcompact hsupport
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _
        (Finset.prod_nonneg fun i _ => spatialDecay_nonneg _ _ (by linarith))
      apply mul_le_mul_of_nonneg_right _ (frequencyDecay_nonneg _)
      exact mul_le_mul_of_nonneg_left hM (mul_nonneg (by norm_num) (pow_nonneg hK.le m))

/-- A paired amplitude has support inside the support of its second factor. -/
theorem tsupport_pairAmplitude_subset_right
    (a : Space m → Space (m + 1) → ℂ) (x z : Space m) :
    tsupport (pairAmplitude a x z) ⊆ tsupport (a z) := by
  apply closure_mono
  intro v hv hz
  exact hv (by simp [pairAmplitude, hz])

theorem hasCompactSupport_pairAmplitude
    (a : Space m → Space (m + 1) → ℂ) (x z : Space m)
    (hcompact : HasCompactSupport (a z)) : HasCompactSupport (pairAmplitude a x z) :=
  hcompact.of_isClosed_subset (isClosed_tsupport _) (tsupport_pairAmplitude_subset_right a x z)

theorem contDiff_pairAmplitude (a : Space m → Space (m + 1) → ℂ) (x z : Space m)
    {k : ℕ} (hax : ContDiff ℝ k (a x)) (haz : ContDiff ℝ k (a z)) :
    ContDiff ℝ k (pairAmplitude a x z) := by
  unfold pairAmplitude
  exact hax.mul (Complex.conjCLE.contDiff.comp haz)

/-- Specialize the joint estimate to the actual amplitude product in the Gram kernel. -/
theorem norm_integral_pairAmplitude_le
    (R c0 bmin : ℝ) (hR : 1 ≤ R) (hc0 : 0 < c0) (hbmin : 0 < bmin)
    (coeff : GraphCoefficients m) (lambda tau sigma : ℝ) (x z : Space m)
    (hlambda : 1 ≤ lambda) (htau : c0 * lambda ≤ |tau|)
    (hb : ∀ i, bmin ≤ coeff.quadratic x i)
    (a : Space m → Space (m + 1) → ℂ)
    (hax : ContDiff ℝ (m + 2 : ℕ) (a x)) (haz : ContDiff ℝ (m + 2 : ℕ) (a z))
    (hcompact : HasCompactSupport (a z)) (hsupport : tsupport (a z) ⊆ inputSupport R z) :
    ‖∫ v, oscillation (tau * graphGap coeff x v - sigma * graphGap coeff z v) *
        pairAmplitude a x z v‖ ≤
      4 * Quadratic1D.oscillationConstant R (c0 * bmin) ^ m *
        amplitudeSeminorm (pairAmplitude a x z) * frequencyDecay (tau - sigma) *
          ∏ i, spatialDecay lambda (x i - z i) :=
  norm_integral_graphPair_le R c0 bmin hR hc0 hbmin coeff lambda tau sigma x z
    hlambda htau hb (contDiff_pairAmplitude a x z hax haz)
    (hasCompactSupport_pairAmplitude a x z hcompact)
    ((tsupport_pairAmplitude_subset_right a x z).trans hsupport)

end StrongSpherical.JointOscillation
