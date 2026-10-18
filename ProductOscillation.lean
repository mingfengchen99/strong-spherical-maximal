import Quadratic1D
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Data.List.FinRange

/-!
# Product oscillation for a general amplitude

Lemma 3.1 of arXiv:2609.32421v2. We transfer one derivative in each
coordinate onto the amplitude using the multidimensional integration by
parts theorem in mathlib. That theorem includes the requisite Fubini argument.
The amplitude is an arbitrary complex-valued function on Euclidean space.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace StrongSpherical.ProductOscillation

variable {n : ℕ}

/-- The `i`-th Euclidean coordinate vector. -/
def coordinateVector (i : Fin n) : Space n := PiLp.single 2 i 1

@[simp] theorem coordinateVector_apply (i j : Fin n) :
    coordinateVector i j = if j = i then 1 else 0 := by
  simp [coordinateVector, PiLp.single_apply]

/-- The actual Fréchet derivative in a coordinate direction. -/
def coordinateDerivative (i : Fin n) (a : Space n → ℂ) (u : Space n) : ℂ :=
  fderiv ℝ a u (coordinateVector i)

/-- Apply the coordinate derivatives in the order listed. In particular,
`mixedDerivative (List.finRange n) a = D_{n-1} ⋯ D_0 a`. -/
def mixedDerivative : List (Fin n) → (Space n → ℂ) → Space n → ℂ
  | [], a => a
  | i :: l, a => mixedDerivative l (coordinateDerivative i a)

theorem tsupport_partial_subset (i : Fin n) (a : Space n → ℂ) :
    tsupport (coordinateDerivative i a) ⊆ tsupport a :=
  tsupport_fderiv_apply_subset ℝ (coordinateVector i)

theorem hasCompactSupport_partial (i : Fin n) {a : Space n → ℂ}
    (ha : HasCompactSupport a) : HasCompactSupport (coordinateDerivative i a) :=
  ha.of_isClosed_subset (isClosed_tsupport _) (tsupport_partial_subset i a)

theorem contDiff_partial (i : Fin n) {r : ℕ} {a : Space n → ℂ}
    (ha : ContDiff ℝ (r + 1 : ℕ) a) : ContDiff ℝ r (coordinateDerivative i a) := by
  exact (ha.fderiv_right (by norm_cast)).clm_apply contDiff_const

theorem tsupport_mixedDerivative_subset (l : List (Fin n)) (a : Space n → ℂ) :
    tsupport (mixedDerivative l a) ⊆ tsupport a := by
  induction l generalizing a with
  | nil => exact subset_rfl
  | cons i l ih => exact (ih (coordinateDerivative i a)).trans (tsupport_partial_subset i a)

theorem hasCompactSupport_mixedDerivative (l : List (Fin n)) {a : Space n → ℂ}
    (ha : HasCompactSupport a) : HasCompactSupport (mixedDerivative l a) :=
  ha.of_isClosed_subset (isClosed_tsupport _) (tsupport_mixedDerivative_subset l a)

theorem contDiff_mixedDerivative (l : List (Fin n)) (r : ℕ) {a : Space n → ℂ}
    (ha : ContDiff ℝ (r + l.length : ℕ) a) :
    ContDiff ℝ r (mixedDerivative l a) := by
  induction l generalizing a with
  | nil => simpa [mixedDerivative] using ha
  | cons i l ih =>
    apply ih
    apply contDiff_partial
    simpa only [List.length_cons, Nat.add_assoc] using ha

/-- A product in which the coordinates in `S` have already been replaced
by their primitives. -/
def weight (w G : Fin n → ℝ → ℂ) (S : Finset (Fin n)) (u : Space n) : ℂ :=
  ∏ i, if i ∈ S then G i (u i) else w i (u i)

theorem continuous_weight (w G : Fin n → ℝ → ℂ) (S : Finset (Fin n))
    (hw : ∀ i, Continuous (w i)) (hG : ∀ i, Continuous (G i)) :
    Continuous (weight w G S) := by
  apply continuous_finsetProd
  intro i _
  by_cases hi : i ∈ S
  · simpa only [if_pos hi, Function.comp_def] using
      (hG i).comp (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i)
  · simpa only [if_neg hi, Function.comp_def] using
      (hw i).comp (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i)

/-- Along coordinate `i`, all other factors are constant. Only the primitive
in this coordinate is differentiated. -/
theorem hasLineDerivAt_weight_insert
    (w G : Fin n → ℝ → ℂ) (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S)
    (hG : ∀ j t, HasDerivAt (G j) (w j t) t) (u : Space n) :
    HasLineDerivAt ℝ (weight w G (insert i S)) (weight w G S u) u
      (coordinateVector i) := by
  let H := ∏ j ∈ Finset.univ.erase i, if j ∈ S then G j (u j) else w j (u j)
  have hpath : ∀ t : ℝ, weight w G (insert i S) (u + t • coordinateVector i) =
      G i (u i + t) * H := by
    intro t
    unfold weight
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    congr 1
    · simp
    · apply Finset.prod_congr rfl
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      simp [hji]
  have hvalue : weight w G S u = w i (u i) * H := by
    unfold weight
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    simp only [if_neg hi]
    rfl
  unfold HasLineDerivAt
  simp_rw [hpath]
  rw [hvalue]
  convert! ((hG i (u i)).scomp_of_eq 0 ((hasDerivAt_id 0).const_add (u i))
    (by simp)).mul_const H using 1
  simp

theorem integrable_weight_mul
    (w G : Fin n → ℝ → ℂ) (S : Finset (Fin n))
    (hw : ∀ i, Continuous (w i)) (hG : ∀ i, Continuous (G i))
    {a : Space n → ℂ} (ha : Continuous a) (hcompact : HasCompactSupport a) :
    Integrable (fun u => weight w G S u * a u) :=
  ((continuous_weight w G S hw hG).mul ha).integrable_of_hasCompactSupport hcompact.mul_left

/-- One coordinate of the integration-by-parts identity. Compact support
of the amplitude makes every term integrable and removes boundary terms. -/
theorem integral_weight_mul_eq_neg_partial
    (w G : Fin n → ℝ → ℂ) (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S)
    (hw : ∀ j, Continuous (w j)) (hGc : ∀ j, Continuous (G j))
    (hG : ∀ j t, HasDerivAt (G j) (w j t) t)
    {a : Space n → ℂ} (ha : Differentiable ℝ a) (hpa : Continuous (coordinateDerivative i a))
    (hcompact : HasCompactSupport a) :
    (∫ u, weight w G S u * a u) =
      -(∫ u, weight w G (insert i S) u * coordinateDerivative i a u) := by
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Space n))) (B := ContinuousLinearMap.mul ℝ ℂ)
    (f := a) (f' := coordinateDerivative i a) (g := weight w G (insert i S)) (g' := weight w G S)
    (v := coordinateVector i)
    (by
      simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
        integrable_weight_mul w G (insert i S) hw hGc hpa
        (hasCompactSupport_partial i hcompact))
    (by simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
      integrable_weight_mul w G S hw hGc ha.continuous hcompact)
    (by simpa only [ContinuousLinearMap.mul_apply', mul_comm] using
      integrable_weight_mul w G (insert i S) hw hGc ha.continuous hcompact)
    (fun u _ => (ha u).hasFDerivAt.hasLineDerivAt (coordinateVector i))
    (fun u _ => hasLineDerivAt_weight_insert w G S i hi hG u)
  simpa only [ContinuousLinearMap.mul_apply', mul_comm] using h

/-- Transfer every derivative in a list of distinct, as-yet-unprocessed
coordinates. The smoothness required is exactly the length of the list. -/
theorem integral_weight_transfer
    (w G : Fin n → ℝ → ℂ)
    (hw : ∀ i, Continuous (w i)) (hGc : ∀ i, Continuous (G i))
    (hG : ∀ i t, HasDerivAt (G i) (w i t) t)
    (l : List (Fin n)) (hl : l.Nodup) (S : Finset (Fin n))
    (hdisjoint : ∀ i ∈ l, i ∉ S) {a : Space n → ℂ}
    (ha : ContDiff ℝ l.length a) (hcompact : HasCompactSupport a) :
    (∫ u, weight w G S u * a u) = (-1 : ℂ) ^ l.length *
      ∫ u, weight w G (S ∪ l.toFinset) u * mixedDerivative l a u := by
  induction l generalizing S a with
  | nil => simp [mixedDerivative]
  | cons i l ih =>
    have hnodup := List.nodup_cons.mp hl
    have hi : i ∉ S := hdisjoint i (by simp)
    have htail : ∀ j ∈ l, j ∉ insert i S := by
      intro j hj
      simp only [Finset.mem_insert, not_or]
      constructor
      · intro hji
        subst j
        exact hnodup.1 hj
      · exact hdisjoint j (by simp [hj])
    have hpartial : ContDiff ℝ l.length (coordinateDerivative i a) := by
      apply contDiff_partial
      simpa only [List.length_cons] using ha
    rw [integral_weight_mul_eq_neg_partial w G S i hi hw hGc hG
      (ha.differentiable (by simp)) hpartial.continuous hcompact,
      ih hnodup.2 (insert i S) htail hpartial (hasCompactSupport_partial i hcompact)]
    have hsets : insert i S ∪ l.toFinset = S ∪ (i :: l).toFinset := by
      ext j
      simp only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons]
      tauto
    rw [hsets]
    simp only [List.length_cons, mixedDerivative, pow_succ]
    ring

/-- The full multidimensional integration-by-parts identity. The derivatives
on the right are applied to the general amplitude, one in every coordinate. -/
theorem integral_product_eq_mixedDerivative
    (w G : Fin n → ℝ → ℂ)
    (hw : ∀ i, Continuous (w i)) (hGc : ∀ i, Continuous (G i))
    (hG : ∀ i t, HasDerivAt (G i) (w i t) t)
    {a : Space n → ℂ} (ha : ContDiff ℝ n a) (hcompact : HasCompactSupport a) :
    (∫ u : Space n, (∏ i, w i (u i)) * a u) = (-1 : ℂ) ^ n *
      ∫ u : Space n, (∏ i, G i (u i)) * mixedDerivative (List.finRange n) a u := by
  have h := integral_weight_transfer w G hw hGc hG (List.finRange n)
    (List.nodup_finRange n) ∅ (by simp) (by simpa using ha) hcompact
  simpa [weight] using h

/-- The abstract product estimate: uniform primitive bounds multiply, while
the amplitude contributes the `L¹` norm of its mixed coordinate derivative. -/
theorem norm_integral_product_le
    (w G : Fin n → ℝ → ℂ)
    (hw : ∀ i, Continuous (w i)) (hGc : ∀ i, Continuous (G i))
    (hG : ∀ i t, HasDerivAt (G i) (w i t) t)
    (M : Fin n → ℝ)
    {a : Space n → ℂ} (ha : ContDiff ℝ n a) (hcompact : HasCompactSupport a)
    (hbound : ∀ u ∈ tsupport a, ∀ i, ‖G i (u i)‖ ≤ M i) :
    ‖∫ u : Space n, (∏ i, w i (u i)) * a u‖ ≤
      (∏ i, M i) * ∫ u : Space n, ‖mixedDerivative (List.finRange n) a u‖ := by
  let D := mixedDerivative (List.finRange n) a
  have hDc : Continuous D :=
    (contDiff_mixedDerivative (List.finRange n) 0 (by simpa using ha)).continuous
  have hDcpt : HasCompactSupport D := hasCompactSupport_mixedDerivative _ hcompact
  have hDint : Integrable D := hDc.integrable_of_hasCompactSupport hDcpt
  have hp : ∀ u : Space n, ‖(∏ i, G i (u i)) * D u‖ ≤ (∏ i, M i) * ‖D u‖ := by
    intro u
    by_cases hzero : D u = 0
    · simp [hzero]
    · have hu : u ∈ tsupport a :=
        tsupport_mixedDerivative_subset (List.finRange n) a
          (subset_closure (show u ∈ Function.support D from hzero))
      rw [norm_mul, norm_prod]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      exact Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => hbound u hu i)
  rw [integral_product_eq_mixedDerivative w G hw hGc hG ha hcompact,
    norm_mul, norm_pow]
  simp only [norm_neg, norm_one, one_pow, one_mul]
  calc
    _ ≤ ∫ u : Space n, (∏ i, M i) * ‖D u‖ :=
      norm_integral_le_of_norm_le (hDint.norm.const_mul _) (Filter.Eventually.of_forall hp)
    _ = _ := integral_const_mul _ _

/-- The closed cube centered at `z`, expressed in Euclidean coordinates. -/
def supportBox (z : Space n) (R : ℝ) : Set (Space n) :=
  {u | ∀ i, |u i - z i| ≤ R}

theorem supportBox_mono (z : Space n) {R S : ℝ} (hRS : R ≤ S) :
    supportBox z R ⊆ supportBox z S := fun _ hu i => (hu i).trans hRS

/-- The mixed derivative vanishes outside any box containing the original
amplitude's support. Thus the global integral can be restricted to the box. -/
theorem integral_mixedDerivative_eq_setIntegral
    (l : List (Fin n)) (F a : Space n → ℂ) (z : Space n) (R : ℝ)
    (hsupport : tsupport a ⊆ supportBox z R) :
    (∫ u, F u * mixedDerivative l a u) =
      ∫ u in supportBox z (R + 1), F u * mixedDerivative l a u := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro u hu
  have hz : mixedDerivative l a u = 0 := by
    by_contra hne
    apply hu
    exact supportBox_mono z (by linarith : R ≤ R + 1)
      (hsupport (tsupport_mixedDerivative_subset l a
        (subset_closure (show u ∈ Function.support (mixedDerivative l a) from hne))))
  simp only [hz, mul_zero]

/-- The sum of the one-coordinate quadratic phases in (3.2). -/
def productPhase (tau sigma : ℝ) (b c : Fin n → ℝ) (x z u : Space n) : ℝ :=
  ∑ i, Quadratic1D.quadraticPhase tau sigma (b i) (c i) (x i) (z i) (u i)

theorem product_centeredWave_eq_exp
    (tau sigma : ℝ) (b c : Fin n → ℝ) (x z u : Space n) :
    (∏ i, Quadratic1D.centeredWave (tau * b i) (sigma * c i) (x i) (z i) (u i)) =
      Complex.exp (((2 * Real.pi * productPhase tau sigma b c x z u : ℝ) : ℂ)
        * Complex.I) := by
  simp_rw [Quadratic1D.centeredWave_eq_exp]
  rw [← Complex.exp_sum]
  congr 1
  unfold productPhase Quadratic1D.quadraticPhase
  push_cast
  simp only [Finset.mul_sum, Finset.sum_mul]

/-- Equation (3.8), including the restriction to the enlarged support box.
Only `C^n` regularity of the general amplitude is required. -/
theorem quadratic_integration_by_parts
    (R tau sigma : ℝ) (b c : Fin n → ℝ) (x z : Space n)
    {a : Space n → ℂ} (ha : ContDiff ℝ n a) (hcompact : HasCompactSupport a)
    (hsupport : tsupport a ⊆ supportBox z R) :
    (∫ u : Space n,
      Complex.exp (((2 * Real.pi * productPhase tau sigma b c x z u : ℝ) : ℂ) * Complex.I)
        * a u) = (-1 : ℂ) ^ n *
      ∫ u in supportBox z (R + 1),
        (∏ i, Quadratic1D.quadraticPrimitive R (tau * b i) (sigma * c i)
          (x i) (z i) (u i)) * mixedDerivative (List.finRange n) a u := by
  let w := fun i => Quadratic1D.centeredWave (tau * b i) (sigma * c i) (x i) (z i)
  let G := fun i => Quadratic1D.quadraticPrimitive R (tau * b i) (sigma * c i) (x i) (z i)
  have hw : ∀ i, Continuous (w i) := fun _ => Quadratic1D.continuous_wave _ _ _
  have hG : ∀ i t, HasDerivAt (G i) (w i t) t :=
    fun _ _ => Quadratic1D.hasDerivAt_quadraticPrimitive _ _ _ _ _ _
  have hGc : ∀ i, Continuous (G i) := fun i =>
    continuous_iff_continuousAt.mpr fun t => (hG i t).continuousAt
  have h := integral_product_eq_mixedDerivative w G hw hGc hG ha hcompact
  simp only [w, product_centeredWave_eq_exp] at h
  rw [integral_mixedDerivative_eq_setIntegral (List.finRange n)
    (fun u => ∏ i, G i (u i)) a z R hsupport] at h
  exact h

/-- Lemma 3.1 / (3.3), with an explicit uniform constant. The assumptions
from (3.1) that are not needed for the proof are omitted: no upper coefficient
bounds and no restriction on `σ` are necessary for this estimate. -/
theorem norm_integral_quadratic_product_le
    (R c0 bmin : ℝ) (hR : 1 ≤ R) (hc0 : 0 < c0) (hbmin : 0 < bmin)
    (lambda tau sigma : ℝ) (b c : Fin n → ℝ) (x z : Space n)
    (hlambda : 1 ≤ lambda) (htau : c0 * lambda ≤ |tau|)
    (hb : ∀ i, bmin ≤ b i)
    {a : Space n → ℂ} (ha : ContDiff ℝ n a) (hcompact : HasCompactSupport a)
    (hsupport : tsupport a ⊆ supportBox z R) :
    ‖∫ u : Space n,
        Complex.exp (((2 * Real.pi * productPhase tau sigma b c x z u : ℝ) : ℂ) * Complex.I)
          * a u‖ ≤
      Quadratic1D.oscillationConstant R (c0 * bmin) ^ n *
        (∫ u : Space n, ‖mixedDerivative (List.finRange n) a u‖) *
          ∏ i, (1 + lambda * |x i - z i|) ^ (-(1 / 2 : ℝ)) := by
  let K := Quadratic1D.oscillationConstant R (c0 * bmin)
  let w := fun i => Quadratic1D.centeredWave (tau * b i) (sigma * c i) (x i) (z i)
  let G := fun i => Quadratic1D.quadraticPrimitive R (tau * b i) (sigma * c i) (x i) (z i)
  let d := fun i => (1 + lambda * |x i - z i|) ^ (-(1 / 2 : ℝ))
  have hw : ∀ i, Continuous (w i) := fun _ => Quadratic1D.continuous_wave _ _ _
  have hG : ∀ i t, HasDerivAt (G i) (w i t) t :=
    fun _ _ => Quadratic1D.hasDerivAt_quadraticPrimitive _ _ _ _ _ _
  have hGc : ∀ i, Continuous (G i) := fun i =>
    continuous_iff_continuousAt.mpr fun t => (hG i t).continuousAt
  have hbound : ∀ u ∈ tsupport a, ∀ i, ‖G i (u i)‖ ≤ K * d i := by
    intro u hu i
    have hbpos : 0 < b i := lt_of_lt_of_le hbmin (hb i)
    have halpha : (c0 * bmin) * lambda ≤ |tau * b i| := by
      calc
        _ = (c0 * lambda) * bmin := by ring
        _ ≤ |tau| * b i := mul_le_mul htau (hb i) hbmin.le (abs_nonneg tau)
        _ = _ := by rw [abs_mul, abs_of_pos hbpos]
    have hui := hsupport hu i
    have ht : u i ∈ Icc (z i - R - 1) (z i + R + 1) := by
      have habs := abs_le.mp hui
      constructor <;> linarith [habs.1, habs.2]
    have h := Quadratic1D.norm_quadraticPrimitive_le R (c0 * bmin) hR (mul_pos hc0 hbmin)
      lambda (tau * b i) (sigma * c i) (x i) (z i) (u i)
      (by linarith) halpha ht
    dsimp [d]
    rw [Real.rpow_neg (by positivity : 0 ≤ 1 + lambda * |x i - z i|),
      ← Real.sqrt_eq_rpow, ← div_eq_mul_inv]
    exact h
  have h := norm_integral_product_le w G hw hGc hG (fun i => K * d i) ha hcompact hbound
  have hprod : (∏ i, K * d i) = K ^ n * ∏ i, d i := by
    rw [Finset.prod_mul_distrib]
    simp
  simp only [w, product_centeredWave_eq_exp] at h
  calc
    _ ≤ (∏ i, K * d i) * ∫ u : Space n, ‖mixedDerivative (List.finRange n) a u‖ := h
    _ = _ := by rw [hprod]; ring

/-- A single constant, chosen before all varying phase parameters and the
amplitude, gives the full product bound in dimension `n`. -/
theorem exists_uniform_product_bound
    (n : ℕ) (R c0 bmin : ℝ) (hR : 1 ≤ R) (hc0 : 0 < c0) (hbmin : 0 < bmin) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (lambda tau sigma : ℝ) (b c : Fin n → ℝ) (x z : Space n) (a : Space n → ℂ),
        1 ≤ lambda → c0 * lambda ≤ |tau| → (∀ i, bmin ≤ b i) →
        ContDiff ℝ n a → HasCompactSupport a → tsupport a ⊆ supportBox z R →
        ‖∫ u : Space n,
            Complex.exp (((2 * Real.pi * productPhase tau sigma b c x z u : ℝ) : ℂ)
              * Complex.I) * a u‖ ≤
          C * (∫ u : Space n, ‖mixedDerivative (List.finRange n) a u‖) *
            ∏ i, (1 + lambda * |x i - z i|) ^ (-(1 / 2 : ℝ)) := by
  refine ⟨Quadratic1D.oscillationConstant R (c0 * bmin) ^ n,
    pow_pos (Quadratic1D.oscillationConstant_pos hR (mul_pos hc0 hbmin)) n, ?_⟩
  intro lambda tau sigma b c x z a hlambda htau hb ha hcompact hsupport
  exact norm_integral_quadratic_product_le R c0 bmin hR hc0 hbmin
    lambda tau sigma b c x z hlambda htau hb ha hcompact hsupport

end StrongSpherical.ProductOscillation
