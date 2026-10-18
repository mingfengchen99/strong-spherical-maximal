import Definitions
import SchurTest
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Product cutoff energy and the large-box limit

These are the measure-theoretic steps in §5.1. The cutoff is the actual
indicator of a coordinate cube, and its energy is computed with the product
of the two Euclidean Lebesgue measures. The large-box argument retains
extended nonnegative values, including zero and infinity.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology

namespace StrongSpherical.MarginalEnergy

/-- The closed coordinate cube in Euclidean space; dimension zero is allowed. -/
def coordinateBox (j : ℕ) (L : ℝ) : Set (Space j) :=
  {v | ∀ i, v i ∈ Icc (-L) L}

@[simp] theorem mem_coordinateBox {j : ℕ} {L : ℝ} {v : Space j} :
    v ∈ coordinateBox j L ↔ ∀ i, -L ≤ v i ∧ v i ≤ L := Iff.rfl

theorem measurableSet_coordinateBox (j : ℕ) (L : ℝ) :
    MeasurableSet (coordinateBox j L) := by
  have h : coordinateBox j L = ⋂ i : Fin j, {v : Space j | v i ∈ Icc (-L) L} := by
    ext v
    simp [coordinateBox]
  rw [h]
  exact MeasurableSet.iInter fun i =>
    (by fun_prop : Measurable (fun v : Space j => v i)) measurableSet_Icc

/-- The cube volume is exact, also when the cube is empty or has dimension zero. -/
theorem volume_coordinateBox (j : ℕ) (L : ℝ) :
    volume (coordinateBox j L) = ENNReal.ofReal (2 * L) ^ j := by
  have hbox : coordinateBox j L =
      WithLp.ofLp ⁻¹' (Set.pi univ fun _ : Fin j => Icc (-L) L) := by
    ext v
    simp only [coordinateBox, mem_preimage, mem_setOf_eq, Set.mem_pi, mem_univ, true_implies]
  have hmeas : MeasurableSet (Set.pi univ fun _ : Fin j => Icc (-L) L) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).isClosed.measurableSet
  rw [hbox, (PiLp.volume_preserving_ofLp (Fin j)).measure_preimage
    hmeas.nullMeasurableSet]
  change Measure.pi (fun _ : Fin j => (volume : Measure ℝ))
    (Set.pi univ fun _ => Icc (-L) L) = _
  rw [Measure.pi_pi]
  simp [Real.volume_Icc, sub_neg_eq_add, two_mul]

/-- The input used to test a coordinate marginal: g times a box indicator. -/
def cutoffInput {m j : ℕ} (L : ℝ) (g : Space m → ℂ)
    (p : Space m × Space j) : ℂ :=
  g p.1 * (coordinateBox j L).indicator (fun _ => 1) p.2

theorem measurable_cutoffInput {m j : ℕ} (L : ℝ) (g : Space m → ℂ)
    (hg : Measurable g) : Measurable (cutoffInput (j := j) L g) :=
  (hg.comp measurable_fst).mul
    ((measurable_const.indicator (measurableSet_coordinateBox j L)).comp measurable_snd)

/-- Product box factorization for any measurable nonnegative quantity. -/
theorem lintegral_coordinateBox_product {m j : ℕ} (L : ℝ)
    (F : Space m → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ p : Space m × Space j,
      (coordinateBox j L).indicator (fun _ => F p.1) p.2
      ∂(volume : Measure (Space m)).prod (volume : Measure (Space j))) =
      ENNReal.ofReal (2 * L) ^ j * ∫⁻ u, F u := by
  have heq : ∀ p : Space m × Space j,
      (coordinateBox j L).indicator (fun _ => F p.1) p.2 =
        F p.1 * (coordinateBox j L).indicator (fun _ => (1 : ℝ≥0∞)) p.2 := by
    intro p
    by_cases hp : p.2 ∈ coordinateBox j L <;> simp [hp]
  simp_rw [heq]
  rw [lintegral_prod_mul hF.aemeasurable
    (measurable_const.indicator (measurableSet_coordinateBox j L)).aemeasurable,
    lintegral_indicator_const (measurableSet_coordinateBox j L), one_mul,
    volume_coordinateBox, mul_comm]

/-- Tonelli computes the full product cutoff energy without an integrability assumption. -/
theorem lintegral_cutoffInput_sq {m j : ℕ} (L : ℝ) (g : Space m → ℂ)
    (hg : Measurable g) :
    (∫⁻ p : Space m × Space j, ‖cutoffInput L g p‖ₑ ^ 2
      ∂(volume : Measure (Space m)).prod (volume : Measure (Space j))) =
      ENNReal.ofReal (2 * L) ^ j * ∫⁻ u, ‖g u‖ₑ ^ 2 := by
  have heq : ∀ p : Space m × Space j, ‖cutoffInput L g p‖ₑ ^ 2 =
      ‖g p.1‖ₑ ^ 2 * (coordinateBox j L).indicator (fun _ => (1 : ℝ≥0∞)) p.2 := by
    intro p
    by_cases hp : p.2 ∈ coordinateBox j L <;> simp [cutoffInput, hp]
  simp_rw [heq]
  rw [lintegral_prod_mul (hg.enorm.pow_const 2).aemeasurable
    (measurable_const.indicator (measurableSet_coordinateBox j L)).aemeasurable,
    lintegral_indicator_const (measurableSet_coordinateBox j L), one_mul,
    volume_coordinateBox, mul_comm]

/-- A square-integrable g remains square-integrable after the finite box cutoff. -/
theorem memLp_cutoffInput {m j : ℕ} (L : ℝ) (g : Space m → ℂ)
    (hg : Measurable g) (hLp : MemLp g 2 volume) :
    MemLp (cutoffInput (j := j) L g) 2
      ((volume : Measure (Space m)).prod (volume : Measure (Space j))) := by
  refine ⟨(measurable_cutoffInput L g hg).aestronglyMeasurable, ?_⟩
  have henergy : (∫⁻ p : Space m × Space j, ‖cutoffInput L g p‖ₑ ^ 2
      ∂(volume : Measure (Space m)).prod (volume : Measure (Space j))) < ∞ := by
    rw [lintegral_cutoffInput_sq L g hg, ← SchurTest.eLpNorm_two_sq]
    exact ENNReal.mul_lt_top (by finiteness) (ENNReal.pow_lt_top hLp.eLpNorm_lt_top)
  rw [← SchurTest.eLpNorm_two_sq] at henergy
  simpa only [ENNReal.pow_lt_top_iff, OfNat.ofNat_ne_zero, or_false] using henergy

/-- Removing a boundary strip of width R gives exactly the smaller-box factor. -/
theorem volume_inner_coordinateBox (j : ℕ) (L R : ℝ) :
    volume (coordinateBox j (L - R)) = ENNReal.ofReal (2 * L - 2 * R) ^ j := by
  rw [volume_coordinateBox]
  congr 2
  ring

/-- Exact removal of the boundary-volume loss as the box radius tends to infinity.
No finiteness assumptions on X or Z are imposed. -/
theorem large_box_transfer (R : ℝ) (hR : 0 ≤ R) (j : ℕ) (X Z : ℝ≥0∞)
    (h : ∀ L : ℝ, R < L →
      ENNReal.ofReal (2 * L - 2 * R) ^ j * X ≤
        ENNReal.ofReal (2 * L) ^ j * Z) :
    X ≤ Z := by
  let ratio : ℕ → ℝ := fun k => (1 + (k : ℝ)) / (R + 1 + (k : ℝ))
  have hr : Tendsto ratio atTop (𝓝 1) := by
    simpa [ratio] using
      (tendsto_add_mul_div_add_mul_atTop_nhds (1 : ℝ) (R + 1) 1
        (by norm_num : (1 : ℝ) ≠ 0))
  have hp : Tendsto (fun k => ENNReal.ofReal (ratio k ^ j)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, one_pow, ENNReal.ofReal_one] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hr.pow j)
  have hm : Tendsto (fun k => ENNReal.ofReal (ratio k ^ j) * X) atTop (𝓝 X) := by
    simpa using ENNReal.Tendsto.mul_const hp (Or.inl (by norm_num : (1 : ℝ≥0∞) ≠ 0))
  apply le_of_tendsto' hm
  intro k
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hden : 0 < R + 1 + (k : ℝ) := by linarith
  have hL : R < R + 1 + (k : ℝ) := by linarith
  have houter : 0 < 2 * (R + 1 + (k : ℝ)) := by positivity
  have houter0 : ENNReal.ofReal (2 * (R + 1 + (k : ℝ))) ^ j ≠ 0 := by
    positivity
  have houterTop : ENNReal.ofReal (2 * (R + 1 + (k : ℝ))) ^ j ≠ ⊤ := by
    finiteness
  have hrnonneg : 0 ≤ ratio k := by dsimp [ratio]; positivity
  have heq : ENNReal.ofReal (ratio k ^ j) =
      ENNReal.ofReal (2 * (R + 1 + (k : ℝ)) - 2 * R) ^ j /
        ENNReal.ofReal (2 * (R + 1 + (k : ℝ))) ^ j := by
    rw [ENNReal.ofReal_pow hrnonneg,
      show ratio k = (2 * (R + 1 + (k : ℝ)) - 2 * R) /
        (2 * (R + 1 + (k : ℝ))) by
          dsimp [ratio]
          field_simp
          ring,
      ENNReal.ofReal_div_of_pos houter]
    simp only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow]
  rw [heq]
  have hcancel := (ENNReal.inv_mul_le_iff houter0 houterTop).2 (h _ hL)
  simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcancel

end StrongSpherical.MarginalEnergy
