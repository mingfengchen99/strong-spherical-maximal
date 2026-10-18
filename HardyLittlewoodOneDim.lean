import Definitions
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Bases
import Mathlib.MeasureTheory.Integral.Layercake
import LayercakeL2
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! # One-dimensional centered averaging and the Vitali weak estimate -/
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology

namespace StrongSpherical.HardyLittlewoodOneDim

/-- Centered interval average, with genuine nonnegative Lebesgue integrals. -/
def intervalAverage (r : ℝ) (F : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  (ENNReal.ofReal (2 * r))⁻¹ * ∫⁻ y in ball x r, F y

/-- Countably parametrized centered maximal function. All rational radii are included. -/
def rationalMaximal (F : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ⨆ q : ℚ, intervalAverage q F x

theorem measurable_intervalAverage (r : ℝ) (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    Measurable (intervalAverage r F) := by
  change Measurable (fun x => (ENNReal.ofReal (2 * r))⁻¹ * ∫⁻ y in ball x r, F y)
  have hset : MeasurableSet {p : ℝ × ℝ | dist p.2 p.1 < r} := by
    exact measurableSet_lt (by fun_prop) measurable_const
  have hm : Measurable (fun p : ℝ × ℝ =>
      {p : ℝ × ℝ | dist p.2 p.1 < r}.indicator (fun p => F p.2) p) :=
    (hF.comp measurable_snd).indicator hset
  have heq : ∀ x, (∫⁻ y, {p : ℝ × ℝ | dist p.2 p.1 < r}.indicator
      (fun p => F p.2) (x, y)) = ∫⁻ y in ball x r, F y := by
    intro x
    rw [← lintegral_indicator measurableSet_ball]
    congr 1
  simpa only [heq] using
    (measurable_const : Measurable (fun _ : ℝ =>
      (ENNReal.ofReal (2 * r))⁻¹)).mul
        (hm.lintegral_prod_right' (ν := (volume : Measure ℝ)))

theorem measurable_rationalMaximal (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    Measurable (rationalMaximal F) :=
  Measurable.iSup fun q => measurable_intervalAverage q F hF

theorem intervalAverage_eq_zero_of_nonpos (r : ℝ) (hr : r ≤ 0)
    (F : ℝ → ℝ≥0∞) (x : ℝ) : intervalAverage r F x = 0 := by
  simp [intervalAverage, ball_eq_empty.mpr hr]

def boundedRationalMaximal (R : ℝ) (F : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ⨆ q : ℚ, if 0 < (q : ℝ) ∧ (q : ℝ) ≤ R then intervalAverage q F x else 0

theorem measurable_boundedRationalMaximal (R : ℝ) (F : ℝ → ℝ≥0∞)
    (hF : Measurable F) : Measurable (boundedRationalMaximal R F) := by
  apply Measurable.iSup
  intro q
  by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) ≤ R
  · simpa only [if_pos hq] using measurable_intervalAverage q F hF
  · simp only [if_neg hq]
    exact measurable_const

/-- Vitali's disjoint intervals prove the weak estimate for any bounded-radius family.
This is an actual covering argument, with no maximal-operator assumption. -/
theorem vitali_weak_bound {ι : Type*} (F : ℝ → ℝ≥0∞) (ε : ℝ≥0∞)
    (s : Set ι) (c r : ι → ℝ) (R : ℝ)
    (hpos : ∀ a ∈ s, 0 < r a) (hbound : ∀ a ∈ s, r a ≤ R)
    (havg : ∀ a ∈ s, ε * volume (ball (c a) (r a)) ≤
      ∫⁻ y in ball (c a) (r a), F y) :
    ε * volume (⋃ a ∈ s, ball (c a) (r a)) ≤ 5 * ∫⁻ y, F y := by
  obtain ⟨u, hus, hdisj, hcover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_ball s c r R hbound 5 (by norm_num)
  have hu : u.Countable := hdisj.countable_of_isOpen
    (fun _ _ => isOpen_ball) (fun a ha => ⟨c a, mem_ball_self (hpos a (hus ha))⟩)
  have hsub : (⋃ a ∈ s, ball (c a) (r a)) ⊆
      ⋃ a ∈ u, ball (c a) (5 * r a) := by
    intro x hx
    rcases mem_iUnion₂.mp hx with ⟨a, ha, hxa⟩
    obtain ⟨b, hb, hab⟩ := hcover a ha
    exact mem_iUnion₂.mpr ⟨b, hb, hab hxa⟩
  calc
    _ ≤ ε * ∑' a : u, volume (ball (c a) (5 * r a)) :=
      mul_le_mul' le_rfl ((measure_mono hsub).trans (measure_biUnion_le volume hu _))
    _ = 5 * ∑' a : u, ε * volume (ball (c a) (r a)) := by
      have hvol : ∀ a : u, volume (ball (c a) (5 * r a)) =
          5 * volume (ball (c a) (r a)) := by
        intro a
        simp only [Real.volume_ball]
        rw [show 2 * (5 * r a) = 5 * (2 * r a) by ring,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5)]
        norm_num
      simp_rw [hvol, ENNReal.tsum_mul_left]
      ac_rfl
    _ ≤ 5 * ∑' a : u, ∫⁻ y in ball (c a) (r a), F y := by
      gcongr with a
      exact havg _ (hus a.property)
    _ = 5 * ∫⁻ y in ⋃ a ∈ u, ball (c a) (r a), F y := by
      rw [lintegral_biUnion hu (fun _ _ => measurableSet_ball) hdisj]
    _ ≤ _ := mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

/-- Weak (1,1) with the five-interval covering constant. No integrability
assumption is needed: all quantities take extended nonnegative values. -/
theorem boundedRationalMaximal_weak (R : ℝ) (F : ℝ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ε * volume {x | ε < boundedRationalMaximal R F x} ≤ 5 * ∫⁻ y, F y := by
  let s : Set (ℝ × ℚ) := {p | 0 < (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ R ∧
    ε < intervalAverage p.2 F p.1}
  have hsub : {x | ε < boundedRationalMaximal R F x} ⊆
      ⋃ p ∈ s, ball p.1 (p.2 : ℝ) := by
    intro x hx
    change ε < ⨆ q : ℚ, if 0 < (q : ℝ) ∧ (q : ℝ) ≤ R then intervalAverage q F x else 0 at hx
    obtain ⟨q, hq⟩ := lt_iSup_iff.mp hx
    by_cases hqr : 0 < (q : ℝ) ∧ (q : ℝ) ≤ R
    · rw [if_pos hqr] at hq
      exact mem_iUnion₂.mpr ⟨(x, q), ⟨hqr.1, hqr.2, hq⟩, mem_ball_self hqr.1⟩
    · rw [if_neg hqr] at hq
      exact (not_lt_of_ge bot_le hq).elim
  have hv := vitali_weak_bound F ε s Prod.fst (fun p => (p.2 : ℝ)) R
    (fun _ hp => hp.1) (fun _ hp => hp.2.1) (fun p hp => by
      have hpos : 0 < ENNReal.ofReal (2 * (p.2 : ℝ)) := ENNReal.ofReal_pos.mpr (by linarith [hp.1])
      have hm := mul_le_mul_right hp.2.2.le (ENNReal.ofReal (2 * (p.2 : ℝ)))
      rw [intervalAverage, ← mul_assoc,
        ENNReal.mul_inv_cancel hpos.ne' ENNReal.ofReal_ne_top, one_mul] at hm
      simpa only [Real.volume_ball, mul_comm] using hm)
  exact (mul_le_mul' le_rfl (measure_mono hsub)).trans hv

theorem boundedRationalMaximal_mono_radius (F : ℝ → ℝ≥0∞) :
    Monotone (fun R x => boundedRationalMaximal R F x) := by
  intro R S hRS x
  apply iSup_le
  intro q
  by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) ≤ R
  · rw [if_pos hq]
    exact le_iSup_of_le q (by rw [if_pos ⟨hq.1, hq.2.trans hRS⟩])
  · rw [if_neg hq]
    exact bot_le

theorem rationalMaximal_eq_iSup_bounded (F : ℝ → ℝ≥0∞) (x : ℝ) :
    rationalMaximal F x = ⨆ N : ℕ, boundedRationalMaximal N F x := by
  apply le_antisymm
  · apply iSup_le
    intro q
    by_cases hq : 0 < (q : ℝ)
    · obtain ⟨N, hN⟩ := exists_nat_ge (q : ℝ)
      exact le_iSup_of_le N (le_iSup_of_le q (by rw [if_pos ⟨hq, hN⟩]))
    · rw [intervalAverage_eq_zero_of_nonpos _ (le_of_not_gt hq)]
      exact bot_le
  · apply iSup_le
    intro N
    apply iSup_le
    intro q
    by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) ≤ (N : ℝ)
    · rw [if_pos hq]
      exact le_iSup (fun q : ℚ => intervalAverage q F x) q
    · rw [if_neg hq]
      exact bot_le

theorem rationalMaximal_weak (F : ℝ → ℝ≥0∞) (ε : ℝ≥0∞) :
    ε * volume {x | ε < rationalMaximal F x} ≤ 5 * ∫⁻ y, F y := by
  have heq : {x | ε < rationalMaximal F x} =
      ⋃ N : ℕ, {x | ε < boundedRationalMaximal N F x} := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion, rationalMaximal_eq_iSup_bounded, lt_iSup_iff]
  have hm : Monotone (fun N : ℕ => {x | ε < boundedRationalMaximal N F x}) := by
    intro i j hij x hx
    exact hx.trans_le (boundedRationalMaximal_mono_radius F (by exact_mod_cast hij) x)
  rw [heq, hm.measure_iUnion, ENNReal.mul_iSup]
  exact iSup_le fun N => boundedRationalMaximal_weak N F ε

def highInput (c : ℝ) (F : ℝ → ℝ) : ℝ → ℝ≥0∞ :=
  {x | c < F x}.indicator (fun x => ENNReal.ofReal (F x))

theorem measurable_highInput (c : ℝ) (F : ℝ → ℝ) (hF : Measurable F) :
    Measurable (highInput c F) :=
  (ENNReal.measurable_ofReal.comp hF).indicator (measurableSet_lt measurable_const hF)

theorem rationalMaximal_truncate_le (F : ℝ → ℝ) (hF : Measurable F)
    (c : ℝ) (_hc : 0 ≤ c) (x : ℝ) :
    rationalMaximal (fun y => ENNReal.ofReal (F y)) x ≤
      rationalMaximal (highInput c F) x + ENNReal.ofReal c := by
  apply iSup_le
  intro q
  by_cases hq : 0 < (q : ℝ)
  · have hvol0 : ENNReal.ofReal (2 * (q : ℝ)) ≠ 0 := by positivity
    have hpoint : ∀ y, ENNReal.ofReal (F y) ≤ highInput c F y + ENNReal.ofReal c := by
      intro y
      by_cases hy : c < F y
      · simp [highInput, hy]
      · simpa [highInput, hy] using ENNReal.ofReal_le_ofReal (le_of_not_gt hy)
    have hAvg : intervalAverage q (fun y => ENNReal.ofReal (F y)) x ≤
        intervalAverage q (highInput c F) x + ENNReal.ofReal c := by
      calc
        _ ≤ (ENNReal.ofReal (2 * (q : ℝ)))⁻¹ *
            ∫⁻ y in ball x (q : ℝ), highInput c F y + ENNReal.ofReal c := by
          exact mul_le_mul' le_rfl (lintegral_mono hpoint)
        _ = _ := by
          rw [lintegral_add_left (measurable_highInput c F hF), setLIntegral_const,
            Real.volume_ball, mul_add]
          rw [mul_left_comm _ (ENNReal.ofReal c),
            ENNReal.inv_mul_cancel hvol0 ENNReal.ofReal_ne_top, mul_one]
          rfl
    exact hAvg.trans (add_le_add (le_iSup (fun q : ℚ => intervalAverage q (highInput c F) x) q) le_rfl)
  · rw [intervalAverage_eq_zero_of_nonpos _ (le_of_not_gt hq)]
    exact bot_le

/-- The high-input refinement of weak (1,1), needed to integrate the tail at p=2. -/
theorem rationalMaximal_high_tail (F : ℝ → ℝ) (hF : Measurable F)
    (t : ℝ) (ht : 0 < t) :
    ENNReal.ofReal t * volume {x | ENNReal.ofReal t <
      rationalMaximal (fun y => ENNReal.ofReal (F y)) x} ≤
        10 * ∫⁻ x, highInput (t / 2) F x := by
  have hc : 0 ≤ t / 2 := by positivity
  have hhalf : ENNReal.ofReal (t / 2) + ENNReal.ofReal (t / 2) = ENNReal.ofReal t := by
    rw [← ENNReal.ofReal_add hc hc]
    congr 1
    ring
  have hsub : {x | ENNReal.ofReal t < rationalMaximal (fun y => ENNReal.ofReal (F y)) x} ⊆
      {x | ENNReal.ofReal (t / 2) < rationalMaximal (highInput (t / 2) F) x} := by
    intro x hx
    by_contra hn
    have hh := (rationalMaximal_truncate_le F hF (t / 2) hc x).trans
      (add_le_add (le_of_not_gt hn) (le_rfl : ENNReal.ofReal (t / 2) ≤ ENNReal.ofReal (t / 2)))
    rw [hhalf] at hh
    exact not_lt_of_ge hh hx
  have hw := (mul_le_mul' le_rfl (measure_mono hsub)).trans
    (rationalMaximal_weak (highInput (t / 2) F) (ENNReal.ofReal (t / 2)))
  have hm := mul_le_mul_right hw (2 : ℝ≥0∞)
  have he : (2 : ℝ≥0∞) * ENNReal.ofReal (t / 2) = ENNReal.ofReal t := by
    rw [← show ENNReal.ofReal (2 : ℝ) = 2 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  simpa only [← mul_assoc, he, show (2 : ℝ≥0∞) * 5 = 10 by norm_num] using hm

/-- The one-dimensional rational centered maximal function has squared L² norm at most 40. -/
theorem rationalMaximal_L2 (F : ℝ → ℝ) (hF : Measurable F) (hn : ∀ x, 0 ≤ F x) :
    (∫⁻ x, rationalMaximal (fun y => ENNReal.ofReal (F y)) x ^ 2) ≤
      40 * ∫⁻ x, ENNReal.ofReal (F x) ^ 2 := by
  let M : ℝ → ℝ≥0∞ := rationalMaximal (fun y => ENNReal.ofReal (F y))
  have hM : Measurable M := measurable_rationalMaximal _ (ENNReal.measurable_ofReal.comp hF)
  let G : ℕ → ℝ → ℝ := fun N x => (min (M x) (N : ℝ≥0∞)).toReal
  have hcap : ∀ (N : ℕ) (x : ℝ), min (M x) (N : ℝ≥0∞) ≠ ∞ := fun N x =>
    ne_top_of_le_ne_top (by simp) (min_le_right _ _)
  have hG : ∀ N : ℕ, Measurable (G N) := fun N => (hM.min measurable_const).ennreal_toReal
  have hnG : ∀ (N : ℕ) (x : ℝ), 0 ≤ G N x := fun N x => ENNReal.toReal_nonneg
  have hpow : ∀ (N : ℕ) (x : ℝ), ENNReal.ofReal (G N x) ^ 2 = min (M x) (N : ℝ≥0∞) ^ 2 := by
    intro N x
    change ENNReal.ofReal ((min (M x) (N : ℝ≥0∞)).toReal) ^ 2 = _
    rw [ENNReal.ofReal_toReal (hcap N x)]
  have hb : ∀ N : ℕ, (∫⁻ x, min (M x) (N : ℝ≥0∞) ^ 2) ≤
      40 * ∫⁻ x, ENNReal.ofReal (F x) ^ 2 := by
    intro N
    have h := LayercakeL2.lintegral_sq_le_of_high_tail F (G N) hF hn (hG N) (hnG N) 10
      (fun t ht => by
        have hsub : {x | t < G N x} ⊆ {x | ENNReal.ofReal t < M x} := by
          intro x hx
          exact ((ENNReal.ofReal_lt_iff_lt_toReal ht.le (hcap N x)).2 hx).trans_le
            (min_le_left _ _)
        exact (mul_le_mul' le_rfl (measure_mono hsub)).trans
          (rationalMaximal_high_tail F hF t ht))
    simpa only [hpow, show (4 : ℝ≥0∞) * 10 = 40 by norm_num] using h
  have heq : ∀ x, M x ^ 2 = ⨆ N : ℕ, min (M x) (N : ℝ≥0∞) ^ 2 := by
    intro x
    rw [← ENNReal.iSup_pow]
    congr 1
    change M x = ⨆ N : ℕ, M x ⊓ (N : ℝ≥0∞)
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  change (∫⁻ x, M x ^ 2) ≤ _
  simp_rw [heq]
  rw [lintegral_iSup (fun N => (hM.min measurable_const).pow_const 2)
    (fun i j hij x => pow_le_pow_left' (min_le_min_left _ (by exact_mod_cast hij)) 2)]
  exact iSup_le hb

/-- Extended-valued version: Tonelli may apply this on every measurable fiber,
without first excluding exceptional fibers of infinite energy. -/
theorem rationalMaximal_L2_ennreal (F : ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, rationalMaximal F x ^ 2) ≤ 40 * ∫⁻ x, F x ^ 2 := by
  by_cases hfin : (∫⁻ x, F x ^ 2) = ∞
  · simp [hfin]
  have hAE : ∀ᵐ x : ℝ, F x ≠ ∞ := by
    filter_upwards [ae_lt_top (hF.pow_const 2) hfin] with x hx
    have hf : F x < ∞ := by
      simpa only [ENNReal.pow_lt_top_iff, OfNat.ofNat_ne_zero, or_false] using hx
    exact hf.ne
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
    ext q
    exact havg q x
  have henergy : (∫⁻ x, ENNReal.ofReal ((F x).toReal) ^ 2) = ∫⁻ x, F x ^ 2 := by
    apply lintegral_congr_ae
    filter_upwards [hAE] with x hx
    rw [ENNReal.ofReal_toReal hx]
  rw [hmax]
  have h := rationalMaximal_L2 (fun y => (F y).toReal) hF.ennreal_toReal
    (fun _ => ENNReal.toReal_nonneg)
  rw [henergy] at h
  exact h

/-- The fiberwise maximal operation preserves joint measurability with any parameter. -/
theorem measurable_rationalMaximal_with_param {P : Type*} [MeasurableSpace P]
    (F : P × ℝ → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun p : P × ℝ => rationalMaximal (fun t => F (p.1, t)) p.2) := by
  apply Measurable.iSup
  intro q
  let H : (P × ℝ) × ℝ → ℝ≥0∞ := fun z =>
    {z : (P × ℝ) × ℝ | dist z.2 z.1.2 < (q : ℝ)}.indicator
      (fun z => F (z.1.1, z.2)) z
  have hH : Measurable H :=
    (hF.comp (measurable_fst.fst.prodMk measurable_snd)).indicator
      (measurableSet_lt (by fun_prop) measurable_const)
  have hm := (measurable_const : Measurable (fun _ : P × ℝ =>
    (ENNReal.ofReal (2 * (q : ℝ)))⁻¹)).mul
      (hH.lintegral_prod_right' (ν := (volume : Measure ℝ)))
  have heq : (fun p : P × ℝ => (ENNReal.ofReal (2 * (q : ℝ)))⁻¹ * ∫⁻ y, H (p, y)) =
      (fun p : P × ℝ => intervalAverage q (fun t => F (p.1, t)) p.2) := by
    funext p
    unfold intervalAverage
    rw [← lintegral_indicator measurableSet_ball]
    rfl
  rw [heq] at hm
  exact hm

/-- Every positive real radius is controlled by a nearby rational radius. -/
theorem intervalAverage_le_two_rationalMaximal (r : ℝ) (hr : 0 < r)
    (F : ℝ → ℝ≥0∞) (x : ℝ) :
    intervalAverage r F x ≤ 2 * rationalMaximal F x := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (by linarith : r < 2 * r)
  have hq : 0 < (q : ℝ) := hr.trans hq1
  have hv : ENNReal.ofReal (2 * r) ≠ 0 := by positivity
  have hqv : ENNReal.ofReal (2 * (q : ℝ)) ≠ 0 := by positivity
  have hVr : ENNReal.ofReal (2 * r) * intervalAverage r F x = ∫⁻ y in ball x r, F y := by
    rw [intervalAverage, ← mul_assoc, ENNReal.mul_inv_cancel hv ENNReal.ofReal_ne_top, one_mul]
  have hVq : ENNReal.ofReal (2 * (q : ℝ)) * intervalAverage q F x =
      ∫⁻ y in ball x (q : ℝ), F y := by
    rw [intervalAverage, ← mul_assoc, ENNReal.mul_inv_cancel hqv ENNReal.ofReal_ne_top, one_mul]
  have hvq : ENNReal.ofReal (2 * (q : ℝ)) ≤ 2 * ENNReal.ofReal (2 * r) := by
    rw [← show ENNReal.ofReal (2 : ℝ) = 2 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hmain : ENNReal.ofReal (2 * r) * intervalAverage r F x ≤
      ENNReal.ofReal (2 * r) * (2 * intervalAverage q F x) := by
    calc
      _ = ∫⁻ y in ball x r, F y := hVr
      _ ≤ ∫⁻ y in ball x (q : ℝ), F y := lintegral_mono_set (ball_subset_ball hq1.le)
      _ = ENNReal.ofReal (2 * (q : ℝ)) * intervalAverage q F x := hVq.symm
      _ ≤ (2 * ENNReal.ofReal (2 * r)) * intervalAverage q F x := mul_le_mul' hvq le_rfl
      _ = _ := by ring
  exact ((ENNReal.mul_le_mul_iff_right hv ENNReal.ofReal_ne_top).1 hmain).trans
    (mul_le_mul' le_rfl (le_iSup (fun q : ℚ => intervalAverage q F x) q))

end StrongSpherical.HardyLittlewoodOneDim
