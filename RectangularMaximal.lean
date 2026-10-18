import HardyLittlewoodOneDim
import SliceMeasure
import ProductCoordinates
import ProductSmoothing
import MaximalWeight

/-! # Iterated one-dimensional maximal operators on Euclidean coordinate spaces -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Topology

namespace StrongSpherical.RectangularMaximal
open HardyLittlewoodOneDim QuadraticGraph EllipsoidGraph
open MaximalWeight

/-- A positive controlling operator obtained by applying centered one-dimensional
maximal operators successively to the Euclidean coordinates. -/
def controllingMaximal : (n : ℕ) → (Space n → ℝ≥0∞) → Space n → ℝ≥0∞
  | 0, F, x => F x
  | n + 1, F, v => rationalMaximal
      (fun t => controllingMaximal n (fun u => F (slicePoint u t)) (spatialInput v))
      (normalInput v)

/-- Joint measurability is retained with arbitrary auxiliary parameters. -/
theorem measurable_controllingMaximal_with_param (n : ℕ)
    {P : Type*} [MeasurableSpace P] (F : P × Space n → ℝ≥0∞) (hF : Measurable F) :
    Measurable (fun p : P × Space n => controllingMaximal n (fun u => F (p.1, u)) p.2) := by
  induction n generalizing P with
  | zero => exact hF
  | succ n ih =>
    let H : (P × ℝ) × Space n → ℝ≥0∞ := fun z => F (z.1.1, slicePoint z.2 z.1.2)
    have hH : Measurable H := by
      have hs : Measurable (fun z : (P × ℝ) × Space n => slicePoint z.2 z.1.2) := by
        unfold slicePoint
        fun_prop
      exact hF.comp (measurable_fst.fst.prodMk hs)
    have hI := ih H hH
    let G : (P × Space n) × ℝ → ℝ≥0∞ := fun z =>
      controllingMaximal n (fun u => F (z.1.1, slicePoint u z.2)) z.1.2
    have hG : Measurable G := by
      have hm : Measurable (fun z : (P × Space n) × ℝ => ((z.1.1, z.2), z.1.2)) := by
        fun_prop
      exact hI.comp hm
    have hOuter := measurable_rationalMaximal_with_param G hG
    have hm : Measurable (fun p : P × Space (n + 1) =>
        ((p.1, spatialInput p.2), normalInput p.2)) := by
      unfold spatialInput normalInput
      fun_prop
    simpa only [Function.comp_def, controllingMaximal, G] using hOuter.comp hm

theorem measurable_controllingMaximal (n : ℕ) (F : Space n → ℝ≥0∞) (hF : Measurable F) :
    Measurable (controllingMaximal n F) := by
  have h := measurable_controllingMaximal_with_param n
    (fun p : Unit × Space n => F p.2) (hF.comp measurable_snd)
  simpa only [Function.comp_def] using h.comp
    (measurable_const.prodMk measurable_id : Measurable (fun x : Space n => ((), x)))

set_option maxHeartbeats 1000000 in
/-- Each coordinate costs at most 40 in squared L² energy. This is valid for
extended-valued measurable inputs, including fibers with infinite energy. -/
theorem controllingMaximal_L2 (n : ℕ) (F : Space n → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ x, controllingMaximal n F x ^ 2) ≤ (40 : ℝ≥0∞) ^ n * ∫⁻ x, F x ^ 2 := by
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
    have hslices : (∫⁻ v, controllingMaximal (n + 1) F v ^ 2) =
        ∫⁻ h, ∫⁻ u : Space n, rationalMaximal (fun t => G (t, u)) h ^ 2 := by
      simpa [controllingMaximal, normalInput, spatialInput, G] using
        (SliceMeasure.lintegral_slices
          (fun v => controllingMaximal (n + 1) F v ^ 2)
          ((measurable_controllingMaximal (n + 1) F hF).pow_const 2))
    calc
      _ = ∫⁻ h, ∫⁻ u : Space n, rationalMaximal (fun t => G (t, u)) h ^ 2 := hslices
      _ = ∫⁻ u : Space n, ∫⁻ h, rationalMaximal (fun t => G (t, u)) h ^ 2 :=
        lintegral_lintegral_swap (hQ'.pow_const 2).aemeasurable
      _ ≤ ∫⁻ u : Space n, 40 * ∫⁻ t, G (t, u) ^ 2 := by
        apply lintegral_mono
        intro u
        exact rationalMaximal_L2_ennreal _
          (hG.comp (measurable_id.prodMk measurable_const))
      _ = 40 * ∫⁻ u : Space n, ∫⁻ t, G (t, u) ^ 2 :=
        lintegral_const_mul _ (hG.pow_const 2).lintegral_prod_left'
      _ = 40 * ∫⁻ t, ∫⁻ u : Space n, G (t, u) ^ 2 := by
        have hh : (∫⁻ t, ∫⁻ u : Space n, G (t, u) ^ 2) =
            ∫⁻ u : Space n, ∫⁻ t, G (t, u) ^ 2 :=
          lintegral_lintegral_swap (hG.pow_const 2).aemeasurable
        rw [← hh]
      _ ≤ 40 * ∫⁻ t, (40 : ℝ≥0∞) ^ n * ∫⁻ u : Space n, F (slicePoint u t) ^ 2 := by
        gcongr with t
        exact ih _ (hFs.comp (measurable_const.prodMk measurable_id))
      _ = (40 : ℝ≥0∞) ^ (n + 1) * ∫⁻ v, F v ^ 2 := by
        rw [lintegral_const_mul _ (hFs.pow_const 2).lintegral_prod_right,
          ← SliceMeasure.lintegral_slices _ (hF.pow_const 2), pow_succ]
        ring

theorem eLpNorm_two_sq_ennreal {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (F : X → ℝ≥0∞) : eLpNorm F 2 μ ^ 2 = ∫⁻ x, F x ^ 2 ∂μ := by
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two, enorm_eq_self] using
    (eLpNorm_nnreal_pow_eq_lintegral (f := F) (μ := μ) (p := (2 : ℝ≥0)) (by norm_num))

theorem eLpNorm_controllingMaximal_le (n : ℕ) (F : Space n → ℝ≥0∞) (hF : Measurable F) :
    eLpNorm (controllingMaximal n F) 2 volume ≤
      (8 : ℝ≥0∞) ^ n * eLpNorm F 2 volume := by
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  simp only [ENNReal.rpow_two, mul_pow]
  rw [eLpNorm_two_sq_ennreal, eLpNorm_two_sq_ennreal]
  have hc : (40 : ℝ≥0∞) ^ n ≤ ((8 : ℝ≥0∞) ^ n) ^ 2 := by
    rw [← pow_mul, mul_comm n 2, pow_mul]
    exact pow_le_pow_left' (by norm_num : (40 : ℝ≥0∞) ≤ 8 ^ 2) n
  exact (controllingMaximal_L2 n F hF).trans (mul_le_mul' hc le_rfl)

/-- Apply the coordinate maximal operator only in the first m coordinates. -/
def partialBlockMaximal (m j : ℕ) (F : Space (m + j) → ℝ≥0∞)
    (v : Space (m + j)) : ℝ≥0∞ :=
  controllingMaximal m (fun u => F ((ProductCoordinates.split m j).symm
    (u, (ProductCoordinates.split m j v).2))) (ProductCoordinates.split m j v).1

set_option maxHeartbeats 1000000 in
theorem measurable_partialBlockMaximal (m j : ℕ) (F : Space (m + j) → ℝ≥0∞)
    (hF : Measurable F) : Measurable (partialBlockMaximal m j F) := by
  unfold partialBlockMaximal
  have hH : Measurable (fun p : Space j × Space m =>
      F ((ProductCoordinates.split m j).symm (p.2, p.1))) :=
    hF.comp ((ProductCoordinates.split m j).symm.measurable.comp measurable_swap)
  have hM := measurable_controllingMaximal_with_param m _ hH
  have hm : Measurable (fun v : Space (m + j) =>
      ((ProductCoordinates.split m j v).2, (ProductCoordinates.split m j v).1)) :=
    measurable_swap.comp (ProductCoordinates.split m j).measurable
  simpa only [Function.comp_def] using hM.comp hm

set_option maxHeartbeats 1000000 in
theorem partialBlockMaximal_L2 (m j : ℕ) (F : Space (m + j) → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ v, partialBlockMaximal m j F v ^ 2) ≤
      (40 : ℝ≥0∞) ^ m * ∫⁻ v, F v ^ 2 := by
  let H : Space j × Space m → ℝ≥0∞ := fun p =>
    F ((ProductCoordinates.split m j).symm (p.2, p.1))
  have hH : Measurable H :=
    hF.comp ((ProductCoordinates.split m j).symm.measurable.comp measurable_swap)
  have hM := measurable_controllingMaximal_with_param m H hH
  calc
    _ = ∫⁻ u : Space m, ∫⁻ w : Space j,
        controllingMaximal m (fun u => H (w, u)) u ^ 2 := by
      simpa [partialBlockMaximal, H] using
        ProductCoordinates.lintegral_split
          (fun v => partialBlockMaximal m j F v ^ 2)
          ((measurable_partialBlockMaximal m j F hF).pow_const 2)
    _ = ∫⁻ w : Space j, ∫⁻ u : Space m,
        controllingMaximal m (fun u => H (w, u)) u ^ 2 := by
      exact lintegral_lintegral_swap ((hM.comp measurable_swap).pow_const 2).aemeasurable
    _ ≤ ∫⁻ w : Space j, (40 : ℝ≥0∞) ^ m * ∫⁻ u : Space m, H (w, u) ^ 2 := by
      apply lintegral_mono
      intro w
      exact controllingMaximal_L2 m _ (hH.comp (measurable_const.prodMk measurable_id))
    _ = (40 : ℝ≥0∞) ^ m * ∫⁻ w : Space j, ∫⁻ u : Space m, H (w, u) ^ 2 :=
      lintegral_const_mul _ (hH.pow_const 2).lintegral_prod_right
    _ = _ := by
      rw [lintegral_lintegral_swap (hH.pow_const 2).aemeasurable]
      congr 1
      exact (ProductCoordinates.lintegral_split _ (hF.pow_const 2)).symm

theorem eLpNorm_partialBlockMaximal_le (m j : ℕ) (F : Space (m + j) → ℝ≥0∞)
    (hF : Measurable F) :
    eLpNorm (partialBlockMaximal m j F) 2 volume ≤
      (8 : ℝ≥0∞) ^ m * eLpNorm F 2 volume := by
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  simp only [ENNReal.rpow_two, mul_pow]
  rw [eLpNorm_two_sq_ennreal, eLpNorm_two_sq_ennreal]
  have hc : (40 : ℝ≥0∞) ^ m ≤ ((8 : ℝ≥0∞) ^ m) ^ 2 := by
    rw [← pow_mul, mul_comm m 2, pow_mul]
    exact pow_le_pow_left' (by norm_num : (40 : ℝ≥0∞) ≤ 8 ^ 2) m
  exact (partialBlockMaximal_L2 m j F hF).trans (mul_le_mul' hc le_rfl)

def initRadii {n : ℕ} (r : Radii (n + 1)) : Radii n :=
  ⟨fun i => r.1 i.castSucc, fun i => r.2 i.castSucc⟩

theorem productWeight_slice {n : ℕ} (r : Radii (n + 1)) (u : Space n) (s : ℝ) :
    ProductSmoothing.productWeight r (slicePoint u s) =
      ProductSmoothing.productWeight (initRadii r) u * oneDimWeight (r.1 (Fin.last n)) s := by
  simp [ProductSmoothing.productWeight, Fin.prod_univ_castSucc, initRadii, oneDimWeight]

theorem continuous_productWeight {n : ℕ} (r : Radii n) :
    Continuous (ProductSmoothing.productWeight r) := by
  apply continuous_finsetProd
  intro i _
  have hi : Continuous (fun x : Space n => oneDimWeight (r.1 i) (x i)) :=
    (continuous_oneDimWeight (r.1 i) (r.2 i)).comp
      (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i)
  exact hi

theorem sub_slicePoint {n : ℕ} (v : Space (n + 1)) (u : Space n) (s : ℝ) :
    v - slicePoint u s = slicePoint (spatialInput v - u) (normalInput v - s) := by
  ext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [spatialInput, normalInput]

theorem volume_space_zero : volume (univ : Set (Space 0)) = 1 := by
  have h := (PiLp.volume_preserving_ofLp (Fin 0)).measure_preimage
    (MeasurableSet.univ.nullMeasurableSet : NullMeasurableSet (univ : Set (Fin 0 → ℝ)) volume)
  simp only [preimage_univ] at h
  rw [h]
  change Measure.pi (fun _ : Fin 0 => (volume : Measure ℝ)) univ = 1
  simp

set_option maxHeartbeats 1500000 in
/-- Genuine product-weight convolution is uniformly controlled by the iterated
coordinate maximal operator, with a dimension-only constant. -/
theorem lintegral_productWeight_le (n : ℕ) (r : Radii n)
    (F : Space n → ℝ≥0∞) (hF : Measurable F) (x : Space n) :
    (∫⁻ y, ENNReal.ofReal (ProductSmoothing.productWeight r y) * F (x - y)) ≤
      (16 : ℝ≥0∞) ^ n * controllingMaximal n F x := by
  induction n with
  | zero =>
    have heq : (fun y : Space 0 => ENNReal.ofReal
        (ProductSmoothing.productWeight r y) * F (x - y)) = fun _ => F x := by
      funext y
      rw [show x - y = x by exact Subsingleton.elim _ _]
      simp [ProductSmoothing.productWeight]
    rw [heq, lintegral_const, volume_space_zero]
    simp [controllingMaximal]
  | succ n ih =>
    let G : ℝ → ℝ≥0∞ := fun t =>
      controllingMaximal n (fun u => F (slicePoint u t)) (spatialInput x)
    have hFs : Measurable (fun p : ℝ × Space n => F (slicePoint p.2 p.1)) := by
      apply hF.comp
      unfold slicePoint
      fun_prop
    have hGI := measurable_controllingMaximal_with_param n _ hFs
    have hG : Measurable G := hGI.comp (measurable_id.prodMk measurable_const)
    have hw : Measurable (fun y : Space (n + 1) =>
        ENNReal.ofReal (ProductSmoothing.productWeight r y) * F (x - y)) :=
      (ENNReal.measurable_ofReal.comp (continuous_productWeight r).measurable).mul
        (hF.comp (measurable_const.sub measurable_id))
    have hinner : ∀ s : ℝ,
        (∫⁻ u : Space n, ENNReal.ofReal (ProductSmoothing.productWeight r (slicePoint u s)) *
          F (x - slicePoint u s)) =
        ENNReal.ofReal (oneDimWeight (r.1 (Fin.last n)) s) *
          ∫⁻ u : Space n, ENNReal.ofReal (ProductSmoothing.productWeight (initRadii r) u) *
            F (slicePoint (spatialInput x - u) (normalInput x - s)) := by
      intro s
      have hm : Measurable (fun u : Space n =>
          ENNReal.ofReal (ProductSmoothing.productWeight (initRadii r) u) *
            F (slicePoint (spatialInput x - u) (normalInput x - s))) := by
        apply (ENNReal.measurable_ofReal.comp (continuous_productWeight _).measurable).mul
        apply hF.comp
        unfold slicePoint
        fun_prop
      rw [← lintegral_const_mul _ hm]
      apply lintegral_congr
      intro u
      rw [productWeight_slice,
        ENNReal.ofReal_mul (ProductSmoothing.productWeight_nonneg _ _), sub_slicePoint]
      ring
    have hOne : Measurable (fun s : ℝ =>
        ENNReal.ofReal (oneDimWeight (r.1 (Fin.last n)) s) * G (normalInput x - s)) :=
      (ENNReal.measurable_ofReal.comp (continuous_oneDimWeight _ (r.2 _)).measurable).mul
        (hG.comp (measurable_const.sub measurable_id))
    calc
      _ = ∫⁻ s, ∫⁻ u : Space n,
          ENNReal.ofReal (ProductSmoothing.productWeight r (slicePoint u s)) *
            F (x - slicePoint u s) := SliceMeasure.lintegral_slices _ hw
      _ = ∫⁻ s, ENNReal.ofReal (oneDimWeight (r.1 (Fin.last n)) s) *
          ∫⁻ u : Space n, ENNReal.ofReal (ProductSmoothing.productWeight (initRadii r) u) *
            F (slicePoint (spatialInput x - u) (normalInput x - s)) := by simp_rw [hinner]
      _ ≤ ∫⁻ s, ENNReal.ofReal (oneDimWeight (r.1 (Fin.last n)) s) *
          ((16 : ℝ≥0∞) ^ n * G (normalInput x - s)) := by
        apply lintegral_mono
        intro s
        apply mul_le_mul' le_rfl
        exact ih (initRadii r) (fun u => F (slicePoint u (normalInput x - s)))
          (hFs.comp (measurable_const.prodMk measurable_id)) (spatialInput x)
      _ = (16 : ℝ≥0∞) ^ n * ∫⁻ s,
          ENNReal.ofReal (oneDimWeight (r.1 (Fin.last n)) s) * G (normalInput x - s) := by
        rw [← lintegral_const_mul _ hOne]
        apply lintegral_congr
        intro s
        ring
      _ ≤ (16 : ℝ≥0∞) ^ n * (16 * rationalMaximal G (normalInput x)) :=
        mul_le_mul' le_rfl (lintegral_weight_le _ (r.2 _) G hG _)
      _ = _ := by rw [controllingMaximal, pow_succ]; ring

theorem lintegral_partialBlockWeight_le (m j : ℕ) (r : Radii m)
    (F : Space (m + j) → ℝ≥0∞) (hF : Measurable F) (x : Space (m + j)) :
    (∫⁻ u : Space m, ENNReal.ofReal (ProductSmoothing.productWeight r u) *
      F ((ProductCoordinates.split m j).symm
        ((ProductCoordinates.split m j x).1 - u, (ProductCoordinates.split m j x).2))) ≤
      (16 : ℝ≥0∞) ^ m * partialBlockMaximal m j F x := by
  apply lintegral_productWeight_le m r
    (fun u => F ((ProductCoordinates.split m j).symm (u, (ProductCoordinates.split m j x).2)))
  exact hF.comp ((ProductCoordinates.split m j).symm.measurable.comp
    (measurable_id.prodMk measurable_const))

end StrongSpherical.RectangularMaximal
