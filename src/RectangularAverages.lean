import RectangularMaximalLp
import DilationL1
import MarginalEnergy

/-! # Actual centered rectangular averages and bounded-kernel domination -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators Topology

namespace StrongSpherical.RectangularAverages
variable {n : ℕ}

/-- A coordinate rectangle of half-side lengths r, centered at the origin. -/
def rectangle (r : Radii n) : Set (Space n) :=
  {y | ∀ i, y i ∈ Icc (-(r.1 i)) (r.1 i)}

/-- The actual Euclidean Lebesgue volume of this rectangle. -/
def rectangleVolume (r : Radii n) : ℝ := ∏ i, 2 * r.1 i

theorem rectangleVolume_pos (r : Radii n) : 0 < rectangleVolume r :=
  Finset.prod_pos fun i _ => mul_pos (by norm_num) (r.2 i)

theorem measurableSet_rectangle (r : Radii n) : MeasurableSet (rectangle r) := by
  have heq : rectangle r = ⋂ i : Fin n, {y : Space n | y i ∈ Icc (-(r.1 i)) (r.1 i)} := by
    ext y
    simp [rectangle]
  rw [heq]
  exact MeasurableSet.iInter fun i =>
    (by fun_prop : Measurable (fun y : Space n => y i)) measurableSet_Icc

theorem volume_rectangle (r : Radii n) :
    volume (rectangle r) = ENNReal.ofReal (rectangleVolume r) := by
  have heq : rectangle r =
      WithLp.ofLp ⁻¹' (Set.pi univ fun i : Fin n => Icc (-(r.1 i)) (r.1 i)) := by
    ext y
    simp only [rectangle, mem_preimage, mem_setOf_eq, Set.mem_pi, mem_univ, true_implies]
  have hm : MeasurableSet (Set.pi univ fun i : Fin n => Icc (-(r.1 i)) (r.1 i)) :=
    (isCompact_univ_pi fun _ => isCompact_Icc).isClosed.measurableSet
  rw [heq, (PiLp.volume_preserving_ofLp (Fin n)).measure_preimage hm.nullMeasurableSet]
  change Measure.pi (fun _ : Fin n => (volume : Measure ℝ))
    (Set.pi univ fun i => Icc (-(r.1 i)) (r.1 i)) = _
  rw [Measure.pi_pi]
  simp only [Real.volume_Icc, sub_neg_eq_add, ← two_mul]
  exact (ENNReal.ofReal_prod_of_nonneg (fun i _ => (mul_pos (by norm_num) (r.2 i)).le)).symm

/-- The Lebesgue integral over x minus a genuine rectangle, divided by its
volume. Closed faces do not change these averages. -/
def rectangularAverage (r : Radii n) (F : Space n → ℝ≥0∞) (x : Space n) : ℝ≥0∞ :=
  (ENNReal.ofReal (rectangleVolume r))⁻¹ * ∫⁻ y in rectangle r, F (x - y)

/-- The actual centered strong rectangular maximal function, with all
positive real half-side lengths in the supremum. -/
def rectangularMaximal (F : Space n → ℝ≥0∞) (x : Space n) : ℝ≥0∞ :=
  ⨆ r : Radii n, rectangularAverage r F x

/-- A bounded kernel supported in one actual rectangle is dominated by its
normalized average. The Bochner integral bound also applies to raw inputs. -/
theorem kernelConvolution_le_rectangularAverage (H : Space n → ℂ) (r : Radii n)
    (B : ℝ) (hB : ∀ y, ‖H y‖ ≤ B) (hs : Function.support H ⊆ rectangle r)
    (f : Space n → ℂ) (x : Space n) :
    ‖kernelConvolution H f x‖ₑ ≤ ENNReal.ofReal (B * rectangleVolume r) *
      rectangularAverage r (fun y => ‖f y‖ₑ) x := by
  have hB0 : 0 ≤ B := (norm_nonneg (H 0)).trans (hB 0)
  have hV0 : ENNReal.ofReal (rectangleVolume r) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (rectangleVolume_pos r)
  calc
    _ ≤ ∫⁻ y, ‖H y‖ₑ * ‖f (x - y)‖ₑ := by
      rw [kernelConvolution_eq_integral]
      simpa only [enorm_mul] using enorm_integral_le_lintegral_enorm (fun y => H y * f (x - y))
    _ ≤ ∫⁻ y, ENNReal.ofReal B * (rectangle r).indicator (fun y => ‖f (x - y)‖ₑ) y := by
      apply lintegral_mono
      intro y
      dsimp only
      by_cases hy : y ∈ rectangle r
      · rw [indicator_of_mem hy]
        exact mul_le_mul' (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal (hB y)) le_rfl
      · have hz : H y = 0 := by
          by_contra hn
          exact hy (hs hn)
        simp only [hz, enorm_zero, zero_mul, indicator_of_notMem hy, mul_zero, le_refl]
    _ = ENNReal.ofReal B * ∫⁻ y in rectangle r, ‖f (x - y)‖ₑ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_indicator (measurableSet_rectangle r)]
    _ = ENNReal.ofReal (B * rectangleVolume r) *
        rectangularAverage r (fun y => ‖f y‖ₑ) x := by
      unfold rectangularAverage
      rw [ENNReal.ofReal_mul hB0]
      calc
        _ = ENNReal.ofReal B *
            ((ENNReal.ofReal (rectangleVolume r) * (ENNReal.ofReal (rectangleVolume r))⁻¹) *
              ∫⁻ y in rectangle r, ‖f (x - y)‖ₑ) := by
          rw [ENNReal.mul_inv_cancel hV0 ENNReal.ofReal_ne_top, one_mul]
        _ = _ := by ring

def doubleRadii (r : Radii n) : Radii n :=
  ⟨fun i => 2 * r.1 i, fun i => mul_pos (by norm_num) (r.2 i)⟩

theorem rectangleVolume_double (r : Radii n) :
    rectangleVolume (doubleRadii r) = (4 : ℝ) ^ n * dilationJacobian r := by
  simp only [rectangleVolume, doubleRadii, show ∀ i : Fin n, 2 * (2 * r.1 i) = 4 * r.1 i by
    intro i; ring]
  rw [Finset.prod_mul_distrib]
  simp [dilationJacobian]

theorem dilatedKernel_support_rectangle (K : Space n → ℂ)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n 2) (r : Radii n) :
    Function.support (dilatedKernel K r) ⊆ rectangle (doubleRadii r) := by
  intro y hy i
  have hne : K (inverseDilation r y) ≠ 0 := by
    intro hz
    apply hy
    simp [dilatedKernel, hz]
  have hh : |(r.1 i)⁻¹ * y i| ≤ 2 := abs_le.mpr (hs hne i)
  rw [abs_mul, abs_inv, abs_of_pos (r.2 i)] at hh
  have hm := mul_le_mul_of_nonneg_left hh (r.2 i).le
  have he : r.1 i * ((r.1 i)⁻¹ * |y i|) = |y i| := by
    rw [← mul_assoc, mul_inv_cancel₀ (r.2 i).ne', one_mul]
  rw [he] at hm
  exact abs_le.mp (by simpa only [doubleRadii, mul_comm] using hm)

/-- The exact rectangle domination used in (6.12). Its constant is uniform
in the dilation and the raw input; the coordinate support cube has radius two. -/
theorem strongKernelMaximal_le_rectangular (K : Space n → ℂ)
    (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n 2)
    (B : ℝ) (hB : ∀ y, ‖K y‖ ≤ B) (f : Space n → ℂ) (x : Space n) :
    strongKernelMaximal K f x ≤ ENNReal.ofReal ((4 : ℝ) ^ n * B) *
      rectangularMaximal (fun y => ‖f y‖ₑ) x := by
  unfold strongKernelMaximal maximalOver
  refine iSup_le fun r => iSup_le fun _ => ?_
  have h := kernelConvolution_le_rectangularAverage (dilatedKernel K r) (doubleRadii r)
    ((dilationJacobian r)⁻¹ * B) (DilationL1.norm_dilatedKernel_le K r B hB)
    (dilatedKernel_support_rectangle K hs r) f x
  rw [rectangleVolume_double] at h
  have hc : (dilationJacobian r)⁻¹ * B * ((4 : ℝ) ^ n * dilationJacobian r) =
      (4 : ℝ) ^ n * B := by
    field_simp [(dilationJacobian_pos r).ne']
  rw [hc] at h
  exact h.trans (mul_le_mul' le_rfl (le_iSup
    (fun s : Radii n => rectangularAverage s (fun y => ‖f y‖ₑ) x) (doubleRadii r)))

end StrongSpherical.RectangularAverages
