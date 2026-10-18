import KernelMaximalLp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-! # Amplitude truncation of actual convolution inputs -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace StrongSpherical.KernelTruncation
variable {n : ℕ}

def highPart (f : Space n → ℂ) (a : ℝ) : Space n → ℂ :=
  {x | a < ‖f x‖}.indicator f

def lowPart (f : Space n → ℂ) (a : ℝ) : Space n → ℂ :=
  {x | ‖f x‖ ≤ a}.indicator f

theorem measurable_highPart (f : Space n → ℂ) (hf : Measurable f) (a : ℝ) :
    Measurable (highPart f a) := hf.indicator (measurableSet_lt measurable_const hf.norm)

theorem measurable_lowPart (f : Space n → ℂ) (hf : Measurable f) (a : ℝ) :
    Measurable (lowPart f a) := hf.indicator (measurableSet_le hf.norm measurable_const)

theorem highPart_add_lowPart (f : Space n → ℂ) (a : ℝ) :
    highPart f a + lowPart f a = f := by
  funext x
  by_cases h : a < ‖f x‖ <;> simp [highPart, lowPart, h, le_of_not_gt]

theorem enorm_highPart (f : Space n → ℂ) (a : ℝ) (x : Space n) :
    ‖highPart f a x‖ₑ = {y | a < ‖f y‖}.indicator (fun y => ‖f y‖ₑ) x := by
  by_cases h : a < ‖f x‖ <;> simp [highPart, h]

theorem enorm_lowPart (f : Space n → ℂ) (a : ℝ) (x : Space n) :
    ‖lowPart f a x‖ₑ = {y | ‖f y‖ ≤ a}.indicator (fun y => ‖f y‖ₑ) x := by
  by_cases h : ‖f x‖ ≤ a <;> simp [lowPart, h]

theorem highPart_energy (f : Space n → ℂ) (a q : ℝ) (hq : 0 < q) :
    (∫⁻ x, ‖highPart f a x‖ₑ ^ q) =
      ∫⁻ x, {x | a < ‖f x‖}.indicator (fun x => ‖f x‖ₑ ^ q) x := by
  apply lintegral_congr
  intro x
  by_cases h : a < ‖f x‖ <;> simp [highPart, h, ENNReal.zero_rpow_of_pos hq]

theorem lowPart_energy (f : Space n → ℂ) (a q : ℝ) (hq : 0 < q) :
    (∫⁻ x, ‖lowPart f a x‖ₑ ^ q) =
      ∫⁻ x, {x | ‖f x‖ ≤ a}.indicator (fun x => ‖f x‖ₑ ^ q) x := by
  apply lintegral_congr
  intro x
  by_cases h : ‖f x‖ ≤ a <;> simp [lowPart, h, ENNReal.zero_rpow_of_pos hq]

theorem eLpNorm_rpow_eq_energy (f : Space n → ℂ) (p : ℝ) (hp : 0 < p) :
    eLpNorm f (ENNReal.ofReal p) volume ^ p = ∫⁻ x, ‖f x‖ₑ ^ p := by
  simpa only [eLpNorm_enorm] using RectangularMaximalLp.eLpNorm_ofReal_rpow volume
    (fun x => ‖f x‖ₑ) p hp

theorem energy_lt_top (f : Space n → ℂ) (p : ℝ) (hp : 0 < p)
    (hf : MemLp f (ENNReal.ofReal p) volume) : (∫⁻ x, ‖f x‖ₑ ^ p) < ∞ := by
  rw [← eLpNorm_rpow_eq_energy f p hp]
  exact ENNReal.rpow_lt_top_of_nonneg hp.le hf.eLpNorm_ne_top

theorem norm_highPart_rpow_le (f : Space n → ℂ) (p q : ℝ) (hq : 0 < q)
    (hqp : q < p) (a : ℝ) (ha : 0 < a) (x : Space n) :
    ‖highPart f a x‖ ^ q ≤ a ^ (q - p) * ‖f x‖ ^ p := by
  by_cases h : a < ‖f x‖
  · have hx : 0 < ‖f x‖ := ha.trans h
    rw [show highPart f a x = f x by simp [highPart, h]]
    calc
      ‖f x‖ ^ q = ‖f x‖ ^ p * ‖f x‖ ^ (q - p) := by
        rw [← Real.rpow_add hx]
        congr 1
        ring
      _ ≤ ‖f x‖ ^ p * a ^ (q - p) :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos ha h.le (by linarith))
          (Real.rpow_nonneg (norm_nonneg _) _)
      _ = _ := mul_comm _ _
  · rw [show highPart f a x = 0 by simp [highPart, h], norm_zero, Real.zero_rpow hq.ne']
    exact mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg (norm_nonneg _) _)

theorem norm_lowPart_rpow_le (f : Space n → ℂ) (p r : ℝ) (hp : 0 < p)
    (hpr : p < r) (a : ℝ) (ha : 0 < a) (x : Space n) :
    ‖lowPart f a x‖ ^ r ≤ a ^ (r - p) * ‖f x‖ ^ p := by
  by_cases h : ‖f x‖ ≤ a
  · rw [show lowPart f a x = f x by simp [lowPart, h]]
    by_cases hz : ‖f x‖ = 0
    · simp [hz, Real.zero_rpow hp.ne', Real.zero_rpow (by linarith : r ≠ 0)]
    · have hx : 0 < ‖f x‖ := (norm_nonneg _).lt_of_ne' hz
      calc
        ‖f x‖ ^ r = ‖f x‖ ^ p * ‖f x‖ ^ (r - p) := by
          rw [← Real.rpow_add hx]
          congr 1
          ring
        _ ≤ ‖f x‖ ^ p * a ^ (r - p) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) h (by linarith))
            (Real.rpow_nonneg (norm_nonneg _) _)
        _ = _ := mul_comm _ _
  · rw [show lowPart f a x = 0 by simp [lowPart, h], norm_zero,
      Real.zero_rpow (by linarith : r ≠ 0)]
    exact mul_nonneg (Real.rpow_nonneg ha.le _) (Real.rpow_nonneg (norm_nonneg _) _)

theorem highPart_energy_le (f : Space n → ℂ) (p q : ℝ) (hq : 0 < q)
    (hqp : q < p) (a : ℝ) (ha : 0 < a) :
    (∫⁻ x, ‖highPart f a x‖ₑ ^ q) ≤
      ENNReal.ofReal (a ^ (q - p)) * ∫⁻ x, ‖f x‖ₑ ^ p := by
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (a ^ (q - p)) * ‖f x‖ₑ ^ p := by
      apply lintegral_mono
      intro x
      have h := ENNReal.ofReal_le_ofReal (norm_highPart_rpow_le f p q hq hqp a ha x)
      simpa only [ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _),
        ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (highPart f a x)) hq.le,
        ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) (by linarith : 0 ≤ p), ofReal_norm] using h
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem lowPart_energy_le (f : Space n → ℂ) (p r : ℝ) (hp : 0 < p)
    (hpr : p < r) (a : ℝ) (ha : 0 < a) :
    (∫⁻ x, ‖lowPart f a x‖ₑ ^ r) ≤
      ENNReal.ofReal (a ^ (r - p)) * ∫⁻ x, ‖f x‖ₑ ^ p := by
  calc
    _ ≤ ∫⁻ x, ENNReal.ofReal (a ^ (r - p)) * ‖f x‖ₑ ^ p := by
      apply lintegral_mono
      intro x
      have h := ENNReal.ofReal_le_ofReal (norm_lowPart_rpow_le f p r hp hpr a ha x)
      simpa only [ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _),
        ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (lowPart f a x)) (by linarith : 0 ≤ r),
        ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) hp.le, ofReal_norm] using h
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem memLp_highPart (f : Space n → ℂ) (hmeas : Measurable f)
    (p q : ℝ) (hq : 0 < q) (hqp : q < p) (a : ℝ) (ha : 0 < a)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    MemLp (highPart f a) (ENNReal.ofReal q) volume := by
  refine ⟨(measurable_highPart f hmeas a).aestronglyMeasurable, ?_⟩
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ENNReal.ofReal_ne_zero_iff.mpr hq) ENNReal.ofReal_ne_top).mpr
  rw [ENNReal.toReal_ofReal hq.le]
  exact (highPart_energy_le f p q hq hqp a ha).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (energy_lt_top f p (hq.trans hqp) hf))

theorem memLp_lowPart (f : Space n → ℂ) (hmeas : Measurable f)
    (p r : ℝ) (hp : 0 < p) (hpr : p < r) (a : ℝ) (ha : 0 < a)
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    MemLp (lowPart f a) (ENNReal.ofReal r) volume := by
  refine ⟨(measurable_lowPart f hmeas a).aestronglyMeasurable, ?_⟩
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (ENNReal.ofReal_ne_zero_iff.mpr (hp.trans hpr)) ENNReal.ofReal_ne_top).mpr
  rw [ENNReal.toReal_ofReal (hp.trans hpr).le]
  exact (lowPart_energy_le f p r hp hpr a ha).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (energy_lt_top f p hp hf))

theorem norm_lowPart_le (f : Space n → ℂ) (a : ℝ) (ha : 0 ≤ a) (x : Space n) :
    ‖lowPart f a x‖ ≤ a := by
  by_cases h : ‖f x‖ ≤ a <;> simp [lowPart, h, ha]

theorem eLpNorm_lowPart_top_le (f : Space n → ℂ) (a : ℝ) (ha : 0 ≤ a) :
    eLpNorm (lowPart f a) ∞ volume ≤ ENNReal.ofReal a := by
  rw [eLpNorm_exponent_top]
  exact eLpNormEssSup_le_of_ae_bound (Filter.Eventually.of_forall (norm_lowPart_le f a ha))

theorem memLp_lowPart_top (f : Space n → ℂ) (hmeas : Measurable f)
    (a : ℝ) (ha : 0 ≤ a) : MemLp (lowPart f a) ∞ volume :=
  ⟨(measurable_lowPart f hmeas a).aestronglyMeasurable,
    (eLpNorm_lowPart_top_le f a ha).trans_lt ENNReal.ofReal_lt_top⟩

theorem convolution_parts (K : Space n → ℂ) (hK : Continuous K) (hc : HasCompactSupport K)
    (f : Space n → ℂ) (hmeas : Measurable f) (p : ℝ≥0∞) (hp : 1 ≤ p) (a : ℝ)
    (hf : MemLp f p volume) (r : Radii n) (x : Space n) :
    kernelConvolution (dilatedKernel K r) f x =
      kernelConvolution (dilatedKernel K r) (highPart f a) x +
      kernelConvolution (dilatedKernel K r) (lowPart f a) x := by
  have hh : MemLp (highPart f a) p volume :=
    MemLp.indicator (measurableSet_lt measurable_const hmeas.norm) hf
  have hl : MemLp (lowPart f a) p volume :=
    MemLp.indicator (measurableSet_le hmeas.norm measurable_const) hf
  have hcr : HasCompactSupport (dilatedKernel K r) :=
    (hc.comp_homeomorph (CoordinateMarginals.inverseDilationHomeomorph r)).mul_left
  have hhc := hcr.convolutionExists_left (ContinuousLinearMap.mul ℂ ℂ)
    (GenericKernelRegularity.continuous_fixed_kernel K hK r) (hh.locallyIntegrable hp)
  have hlc := hcr.convolutionExists_left (ContinuousLinearMap.mul ℂ ℂ)
    (GenericKernelRegularity.continuous_fixed_kernel K hK r) (hl.locallyIntegrable hp)
  calc
    _ = kernelConvolution (dilatedKernel K r) (highPart f a + lowPart f a) x :=
      congrArg (fun g => kernelConvolution (dilatedKernel K r) g x) (highPart_add_lowPart f a).symm
    _ = _ := (hhc x).distrib_add (hlc x)

theorem strongKernelMaximal_le_parts (K : Space n → ℂ) (hK : Continuous K)
    (hc : HasCompactSupport K) (f : Space n → ℂ) (hmeas : Measurable f)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (a : ℝ) (hf : MemLp f p volume) (x : Space n) :
    strongKernelMaximal K f x ≤ strongKernelMaximal K (highPart f a) x +
      strongKernelMaximal K (lowPart f a) x := by
  unfold strongKernelMaximal maximalOver
  refine iSup_le fun r => iSup_le fun _ => ?_
  dsimp only
  rw [convolution_parts K hK hc f hmeas p hp a hf r x]
  refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact le_iSup_of_le r (le_iSup_of_le (mem_univ r) le_rfl)
  · exact le_iSup_of_le r (le_iSup_of_le (mem_univ r) le_rfl)

end StrongSpherical.KernelTruncation
