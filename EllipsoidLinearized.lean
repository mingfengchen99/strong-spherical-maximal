import EllipsoidSlice

/-! # Uniform L² bound for measurable radius selections on a normal patch -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal FourierTransform ContDiff
namespace StrongSpherical.EllipsoidLinearized
open QuadraticGraph EllipsoidGraph EllipsoidAmplitude EllipsoidSlice SliceMeasure NormalKernelRegularity
variable {m : ℕ}

/-- Package a measurable local radius choice in the compact parameter space. -/
def localParameterChoice {n : ℕ} (r : Space n → Radii n) (hr : ∀ x, r x ∈ localRadii n)
    (x : Space n) : LocalParameters n := ⟨(r x).1, fun j _ => hr x j⟩

theorem measurable_localParameterChoice {n : ℕ} (r : Space n → Radii n)
    (hr : ∀ x, r x ∈ localRadii n) (hm : ∀ j, Measurable (fun x => (r x).1 j)) :
    Measurable (localParameterChoice r hr) :=
  (measurable_pi_iff.mpr hm).subtype_mk

@[simp] theorem parameterRadii_choice {n : ℕ} (r : Space n → Radii n)
    (hr : ∀ x, r x ∈ localRadii n) (x : Space n) :
    parameterRadii (localParameterChoice r hr x) = r x := Subtype.ext rfl

theorem measurable_linearizedConvolution (chi : Space (m + 1) → ℂ) (hchi : Continuous chi)
    (hs : Function.support chi ⊆ {u | ‖u‖ ≤ 2})
    (beta : ℝ → ℂ) (hb : Continuous beta) (hbc : HasCompactSupport beta)
    (lambda : ℝ) (f : Space (m + 1) → ℂ) (hf : Continuous f)
    (r : Space (m + 1) → Radii (m + 1)) (hr : ∀ x, r x ∈ localRadii (m + 1))
    (hm : ∀ j, Measurable (fun x => (r x).1 j)) :
    Measurable (fun x => kernelConvolution (dilatedNormalKernel chi beta lambda (r x)) f x) := by
  have hmap : Measurable (fun x : Space (m + 1) => (localParameterChoice r hr x, x)) :=
    (measurable_localParameterChoice r hr hm).prodMk measurable_id
  have h := (continuous_parameter_convolution chi hchi hs beta hb hbc lambda f hf).measurable.comp hmap
  simp only [Function.comp_def, parameterRadii_choice] at h
  exact h

theorem measurable_linearizedConvolution_L2 (chi : Space (m + 1) → ℂ) (hchi : Continuous chi)
    (hs : Function.support chi ⊆ {u | ‖u‖ ≤ 2})
    (beta : ℝ → ℂ) (hb : Continuous beta) (hbc : HasCompactSupport beta)
    (lambda : ℝ) (f : Space (m + 1) → ℂ) (hf : MemLp f 2 volume)
    (r : Space (m + 1) → Radii (m + 1)) (hr : ∀ x, r x ∈ localRadii (m + 1))
    (hm : ∀ j, Measurable (fun x => (r x).1 j)) :
    Measurable (fun x => kernelConvolution (dilatedNormalKernel chi beta lambda (r x)) f x) := by
  have hmap : Measurable (fun x : Space (m + 1) => (localParameterChoice r hr x, x)) :=
    (measurable_localParameterChoice r hr hm).prodMk measurable_id
  have h := (continuous_parameter_convolution_L2 chi hchi hs beta hb hbc lambda f hf).measurable.comp hmap
  simp only [Function.comp_def, parameterRadii_choice] at h
  exact h


/-- Integrating the complete slice estimate proves the original linearized
bound, uniform over all measurable radius choices and all λ≥1. -/
theorem exists_uniform_linearized_patch_bound (m : ℕ) (chi : Space (m + 1) → ℂ)
    (hchi : ContDiff ℝ ∞ chi) (c : ℝ) (hc : 0 < c)
    (hpatch : Function.support chi ⊆ {u | u (Fin.last m) ≤ -c})
    (hsupport : Function.support chi ⊆ {u | ‖u‖ ≤ 2})
    (beta : ℝ → ℂ) (hb : Continuous beta) (hbc : HasCompactSupport beta)
    (hbetaSupport : Function.support beta ⊆ {t | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ lambda : ℝ, 1 ≤ lambda →
      ∀ (r : Space (m + 1) → Radii (m + 1)),
        (∀ j, Measurable (fun x => (r x).1 j)) →
        (∀ x, r x ∈ localRadii (m + 1)) →
        ∀ f : Space (m + 1) → ℂ, Continuous f → HasCompactSupport f →
          eLpNorm (fun x => kernelConvolution (dilatedNormalKernel chi beta lambda (r x)) f x) 2 volume ≤
            ENNReal.ofReal (C * lambda ^ (1 / 2 - (m : ℝ) / 4)) * eLpNorm f 2 volume := by
  obtain ⟨B, hB⟩ := hbc.exists_bound_of_continuous hb
  obtain ⟨C, hC, hSlice⟩ := exists_actual_slice_bound m chi hchi c hc hpatch hsupport
    beta hb.measurable B hB hbetaSupport
  refine ⟨4 * C, by positivity, ?_⟩
  intro lambda hlambda r hr hlocal f hf hfc
  let T : Space (m + 1) → ℂ := fun x =>
    kernelConvolution (dilatedNormalKernel chi beta lambda (r x)) f x
  have hT := measurable_linearizedConvolution chi hchi.continuous hsupport beta hb hbc lambda f hf r hlocal hr
  have hfLp : MemLp f 2 volume := hf.memLp_of_hasCompactSupport hfc
  have hsliceLp := memLp_sliceInput_ae 16 f hf.measurable hfLp
  have he : ∀ᵐ h : ℝ,
      (∫⁻ x : Space m, ‖T (slicePoint x h)‖ₑ ^ 2) ≤
        ENNReal.ofReal (C * lambda ^ (1 / 2 - (m : ℝ) / 4)) ^ 2 *
          (∫⁻ v, ‖sliceInput 16 f h v‖ₑ ^ 2) := by
    filter_upwards [hsliceLp] with h hLp
    let rh : Space m → Radii (m + 1) := fun x => r (slicePoint x h)
    have hrh : ∀ j, Measurable (fun x => (rh x).1 j) := fun j =>
      (hr j).comp (by unfold slicePoint; fun_prop)
    have hlocalh : ∀ x, rh x ∈ localRadii (m + 1) := fun x => hlocal _
    have hbound := (hSlice lambda hlambda rh hrh hlocalh (sliceInput 16 f h) hLp).2
    have heq : (fun x => T (slicePoint x h)) = graphOperator (coefficients rh hrh)
        (graphAmplitude chi rh) (frequencyAmplitude rh beta lambda) (sliceInput 16 f h) := by
      funext x
      exact convolution_eq_graph_slice chi hchi c hc hpatch hsupport beta hb hbc hbetaSupport
        lambda (by linarith) rh hrh hlocalh f hf hfc h x
    have hp := pow_le_pow_left' hbound 2
    rw [← heq, mul_pow, SchurTest.eLpNorm_two_sq, SchurTest.eLpNorm_two_sq] at hp
    exact hp
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  simp only [ENNReal.rpow_two, mul_pow]
  rw [SchurTest.eLpNorm_two_sq]
  calc
    _ = ∫⁻ h, ∫⁻ x : Space m, ‖T (slicePoint x h)‖ₑ ^ 2 :=
      lintegral_slices _ (hT.enorm.pow_const 2)
    _ ≤ ∫⁻ h, ENNReal.ofReal (C * lambda ^ (1 / 2 - (m : ℝ) / 4)) ^ 2 *
        (∫⁻ v, ‖sliceInput 16 f h v‖ₑ ^ 2) := lintegral_mono_ae he
    _ = ENNReal.ofReal (C * lambda ^ (1 / 2 - (m : ℝ) / 4)) ^ 2 *
        (ENNReal.ofReal 16 * eLpNorm f 2 volume ^ 2) := by
      rw [lintegral_const_mul _ ((measurable_sliceInput 16 f hf.measurable).enorm.pow_const 2).lintegral_prod_right',
        lintegral_sliceInput_sq 16 f hf.measurable, ← SchurTest.eLpNorm_two_sq]
    _ = _ := by
      rw [show 4 * C * lambda ^ (1 / 2 - (m : ℝ) / 4) =
        4 * (C * lambda ^ (1 / 2 - (m : ℝ) / 4)) by ring, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), mul_pow]
      norm_num
      ring

theorem exists_uniform_linearized_patch_bound_L2 (m : ℕ) (chi : Space (m + 1) → ℂ)
    (hchi : ContDiff ℝ ∞ chi) (c : ℝ) (hc : 0 < c)
    (hpatch : Function.support chi ⊆ {u | u (Fin.last m) ≤ -c})
    (hsupport : Function.support chi ⊆ {u | ‖u‖ ≤ 2})
    (beta : ℝ → ℂ) (hb : Continuous beta) (hbc : HasCompactSupport beta)
    (hbetaSupport : Function.support beta ⊆ {t | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ lambda : ℝ, 1 ≤ lambda →
      ∀ (r : Space (m + 1) → Radii (m + 1)),
        (∀ j, Measurable (fun x => (r x).1 j)) →
        (∀ x, r x ∈ localRadii (m + 1)) →
        ∀ f : Space (m + 1) → ℂ, Measurable f → MemLp f 2 volume →
          eLpNorm (fun x => kernelConvolution (dilatedNormalKernel chi beta lambda (r x)) f x) 2 volume ≤
            ENNReal.ofReal (C * lambda ^ (1 / 2 - (m : ℝ) / 4)) * eLpNorm f 2 volume := by
  obtain ⟨B, hB⟩ := hbc.exists_bound_of_continuous hb
  obtain ⟨C, hC, hSlice⟩ := exists_actual_slice_bound m chi hchi c hc hpatch hsupport
    beta hb.measurable B hB hbetaSupport
  refine ⟨4 * C, by positivity, ?_⟩
  intro lambda hlambda r hr hlocal f hf hfLp
  let T : Space (m + 1) → ℂ := fun x =>
    kernelConvolution (dilatedNormalKernel chi beta lambda (r x)) f x
  have hT := measurable_linearizedConvolution_L2 chi hchi.continuous hsupport beta hb hbc lambda f hfLp r hlocal hr
  have hsliceLp := memLp_sliceInput_ae 16 f hf hfLp
  have he : ∀ᵐ h : ℝ,
      (∫⁻ x : Space m, ‖T (slicePoint x h)‖ₑ ^ 2) ≤
        ENNReal.ofReal (C * lambda ^ (1 / 2 - (m : ℝ) / 4)) ^ 2 *
          (∫⁻ v, ‖sliceInput 16 f h v‖ₑ ^ 2) := by
    filter_upwards [hsliceLp] with h hLp
    let rh : Space m → Radii (m + 1) := fun x => r (slicePoint x h)
    have hrh : ∀ j, Measurable (fun x => (rh x).1 j) := fun j =>
      (hr j).comp (by unfold slicePoint; fun_prop)
    have hlocalh : ∀ x, rh x ∈ localRadii (m + 1) := fun x => hlocal _
    have hbound := (hSlice lambda hlambda rh hrh hlocalh (sliceInput 16 f h) hLp).2
    have heq : (fun x => T (slicePoint x h)) = graphOperator (coefficients rh hrh)
        (graphAmplitude chi rh) (frequencyAmplitude rh beta lambda) (sliceInput 16 f h) := by
      funext x
      exact convolution_eq_graph_slice_L2 chi hchi c hc hpatch hsupport beta hb hbc hbetaSupport
        lambda (by linarith) rh hrh hlocalh f hfLp h hLp x
    have hp := pow_le_pow_left' hbound 2
    rw [← heq, mul_pow, SchurTest.eLpNorm_two_sq, SchurTest.eLpNorm_two_sq] at hp
    exact hp
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp
  simp only [ENNReal.rpow_two, mul_pow]
  rw [SchurTest.eLpNorm_two_sq]
  calc
    _ = ∫⁻ h, ∫⁻ x : Space m, ‖T (slicePoint x h)‖ₑ ^ 2 :=
      lintegral_slices _ (hT.enorm.pow_const 2)
    _ ≤ ∫⁻ h, ENNReal.ofReal (C * lambda ^ (1 / 2 - (m : ℝ) / 4)) ^ 2 *
        (∫⁻ v, ‖sliceInput 16 f h v‖ₑ ^ 2) := lintegral_mono_ae he
    _ = ENNReal.ofReal (C * lambda ^ (1 / 2 - (m : ℝ) / 4)) ^ 2 *
        (ENNReal.ofReal 16 * eLpNorm f 2 volume ^ 2) := by
      rw [lintegral_const_mul _ ((measurable_sliceInput 16 f hf).enorm.pow_const 2).lintegral_prod_right',
        lintegral_sliceInput_sq 16 f hf, ← SchurTest.eLpNorm_two_sq]
    _ = _ := by
      rw [show 4 * C * lambda ^ (1 / 2 - (m : ℝ) / 4) =
        4 * (C * lambda ^ (1 / 2 - (m : ℝ) / 4)) by ring, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), mul_pow]
      norm_num
      ring

end StrongSpherical.EllipsoidLinearized
