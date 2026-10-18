import EllipsoidAmplitude
import SliceMeasure
import NormalKernelRegularity

/-! # Integral reduction of the original ellipsoid convolution to the graph slice -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff
namespace StrongSpherical.EllipsoidSlice
open QuadraticGraph EllipsoidGraph EllipsoidAmplitude AmplitudeBounds SliceMeasure NormalKernelRegularity
variable {m : ℕ}

/-- Reverse the displacement variable in the genuine convolution. -/
theorem convolution_eq_centered_integral (K f : Space (m + 1) → ℂ) (x : Space (m + 1)) :
    kernelConvolution K f x = ∫ y, K (x - y) * f y := by
  rw [kernelConvolution_eq_integral]
  have h := integral_sub_left_eq_self (fun y => K (x - y) * f y) volume x
  simpa only [sub_sub_cancel] using h

/-- On the negative normal patch the centered integrand vanishes below the output height. -/
theorem centered_kernel_eq_zero (chi : Space (m + 1) → ℂ) (c : ℝ) (hc : 0 < c)
    (hpatch : Function.support chi ⊆ {u | u (Fin.last m) ≤ -c})
    (beta : ℝ → ℂ) (lambda : ℝ) (r : Radii (m + 1))
    (x u : Space m) (h t : ℝ) (ht : t ≤ h) :
    dilatedNormalKernel chi beta lambda r (slicePoint x h - slicePoint u t) = 0 := by
  have hzero : chi (inverseDilation r (slicePoint x h - slicePoint u t)) = 0 := by
    by_contra hne
    have hp := hpatch hne
    have hh : 0 ≤ inverseDilation r (slicePoint x h - slicePoint u t) (Fin.last m) := by
      simpa [inverseDilation, diagonalDilation] using
        mul_nonneg (inv_nonneg.mpr (r.2 (Fin.last m)).le) (sub_nonneg.mpr ht)
    change inverseDilation r (slicePoint x h - slicePoint u t) (Fin.last m) ≤ -c at hp
    linarith
  simp [dilatedNormalKernel, dilatedKernel, normalKernel, hzero]

/-- The fixed input cutoff equals one on the actual amplitude support. -/
theorem inputKernel_mul_sliceInput (chi : Space (m + 1) → ℂ)
    (hs : Function.support chi ⊆ {u | ‖u‖ ≤ 2})
    (r : Space m → Radii (m + 1)) (hr : ∀ j, Measurable (fun x => (r x).1 j))
    (hlocal : ∀ x, r x ∈ localRadii (m + 1)) (beta : ℝ → ℂ) (lambda : ℝ)
    (f : Space (m + 1) → ℂ) (h : ℝ) (x : Space m) (v : Space (m + 1)) :
    inputKernel (coefficients r hr) (graphAmplitude chi r) (frequencyAmplitude r beta lambda) x v *
        sliceInput 16 f h v =
      inputKernel (coefficients r hr) (graphAmplitude chi r) (frequencyAmplitude r beta lambda) x v *
        f (liftedInput h v) := by
  by_cases hv : normalInput v ∈ Icc 0 16
  · simp [sliceInput, hv]
  · have ha : graphAmplitude chi r x v = 0 := by
      by_contra hne
      have hb := (graphAmplitude_support chi hs r hlocal x hne).2
      have hpos : 0 < normalInput v := by
        by_contra hn
        exact hne (by simp [graphAmplitude, hn])
      exact hv ⟨hpos.le, (le_abs_self _).trans hb⟩
    simp [inputKernel, ha]

set_option maxHeartbeats 1000000 in
/-- The complete integral identity (4.3)--(4.7), for the original convolution.
All input integrands are proved integrable before the Fubini steps. -/
theorem convolution_eq_graph_slice (chi : Space (m + 1) → ℂ) (hchi : ContDiff ℝ ∞ chi)
    (c : ℝ) (hc : 0 < c)
    (hpatch : Function.support chi ⊆ {u | u (Fin.last m) ≤ -c})
    (hsupport : Function.support chi ⊆ {u | ‖u‖ ≤ 2})
    (beta : ℝ → ℂ) (hb : Continuous beta) (hbc : HasCompactSupport beta)
    (hbetaSupport : Function.support beta ⊆ {t | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2})
    (lambda : ℝ) (hlambda : 0 < lambda)
    (r : Space m → Radii (m + 1)) (hr : ∀ j, Measurable (fun x => (r x).1 j))
    (hlocal : ∀ x, r x ∈ localRadii (m + 1))
    (f : Space (m + 1) → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (h : ℝ) (x : Space m) :
    kernelConvolution (dilatedNormalKernel chi beta lambda (r x)) f (slicePoint x h) =
      graphOperator (coefficients r hr) (graphAmplitude chi r) (frequencyAmplitude r beta lambda)
        (sliceInput 16 f h) x := by
  have hK := continuous_fixed_kernel chi hchi.continuous beta hb hbc lambda (r x)
  let F : Space (m + 1) → ℂ := fun y =>
    dilatedNormalKernel chi beta lambda (r x) (slicePoint x h - y) * f y
  have hF : Integrable F :=
    ((hK.comp (continuous_const.sub continuous_id)).mul hf).integrable_of_hasCompactSupport hfc.mul_left
  obtain ⟨M, _, hAmp⟩ := exists_graphAmplitude_bounds chi hchi c hc hpatch hsupport
  obtain ⟨B, hB⟩ := hbc.exists_bound_of_continuous hb
  have hq := (frequencyAmplitude_control r hr hlocal beta hb.measurable B hB hbetaSupport lambda hlambda x).integrable
  let H := inputKernel (coefficients r hr) (graphAmplitude chi r) (frequencyAmplitude r beta lambda) x
  have hH : Continuous H :=
    (hAmp r hlocal x).1.continuous.mul (continuous_frequencyKernel _ _ x hq)
  have hHc : HasCompactSupport H :=
    (hasCompactSupport_of_inputSupport 16 x
      (tsupport_subset_inputSupport 16 x (hAmp r hlocal x).2.2)).mul_right
  let G : Space (m + 1) → ℂ := fun v => H v * f (liftedInput h v)
  have hG : Integrable G := (hH.mul (hf.comp (by
    unfold liftedInput slicePoint spatialInput normalInput; fun_prop))).integrable_of_hasCompactSupport hHc.mul_right
  have hFG : ∀ u : Space m, (∫ t, F (slicePoint u t)) = ∫ s, G (slicePoint u s) := by
    intro u
    rw [integral_normal_substitution (fun t => F (slicePoint u t)) h (fun t ht => by
      simp only [F, centered_kernel_eq_zero chi c hc hpatch beta lambda (r x) x u h t ht, zero_mul])]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun s => by
      dsimp only
      by_cases hs : 0 < s
      · rw [if_pos hs]
        have hi := inputKernel_eq_changed_kernel chi r hr beta lambda hlambda x h (slicePoint u s)
          (by simpa [normalInput] using hs)
        dsimp only [G, H]
        rw [hi, Complex.real_smul]
        simp only [F, liftedInput, spatialInput, normalInput, slicePoint_castSucc, slicePoint_last, sqrtJacobian]
        push_cast
        ring
      · rw [if_neg hs]
        simp [G, H, inputKernel, graphAmplitude, normalInput, hs]
  rw [convolution_eq_centered_integral, integral_slices_reverse F hF]
  simp_rw [hFG]
  rw [← integral_slices_reverse G hG]
  unfold graphOperator
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v =>
    (inputKernel_mul_sliceInput chi hsupport r hr hlocal beta lambda f h x v).symm

set_option maxHeartbeats 1000000 in
/-- The complete integral identity (4.3)--(4.7), for the original convolution.
All input integrands are proved integrable before the Fubini steps. -/
theorem convolution_eq_graph_slice_L2 (chi : Space (m + 1) → ℂ) (hchi : ContDiff ℝ ∞ chi)
    (c : ℝ) (hc : 0 < c)
    (hpatch : Function.support chi ⊆ {u | u (Fin.last m) ≤ -c})
    (hsupport : Function.support chi ⊆ {u | ‖u‖ ≤ 2})
    (beta : ℝ → ℂ) (hb : Continuous beta) (hbc : HasCompactSupport beta)
    (hbetaSupport : Function.support beta ⊆ {t | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2})
    (lambda : ℝ) (hlambda : 0 < lambda)
    (r : Space m → Radii (m + 1)) (hr : ∀ j, Measurable (fun x => (r x).1 j))
    (hlocal : ∀ x, r x ∈ localRadii (m + 1))
    (f : Space (m + 1) → ℂ) (hf : MemLp f 2 volume)
    (h : ℝ) (hgh : MemLp (sliceInput 16 f h) 2 volume) (x : Space m) :
    kernelConvolution (dilatedNormalKernel chi beta lambda (r x)) f (slicePoint x h) =
      graphOperator (coefficients r hr) (graphAmplitude chi r) (frequencyAmplitude r beta lambda)
        (sliceInput 16 f h) x := by
  let F : Space (m + 1) → ℂ := fun y =>
    dilatedNormalKernel chi beta lambda (r x) (slicePoint x h - y) * f y
  have hF : Integrable F := (memLp_centered_kernel chi hchi.continuous hsupport beta hb hbc
    lambda (r x) (hlocal x) (slicePoint x h)).integrable_mul hf
  obtain ⟨M, _, hAmp⟩ := exists_graphAmplitude_bounds chi hchi c hc hpatch hsupport
  obtain ⟨B, hB⟩ := hbc.exists_bound_of_continuous hb
  have hq := (frequencyAmplitude_control r hr hlocal beta hb.measurable B hB hbetaSupport lambda hlambda x).integrable
  let H := inputKernel (coefficients r hr) (graphAmplitude chi r) (frequencyAmplitude r beta lambda) x
  have hH : Continuous H :=
    (hAmp r hlocal x).1.continuous.mul (continuous_frequencyKernel _ _ x hq)
  have hHc : HasCompactSupport H :=
    (hasCompactSupport_of_inputSupport 16 x
      (tsupport_subset_inputSupport 16 x (hAmp r hlocal x).2.2)).mul_right
  let G : Space (m + 1) → ℂ := fun v => H v * sliceInput 16 f h v
  have hHLp : MemLp H 2 volume := hH.memLp_of_hasCompactSupport hHc
  have hG : Integrable G := hHLp.integrable_mul hgh
  have hFG : ∀ u : Space m, (∫ t, F (slicePoint u t)) = ∫ s, G (slicePoint u s) := by
    intro u
    rw [integral_normal_substitution (fun t => F (slicePoint u t)) h (fun t ht => by
      simp only [F, centered_kernel_eq_zero chi c hc hpatch beta lambda (r x) x u h t ht, zero_mul])]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun s => by
      dsimp only
      by_cases hs : 0 < s
      · rw [if_pos hs]
        have hi := inputKernel_eq_changed_kernel chi r hr beta lambda hlambda x h (slicePoint u s)
          (by simpa [normalInput] using hs)
        dsimp only [G, H]
        rw [inputKernel_mul_sliceInput chi hsupport r hr hlocal beta lambda f h x, hi, Complex.real_smul]
        simp only [F, liftedInput, spatialInput, normalInput, slicePoint_castSucc, slicePoint_last, sqrtJacobian]
        push_cast
        ring
      · rw [if_neg hs]
        simp [G, H, inputKernel, graphAmplitude, normalInput, hs]
  rw [convolution_eq_centered_integral, integral_slices_reverse F hF]
  simp_rw [hFG]
  rw [← integral_slices_reverse G hG]
  rfl

end StrongSpherical.EllipsoidSlice
