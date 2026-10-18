import EllipsoidGraph
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Compact local radius parameters and continuity of the original kernels -/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal FourierTransform BigOperators Topology
namespace StrongSpherical.NormalKernelRegularity
open QuadraticGraph EllipsoidGraph
variable {n : ℕ}

def radiusBox (n : ℕ) : Set (Fin n → ℝ) := Set.pi univ (fun _ => Icc 1 2)
abbrev LocalParameters (n : ℕ) := radiusBox n

instance localParameters_nonempty (n : ℕ) : Nonempty (LocalParameters n) :=
  ⟨⟨fun _ => 1, fun _ _ => ⟨le_rfl, by norm_num⟩⟩⟩
instance localParameters_compact (n : ℕ) : CompactSpace (LocalParameters n) :=
  isCompact_iff_compactSpace.mp (isCompact_univ_pi (fun _ => isCompact_Icc))

def parameterRadii (p : LocalParameters n) : Radii n :=
  ⟨p.1, fun j => lt_of_lt_of_le zero_lt_one (p.2 j (mem_univ j)).1⟩

theorem parameterRadii_local (p : LocalParameters n) : parameterRadii p ∈ localRadii n :=
  fun j => p.2 j (mem_univ j)

theorem exists_parameter_of_local (r : Radii n) (hr : r ∈ localRadii n) :
    ∃ p : LocalParameters n, parameterRadii p = r :=
  ⟨⟨r.1, fun j _ => hr j⟩, Subtype.ext rfl⟩

theorem continuous_inverseFourier (beta : ℝ → ℂ) (hb : Continuous beta)
    (hc : HasCompactSupport beta) : Continuous (𝓕⁻ beta) := by
  have h : Continuous (fun t : ℝ => ∫ tau, beta tau * oscillation (tau * t)) := by
    have hh : ContinuousOn (fun p : ℝ × ℝ => beta p.2 * oscillation (p.2 * p.1)) (univ ×ˢ univ) :=
      ((hb.comp continuous_snd).mul (continuous_oscillation.comp (continuous_snd.mul continuous_fst))).continuousOn
    exact continuousOn_univ.mp (continuousOn_integral_of_compact_support hc hh
      (fun t tau _ htau => by rw [image_eq_zero_of_notMem_tsupport htau, zero_mul]))
  simpa only [← inverseFourier_eq_integral] using h

theorem continuous_parameter_inverseDilation :
    Continuous (fun p : LocalParameters n × Space n => inverseDilation (parameterRadii p.1) p.2) := by
  have hh : ∀ j, Continuous (fun p : LocalParameters n × Space n =>
      ((parameterRadii p.1).1 j)⁻¹ * p.2 j) := by
    intro j
    have hcoord : Continuous (fun p : LocalParameters n × Space n => (parameterRadii p.1).1 j) := by
      change Continuous (fun p : LocalParameters n × Space n => p.1.1 j)
      exact (continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)
    exact (hcoord.inv₀ (fun p => ne_of_gt ((parameterRadii p.1).2 j))).mul
      ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp continuous_snd)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).comp (continuous_pi hh)

theorem continuous_parameter_kernel (chi : Space n → ℂ) (hchi : Continuous chi)
    (beta : ℝ → ℂ) (hb : Continuous beta) (hbc : HasCompactSupport beta) (lambda : ℝ) :
    Continuous (fun p : LocalParameters n × Space n =>
      dilatedNormalKernel chi beta lambda (parameterRadii p.1) p.2) := by
  have hd : Continuous (fun p : LocalParameters n × Space n => dilationJacobian (parameterRadii p.1)) := by
    unfold dilationJacobian parameterRadii
    fun_prop
  have hdc := Complex.ofRealCLM.continuous.comp hd
  have harg := continuous_parameter_inverseDilation (n := n)
  change Continuous (fun p : LocalParameters n × Space n =>
    (dilationJacobian (parameterRadii p.1) : ℂ)⁻¹ *
      (chi (inverseDilation (parameterRadii p.1) p.2) * (lambda : ℂ) *
        (𝓕⁻ beta) (lambda * (‖inverseDilation (parameterRadii p.1) p.2‖ ^ 2 - 1))))
  exact (hdc.inv₀ (fun p => Complex.ofReal_ne_zero.mpr (ne_of_gt (dilationJacobian_pos _)))).mul
    (((hchi.comp harg).mul continuous_const).mul
      ((continuous_inverseFourier beta hb hbc).comp
        (continuous_const.mul ((harg.norm.pow 2).sub continuous_const))))

def displacementBox (n : ℕ) : Set (Space n) :=
  (@WithLp.ofLp 2 (Fin n → ℝ)) ⁻¹' Set.pi univ (fun _ => Icc (-4) 4)

theorem isCompact_displacementBox (n : ℕ) : IsCompact (displacementBox n) :=
  (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isCompact_preimage.2
    (isCompact_univ_pi (fun _ => isCompact_Icc))

theorem parameter_kernel_support (chi : Space n → ℂ)
    (hchi : Function.support chi ⊆ {u | ‖u‖ ≤ 2})
    (beta : ℝ → ℂ) (lambda : ℝ) (p : LocalParameters n) :
    Function.support (dilatedNormalKernel chi beta lambda (parameterRadii p)) ⊆ displacementBox n := by
  intro y hy
  have hne : chi (inverseDilation (parameterRadii p) y) ≠ 0 := by
    intro hz
    apply hy
    simp [dilatedNormalKernel, dilatedKernel, normalKernel, hz]
  have hnorm := hchi hne
  intro j _
  have hcoord : |inverseDilation (parameterRadii p) y j| ≤ ‖inverseDilation (parameterRadii p) y‖ := by
    simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (inverseDilation (parameterRadii p) y) j
  have hh : |inverseDilation (parameterRadii p) y j| ≤ 2 := hcoord.trans hnorm
  change |((parameterRadii p).1 j)⁻¹ * y j| ≤ 2 at hh
  rw [abs_mul, abs_inv, abs_of_pos ((parameterRadii p).2 j)] at hh
  have hm := mul_le_mul_of_nonneg_left hh ((parameterRadii p).2 j).le
  have he : (parameterRadii p).1 j * (((parameterRadii p).1 j)⁻¹ * |y j|) = |y j| := by
    field_simp [ne_of_gt ((parameterRadii p).2 j)]
  rw [he] at hm
  have hlocal := (parameterRadii_local p j).2
  have hbound : |y j| ≤ 4 := by linarith
  exact abs_le.mp hbound

set_option maxHeartbeats 1000000 in
/-- Joint continuity gives both output measurability and radius continuity,
for the actual original convolution used by Proposition 1.3. -/
theorem continuous_parameter_convolution (chi : Space n → ℂ) (hchi : Continuous chi)
    (hs : Function.support chi ⊆ {u | ‖u‖ ≤ 2})
    (beta : ℝ → ℂ) (hb : Continuous beta) (hbc : HasCompactSupport beta)
    (lambda : ℝ) (f : Space n → ℂ) (hf : Continuous f) :
    Continuous (fun p : LocalParameters n × Space n =>
      kernelConvolution (dilatedNormalKernel chi beta lambda (parameterRadii p.1)) f p.2) := by
  have hK := continuous_parameter_kernel chi hchi beta hb hbc lambda
  have hInt : ContinuousOn (fun z : (LocalParameters n × Space n) × Space n =>
      dilatedNormalKernel chi beta lambda (parameterRadii z.1.1) z.2 * f (z.1.2 - z.2)) (univ ×ˢ univ) :=
    ((hK.comp (continuous_fst.fst.prodMk continuous_snd)).mul
      (hf.comp (continuous_fst.snd.sub continuous_snd))).continuousOn
  have h := continuousOn_univ.mp (continuousOn_integral_of_compact_support
    (μ := (volume : Measure (Space n))) (f := fun (p : LocalParameters n × Space n) (y : Space n) =>
      dilatedNormalKernel chi beta lambda (parameterRadii p.1) y * f (p.2 - y))
    (isCompact_displacementBox n) hInt (fun (p : LocalParameters n × Space n) (y : Space n) _ hy => by
      have hz : dilatedNormalKernel chi beta lambda (parameterRadii p.1) y = 0 := by
        by_contra hn
        exact hy (parameter_kernel_support chi hs beta lambda p.1 hn)
      rw [hz, zero_mul]))
  simpa only [kernelConvolution_eq_integral] using h

end StrongSpherical.NormalKernelRegularity

namespace StrongSpherical.NormalKernelRegularity
open QuadraticGraph EllipsoidGraph
variable {n : ℕ}

theorem continuous_fixed_kernel (chi : Space n → ℂ) (hchi : Continuous chi)
    (beta : ℝ → ℂ) (hb : Continuous beta) (hbc : HasCompactSupport beta)
    (lambda : ℝ) (r : Radii n) :
    Continuous (dilatedNormalKernel chi beta lambda r) := by
  have ha : Continuous (inverseDilation r) := continuous_diagonalDilation _
  have hF := continuous_inverseFourier beta hb hbc
  change Continuous (fun y : Space n => (dilationJacobian r : ℂ)⁻¹ *
    (chi (inverseDilation r y) * (lambda : ℂ) *
      (𝓕⁻ beta) (lambda * (‖inverseDilation r y‖ ^ 2 - 1))))
  exact continuous_const.mul (((hchi.comp ha).mul continuous_const).mul
    (hF.comp (continuous_const.mul ((ha.norm.pow 2).sub continuous_const))))

theorem integrable_centered_kernel (chi : Space n → ℂ) (hchi : Continuous chi)
    (beta : ℝ → ℂ) (hb : Continuous beta) (hbc : HasCompactSupport beta)
    (lambda : ℝ) (r : Radii n)
    (f : Space n → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (x : Space n) :
    Integrable (fun y => dilatedNormalKernel chi beta lambda r (x - y) * f y) :=
  (((continuous_fixed_kernel chi hchi beta hb hbc lambda r).comp
    (continuous_const.sub continuous_id)).mul hf).integrable_of_hasCompactSupport hfc.mul_left

end StrongSpherical.NormalKernelRegularity

namespace StrongSpherical.NormalKernelRegularity
open QuadraticGraph EllipsoidGraph
variable {n : ℕ}

/-- The fixed kernel is compactly supported in the uniform displacement box. -/
theorem hasCompactSupport_local_kernel (chi : Space n → ℂ)
    (hs : Function.support chi ⊆ {u | ‖u‖ ≤ 2}) (beta : ℝ → ℂ) (lambda : ℝ)
    (r : Radii n) (hr : r ∈ localRadii n) :
    HasCompactSupport (dilatedNormalKernel chi beta lambda r) := by
  let p : LocalParameters n := ⟨r.1, fun j _ => hr j⟩
  have hsupport : Function.support (dilatedNormalKernel chi beta lambda r) ⊆ displacementBox n :=
    parameter_kernel_support chi hs beta lambda p
  exact (isCompact_displacementBox n).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal hsupport (isCompact_displacementBox n).isClosed)

/-- Genuine centered kernel rows are L², so pairing with any L² input is integrable. -/
theorem memLp_centered_kernel (chi : Space n → ℂ) (hchi : Continuous chi)
    (hs : Function.support chi ⊆ {u | ‖u‖ ≤ 2})
    (beta : ℝ → ℂ) (hb : Continuous beta) (hbc : HasCompactSupport beta)
    (lambda : ℝ) (r : Radii n) (hr : r ∈ localRadii n) (x : Space n) :
    MemLp (fun y => dilatedNormalKernel chi beta lambda r (x - y)) 2 volume := by
  have hc := hasCompactSupport_local_kernel chi hs beta lambda r hr
  exact ((continuous_fixed_kernel chi hchi beta hb hbc lambda r).comp
    (continuous_const.sub continuous_id)).memLp_of_hasCompactSupport (hc.comp_homeomorph (Homeomorph.subLeft x))

/-- Local integrability suffices for joint parameter/output continuity of the
original convolution. Every L² input has this property. -/
theorem continuous_parameter_convolution_L2 (chi : Space n → ℂ) (hchi : Continuous chi)
    (hs : Function.support chi ⊆ {u | ‖u‖ ≤ 2})
    (beta : ℝ → ℂ) (hb : Continuous beta) (hbc : HasCompactSupport beta)
    (lambda : ℝ) (f : Space n → ℂ) (hf : MemLp f 2 volume) :
    Continuous (fun p : LocalParameters n × Space n =>
      kernelConvolution (dilatedNormalKernel chi beta lambda (parameterRadii p.1)) f p.2) := by
  have hK := continuous_parameter_kernel chi hchi beta hb hbc lambda
  have h : ContinuousOn (fun p : LocalParameters n × Space n =>
      convolution f (dilatedNormalKernel chi beta lambda (parameterRadii p.1))
        (ContinuousLinearMap.mul ℂ ℂ).flip volume p.2) (univ ×ˢ univ) :=
    continuousOn_convolution_right_with_param (f := f)
      (g := fun p => dilatedNormalKernel chi beta lambda (parameterRadii p))
      (μ := (volume : Measure (Space n))) (ContinuousLinearMap.mul ℂ ℂ).flip
      (isCompact_displacementBox n) (fun p y _ hy => by
        by_contra hn
        exact hy (parameter_kernel_support chi hs beta lambda p hn))
      (hf.locallyIntegrable (by norm_num)) hK.continuousOn
  have he : ∀ p : LocalParameters n, convolution f
      (dilatedNormalKernel chi beta lambda (parameterRadii p))
      (ContinuousLinearMap.mul ℂ ℂ).flip volume =
        kernelConvolution (dilatedNormalKernel chi beta lambda (parameterRadii p)) f :=
    fun p => by
      change convolution f (dilatedNormalKernel chi beta lambda (parameterRadii p))
        (ContinuousLinearMap.mul ℂ ℂ).flip volume = convolution
          (dilatedNormalKernel chi beta lambda (parameterRadii p)) f (ContinuousLinearMap.mul ℂ ℂ) volume
      exact convolution_flip (ContinuousLinearMap.mul ℂ ℂ)
  have hh : Continuous (fun p : LocalParameters n × Space n => convolution f
      (dilatedNormalKernel chi beta lambda (parameterRadii p.1))
      (ContinuousLinearMap.mul ℂ ℂ).flip volume p.2) :=
    continuousOn_univ.mp (by simpa only [univ_prod_univ] using h)
  have heq : (fun p : LocalParameters n × Space n => convolution f
      (dilatedNormalKernel chi beta lambda (parameterRadii p.1))
      (ContinuousLinearMap.mul ℂ ℂ).flip volume p.2) =
      (fun p : LocalParameters n × Space n => kernelConvolution
        (dilatedNormalKernel chi beta lambda (parameterRadii p.1)) f p.2) := by
    funext p
    exact congrFun (he p.1) p.2
  rw [heq] at hh
  exact hh

end StrongSpherical.NormalKernelRegularity
