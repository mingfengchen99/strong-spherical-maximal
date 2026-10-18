import ProductSmoothing
import MarginalLocalEstimate
import Mathlib.Analysis.Fourier.Convolution

/-! # Physical convolution commutes with normalized partial smoothing -/
noncomputable section
open MeasureTheory Set
open scoped SchwartzMap BigOperators

namespace StrongSpherical.ConvolutionSmoothing
open ProductSmoothing
variable {d j : ℕ}

/-- Actual smoothing along the image of a continuous linear coordinate inclusion. -/
def partialConvolution (A : Space j →L[ℝ] Space d) (r : Radii j)
    (g : Space d → ℂ) (x : Space d) : ℂ :=
  ∫ y, productPhi r y * g (x - A y)

theorem integrable_partial_double (K : Space d → ℂ) (hK : Continuous K)
    (hKi : Integrable K) (A : Space j →L[ℝ] Space d) (r : Radii j)
    (f : 𝓢(Space d, ℂ)) (x : Space d) :
    Integrable (fun p : Space d × Space j =>
      K p.1 * (productPhi r p.2 * f (x - p.1 - A p.2))) (volume.prod volume) := by
  have hcont : Continuous (fun p : Space d × Space j =>
      K p.1 * (productPhi r p.2 * f (x - p.1 - A p.2))) := by
    have hp := continuous_productPhi r
    fun_prop
  have hb : Integrable (fun p : Space d × Space j =>
      ‖K p.1‖ * ‖productPhi r p.2‖ * SchwartzMap.seminorm ℝ 0 0 f)
      ((volume : Measure (Space d)).prod volume) :=
    (hKi.norm.mul_prod (integrable_productPhi r).norm).mul_const _
  apply hb.mono' hcont.aestronglyMeasurable
  filter_upwards with p
  rw [norm_mul, norm_mul]
  have hf := SchwartzMap.norm_le_seminorm ℝ f (x - p.1 - A p.2)
  calc
    _ = (‖K p.1‖ * ‖productPhi r p.2‖) * ‖f (x - p.1 - A p.2)‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hf (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Partial smoothing commutes with the original convolution integral on Schwartz inputs. -/
theorem convolution_partial_commute (K : Space d → ℂ) (hK : Continuous K)
    (hKi : Integrable K) (A : Space j →L[ℝ] Space d) (r : Radii j)
    (f : 𝓢(Space d, ℂ)) (x : Space d) :
    kernelConvolution K (partialConvolution A r f) x =
      partialConvolution A r (kernelConvolution K f) x := by
  rw [kernelConvolution_eq_integral]
  unfold partialConvolution
  calc
    _ = ∫ z, ∫ y, K z * (productPhi r y * f (x - z - A y)) := by
      simp only [integral_const_mul]
    _ = ∫ y, ∫ z, K z * (productPhi r y * f (x - z - A y)) :=
      integral_integral_swap (integrable_partial_double K hK hKi A r f x)
    _ = ∫ y, productPhi r y * kernelConvolution K f (x - A y) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [kernelConvolution_eq_integral, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      rw [sub_right_comm x z (A y)]
      ring

theorem convolution_partial_commute_compact (K : Space d → ℂ) (hK : Continuous K)
    (hc : HasCompactSupport K) (A : Space j →L[ℝ] Space d) (r : Radii j)
    (f : 𝓢(Space d, ℂ)) (x : Space d) :
    kernelConvolution K (partialConvolution A r f) x =
      partialConvolution A r (kernelConvolution K f) x :=
  convolution_partial_commute K hK (hK.integrable_of_hasCompactSupport hc) A r f x

theorem integrable_convolution_schwartz (K : Space d → ℂ) (hKi : Integrable K)
    (g : 𝓢(Space d, ℂ)) (x : Space d) :
    Integrable (fun y => K y * g (x - y)) := by
  apply hKi.mul_bdd ((g.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  filter_upwards with y
  exact SchwartzMap.norm_le_seminorm ℝ g _

theorem integrable_full_double (K : Space d → ℂ) (hK : Continuous K)
    (hKi : Integrable K) (g f : 𝓢(Space d, ℂ)) (x : Space d) :
    Integrable (fun p : Space d × Space d =>
      K p.2 * (g (p.1 - p.2) * f (x - p.1))) (volume.prod volume) := by
  have hbase := Real.integrable_prod_sub (ContinuousLinearMap.mul ℂ ℂ)
    g.integrable hKi g.continuous hK
  have hb : Integrable (fun p : Space d × Space d =>
      ‖g (p.1 - p.2)‖ * ‖K p.2‖ * SchwartzMap.seminorm ℝ 0 0 f) (volume.prod volume) := by
    have hmass : Integrable (fun p : Space d × Space d => ‖g (p.1 - p.2)‖ * ‖K p.2‖)
        (volume.prod volume) := by
      simpa only [ContinuousLinearMap.opNorm_mul, one_mul] using hbase
    exact hmass.mul_const _
  have hm : AEStronglyMeasurable (fun p : Space d × Space d =>
      K p.2 * (g (p.1 - p.2) * f (x - p.1))) (volume.prod volume) := by
    exact (by fun_prop : Continuous (fun p : Space d × Space d =>
      K p.2 * (g (p.1 - p.2) * f (x - p.1)))).aestronglyMeasurable
  apply hb.mono' hm
  filter_upwards with p
  rw [norm_mul, norm_mul]
  have hf := SchwartzMap.norm_le_seminorm ℝ f (x - p.1)
  calc
    _ = (‖g (p.1 - p.2)‖ * ‖K p.2‖) * ‖f (x - p.1)‖ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hf (mul_nonneg (norm_nonneg _) (norm_nonneg _))

/-- Genuine full convolution associativity for an integrable continuous kernel and Schwartz factors. -/
theorem convolution_assoc_schwartz (K : Space d → ℂ) (hK : Continuous K)
    (hKi : Integrable K) (g f : 𝓢(Space d, ℂ)) (x : Space d) :
    kernelConvolution (kernelConvolution K g) f x =
      kernelConvolution K (kernelConvolution g f) x := by
  apply MeasureTheory.convolution_assoc'
    (ContinuousLinearMap.mul ℂ ℂ) (ContinuousLinearMap.mul ℂ ℂ)
    (ContinuousLinearMap.mul ℂ ℂ) (ContinuousLinearMap.mul ℂ ℂ)
  · intro a b c
    exact mul_assoc a b c
  · filter_upwards with y
    exact integrable_convolution_schwartz K hKi g y
  · filter_upwards with y
    exact integrable_convolution_schwartz g g.integrable f y
  · exact integrable_full_double K hK hKi g f x

theorem integrable_partial_kernel_double (K : Space d → ℂ) (hK : Continuous K)
    (hKi : Integrable K) (A : Space j →L[ℝ] Space d) (r : Radii j) :
    Integrable (fun p : Space j × Space d => productPhi r p.1 * K (p.2 - A p.1))
      (volume.prod volume) := by
  have hc : Continuous (fun p : Space j × Space d => productPhi r p.1 * K (p.2 - A p.1)) := by
    have hp := continuous_productPhi r
    fun_prop
  apply (integrable_prod_iff (μ := (volume : Measure (Space j)))
    (ν := (volume : Measure (Space d))) hc.aestronglyMeasurable).mpr
  constructor
  · filter_upwards with y
    exact (hKi.comp_sub_right (A y)).const_mul _
  · have hi := (integrable_productPhi r).norm.mul_const (∫ z, ‖K z‖)
    have hn (y : Space j) : (∫ z : Space d, ‖K (z - A y)‖) = ∫ z : Space d, ‖K z‖ :=
      integral_sub_right_eq_self (fun z : Space d => ‖K z‖) (A y) (μ := volume)
    simpa only [norm_mul, integral_const_mul, hn] using hi

theorem integrable_partial_kernel_test_double (K : Space d → ℂ) (hK : Continuous K)
    (hKi : Integrable K) (A : Space j →L[ℝ] Space d) (r : Radii j)
    (f : 𝓢(Space d, ℂ)) (x : Space d) :
    Integrable (fun p : Space j × Space d =>
      (productPhi r p.1 * K (p.2 - A p.1)) * f (x - p.2)) (volume.prod volume) := by
  apply (integrable_partial_kernel_double K hK hKi A r).mul_bdd
    ((f.continuous.comp (continuous_const.sub continuous_snd)).aestronglyMeasurable)
  filter_upwards with p
  exact SchwartzMap.norm_le_seminorm ℝ f _

/-- Smoothing the kernel and then convolving is the same physical partial smoothing of `K*f`. -/
theorem partial_kernel_convolution (K : Space d → ℂ) (hK : Continuous K)
    (hKi : Integrable K) (A : Space j →L[ℝ] Space d) (r : Radii j)
    (f : 𝓢(Space d, ℂ)) (x : Space d) :
    kernelConvolution (partialConvolution A r K) f x =
      partialConvolution A r (kernelConvolution K f) x := by
  rw [kernelConvolution_eq_integral]
  unfold partialConvolution
  calc
    _ = ∫ z, ∫ y, (productPhi r y * K (z - A y)) * f (x - z) := by
      simp only [integral_mul_const]
    _ = ∫ y, ∫ z, (productPhi r y * K (z - A y)) * f (x - z) :=
      (integral_integral_swap (integrable_partial_kernel_test_double K hK hKi A r f x)).symm
    _ = ∫ y, productPhi r y * kernelConvolution K f (x - A y) := by
      apply integral_congr_ae
      filter_upwards with y
      rw [kernelConvolution_eq_integral, ← integral_const_mul]
      have h := integral_sub_right_eq_self
        (fun z : Space d => productPhi r y * (K z * f (x - A y - z))) (A y)
        (μ := volume)
      convert h using 1
      congr 1
      funext z
      simp only [sub_sub_sub_cancel_right]
      ring

theorem convolution_partial_kernel (K : Space d → ℂ) (hK : Continuous K)
    (hKi : Integrable K) (A : Space j →L[ℝ] Space d) (r : Radii j)
    (f : 𝓢(Space d, ℂ)) (x : Space d) :
    kernelConvolution K (partialConvolution A r f) x =
      kernelConvolution (partialConvolution A r K) f x := by
  rw [convolution_partial_commute K hK hKi, partial_kernel_convolution K hK hKi]

end StrongSpherical.ConvolutionSmoothing
