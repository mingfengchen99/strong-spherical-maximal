import CoordinateSubsets
import DilationL2
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Sequences

/-! # Extending an actual Schwartz maximal estimate to every L² input -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology SchwartzMap ComplexConjugate
namespace StrongSpherical.MaximalDensity
variable {n : ℕ}

theorem memLp_centered_kernel_any_radius (K : Space n → ℂ) (hK : Continuous K)
    (R : ℝ) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R)
    (r : Radii n) (x : Space n) :
    MemLp (fun y => dilatedKernel K r (x - y)) 2 volume := by
  have hc : HasCompactSupport K :=
    (GenericKernelRegularity.isCompact_coordinateBox n R).of_isClosed_subset (isClosed_tsupport _)
      (closure_minimal hs (GenericKernelRegularity.isCompact_coordinateBox n R).isClosed)
  have hcr : HasCompactSupport (dilatedKernel K r) :=
    (hc.comp_homeomorph (CoordinateMarginals.inverseDilationHomeomorph r)).mul_left
  exact ((GenericKernelRegularity.continuous_fixed_kernel K hK r).comp
    (continuous_const.sub continuous_id)).memLp_of_hasCompactSupport
      (hcr.comp_homeomorph (Homeomorph.subLeft x))

/-- Point evaluation of convolution is the genuine L² inner-product functional. -/
theorem convolution_eq_inner_toLp (H f : Space n → ℂ) (x : Space n)
    (hrow : MemLp (fun y => H (x - y)) 2 volume) (hf : MemLp f 2 volume) :
    kernelConvolution H f x =
      inner ℂ (hrow.star.toLp (star (fun y => H (x - y)))) (hf.toLp f) := by
  rw [MarginalLocalEstimate.convolution_eq_centered_integral, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hrow.star.coeFn_toLp, hf.coeFn_toLp] with y hy hf'
  rw [hy, hf']
  simp [Pi.star_apply, RCLike.inner_apply, mul_comm]

theorem tendsto_convolution_of_toLp (H f : Space n → ℂ) (x : Space n)
    (hrow : MemLp (fun y => H (x - y)) 2 volume) (hf : MemLp f 2 volume)
    (F : ℕ → Space n → ℂ) (hF : ∀ q, MemLp (F q) 2 volume)
    (ht : Tendsto (fun q => (hF q).toLp (F q)) atTop (𝓝 (hf.toLp f))) :
    Tendsto (fun q => kernelConvolution H (F q) x) atTop (𝓝 (kernelConvolution H f x)) := by
  have h := ((innerSL ℂ (hrow.star.toLp (star (fun y => H (x - y))))).continuous.tendsto
    (hf.toLp f)).comp ht
  simpa only [Function.comp_def, innerSL_apply_apply,
    ← convolution_eq_inner_toLp H f x hrow hf,
    ← convolution_eq_inner_toLp H (F _) x hrow (hF _)] using h

theorem exists_schwartz_L2_sequence (f : Space n → ℂ) (hf : MemLp f 2 volume) :
    ∃ F : ℕ → 𝓢(Space n, ℂ),
      Tendsto (fun q => (F q).toLp 2 volume) atTop (𝓝 (hf.toLp f)) := by
  have hd : DenseRange (SchwartzMap.toLpCLM ℝ ℂ 2 (volume : Measure (Space n))) :=
    SchwartzMap.denseRange_toLpCLM (by norm_num)
  obtain ⟨u, hu, ht⟩ := mem_closure_iff_seq_limit.mp (hd (hf.toLp f))
  choose F hF using hu
  refine ⟨F, ?_⟩
  have he : u = fun q => (F q).toLp 2 volume := by
    funext q
    exact (hF q).symm
  rwa [he] at ht

/-- A finite constant proved for every actual Schwartz input extends unchanged
to every raw L² input of the original full strong maximal function. -/
theorem schwartz_bound_to_L2 (K : Space n → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox n R)
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (hSchwartz : ∀ F : 𝓢(Space n, ℂ),
      eLpNorm (strongKernelMaximal K F) 2 volume ≤ C * eLpNorm F 2 volume)
    (f : Space n → ℂ) (hf : MemLp f 2 volume) :
    Measurable (strongKernelMaximal K f) ∧
      eLpNorm (strongKernelMaximal K f) 2 volume ≤ C * eLpNorm f 2 volume := by
  have hMf := DilationL2.strongKernelMaximal_measurable K hK R hR hs f hf
  refine ⟨hMf, ?_⟩
  obtain ⟨F, ht⟩ := exists_schwartz_L2_sequence f hf
  have hF : ∀ q, MemLp (F q) 2 volume := fun q => (F q).memLp 2 volume
  have hMF : ∀ q, Measurable (strongKernelMaximal K (F q)) :=
    fun q => DilationL2.strongKernelMaximal_measurable K hK R hR hs (F q) (hF q)
  have htN : Tendsto (fun q => eLpNorm (F q) 2 volume) atTop (𝓝 (eLpNorm f 2 volume)) := by
    have h := ht.enorm
    simpa only [SchwartzMap.toLp, Lp.enorm_toLp] using h
  have htC : Tendsto (fun q => (C * eLpNorm (F q) 2 volume) ^ 2) atTop
      (𝓝 ((C * eLpNorm f 2 volume) ^ 2)) :=
    ENNReal.Tendsto.pow (n := 2) (ENNReal.Tendsto.const_mul htN (Or.inr hC))
  have hpoint : ∀ x, strongKernelMaximal K f x ^ 2 ≤
      liminf (fun q => strongKernelMaximal K (F q) x ^ 2) atTop := by
    intro x
    simp only [strongKernelMaximal, maximalOver, mem_univ, iSup_pos]
    rw [ENNReal.iSup_pow_of_ne_zero (by norm_num : (2 : ℕ) ≠ 0)]
    apply iSup_le
    intro r
    have hr := memLp_centered_kernel_any_radius K hK R hs r x
    have hconv := tendsto_convolution_of_toLp (dilatedKernel K r) f x hr hf
      (fun q => F q) hF ht
    have hp := ENNReal.Tendsto.pow (n := 2) hconv.enorm
    rw [← hp.liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall fun q => by
      simpa only [maximalOver, mem_univ, iSup_pos] using pow_le_pow_left'
        (le_maximalOver univ (fun r => kernelConvolution (dilatedKernel K r) (F q)) x (mem_univ r)) 2)
  apply (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
  calc
    _ = ∫⁻ x, strongKernelMaximal K f x ^ 2 :=
      MarginalLocalEstimate.eLpNorm_two_sq_ennreal _ _
    _ ≤ ∫⁻ x, liminf (fun q => strongKernelMaximal K (F q) x ^ 2) atTop := lintegral_mono hpoint
    _ ≤ liminf (fun q => ∫⁻ x, strongKernelMaximal K (F q) x ^ 2) atTop :=
      lintegral_liminf_le (fun q => (hMF q).pow_const 2)
    _ ≤ liminf (fun q => (C * eLpNorm (F q) 2 volume) ^ 2) atTop := by
      exact liminf_le_liminf (Eventually.of_forall fun q => by
        rw [← MarginalLocalEstimate.eLpNorm_two_sq_ennreal]
        exact pow_le_pow_left' (hSchwartz (F q)) 2)
    _ = _ := htC.liminf_eq

end StrongSpherical.MaximalDensity
