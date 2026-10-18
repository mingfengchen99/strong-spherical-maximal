import MiddleMaximalL2
import MaximalDensity
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! # Assembling the actual Fourier maximal pieces -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal BigOperators ComplexConjugate
namespace StrongSpherical.MaximalAssembly
set_option maxHeartbeats 1000000
open FourierMiddle DilationL2 MaximalDensity
variable {d : ℕ}

theorem strongKernelMaximal_congr_ae (K f g : Space d → ℂ) (hfg : f =ᵐ[volume] g) :
    strongKernelMaximal K f = strongKernelMaximal K g := by
  funext x
  unfold strongKernelMaximal maximalOver
  apply iSup_congr
  intro r
  have he := MeasureTheory.convolution_congr (ContinuousLinearMap.mul ℂ ℂ)
    (Filter.EventuallyEq.rfl : dilatedKernel K r =ᵐ[volume] dilatedKernel K r) hfg
  apply iSup_congr
  intro _
  change ‖kernelConvolution (dilatedKernel K r) f x‖ₑ =
    ‖kernelConvolution (dilatedKernel K r) g x‖ₑ
  exact congrArg (fun H : Space d → ℂ => ‖H x‖ₑ) he

/-- The maximal function formed from a family of actual L² operators. -/
def projectionMaximal (K : Space d → ℂ)
    (P : (Fin d → ℤ) → L2 d →L[ℂ] L2 d) (f : L2 d) (x : Space d) : ℝ≥0∞ :=
  ⨆ k, rectangleMaximal K (DyadicRadii.scales k) (P k f) x

theorem measurable_projectionMaximal (K : Space d → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox d R)
    (P : (Fin d → ℤ) → L2 d →L[ℂ] L2 d) (f : L2 d) :
    Measurable (projectionMaximal K P f) :=
  Measurable.iSup fun k => measurable_rectangleMaximal K hK R hR hs
    (DyadicRadii.scales k) (P k f) (Lp.memLp _)

def convolutionL2CLM (H : Space d → ℂ) (x : Space d)
    (hrow : MemLp (fun y => H (x - y)) 2 volume) : L2 d →L[ℂ] ℂ :=
  innerSL ℂ (hrow.star.toLp (star (fun y => H (x - y))))

theorem convolutionL2CLM_apply (H : Space d → ℂ) (x : Space d)
    (hrow : MemLp (fun y => H (x - y)) 2 volume) (f : L2 d) :
    convolutionL2CLM H x hrow f = kernelConvolution H f x := by
  rw [convolution_eq_inner_toLp H f x hrow (Lp.memLp f), Lp.toLp_coeFn]
  rfl

theorem convolution_operator_decomposition (K : Space d → ℂ) (hK : Continuous K)
    (R : ℝ) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox d R)
    (M : ℕ) (hM : 3 ≤ M) (k : Fin d → ℤ) (r : Radii d) (f : L2 d) (x : Space d) :
    kernelConvolution (dilatedKernel K r) f x =
      kernelConvolution (dilatedKernel K r) (middleOperator M k f) x +
      (∑ J ∈ (Finset.univ.powerset.erase ∅), (-1 : ℂ) ^ (J.card + 1) *
        kernelConvolution (dilatedKernel K r) (lowSubsetOperator M k J f) x) +
      kernelConvolution (dilatedKernel K r) (errorOperator M k f) x := by
  let L := convolutionL2CLM (dilatedKernel K r) x
    (memLp_centered_kernel_any_radius K hK R hs r x)
  have h := congrArg L (operator_decomposition M hM k f)
  simp only [map_add, map_sum, map_smul, smul_eq_mul] at h
  simpa only [L, convolutionL2CLM_apply] using h

theorem strongKernelMaximal_le_pieces (K : Space d → ℂ) (hK : Continuous K)
    (R : ℝ) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox d R)
    (M : ℕ) (hM : 3 ≤ M) (f : L2 d) (x : Space d) :
    strongKernelMaximal K f x ≤ MiddleMaximalL2.middleMaximal K M f x +
      (∑ J ∈ (Finset.univ.powerset.erase ∅),
        projectionMaximal K (fun k => lowSubsetOperator M k J) f x) +
      projectionMaximal K (errorOperator M) f x := by
  classical
  rw [DyadicRadii.strongKernelMaximal_eq_dyadic]
  refine iSup_le fun k => iSup_le fun t => iSup_le fun ht => ?_
  rw [convolution_operator_decomposition K hK R hs M hM k]
  refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (enorm_add_le _ _).trans (add_le_add ?_ ?_)
    · exact le_iSup_of_le k (le_iSup_of_le t (le_iSup_of_le ht le_rfl))
    · refine (enorm_sum_le _ _).trans (Finset.sum_le_sum fun J hJ => ?_)
      simp only [enorm_mul, enorm_pow, enorm_neg, enorm_one, one_pow, one_mul]
      exact le_iSup_of_le k (le_iSup_of_le t (le_iSup_of_le ht le_rfl))
  · exact le_iSup_of_le k (le_iSup_of_le t (le_iSup_of_le ht le_rfl))

theorem eLpNorm_le_three_pieces {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (S : Finset ι) (T F E : X → ℝ≥0∞) (L : ι → X → ℝ≥0∞)
    (hF : Measurable F) (hE : Measurable E) (hL : ∀ i, Measurable (L i))
    (hpoint : ∀ x, T x ≤ F x + (∑ i ∈ S, L i x) + E x) :
    eLpNorm T 2 μ ≤ eLpNorm F 2 μ + (∑ i ∈ S, eLpNorm (L i) 2 μ) + eLpNorm E 2 μ := by
  classical
  have hsum : ∀ S : Finset ι,
      eLpNorm (fun x => ∑ i ∈ S, L i x) 2 μ ≤ ∑ i ∈ S, eLpNorm (L i) 2 μ := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | @insert a S ha ih =>
      simp only [Finset.sum_insert ha]
      let V : X → ℝ≥0∞ := fun x => ∑ i ∈ S, L i x
      have hv : Measurable V := Finset.measurable_sum S (fun i _ => hL i)
      change eLpNorm (L a + V) 2 μ ≤ _
      exact (eLpNorm_add_le (f := L a) (g := V) (hL a).aestronglyMeasurable
        hv.aestronglyMeasurable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).trans
          (add_le_add le_rfl ih)
  let V : X → ℝ≥0∞ := fun x => ∑ i ∈ S, L i x
  have hv : Measurable V := Finset.measurable_sum S (fun i _ => hL i)
  have hmono : eLpNorm T 2 μ ≤ eLpNorm ((F + V) + E) 2 μ := by
    apply eLpNorm_mono_enorm
    intro x
    simpa only [enorm_eq_self, Pi.add_apply, V] using hpoint x
  have hadd : eLpNorm (F + V) 2 μ ≤ eLpNorm F 2 μ + eLpNorm V 2 μ :=
    eLpNorm_add_le (f := F) (g := V) hF.aestronglyMeasurable hv.aestronglyMeasurable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hadd2 : eLpNorm ((F + V) + E) 2 μ ≤ eLpNorm (F + V) 2 μ + eLpNorm E 2 μ :=
    eLpNorm_add_le (f := F + V) (g := E) (hF.add hv).aestronglyMeasurable hE.aestronglyMeasurable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  exact hmono.trans (hadd2.trans ((add_le_add hadd le_rfl).trans
    (add_le_add (add_le_add le_rfl (hsum S)) le_rfl)))

theorem eLpNorm_strongKernelMaximal_le_pieces (K : Space d → ℂ) (hK : Continuous K)
    (R : ℝ) (hR : 0 ≤ R) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox d R)
    (M : ℕ) (hM : 3 ≤ M) (f : L2 d) :
    eLpNorm (strongKernelMaximal K f) 2 volume ≤
      eLpNorm (MiddleMaximalL2.middleMaximal K M f) 2 volume +
      (∑ J ∈ (Finset.univ.powerset.erase ∅),
        eLpNorm (projectionMaximal K (fun k => lowSubsetOperator M k J) f) 2 volume) +
      eLpNorm (projectionMaximal K (errorOperator M) f) 2 volume := by
  classical
  exact eLpNorm_le_three_pieces volume (Finset.univ.powerset.erase ∅)
    (strongKernelMaximal K f) (MiddleMaximalL2.middleMaximal K M f)
    (projectionMaximal K (errorOperator M) f)
    (fun J => projectionMaximal K (fun k => lowSubsetOperator M k J) f)
    (MiddleMaximalL2.measurable_middleMaximal K hK R hR hs M f)
    (measurable_projectionMaximal K hK R hR hs _ f)
    (fun _ => measurable_projectionMaximal K hK R hR hs _ f)
    (strongKernelMaximal_le_pieces K hK R hs M hM f)

end StrongSpherical.MaximalAssembly
