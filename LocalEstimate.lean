import EllipsoidLinearized
import EllipsoidPatches
import CoordinateTransport
import MaximalLinearization

/-!
# Proposition 1.3: the original local kernel maximal operator

The proof joins the actual amplitude bounds, exact integral substitution,
height energy identity, signed coordinate patches and measurable linearization.
The final statement uses `localKernelMaximal (normalKernel chi beta lambda)`.
-/
noncomputable section
open MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff
namespace StrongSpherical.LocalEstimate
open QuadraticGraph EllipsoidGraph EllipsoidPatches EllipsoidLinearized
open CoordinateTransport NormalKernelRegularity MaximalLinearization EllipsoidSlice
variable {m : ℕ}

/-- Coordinate permutation and reflection transfer the negative-normal estimate
to every signed coordinate patch. -/
theorem exists_uniform_coordinate_patch_bound (m : ℕ) (j : PatchIndex (m + 1))
    (chi : Space (m + 1) → ℂ) (hchi : ContDiff ℝ ∞ chi)
    (hsupport : Function.support chi ⊆ {u | ‖u‖ ≤ 2})
    (hpatch : Function.support chi ⊆ patchOpen (m + 1) j)
    (beta : ℝ → ℂ) (hb : Continuous beta) (hbc : HasCompactSupport beta)
    (hbetaSupport : Function.support beta ⊆ {t | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ lambda : ℝ, 1 ≤ lambda →
      ∀ r : Space (m + 1) → Radii (m + 1),
        (∀ i, Measurable (fun x => (r x).1 i)) →
        (∀ x, r x ∈ localRadii (m + 1)) →
        ∀ f : Space (m + 1) → ℂ, Measurable f → MemLp f 2 volume →
          eLpNorm (fun x => kernelConvolution (dilatedNormalKernel chi beta lambda (r x)) f x) 2 volume ≤
            ENNReal.ofReal (C * lambda ^ (1 / 2 - (m : ℝ) / 4)) * eLpNorm f 2 volume := by
  let e := Equiv.swap (Fin.last m) j.1
  let Q := coordinateChange e j.2
  have hchiQ : ContDiff ℝ ∞ (chi ∘ Q) := hchi.comp Q.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
  have hsQ : Function.support (chi ∘ Q) ⊆ {u | ‖u‖ ≤ 2} := by
    intro u hu
    simpa only [mem_setOf_eq, LinearIsometryEquiv.norm_map] using hsupport hu
  have hpQ : Function.support (chi ∘ Q) ⊆ {u | u (Fin.last m) ≤ -patchThreshold (m + 1)} := by
    intro u hu
    have hp := hpatch hu
    change u (Fin.last m) ≤ -patchThreshold (m + 1)
    have he : e.symm j.1 = Fin.last m := by simp [e]
    cases hsign : j.2
    · have hh : u (Fin.last m) < -patchThreshold (m + 1) := by
        simpa only [patchOpen, hsign, Bool.false_eq_true, ↓reduceIte, mem_setOf_eq,
          Q, coordinateChange_apply, he] using hp
      exact hh.le
    · have hh : patchThreshold (m + 1) < -u (Fin.last m) := by
        simpa only [patchOpen, hsign, ↓reduceIte, mem_setOf_eq, Q, coordinateChange_apply, he] using hp
      linarith
  obtain ⟨C, hC, hbound⟩ := exists_uniform_linearized_patch_bound_L2 m (chi ∘ Q) hchiQ
    (patchThreshold (m + 1)) (patchThreshold_pos _) hpQ hsQ beta hb hbc hbetaSupport
  refine ⟨C, hC, ?_⟩
  intro lambda hlambda r hr hlocal f hf hfLp
  let rq : Space (m + 1) → Radii (m + 1) := fun x => transportRadii e (r (Q x))
  have hrq : ∀ i, Measurable (fun x => (rq x).1 i) := fun i =>
    (hr (e i)).comp Q.continuous.measurable
  have hlocalq : ∀ x, rq x ∈ localRadii (m + 1) := fun x => transportRadii_local e _ (hlocal _)
  have hfQ : MemLp (f ∘ Q) 2 volume := by
    refine ⟨(hf.comp Q.continuous.measurable).aestronglyMeasurable, ?_⟩
    rw [eLpNorm_comp_coordinateChange]
    exact hfLp.eLpNorm_lt_top
  have hh := hbound lambda hlambda rq hrq hlocalq (f ∘ Q) (hf.comp Q.continuous.measurable) hfQ
  have heq : (fun x => kernelConvolution (dilatedNormalKernel (chi ∘ Q) beta lambda (rq x)) (f ∘ Q) x) =
      (fun x => kernelConvolution (dilatedNormalKernel chi beta lambda (r x)) f x) ∘ Q := by
    funext x
    exact kernelConvolution_transport e j.2 chi beta lambda (r (Q x)) f x
  rw [heq, eLpNorm_comp_coordinateChange, eLpNorm_comp_coordinateChange] at hh
  exact hh

/-- Linearity in the cutoff is proved for the original integrals, with
integrability of every summand verified. -/
theorem linearizedConvolution_sum {ι : Type*} [Fintype ι]
    (a : ι → Space (m + 1) → ℂ) (ha : ∀ j, Continuous (a j))
    (has : ∀ j, Function.support (a j) ⊆ {u | ‖u‖ ≤ 2})
    (beta : ℝ → ℂ) (hb : Continuous beta) (hbc : HasCompactSupport beta)
    (lambda : ℝ) (r : Radii (m + 1)) (hr : r ∈ localRadii (m + 1))
    (f : Space (m + 1) → ℂ) (hf : MemLp f 2 volume) (x : Space (m + 1)) :
    kernelConvolution (dilatedNormalKernel (fun u => ∑ j, a j u) beta lambda r) f x =
      ∑ j, kernelConvolution (dilatedNormalKernel (a j) beta lambda r) f x := by
  classical
  simp_rw [convolution_eq_centered_integral]
  have hpoint : ∀ y, dilatedNormalKernel (fun u => ∑ j, a j u) beta lambda r (x - y) * f y =
      ∑ j, dilatedNormalKernel (a j) beta lambda r (x - y) * f y := by
    intro y
    simp only [dilatedNormalKernel, dilatedKernel, normalKernel, Finset.sum_mul, Finset.mul_sum]
  simp_rw [hpoint]
  exact integral_finsetSum Finset.univ (fun j _ =>
    (memLp_centered_kernel (a j) (ha j) (has j) beta hb hbc lambda r hr x).integrable_mul hf)

/-- Uniform measurable-selection bound for every smooth annular cutoff. -/
theorem exists_uniform_annular_linearized_bound (m : ℕ) (chi : Space (m + 1) → ℂ)
    (hchi : ContDiff ℝ ∞ chi) (hcompact : HasCompactSupport chi)
    (hsupport : tsupport chi ⊆ {u | (1 / 2 : ℝ) ≤ ‖u‖ ∧ ‖u‖ ≤ 2})
    (beta : ℝ → ℂ) (hb : Continuous beta) (hbc : HasCompactSupport beta)
    (hbetaSupport : Function.support beta ⊆ {t | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ lambda : ℝ, 1 ≤ lambda →
      ∀ r : Space (m + 1) → Radii (m + 1),
        (∀ i, Measurable (fun x => (r x).1 i)) →
        (∀ x, r x ∈ localRadii (m + 1)) →
        ∀ f : Space (m + 1) → ℂ, Measurable f → MemLp f 2 volume →
          eLpNorm (fun x => kernelConvolution (dilatedNormalKernel chi beta lambda (r x)) f x) 2 volume ≤
            ENNReal.ofReal (C * lambda ^ (1 / 2 - (m : ℝ) / 4)) * eLpNorm f 2 volume := by
  classical
  obtain ⟨a, hsum, ha, _, has, hap⟩ := exists_finite_patch_decomposition chi hchi hcompact hsupport
  have hbounds := fun j => exists_uniform_coordinate_patch_bound m j (a j) (ha j) (has j) (hap j)
    beta hb hbc hbetaSupport
  choose C hC hbound using hbounds
  have hsumC : 0 < ∑ j, C j := Finset.sum_pos (fun j _ => hC j) Finset.univ_nonempty
  refine ⟨∑ j, C j, hsumC, ?_⟩
  intro lambda hlambda r hr hlocal f hf hfLp
  have hmeas : ∀ j, AEStronglyMeasurable
      (fun x => kernelConvolution (dilatedNormalKernel (a j) beta lambda (r x)) f x) volume :=
    fun j => (measurable_linearizedConvolution_L2 (a j) (ha j).continuous (has j) beta hb hbc lambda f hfLp r hlocal hr).aestronglyMeasurable
  have heq : (fun x => kernelConvolution (dilatedNormalKernel chi beta lambda (r x)) f x) =
      ∑ j, (fun x => kernelConvolution (dilatedNormalKernel (a j) beta lambda (r x)) f x) := by
    funext x
    rw [show chi = (fun u => ∑ j, a j u) from funext hsum]
    simpa using linearizedConvolution_sum a (fun j => (ha j).continuous) has beta hb hbc lambda (r x) (hlocal x) f hfLp x
  rw [heq]
  calc
    _ ≤ ∑ j, eLpNorm (fun x => kernelConvolution (dilatedNormalKernel (a j) beta lambda (r x)) f x) 2 volume :=
      eLpNorm_sum_le (fun j _ => hmeas j) (by norm_num)
    _ ≤ ∑ j, ENNReal.ofReal (C j * lambda ^ (1 / 2 - (m : ℝ) / 4)) * eLpNorm f 2 volume :=
      Finset.sum_le_sum (fun j _ => hbound j lambda hlambda r hr hlocal f hf hfLp)
    _ = _ := by
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg (fun j _ =>
        mul_nonneg (hC j).le (Real.rpow_nonneg (by linarith) _)), ← Finset.sum_mul]

/-- Parameterizing the original radius set does not alter the maximal operator. -/
theorem localKernelMaximal_eq_parameter_iSup {n : ℕ} (chi : Space n → ℂ) (beta : ℝ → ℂ)
    (lambda : ℝ) (f : Space n → ℂ) (x : Space n) :
    localKernelMaximal (normalKernel chi beta lambda) f x =
      ⨆ p : LocalParameters n, ‖kernelConvolution (dilatedNormalKernel chi beta lambda (parameterRadii p)) f x‖ₑ := by
  unfold localKernelMaximal maximalOver
  apply le_antisymm
  · apply iSup_le
    intro r
    apply iSup_le
    intro hr
    obtain ⟨p, hp⟩ := exists_parameter_of_local r hr
    rw [← hp]
    exact le_iSup (fun p : LocalParameters n =>
      ‖kernelConvolution (dilatedNormalKernel chi beta lambda (parameterRadii p)) f x‖ₑ) p
  · apply iSup_le
    intro p
    exact le_iSup_of_le (parameterRadii p) (le_iSup_of_le (parameterRadii_local p) le_rfl)

set_option maxHeartbeats 1000000 in
/-- Proposition 1.3 in successor dimension, on the original ENNReal-valued
local maximal function. The constant depends only on m, chi and beta. -/
theorem proposition_1_3_succ (m : ℕ) (chi : Space (m + 1) → ℂ)
    (hchi : ContDiff ℝ ∞ chi) (hcompact : HasCompactSupport chi)
    (hsupport : tsupport chi ⊆ {u | (1 / 2 : ℝ) ≤ ‖u‖ ∧ ‖u‖ ≤ 2})
    (beta : ℝ → ℂ) (hb : Continuous beta) (hbc : HasCompactSupport beta)
    (hbetaSupport : Function.support beta ⊆ {t | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ lambda : ℝ, 1 ≤ lambda →
      ∀ f : Space (m + 1) → ℂ, Measurable f → MemLp f 2 volume →
        Measurable (localKernelMaximal (normalKernel chi beta lambda) f) ∧
        eLpNorm (localKernelMaximal (normalKernel chi beta lambda) f) 2 volume ≤
          ENNReal.ofReal (C * lambda ^ (1 / 2 - (m : ℝ) / 4)) * eLpNorm f 2 volume := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_annular_linearized_bound m chi hchi hcompact hsupport
    beta hb hbc hbetaSupport
  refine ⟨2 * C, by positivity, ?_⟩
  intro lambda hlambda f hf hfLp
  let A : LocalParameters (m + 1) → Space (m + 1) → ℂ := fun p x =>
    kernelConvolution (dilatedNormalKernel chi beta lambda (parameterRadii p)) f x
  have hs : Function.support chi ⊆ {u | ‖u‖ ≤ 2} := fun u hu => (hsupport (subset_tsupport chi hu)).2
  have hA := continuous_parameter_convolution_L2 chi hchi.continuous hs beta hb hbc lambda f hfLp
  have hselect : ∀ p : Space (m + 1) → LocalParameters (m + 1), Measurable p →
      eLpNorm (fun x => A (p x) x) 2 volume ≤
        ENNReal.ofReal (C * lambda ^ (1 / 2 - (m : ℝ) / 4)) * eLpNorm f 2 volume := by
    intro p hp
    have hm : ∀ j, Measurable (fun x => (parameterRadii (p x)).1 j) := by
      intro j
      change Measurable (fun x => (p x).1 j)
      exact (measurable_pi_apply j).comp (measurable_subtype_coe.comp hp)
    exact hbound lambda hlambda (fun x => parameterRadii (p x)) hm
      (fun x => parameterRadii_local (p x)) f hf hfLp
  have hAm : ∀ p : LocalParameters (m + 1), Measurable (A p) := by
    intro p
    have hmap : Continuous (fun x : Space (m + 1) => (p, x)) := continuous_const.prodMk continuous_id
    exact (hA.comp hmap).measurable
  have hAc : ∀ x : Space (m + 1), Continuous (fun p : LocalParameters (m + 1) => A p x) := by
    intro x
    have hmap : Continuous (fun p : LocalParameters (m + 1) => (p, x)) := continuous_id.prodMk continuous_const
    simpa only [Function.comp_def, A] using hA.comp hmap
  have hh := compact_maximal_L2 A hAm hAc _ hselect
  have heq : localKernelMaximal (normalKernel chi beta lambda) f = fun x => ⨆ p, ‖A p x‖ₑ := by
    funext x
    exact localKernelMaximal_eq_parameter_iSup chi beta lambda f x
  rw [heq]
  refine ⟨hh.1, hh.2.trans_eq ?_⟩
  rw [show 2 * C * lambda ^ (1 / 2 - (m : ℝ) / 4) =
      2 * (C * lambda ^ (1 / 2 - (m : ℝ) / 4)) by ring,
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num [mul_assoc]

/-- Proposition 1.3, with the paper's dimension and frequency exponent. -/
theorem proposition_1_3 (n : ℕ) (hn : 2 ≤ n) (chi : Space n → ℂ)
    (hchi : ContDiff ℝ ∞ chi) (hcompact : HasCompactSupport chi)
    (hsupport : tsupport chi ⊆ {u | (1 / 2 : ℝ) < ‖u‖ ∧ ‖u‖ < 2})
    (beta : ℝ → ℂ) (hbeta : ContDiff ℝ ∞ beta) (hbetaCompact : HasCompactSupport beta)
    (hbetaSupport : tsupport beta ⊆ {t | (1 / 2 : ℝ) ≤ |t| ∧ |t| ≤ 2}) :
    ∃ C : ℝ, 0 < C ∧ ∀ lambda : ℝ, 1 ≤ lambda →
      ∀ f : Space n → ℂ, MemLp f 2 volume →
        Measurable (localKernelMaximal (normalKernel chi beta lambda) f) ∧
        eLpNorm (localKernelMaximal (normalKernel chi beta lambda) f) 2 volume ≤
          ENNReal.ofReal (C * lambda ^ (-((n : ℝ) - 3) / 4)) * eLpNorm f 2 volume := by
  cases n with
  | zero => omega
  | succ m =>
    have he : (1 / 2 - (m : ℝ) / 4) = -(((m + 1 : ℕ) : ℝ) - 3) / 4 := by push_cast; ring
    obtain ⟨C, hC, hbound⟩ := proposition_1_3_succ m chi hchi hcompact
      (fun u hu => ⟨(hsupport hu).1.le, (hsupport hu).2.le⟩)
      beta hbeta.continuous hbetaCompact (fun t ht => hbetaSupport (subset_tsupport beta ht))
    refine ⟨C, hC, ?_⟩
    intro lambda hlambda f hf
    let g := hf.aestronglyMeasurable.mk f
    have hg : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
    have hfg : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
    have hgLp : MemLp g 2 volume := (memLp_congr_ae hfg).mp hf
    have hconv : ∀ (r : Radii (m + 1)) (x : Space (m + 1)),
        kernelConvolution (dilatedKernel (normalKernel chi beta lambda) r) f x =
          kernelConvolution (dilatedKernel (normalKernel chi beta lambda) r) g x := by
      intro r x
      rw [convolution_eq_centered_integral, convolution_eq_centered_integral]
      apply integral_congr_ae
      filter_upwards [hfg] with y hy
      rw [hy]
    have hmax : localKernelMaximal (normalKernel chi beta lambda) f =
        localKernelMaximal (normalKernel chi beta lambda) g := by
      funext x
      simp only [localKernelMaximal, maximalOver, hconv]
    have hh := hbound lambda hlambda g hg hgLp
    rw [← hmax, ← eLpNorm_congr_ae hfg] at hh
    simpa only [he] using hh

end StrongSpherical.LocalEstimate
