import NormalKernelRegularity
import KernelC1Norm
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.InnerProductSpace.Calculus

/-! # Smoothness and uniform C¹ size of the original normal kernel -/
noncomputable section
open MeasureTheory Set FourierTransform
open scoped FourierTransform SchwartzMap ContDiff
namespace StrongSpherical.NormalKernelC1
set_option maxHeartbeats 1000000
variable {n : ℕ}

/-- The compact smooth frequency cutoff, transformed in the Schwartz space. -/
def inverseBeta (beta : ℝ → ℂ) (hb : ContDiff ℝ ∞ beta)
    (hc : HasCompactSupport beta) : 𝓢(ℝ, ℂ) :=
  𝓕⁻ (hc.toSchwartzMap hb)

theorem inverseBeta_coe (beta : ℝ → ℂ) (hb : ContDiff ℝ ∞ beta)
    (hc : HasCompactSupport beta) :
    (inverseBeta beta hb hc : ℝ → ℂ) = 𝓕⁻ beta := by
  exact SchwartzMap.fourierInv_coe (hc.toSchwartzMap hb)

theorem contDiff_inverseFourier (beta : ℝ → ℂ) (hb : ContDiff ℝ ∞ beta)
    (hc : HasCompactSupport beta) : ContDiff ℝ ∞ (𝓕⁻ beta) := by
  rw [← inverseBeta_coe beta hb hc]
  exact (inverseBeta beta hb hc).smooth ⊤

theorem contDiff_phase (lambda : ℝ) :
    ContDiff ℝ ∞ (fun u : Space n => lambda * (‖u‖ ^ 2 - 1)) :=
  contDiff_const.mul ((contDiff_norm_sq ℝ).sub contDiff_const)

theorem fderiv_phase (lambda : ℝ) (u : Space n) :
    fderiv ℝ (fun v : Space n => lambda * (‖v‖ ^ 2 - 1)) u =
      lambda • ((2 : ℝ) • innerSL ℝ u) := by
  have hd : Differentiable ℝ (fun v : Space n => ‖v‖ ^ 2 - 1) :=
    ((contDiff_norm_sq ℝ : ContDiff ℝ ∞ (fun v : Space n => ‖v‖ ^ 2)).differentiable
      (by simp)).sub_const 1
  rw [fderiv_const_mul (hd u), fderiv_sub_const, fderiv_norm_sq_apply]
  simp only [two_smul]

theorem norm_fderiv_phase_le (lambda : ℝ) (hlambda : 0 ≤ lambda)
    (u : Space n) (hu : ‖u‖ ≤ 2) :
    ‖fderiv ℝ (fun v : Space n => lambda * (‖v‖ ^ 2 - 1)) u‖ ≤ 4 * lambda := by
  rw [fderiv_phase, norm_smul, norm_smul, Real.norm_of_nonneg hlambda,
    Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), innerSL_apply_norm]
  nlinarith

theorem contDiff_normalKernel (chi : Space n → ℂ) (hchi : ContDiff ℝ ∞ chi)
    (beta : ℝ → ℂ) (hb : ContDiff ℝ ∞ beta) (hc : HasCompactSupport beta)
    (lambda : ℝ) : ContDiff ℝ ∞ (normalKernel chi beta lambda) :=
  (hchi.mul contDiff_const).mul
    ((contDiff_inverseFourier beta hb hc).comp (contDiff_phase lambda))

theorem support_normalKernel_subset (chi : Space n → ℂ) (beta : ℝ → ℂ) (lambda : ℝ) :
    Function.support (normalKernel chi beta lambda) ⊆ Function.support chi := by
  intro u hu
  by_contra hz
  apply hu
  have hz' : chi u = 0 := not_ne_iff.mp hz
  simp only [normalKernel, hz', zero_mul]

theorem tsupport_normalKernel_subset (chi : Space n → ℂ) (beta : ℝ → ℂ) (lambda : ℝ) :
    tsupport (normalKernel chi beta lambda) ⊆ tsupport chi :=
  closure_mono (support_normalKernel_subset chi beta lambda)

theorem hasCompactSupport_normalKernel (chi : Space n → ℂ) (hchi : HasCompactSupport chi)
    (beta : ℝ → ℂ) (lambda : ℝ) : HasCompactSupport (normalKernel chi beta lambda) :=
  hchi.of_isClosed_subset (isClosed_tsupport _) (tsupport_normalKernel_subset chi beta lambda)

theorem support_normalKernel_box (chi : Space n → ℂ)
    (hs : tsupport chi ⊆ {u | ‖u‖ ≤ 2}) (beta : ℝ → ℂ) (lambda : ℝ) :
    Function.support (normalKernel chi beta lambda) ⊆ MarginalEnergy.coordinateBox n 2 := by
  intro u hu i
  have hu' := hs (subset_tsupport chi (support_normalKernel_subset chi beta lambda hu))
  have hh : |u i| ≤ ‖u‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le u i
  exact abs_le.mp (hh.trans hu')

/-- The derivative estimate follows from the product and chain rules; only the
upper support radius of chi enters the phase derivative. -/
theorem norm_fderiv_normalKernel_le (chi : Space n → ℂ) (hchi : ContDiff ℝ ∞ chi)
    (hs : tsupport chi ⊆ {u | ‖u‖ ≤ 2})
    (beta : ℝ → ℂ) (hb : ContDiff ℝ ∞ beta) (hc : HasCompactSupport beta)
    (U D V W : ℝ) (hU : 0 ≤ U) (hD : 0 ≤ D) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hchi0 : ∀ u, ‖chi u‖ ≤ U) (hchi1 : ∀ u, ‖fderiv ℝ chi u‖ ≤ D)
    (hbeta0 : ∀ t, ‖(𝓕⁻ beta) t‖ ≤ V) (hbeta1 : ∀ t, ‖fderiv ℝ (𝓕⁻ beta) t‖ ≤ W)
    (lambda : ℝ) (hlambda : 1 ≤ lambda) (u : Space n) :
    ‖fderiv ℝ (normalKernel chi beta lambda) u‖ ≤
      (D * V + 4 * U * W) * lambda ^ 2 := by
  have hlambda0 : 0 ≤ lambda := by linarith
  by_cases hu : u ∈ tsupport chi
  · let q : Space n → ℝ := fun v => lambda * (‖v‖ ^ 2 - 1)
    let F : Space n → ℂ := (𝓕⁻ beta) ∘ q
    have hq : Differentiable ℝ q := (contDiff_phase lambda).differentiable (by simp)
    have hphi := (contDiff_inverseFourier beta hb hc).differentiable (by simp)
    have hF : Differentiable ℝ F := hphi.comp hq
    have hFderiv : ‖fderiv ℝ F u‖ ≤ W * (4 * lambda) := by
      rw [show fderiv ℝ F u = (fderiv ℝ (𝓕⁻ beta) (q u)).comp (fderiv ℝ q u) from
        fderiv_comp u (hphi (q u)) (hq u)]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hbeta1 (q u)) (norm_fderiv_phase_le lambda hlambda0 u (hs hu))
          (norm_nonneg _) hW)
    have hA : Differentiable ℝ (fun v => chi v * (lambda : ℂ)) :=
      hchi.differentiable (by simp) |>.mul_const _
    have hAderiv : ‖fderiv ℝ (fun v => chi v * (lambda : ℂ)) u‖ ≤ lambda * D := by
      rw [fderiv_mul_const (hchi.differentiable (by simp) u), norm_smul,
        Complex.norm_real, Real.norm_of_nonneg hlambda0]
      exact mul_le_mul_of_nonneg_left (hchi1 u) hlambda0
    change ‖fderiv ℝ (fun v => (chi v * (lambda : ℂ)) * F v) u‖ ≤ _
    rw [fderiv_fun_mul (hA u) (hF u)]
    calc
      _ ≤ ‖(chi u * (lambda : ℂ)) • fderiv ℝ F u‖ +
          ‖F u • fderiv ℝ (fun v => chi v * (lambda : ℂ)) u‖ := norm_add_le _ _
      _ = (‖chi u‖ * lambda) * ‖fderiv ℝ F u‖ + ‖F u‖ *
          ‖fderiv ℝ (fun v => chi v * (lambda : ℂ)) u‖ := by
        rw [norm_smul, norm_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlambda0]
      _ ≤ (U * lambda) * (W * (4 * lambda)) + V * (lambda * D) := by
        apply add_le_add
        · exact mul_le_mul (mul_le_mul_of_nonneg_right (hchi0 u) hlambda0) hFderiv
            (norm_nonneg _) (mul_nonneg hU hlambda0)
        · exact mul_le_mul (hbeta0 (q u)) hAderiv (norm_nonneg _) hV
      _ ≤ (D * V + 4 * U * W) * lambda ^ 2 := by
        have hll : lambda ≤ lambda ^ 2 := by nlinarith
        have hh := mul_le_mul_of_nonneg_left hll (mul_nonneg hD hV)
        nlinarith
  · rw [fderiv_of_notMem_tsupport ℝ (fun h => hu (tsupport_normalKernel_subset chi beta lambda h)), norm_zero]
    positivity

/-- A single positive constant is chosen before lambda. No Fourier band support
assumption is needed for this C¹ estimate. -/
theorem exists_normalKernel_C1_bound (chi : Space n → ℂ) (hchi : ContDiff ℝ ∞ chi)
    (hchic : HasCompactSupport chi) (hs : tsupport chi ⊆ {u | ‖u‖ ≤ 2})
    (beta : ℝ → ℂ) (hb : ContDiff ℝ ∞ beta) (hbc : HasCompactSupport beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ lambda : ℝ, 1 ≤ lambda → ∀ u : Space n,
      ‖normalKernel chi beta lambda u‖ ≤ C * lambda ^ 2 ∧
      ‖fderiv ℝ (normalKernel chi beta lambda) u‖ ≤ C * lambda ^ 2 := by
  let X : 𝓢(Space n, ℂ) := hchic.toSchwartzMap hchi
  let P := inverseBeta beta hb hbc
  let U := SchwartzMap.seminorm ℝ 0 0 X
  let D := SchwartzMap.seminorm ℝ 0 1 X
  let V := SchwartzMap.seminorm ℝ 0 0 P
  let W := SchwartzMap.seminorm ℝ 0 1 P
  have hU : 0 ≤ U := apply_nonneg _ _
  have hD : 0 ≤ D := apply_nonneg _ _
  have hV : 0 ≤ V := apply_nonneg _ _
  have hW : 0 ≤ W := apply_nonneg _ _
  have hchi0 : ∀ u, ‖chi u‖ ≤ U := fun u => SchwartzMap.norm_le_seminorm ℝ X u
  have hchi1 : ∀ u, ‖fderiv ℝ chi u‖ ≤ D := fun u => by
    have h := SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ X 1 u
    rw [norm_iteratedFDeriv_one, show (X : Space n → ℂ) = chi from rfl] at h
    exact h
  have hbeta0 : ∀ t, ‖(𝓕⁻ beta) t‖ ≤ V := by
    intro t
    rw [← inverseBeta_coe beta hb hbc]
    exact SchwartzMap.norm_le_seminorm ℝ P t
  have hbeta1 : ∀ t, ‖fderiv ℝ (𝓕⁻ beta) t‖ ≤ W := by
    intro t
    rw [← inverseBeta_coe beta hb hbc]
    simpa only [norm_iteratedFDeriv_one] using SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ P 1 t
  let C := U * V + D * V + 4 * U * W + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro lambda hlambda u
  have hlambda0 : 0 ≤ lambda := by linarith
  have hll : lambda ≤ lambda ^ 2 := by nlinarith
  constructor
  · calc
      _ = ‖chi u‖ * lambda * ‖(𝓕⁻ beta) (lambda * (‖u‖ ^ 2 - 1))‖ := by
        simp only [normalKernel, norm_mul, Complex.norm_real, Real.norm_of_nonneg hlambda0]
      _ ≤ U * lambda * V :=
        mul_le_mul (mul_le_mul_of_nonneg_right (hchi0 u) hlambda0) (hbeta0 _)
          (norm_nonneg _) (mul_nonneg hU hlambda0)
      _ ≤ (U * V) * lambda ^ 2 := by
        simpa only [mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_left hll (mul_nonneg hU hV)
      _ ≤ C * lambda ^ 2 := mul_le_mul_of_nonneg_right
        (by dsimp [C]; nlinarith [mul_nonneg hD hV, mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hU) hW])
        (sq_nonneg lambda)
  · exact (norm_fderiv_normalKernel_le chi hchi hs beta hb hbc U D V W hU hD hV hW
      hchi0 hchi1 hbeta0 hbeta1 lambda hlambda u).trans
      (mul_le_mul_of_nonneg_right
        (by dsimp [C]; nlinarith [mul_nonneg hU hV]) (sq_nonneg lambda))

/-- The canonical global C¹ norm obeys the same quadratic growth law. -/
theorem exists_c1Norm_normalKernel_bound (chi : Space n → ℂ) (hchi : ContDiff ℝ ∞ chi)
    (hchic : HasCompactSupport chi) (hs : tsupport chi ⊆ {u | ‖u‖ ≤ 2})
    (beta : ℝ → ℂ) (hb : ContDiff ℝ ∞ beta) (hbc : HasCompactSupport beta) :
    ∃ C : ℝ, 0 < C ∧ ∀ lambda : ℝ, 1 ≤ lambda →
      KernelC1Norm.c1Norm (normalKernel chi beta lambda) ≤ C * lambda ^ 2 := by
  obtain ⟨C, hC, hbound⟩ := exists_normalKernel_C1_bound chi hchi hchic hs beta hb hbc
  refine ⟨2 * C, by positivity, ?_⟩
  intro lambda hlambda
  have h0 : sSup (Set.range (fun u => ‖normalKernel chi beta lambda u‖)) ≤ C * lambda ^ 2 :=
    csSup_le (Set.range_nonempty _) (by rintro _ ⟨u, rfl⟩; exact (hbound lambda hlambda u).1)
  have h1 : sSup (Set.range (fun u => ‖fderiv ℝ (normalKernel chi beta lambda) u‖)) ≤ C * lambda ^ 2 :=
    csSup_le (Set.range_nonempty _) (by rintro _ ⟨u, rfl⟩; exact (hbound lambda hlambda u).2)
  dsimp [KernelC1Norm.c1Norm]
  nlinarith

end StrongSpherical.NormalKernelC1
