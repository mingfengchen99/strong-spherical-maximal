import Definitions
import Mathlib.MeasureTheory.Integral.Prod

/-! # Polar integration with the actual Euclidean surface measure

The angular input remains arbitrary. The formula is obtained from the Haar
measure preserving sphere/radius homeomorphism and genuine product Fubini.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace StrongSpherical.SpherePolar
set_option maxHeartbeats 1000000

/-- The radius measure used by the sphere/radius homeomorphism has exactly
the density r^k on the positive real ray. -/
theorem integral_volumeIoiPow (k : ℕ) (A : ℝ → ℂ) :
    (∫ r : Ioi (0 : ℝ), A r ∂Measure.volumeIoiPow k) =
      ∫ r in Ioi (0 : ℝ), ((r ^ k : ℝ) : ℂ) * A r := by
  simp only [Measure.volumeIoiPow, ENNReal.ofReal]
  rw [integral_withDensity_eq_integral_smul]
  · rw [integral_subtype_comap measurableSet_Ioi (fun r : ℝ => Real.toNNReal (r ^ k) • A r)]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    change Real.toNNReal (r ^ k) • A r = ((r ^ k : ℝ) : ℂ) * A r
    rw [NNReal.smul_def, Real.coe_toNNReal _ (pow_nonneg hr.le k)]
    exact Complex.real_smul
  · exact (measurable_subtype_coe.pow_const k).real_toNNReal

/-- Integrability of the full polar pullback, including arbitrary dependence
on the sphere coordinate. -/
theorem integrable_polar_pullback (n : ℕ) (_hn : 1 ≤ n)
    (G : Space n → ℂ) (hG : Integrable G) :
    Integrable (fun p : UnitSphere n × Ioi (0 : ℝ) => G (p.2.1 • (p.1 : Space n)))
      ((surfaceMeasure n).prod (Measure.volumeIoiPow (n - 1))) := by
  letI : NeZero n := ⟨by omega⟩
  let e := homeomorphUnitSphereProd (Space n)
  let F : UnitSphere n × Ioi (0 : ℝ) → ℂ := fun p => G (e.symm p).1
  have hdim : Module.finrank ℝ (Space n) = n := finrank_euclideanSpace_fin
  have hMP : MeasurePreserving e (volume.comap ((↑) : ({0}ᶜ : Set (Space n)) → Space n))
      ((surfaceMeasure n).prod (Measure.volumeIoiPow (n - 1))) := by
    simpa only [surfaceMeasure, hdim] using
      (volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd
  have hsub : Integrable (G ∘ ((↑) : ({0}ᶜ : Set (Space n)) → Space n))
      (volume.comap ((↑) : ({0}ᶜ : Set (Space n)) → Space n)) :=
    (integrableOn_iff_comap_subtypeVal (measurableSet_singleton (0 : Space n)).compl).mp hG.restrict
  have hFcomp : F ∘ e = G ∘ ((↑) : ({0}ᶜ : Set (Space n)) → Space n) := by
    funext u
    simp only [Function.comp_apply, F, Homeomorph.symm_apply_apply]
  have hFi : Integrable F ((surfaceMeasure n).prod (Measure.volumeIoiPow (n - 1))) :=
    (hMP.integrable_comp_emb e.measurableEmbedding).mp (hFcomp.symm ▸ hsub)
  simpa only [F, e, homeomorphUnitSphereProd_symm_apply_coe] using hFi

/-- Polar integration for any integrable complex function, without a radiality
assumption. The sphere measure is the original unnormalized surface measure. -/
theorem integral_eq_polar_of_integrable (n : ℕ) (hn : 1 ≤ n)
    (G : Space n → ℂ) (hG : Integrable G) :
    (∫ u, G u) = ∫ r in Ioi (0 : ℝ), ((r ^ (n - 1) : ℝ) : ℂ) *
      (∫ omega : UnitSphere n, G (r • (omega : Space n)) ∂surfaceMeasure n) := by
  letI : NeZero n := ⟨by omega⟩
  let e := homeomorphUnitSphereProd (Space n)
  let F : UnitSphere n × Ioi (0 : ℝ) → ℂ := fun p => G (e.symm p).1
  have hdim : Module.finrank ℝ (Space n) = n := finrank_euclideanSpace_fin
  have hMP : MeasurePreserving e (volume.comap ((↑) : ({0}ᶜ : Set (Space n)) → Space n))
      ((surfaceMeasure n).prod (Measure.volumeIoiPow (n - 1))) := by
    simpa only [surfaceMeasure, hdim] using
      (volume : Measure (Space n)).measurePreserving_homeomorphUnitSphereProd
  calc
    (∫ u, G u) = ∫ u : ({0}ᶜ : Set (Space n)), G u.1 ∂volume.comap Subtype.val := by
      rw [integral_subtype_comap (measurableSet_singleton (0 : Space n)).compl,
        restrict_compl_singleton]
    _ = ∫ p, F p ∂(surfaceMeasure n).prod (Measure.volumeIoiPow (n - 1)) := by
      simpa only [F, Homeomorph.symm_apply_apply] using
        hMP.integral_comp e.measurableEmbedding F
    _ = ∫ r : Ioi (0 : ℝ), ∫ omega : UnitSphere n,
        G (r.1 • (omega : Space n)) ∂surfaceMeasure n ∂Measure.volumeIoiPow (n - 1) := by
      have hFi := integrable_polar_pullback n hn G hG
      simpa only [F, e, homeomorphUnitSphereProd_symm_apply_coe] using
        integral_prod_symm _ hFi
    _ = _ := integral_volumeIoiPow (n - 1)
      (fun r => ∫ omega : UnitSphere n, G (r • (omega : Space n)) ∂surfaceMeasure n)

/-- The usual polar formula for continuous compactly supported functions. -/
theorem integral_eq_polar (n : ℕ) (hn : 1 ≤ n) (G : Space n → ℂ)
    (hG : Continuous G) (hc : HasCompactSupport G) :
    (∫ u, G u) = ∫ r in Ioi (0 : ℝ), ((r ^ (n - 1) : ℝ) : ℂ) *
      (∫ omega : UnitSphere n, G (r • (omega : Space n)) ∂surfaceMeasure n) :=
  integral_eq_polar_of_integrable n hn G (hG.integrable_of_hasCompactSupport hc)

end StrongSpherical.SpherePolar
