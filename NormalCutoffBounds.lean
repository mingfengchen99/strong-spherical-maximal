import NormalRadialDensity

/-! # Positivity and fixed size bounds for the actual normal cutoff -/
noncomputable section
open MeasureTheory Set
namespace StrongSpherical.NormalCutoffBounds

theorem chi_re_nonneg (n : ℕ) (u : Space n) : 0 ≤ (NormalCutoffs.chi n u).re := by
  change 0 ≤ NormalCutoffs.outer (‖u‖ ^ 2) * (1 - NormalCutoffs.inner (‖u‖ ^ 2))
  exact mul_nonneg NormalCutoffs.outer.nonneg (sub_nonneg.mpr NormalCutoffs.inner.le_one)

theorem chi_re_le_one (n : ℕ) (u : Space n) : (NormalCutoffs.chi n u).re ≤ 1 := by
  change NormalCutoffs.outer (‖u‖ ^ 2) * (1 - NormalCutoffs.inner (‖u‖ ^ 2)) ≤ 1
  have houter := NormalCutoffs.outer.le_one (x := ‖u‖ ^ 2)
  have hinner := NormalCutoffs.inner.nonneg (x := ‖u‖ ^ 2)
  have hinner' := NormalCutoffs.inner.le_one (x := ‖u‖ ^ 2)
  have houter' := NormalCutoffs.outer.nonneg (x := ‖u‖ ^ 2)
  nlinarith

theorem norm_chi_eq_re (n : ℕ) (u : Space n) :
    ‖NormalCutoffs.chi n u‖ = (NormalCutoffs.chi n u).re := by
  have hchi : NormalCutoffs.chi n u = ((NormalCutoffs.chi n u).re : ℂ) := by
    apply Complex.ext
    · rfl
    · exact NormalCutoffs.chi_im n u
  calc
    _ = ‖((NormalCutoffs.chi n u).re : ℂ)‖ := congrArg norm hchi
    _ = _ := by rw [Complex.norm_real, Real.norm_of_nonneg (chi_re_nonneg n u)]

theorem norm_chi_le_one (n : ℕ) (u : Space n) : ‖NormalCutoffs.chi n u‖ ≤ 1 := by
  rw [norm_chi_eq_re]
  exact chi_re_le_one n u

theorem chi_eq_coe_norm (n : ℕ) (u : Space n) :
    NormalCutoffs.chi n u = (‖NormalCutoffs.chi n u‖ : ℂ) := by
  apply Complex.ext
  · simpa only [Complex.ofReal_re] using (norm_chi_eq_re n u).symm
  · simp only [NormalCutoffs.chi_im, Complex.ofReal_im]

/-- The coarea density for the fixed spatial cutoff has a positive bound
chosen independently of the normal frequency and the dyadic index. -/
theorem density_one_bound (n : ℕ) :
    ∃ B : ℝ, 0 < B ∧ ∀ t : ℝ,
      ‖NormalRadialDensity.density n (fun _ => 1) t‖ ≤ B := by
  obtain ⟨B, hB⟩ := (NormalRadialDensity.hasCompactSupport_density n (fun _ => 1)).exists_bound_of_continuous
    (NormalRadialDensity.continuous_density n _ continuous_const)
  have h0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨B + 1, by linarith, fun t => (hB t).trans ?_⟩
  linarith

end StrongSpherical.NormalCutoffBounds
