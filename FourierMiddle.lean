import FourierCutoff
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Actual L² Fourier multipliers for the frequency decomposition -/
noncomputable section
open MeasureTheory Set FourierTransform
open scoped FourierTransform SchwartzMap BigOperators ComplexConjugate BoundedContinuousFunction

namespace StrongSpherical.FourierMiddle
open FourierCutoff FrequencyDecomposition
variable {d : ℕ}

abbrev L2 (d : ℕ) := MeasureTheory.Lp (α := Space d) ℂ 2 volume
abbrev Symbol (d : ℕ) := Space d →ᵇ ℂ

theorem symbol_product_memLp (b : Symbol d) (f : L2 d) :
    MemLp (fun x => b x * f x) 2 volume := by
  apply (Lp.memLp f).of_le_mul (c := ‖b‖)
    (b.continuous.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  filter_upwards with x
  change ‖b x * f x‖ ≤ ‖b‖ * ‖f x‖
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (b.norm_coe_le_norm x) (norm_nonneg _)

/-- Pointwise multiplication by a bounded continuous symbol on actual L² classes. -/
def symbolProduct (b : Symbol d) (f : L2 d) : L2 d :=
  (symbol_product_memLp b f).toLp (fun x => b x * f x)

theorem coe_symbolProduct (b : Symbol d) (f : L2 d) :
    (symbolProduct b f : Space d → ℂ) =ᵐ[volume] fun x => b x * f x :=
  MemLp.coeFn_toLp _

theorem symbolProduct_add (b : Symbol d) (f g : L2 d) :
    symbolProduct b (f + g) = symbolProduct b f + symbolProduct b g := by
  apply Lp.ext
  filter_upwards [coe_symbolProduct b (f + g), Lp.coeFn_add f g,
    Lp.coeFn_add (symbolProduct b f) (symbolProduct b g), coe_symbolProduct b f,
    coe_symbolProduct b g] with x h1 h2 h3 h4 h5
  simp only [h1, h2, h3, h4, h5, Pi.add_apply]
  ring

theorem symbolProduct_smul (b : Symbol d) (c : ℂ) (f : L2 d) :
    symbolProduct b (c • f) = c • symbolProduct b f := by
  apply Lp.ext
  filter_upwards [coe_symbolProduct b (c • f), Lp.coeFn_smul c f,
    Lp.coeFn_smul c (symbolProduct b f), coe_symbolProduct b f] with x h1 h2 h3 h4
  simp only [h1, h2, h3, h4, Pi.smul_apply, smul_eq_mul]
  ring

theorem norm_symbolProduct_le (b : Symbol d) (f : L2 d) :
    ‖symbolProduct b f‖ ≤ ‖b‖ * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coe_symbolProduct b f] with x hx
  rw [hx, norm_mul]
  exact mul_le_mul_of_nonneg_right (b.norm_coe_le_norm x) (norm_nonneg _)

def symbolProductCLM (b : Symbol d) : L2 d →L[ℂ] L2 d :=
  LinearMap.mkContinuous
    { toFun := symbolProduct b
      map_add' := symbolProduct_add b
      map_smul' := symbolProduct_smul b }
    ‖b‖ (norm_symbolProduct_le b)

/-- The genuine Fourier multiplier `F⁻¹ (b · Ff)`, using the L² Plancherel isometry. -/
def multiplier (b : Symbol d) : L2 d →L[ℂ] L2 d :=
  (Lp.fourierTransformₗᵢ (Space d) ℂ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((symbolProductCLM b).comp
      (Lp.fourierTransformₗᵢ (Space d) ℂ).toContinuousLinearEquiv.toContinuousLinearMap)

theorem multiplier_apply (b : Symbol d) (f : L2 d) :
    multiplier b f = 𝓕⁻ (symbolProduct b (𝓕 f)) := rfl

@[simp] theorem fourier_multiplier (b : Symbol d) (f : L2 d) :
    𝓕 (multiplier b f) = symbolProduct b (𝓕 f) := by
  rw [multiplier_apply, fourier_fourierInv_eq]

theorem coe_fourier_multiplier (b : Symbol d) (f : L2 d) :
    ((𝓕 (multiplier b f) : L2 d) : Space d → ℂ) =ᵐ[volume]
      fun x => b x * (𝓕 f : L2 d) x := by
  rw [fourier_multiplier]
  exact coe_symbolProduct b (𝓕 f)

theorem norm_multiplier_le (b : Symbol d) (f : L2 d) :
    ‖multiplier b f‖ ≤ ‖b‖ * ‖f‖ := by
  rw [← Lp.norm_fourier_eq (multiplier b f), fourier_multiplier]
  simpa only [Lp.norm_fourier_eq] using norm_symbolProduct_le b (𝓕 f)

theorem multiplier_add_symbol (a b : Symbol d) (f : L2 d) :
    multiplier (a + b) f = multiplier a f + multiplier b f := by
  apply (Lp.fourierTransformₗᵢ (Space d) ℂ).injective
  change 𝓕 (multiplier (a + b) f) = 𝓕 (multiplier a f + multiplier b f)
  rw [FourierAdd.fourier_add, fourier_multiplier, fourier_multiplier, fourier_multiplier]
  apply Lp.ext
  filter_upwards [coe_symbolProduct (a + b) (𝓕 f), coe_symbolProduct a (𝓕 f),
    coe_symbolProduct b (𝓕 f), Lp.coeFn_add (symbolProduct a (𝓕 f))
      (symbolProduct b (𝓕 f))] with x h1 h2 h3 h4
  simp only [h1, h2, h3, h4, Pi.add_apply, BoundedContinuousFunction.add_apply]
  ring

theorem multiplier_smul_symbol (c : ℂ) (b : Symbol d) (f : L2 d) :
    multiplier (c • b) f = c • multiplier b f := by
  apply (Lp.fourierTransformₗᵢ (Space d) ℂ).injective
  change 𝓕 (multiplier (c • b) f) = 𝓕 (c • multiplier b f)
  rw [fourier_smul, fourier_multiplier, fourier_multiplier]
  apply Lp.ext
  filter_upwards [coe_symbolProduct (c • b) (𝓕 f), coe_symbolProduct b (𝓕 f),
    Lp.coeFn_smul c (symbolProduct b (𝓕 f))] with x h1 h2 h3
  simp only [h1, h2, h3, Pi.smul_apply, smul_eq_mul, BoundedContinuousFunction.smul_apply]
  ring

@[simp] theorem multiplier_one (f : L2 d) : multiplier (1 : Symbol d) f = f := by
  apply (Lp.fourierTransformₗᵢ (Space d) ℂ).injective
  change 𝓕 (multiplier 1 f) = 𝓕 f
  rw [fourier_multiplier]
  apply Lp.ext
  filter_upwards [coe_symbolProduct (1 : Symbol d) (𝓕 f)] with x hx
  simpa using hx

@[simp] theorem multiplier_zero (f : L2 d) : multiplier (0 : Symbol d) f = 0 := by
  apply (Lp.fourierTransformₗᵢ (Space d) ℂ).injective
  change 𝓕 (multiplier 0 f) = 𝓕 (0 : L2 d)
  rw [fourier_multiplier, FourierTransform.fourier_zero]
  apply Lp.ext
  filter_upwards [coe_symbolProduct (0 : Symbol d) (𝓕 f), Lp.coeFn_zero (E := ℂ) (p := 2)
    (μ := (volume : Measure (Space d)))] with x hx hz
  simpa only [BoundedContinuousFunction.coe_zero, Pi.zero_apply, zero_mul, hz] using hx

theorem multiplier_sum {ι : Type*} (S : Finset ι) (b : ι → Symbol d) (f : L2 d) :
    multiplier (∑ i ∈ S, b i) f = ∑ i ∈ S, multiplier (b i) f := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih => simp only [Finset.sum_insert hi, multiplier_add_symbol, ih]

theorem multiplier_mul (a b : Symbol d) (f : L2 d) :
    multiplier (a * b) f = multiplier a (multiplier b f) := by
  apply (Lp.fourierTransformₗᵢ (Space d) ℂ).injective
  change 𝓕 (multiplier (a * b) f) = 𝓕 (multiplier a (multiplier b f))
  simp only [fourier_multiplier]
  apply Lp.ext
  filter_upwards [coe_symbolProduct (a * b) (𝓕 f),
    coe_symbolProduct a (symbolProduct b (𝓕 f)), coe_symbolProduct b (𝓕 f)] with x h1 h2 h3
  simp only [h1, h2, h3, BoundedContinuousFunction.mul_apply]
  ring

theorem multipliers_commute (a b : Symbol d) (f : L2 d) :
    multiplier a (multiplier b f) = multiplier b (multiplier a f) := by
  rw [← multiplier_mul, ← multiplier_mul, mul_comm]

def lowSymbol (M : ℕ) (k : Fin d → ℤ) (i : Fin d) : Symbol d :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (lowCoordinate theta M (k i) (x i) : ℂ))
    (by
      have ht : Continuous theta := theta_contDiff.continuous
      unfold lowCoordinate
      fun_prop)
    1 (by
      intro x
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
        (lowCoordinate_nonneg theta_control M (k i) (x i))]
      exact lowCoordinate_le_one theta_control M (k i) (x i))

def highSymbol (M : ℕ) (k : Fin d → ℤ) (i : Fin d) : Symbol d :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => (highCoordinate theta M (k i) (x i) : ℂ))
    (by
      have ht : Continuous theta := theta_contDiff.continuous
      unfold highCoordinate
      fun_prop)
    1 (by
      intro x
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg
        (highCoordinate_nonneg theta_control M (k i) (x i))]
      exact highCoordinate_le_one theta_control M (k i) (x i))

def middleSymbol (M : ℕ) (k : Fin d → ℤ) : Symbol d :=
  ∏ i, (highSymbol M k i - lowSymbol M k i)

def lowSubsetSymbol (M : ℕ) (k : Fin d → ℤ) (J : Finset (Fin d)) : Symbol d :=
  ∏ i ∈ J, lowSymbol M k i

def errorSymbol (M : ℕ) (k : Fin d → ℤ) : Symbol d :=
  (1 - ∏ i, highSymbol M k i) * ∏ i, (1 - lowSymbol M k i)

@[simp] theorem lowSymbol_apply (M : ℕ) (k : Fin d → ℤ) (i : Fin d) (x : Space d) :
    lowSymbol M k i x = (lowCoordinate theta M (k i) (x i) : ℂ) := rfl

@[simp] theorem highSymbol_apply (M : ℕ) (k : Fin d → ℤ) (i : Fin d) (x : Space d) :
    highSymbol M k i x = (highCoordinate theta M (k i) (x i) : ℂ) := rfl

@[simp] theorem middleSymbol_apply (M : ℕ) (k : Fin d → ℤ) (x : Space d) :
    middleSymbol M k x = (middle theta M k x : ℂ) := by
  simp [middleSymbol, middle]

@[simp] theorem lowSubsetSymbol_apply (M : ℕ) (k : Fin d → ℤ)
    (J : Finset (Fin d)) (x : Space d) :
    lowSubsetSymbol M k J x = (lowSubset theta M k J x : ℂ) := by
  simp [lowSubsetSymbol, lowSubset]

@[simp] theorem errorSymbol_apply (M : ℕ) (k : Fin d → ℤ) (x : Space d) :
    errorSymbol M k x = (error theta M k x : ℂ) := by
  simp [errorSymbol, error]

def middleOperator (M : ℕ) (k : Fin d → ℤ) : L2 d →L[ℂ] L2 d := multiplier (middleSymbol M k)
def lowSubsetOperator (M : ℕ) (k : Fin d → ℤ) (J : Finset (Fin d)) :
    L2 d →L[ℂ] L2 d := multiplier (lowSubsetSymbol M k J)
def errorOperator (M : ℕ) (k : Fin d → ℤ) : L2 d →L[ℂ] L2 d := multiplier (errorSymbol M k)

/-- Equation (5.13) for genuine operators on all of L². -/
theorem operator_decomposition (M : ℕ) (hM : 3 ≤ M) (k : Fin d → ℤ) (f : L2 d) :
    f = middleOperator M k f +
      (∑ J ∈ (Finset.univ.powerset.erase ∅),
        ((-1 : ℂ) ^ (J.card + 1)) • lowSubsetOperator M k J f) + errorOperator M k f := by
  have hs : (1 : Symbol d) = middleSymbol M k +
      (∑ J ∈ (Finset.univ.powerset.erase ∅),
        ((-1 : ℂ) ^ (J.card + 1)) • lowSubsetSymbol M k J) + errorSymbol M k := by
    ext x
    have h := congrArg (fun r : ℝ => (r : ℂ)) (decomposition theta_control M hM k x)
    simpa [lowCorrection] using h
  have h := congrArg (fun b : Symbol d => multiplier b f) hs
  simpa only [multiplier_one, multiplier_add_symbol, multiplier_sum,
    multiplier_smul_symbol, middleOperator, lowSubsetOperator, errorOperator] using h

theorem norm_sq_eq_integral (f : L2 d) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ), MeasureTheory.L2.inner_def,
    ← integral_re (MeasureTheory.L2.integrable_inner (𝕜 := ℂ) f f)]
  congr 1
  funext x
  rw [inner_self_eq_norm_sq_to_K]
  exact RCLike.re_ofReal_pow _ _

theorem integrable_sq_norm (f : L2 d) : Integrable (fun x => ‖f x‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)

theorem middle_energy_ae (M : ℕ) (k : Fin d → ℤ) (f : L2 d) :
    (fun x => ‖symbolProduct (middleSymbol M k) (𝓕 f : L2 d) x‖ ^ 2) =ᵐ[volume]
      fun x => |middle theta M k x| ^ 2 * ‖(𝓕 f : L2 d) x‖ ^ 2 := by
  filter_upwards [coe_symbolProduct (middleSymbol M k) (𝓕 f)] with x hx
  rw [hx, norm_mul, mul_pow, middleSymbol_apply, Complex.norm_real, Real.norm_eq_abs]

theorem integrable_middle_energy (M : ℕ) (k : Fin d → ℤ) (f : L2 d) :
    Integrable (fun x => |middle theta M k x| ^ 2 * ‖(𝓕 f : L2 d) x‖ ^ 2) :=
  (integrable_sq_norm (symbolProduct (middleSymbol M k) (𝓕 f))).congr
    (middle_energy_ae M k f)

/-- Plancherel identifies each actual middle operator's energy with its actual symbol. -/
theorem norm_middle_sq (M : ℕ) (k : Fin d → ℤ) (f : L2 d) :
    ‖middleOperator M k f‖ ^ 2 =
      ∫ x, |middle theta M k x| ^ 2 * ‖(𝓕 f : L2 d) x‖ ^ 2 := by
  rw [← Lp.norm_fourier_eq (middleOperator M k f)]
  change ‖𝓕 (multiplier (middleSymbol M k) f)‖ ^ 2 = _
  rw [fourier_multiplier, norm_sq_eq_integral]
  exact integral_congr_ae (middle_energy_ae M k f)

theorem finite_symbol_overlap (M : ℕ) (hM : 3 ≤ M) (x : Space d)
    (S : Finset (Fin d → ℤ)) :
    (∑ k ∈ S, |middle theta M k x| ^ 2) ≤ ((2 * M + 2) ^ d : ℕ) := by
  classical
  have hfin : Function.HasFiniteSupport (fun k : Fin d → ℤ => |middle theta M k x| ^ 2) := by
    apply (activeBox theta_control M hM x).finite_toSet.subset
    intro k hk
    apply (mem_activeBox_iff theta_control M hM x k).mpr
    intro hzero
    exact hk (by simp [hzero])
  exact (Summable.sum_le_tsum S (fun _ _ => sq_nonneg _)
    (summable_of_hasFiniteSupport hfin)).trans (tsum_middle_sq_le theta_control M hM x)

/-- The middle-frequency energy estimate for every finite family of dyadic rectangles. -/
theorem finite_middle_energy (M : ℕ) (hM : 3 ≤ M) (f : L2 d)
    (S : Finset (Fin d → ℤ)) :
    (∑ k ∈ S, ‖middleOperator M k f‖ ^ 2) ≤ ((2 * M + 2) ^ d : ℕ) * ‖f‖ ^ 2 := by
  calc
    _ = ∑ k ∈ S, ∫ x, |middle theta M k x| ^ 2 * ‖(𝓕 f : L2 d) x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro k hk
      exact norm_middle_sq M k f
    _ = ∫ x, ∑ k ∈ S, |middle theta M k x| ^ 2 * ‖(𝓕 f : L2 d) x‖ ^ 2 :=
      (integral_finsetSum S (f := fun (k : Fin d → ℤ) (x : Space d) =>
        |middle theta M k x| ^ 2 * ‖(𝓕 f : L2 d) x‖ ^ 2)
        (fun k _ => integrable_middle_energy M k f)).symm
    _ ≤ ∫ x, (((2 * M + 2) ^ d : ℕ) : ℝ) * ‖(𝓕 f : L2 d) x‖ ^ 2 := by
      apply integral_mono_ae
      · exact integrable_finsetSum S (fun k _ => integrable_middle_energy M k f)
      · exact (integrable_sq_norm (𝓕 f)).const_mul _
      · filter_upwards with x
        rw [← Finset.sum_mul]
        exact mul_le_mul_of_nonneg_right (finite_symbol_overlap M hM x S) (sq_nonneg _)
    _ = ((2 * M + 2) ^ d : ℕ) * ‖f‖ ^ 2 := by
      rw [integral_const_mul, ← norm_sq_eq_integral, Lp.norm_fourier_eq]

/-- Genuine Plancherel middle overlap, with no finiteness restriction on the input class. -/
theorem middle_plancherel (M : ℕ) (hM : 3 ≤ M) (f : L2 d) :
    (∑' k : Fin d → ℤ, ‖middleOperator M k f‖ ^ 2) ≤
      ((2 * M + 2) ^ d : ℕ) * ‖f‖ ^ 2 :=
  Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) (finite_middle_energy M hM f)

theorem summable_middle_energy (M : ℕ) (hM : 3 ≤ M) (f : L2 d) :
    Summable (fun k : Fin d → ℤ => ‖middleOperator M k f‖ ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (finite_middle_energy M hM f)

end StrongSpherical.FourierMiddle
