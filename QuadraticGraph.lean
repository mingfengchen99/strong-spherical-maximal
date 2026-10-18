import ProductOscillation
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Quadratic graph kernels

Definitions and analytic tools for Lemma 3.2 of arXiv:2609.32421v2.
The output is `Space m`; the input is `Space (m + 1)`, whose last coordinate
is the variable `s` in the paper. Output-dependent coefficients are never
differentiated.

This module proves the kernel preliminaries, normal-coordinate integration
by parts, (3.20), and the spatial Schur-profile integrals (3.22). It does not
yet assert the full pointwise Gram-kernel estimate or the L² estimate of Lemma 3.2.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace StrongSpherical.QuadraticGraph

variable {m : ℕ}

/-- The Fourier character used throughout the paper. -/
def oscillation (t : ℝ) : ℂ := Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

@[simp] theorem norm_oscillation (t : ℝ) : ‖oscillation t‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

@[simp] theorem oscillation_zero : oscillation 0 = 1 := by simp [oscillation]

theorem oscillation_add (s t : ℝ) :
    oscillation (s + t) = oscillation s * oscillation t := by
  unfold oscillation
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] theorem conj_oscillation (t : ℝ) : conj (oscillation t) = oscillation (-t) := by
  unfold oscillation
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem continuous_oscillation : Continuous oscillation := by
  unfold oscillation
  fun_prop

theorem hasDerivAt_oscillation_mul (eta t : ℝ) :
    HasDerivAt (fun s => oscillation (eta * s))
      (oscillation (eta * t) * (((2 * Real.pi * eta : ℝ) : ℂ) * Complex.I)) t := by
  unfold oscillation
  have h := (((((hasDerivAt_id t).const_mul eta).const_mul (2 * Real.pi)).ofReal_comp).mul_const Complex.I).cexp
  simpa only [id_eq, mul_one, mul_assoc] using h

/-- The first `m` coordinates of an input point. -/
def spatialInput (v : Space (m + 1)) : Space m :=
  WithLp.toLp 2 (fun i => v i.castSucc)

@[simp] theorem spatialInput_apply (v : Space (m + 1)) (i : Fin m) :
    spatialInput v i = v i.castSucc := rfl

/-- The last input coordinate. -/
def normalInput (v : Space (m + 1)) : ℝ := v (Fin.last m)

/-- Measurable quadratic coefficients; only the input variable will be differentiated. -/
structure GraphCoefficients (m : ℕ) where
  constant : Space m → ℝ
  quadratic : Space m → Fin m → ℝ
  measurable_constant : Measurable constant
  measurable_quadratic : ∀ i, Measurable (fun x => quadratic x i)

/-- The graph `Φₓ(u)` in (3.9). -/
def graph (b : GraphCoefficients m) (x u : Space m) : ℝ :=
  b.constant x - ∑ i, b.quadratic x i * (u i - x i) ^ 2

/-- The defining function `s - Φₓ(u)`. -/
def graphGap (b : GraphCoefficients m) (x : Space m) (v : Space (m + 1)) : ℝ :=
  normalInput v - graph b x (spatialInput v)

theorem phase_difference (b : GraphCoefficients m) (x z : Space m)
    (v : Space (m + 1)) (tau sigma : ℝ) :
    tau * graphGap b x v - sigma * graphGap b z v =
      (tau - sigma) * normalInput v + sigma * b.constant z - tau * b.constant x +
        ProductOscillation.productPhase tau sigma (b.quadratic x) (b.quadratic z)
          x z (spatialInput v) := by
  unfold graphGap graph ProductOscillation.productPhase Quadratic1D.quadraticPhase
  simp only [Finset.sum_sub_distrib]
  rw [mul_sub, mul_sub, mul_sub, mul_sub]
  simp only [Finset.mul_sum]
  ring_nf

theorem continuous_graphGap (b : GraphCoefficients m) (x : Space m) :
    Continuous (graphGap b x) := by
  unfold graphGap graph normalInput spatialInput
  fun_prop

/-- The frequency integral in (3.12). -/
def frequencyKernel (b : GraphCoefficients m) (q : Space m → ℝ → ℂ)
    (x : Space m) (v : Space (m + 1)) : ℂ :=
  ∫ tau, q x tau * oscillation (tau * graphGap b x v)

/-- The integral kernel of the original operator. -/
def inputKernel (b : GraphCoefficients m) (a : Space m → Space (m + 1) → ℂ)
    (q : Space m → ℝ → ℂ) (x : Space m) (v : Space (m + 1)) : ℂ :=
  a x v * frequencyKernel b q x v

/-- The operator in (3.12), defined before any boundedness assertion. -/
def graphOperator (b : GraphCoefficients m) (a : Space m → Space (m + 1) → ℂ)
    (q : Space m → ℝ → ℂ) (f : Space (m + 1) → ℂ) (x : Space m) : ℂ :=
  ∫ v, inputKernel b a q x v * f v

/-- The actual Gram kernel of the input kernel. -/
def gramKernel (b : GraphCoefficients m) (a : Space m → Space (m + 1) → ℂ)
    (q : Space m → ℝ → ℂ) (x z : Space m) : ℂ :=
  ∫ v, inputKernel b a q x v * conj (inputKernel b a q z v)

/-- The pairwise amplitude in the oscillatory integral defining the Gram kernel. -/
def pairAmplitude (a : Space m → Space (m + 1) → ℂ) (x z : Space m)
    (v : Space (m + 1)) : ℂ := a x v * conj (a z v)

/-- Input support in (3.10). -/
def inputSupport (R : ℝ) (x : Space m) : Set (Space (m + 1)) :=
  {v | (∀ i, |v i.castSucc - x i| ≤ R) ∧ |normalInput v| ≤ R}

theorem pairAmplitude_eq_zero_of_separated
    (R : ℝ) (a : Space m → Space (m + 1) → ℂ)
    (hsupport : ∀ x, Function.support (a x) ⊆ inputSupport R x)
    (x z : Space m) (i : Fin m) (hi : 2 * R < |x i - z i|) (v : Space (m + 1)) :
    pairAmplitude a x z v = 0 := by
  by_cases hx : a x v = 0
  · simp [pairAmplitude, hx]
  by_cases hz : a z v = 0
  · simp [pairAmplitude, hz]
  have hxi := (hsupport x hx).1 i
  have hzi := (hsupport z hz).1 i
  have htri := abs_sub_le (x i) (v i.castSucc) (z i)
  rw [abs_sub_comm (x i) (v i.castSucc)] at htri
  exfalso
  linarith

theorem gramKernel_eq_zero_of_separated
    (R : ℝ) (b : GraphCoefficients m) (a : Space m → Space (m + 1) → ℂ)
    (q : Space m → ℝ → ℂ)
    (hsupport : ∀ x, Function.support (a x) ⊆ inputSupport R x)
    (x z : Space m) (i : Fin m) (hi : 2 * R < |x i - z i|) :
    gramKernel b a q x z = 0 := by
  unfold gramKernel
  apply integral_eq_zero_of_ae
  apply Filter.Eventually.of_forall
  intro v
  have hp := pairAmplitude_eq_zero_of_separated R a hsupport x z i hi v
  simp only [pairAmplitude, mul_eq_zero, map_eq_zero] at hp
  rcases hp with hx | hz
  · simp [inputKernel, hx]
  · simp [inputKernel, hz]

/-- The integrable profile of the frequency difference. -/
def frequencyDecay (eta : ℝ) : ℝ := (1 + |eta|) ^ (-(2 : ℝ))

theorem integrable_frequencyDecay : Integrable frequencyDecay := by
  change Integrable (fun eta : ℝ => (1 + |eta|) ^ (-(2 : ℝ)))
  simpa only [Real.norm_eq_abs] using
    (integrable_one_add_norm (E := ℝ) (μ := volume) (r := 2) (by norm_num))

theorem frequencyDecay_nonneg (eta : ℝ) : 0 ≤ frequencyDecay eta := by
  unfold frequencyDecay
  positivity

theorem continuous_frequencyDecay : Continuous frequencyDecay := by
  change Continuous (fun eta : ℝ => (1 + |eta|) ^ (-(2 : ℝ)))
  exact (continuous_abs.const_add 1).rpow_const fun _ => Or.inl (by positivity)

/-- A fixed finite constant, independent of all frequencies. -/
def frequencyMass : ℝ := ∫ eta, frequencyDecay eta

theorem frequencyMass_nonneg : 0 ≤ frequencyMass :=
  integral_nonneg frequencyDecay_nonneg

theorem frequencyMass_pos : 0 < frequencyMass :=
  integral_pos_of_integrable_nonneg_nonzero continuous_frequencyDecay
    integrable_frequencyDecay frequencyDecay_nonneg (x := 0) (by norm_num [frequencyDecay])

theorem integral_frequencyDecay_sub (tau : ℝ) :
    (∫ sigma, frequencyDecay (tau - sigma)) = frequencyMass := by
  simpa [frequencyMass] using integral_sub_left_eq_self frequencyDecay volume tau

/-- The two frequency integrations in (3.20) cost only one power of `lambda`. -/
theorem double_frequency_integral_le (C0 lambda : ℝ) (hC0 : 0 ≤ C0) (hlambda : 0 ≤ lambda) :
    (∫ tau in Icc (-C0 * lambda) (C0 * lambda),
      ∫ sigma in Icc (-C0 * lambda) (C0 * lambda), frequencyDecay (tau - sigma)) ≤
        2 * C0 * frequencyMass * lambda := by
  have hinner : ∀ tau : ℝ,
      (∫ sigma in Icc (-C0 * lambda) (C0 * lambda), frequencyDecay (tau - sigma)) ≤ frequencyMass := by
    intro tau
    rw [← integral_frequencyDecay_sub tau]
    exact setIntegral_le_integral
      (integrable_frequencyDecay.comp_sub_left tau)
      (Filter.Eventually.of_forall fun _ => frequencyDecay_nonneg _)
  have houter : IntegrableOn (fun tau : ℝ => frequencyMass)
      (Icc (-C0 * lambda) (C0 * lambda)) := integrableOn_const (by simp)
  calc
    _ ≤ ∫ tau in Icc (-C0 * lambda) (C0 * lambda), frequencyMass :=
      integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ =>
        integral_nonneg (fun _ => frequencyDecay_nonneg _)) houter
        (Filter.Eventually.of_forall hinner)
    _ = _ := by
      rw [setIntegral_const]
      simp only [Measure.real, Real.volume_Icc]
      rw [ENNReal.toReal_ofReal (by nlinarith [mul_nonneg hC0 hlambda])]
      simp only [smul_eq_mul]
      ring

/-- The frequency kernel is continuous in the input even when `qₓ` is only integrable. -/
theorem continuous_frequencyKernel (b : GraphCoefficients m) (q : Space m → ℝ → ℂ)
    (x : Space m) (hq : Integrable (q x)) : Continuous (frequencyKernel b q x) := by
  unfold frequencyKernel
  apply continuous_of_dominated (bound := fun tau => ‖q x tau‖)
  · intro v
    exact hq.aestronglyMeasurable.mul
      ((continuous_oscillation.comp (continuous_id.mul_const (graphGap b x v))).aestronglyMeasurable)
  · intro v
    exact Filter.Eventually.of_forall fun tau => by simp
  · exact hq.norm
  · exact Filter.Eventually.of_forall fun tau =>
      continuous_const.mul (continuous_oscillation.comp ((continuous_graphGap b x).const_mul tau))

theorem integrable_inputKernel (b : GraphCoefficients m)
    (a : Space m → Space (m + 1) → ℂ) (q : Space m → ℝ → ℂ) (x : Space m)
    (ha : Continuous (a x)) (hcompact : HasCompactSupport (a x)) (hq : Integrable (q x)) :
    Integrable (inputKernel b a q x) :=
  (ha.mul (continuous_frequencyKernel b q x hq)).integrable_of_hasCompactSupport hcompact.mul_right

/-- This uniform preliminary bound will justify the later truncated-operator construction. -/
theorem norm_frequencyKernel_le (b : GraphCoefficients m) (q : Space m → ℝ → ℂ)
    (x : Space m) (v : Space (m + 1)) :
    ‖frequencyKernel b q x v‖ ≤ ∫ tau, ‖q x tau‖ := by
  unfold frequencyKernel
  simpa only [norm_mul, norm_oscillation, mul_one] using
    norm_integral_le_integral_norm (fun tau => q x tau * oscillation (tau * graphGap b x v))

/-- Hermitian symmetry follows from the definition of the actual Gram kernel. -/
theorem gramKernel_conj_symm (b : GraphCoefficients m)
    (a : Space m → Space (m + 1) → ℂ) (q : Space m → ℝ → ℂ) (x z : Space m) :
    gramKernel b a q z x = conj (gramKernel b a q x z) := by
  unfold gramKernel
  rw [← integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun _ => by simp [mul_comm]

/-- The Gram-kernel input integral really is integrable for compact smooth amplitudes. -/
theorem integrable_gramKernel_integrand (b : GraphCoefficients m)
    (a : Space m → Space (m + 1) → ℂ) (q : Space m → ℝ → ℂ) (x z : Space m)
    (ha : Continuous (a x)) (haz : Continuous (a z))
    (hcompact : HasCompactSupport (a x)) (hq : Integrable (q x)) (hqz : Integrable (q z)) :
    Integrable (fun v => inputKernel b a q x v * conj (inputKernel b a q z v)) := by
  have hcx : Continuous (inputKernel b a q x) := ha.mul (continuous_frequencyKernel b q x hq)
  have hcz : Continuous (inputKernel b a q z) := haz.mul (continuous_frequencyKernel b q z hqz)
  exact (hcx.mul hcz.star).integrable_of_hasCompactSupport hcompact.mul_right.mul_right

end StrongSpherical.QuadraticGraph

namespace StrongSpherical.QuadraticGraph
variable {n : ℕ}
/-- A Fourier character along a single input coordinate. -/
def modulation (eta : ℝ) (i : Fin n) (v : Space n) : ℂ :=
  Complex.exp (((2 * Real.pi * eta * v i : ℝ) : ℂ) * Complex.I)
/-- The derivative multiplier for the input-coordinate character. -/
def frequencyFactor (eta : ℝ) : ℂ := ((2 * Real.pi * eta : ℝ) : ℂ) * Complex.I
theorem modulation_eq_oscillation (eta : ℝ) (i : Fin n) (v : Space n) :
    modulation eta i v = oscillation (eta * v i) := by
  simp only [modulation, oscillation, mul_assoc]

@[simp] theorem norm_modulation (eta : ℝ) (i : Fin n) (v : Space n) :
    ‖modulation eta i v‖ = 1 := Complex.norm_exp_ofReal_mul_I _
theorem continuous_modulation (eta : ℝ) (i : Fin n) : Continuous (modulation eta i) := by
  unfold modulation
  fun_prop

theorem hasLineDerivAt_modulation (eta : ℝ) (i : Fin n) (v : Space n) :
    HasLineDerivAt ℝ (modulation eta i) (modulation eta i v * frequencyFactor eta)
      v (ProductOscillation.coordinateVector i) := by
  unfold HasLineDerivAt modulation frequencyFactor
  have hpath : (fun t : ℝ =>
      Complex.exp (((2 * Real.pi * eta * (v + t • ProductOscillation.coordinateVector i) i : ℝ) : ℂ) * Complex.I)) =
      (fun t : ℝ => Complex.exp (((2 * Real.pi * eta * (v i + t) : ℝ) : ℂ) * Complex.I)) := by
    ext t
    simp
  rw [hpath]
  have h := (((((hasDerivAt_id (0 : ℝ)).const_add (v i)).const_mul
    (2 * Real.pi * eta)).ofReal_comp).mul_const Complex.I).cexp
  simpa only [id_eq, add_zero, mul_one, zero_add] using h

/-- An actual input-coordinate integration by parts, with compact-support boundary terms. -/
theorem modulation_integration_by_parts
    (eta : ℝ) (i : Fin n) {a : Space n → ℂ}
    (ha : ContDiff ℝ 1 a) (hcompact : HasCompactSupport a) :
    frequencyFactor eta * (∫ v, modulation eta i v * a v) =
      -(∫ v, modulation eta i v * ProductOscillation.coordinateDerivative i a v) := by
  have hpa := ProductOscillation.contDiff_partial i (r := 0) ha
  have hd := ha.differentiable (by simp)
  have hc := continuous_modulation eta i
  have hi : Integrable (fun v => modulation eta i v * a v) :=
    (hc.mul ha.continuous).integrable_of_hasCompactSupport hcompact.mul_left
  have hip : Integrable (fun v => modulation eta i v * ProductOscillation.coordinateDerivative i a v) :=
    (hc.mul hpa.continuous).integrable_of_hasCompactSupport
      (ProductOscillation.hasCompactSupport_partial i hcompact).mul_left
  have h := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure (Space n))) (B := ContinuousLinearMap.mul ℝ ℂ)
    (f := a) (f' := ProductOscillation.coordinateDerivative i a)
    (g := modulation eta i) (g' := fun v => modulation eta i v * frequencyFactor eta)
    (v := ProductOscillation.coordinateVector i)
    (by simpa only [ContinuousLinearMap.mul_apply', mul_comm] using hip)
    (by simpa only [ContinuousLinearMap.mul_apply', mul_left_comm, mul_comm, mul_assoc] using hi.mul_const (frequencyFactor eta))
    (by simpa only [ContinuousLinearMap.mul_apply', mul_comm] using hi)
    (fun v _ => (hd v).hasFDerivAt.hasLineDerivAt (ProductOscillation.coordinateVector i))
    (fun v _ => hasLineDerivAt_modulation eta i v)
  simp only [ContinuousLinearMap.mul_apply'] at h
  calc
    _ = ∫ v, a v * (modulation eta i v * frequencyFactor eta) := by
      rw [← integral_const_mul]
      congr 1
      ext v
      ring
    _ = _ := by simpa only [mul_comm] using h

/-- Twice integrating by parts along the same input coordinate. -/
theorem modulation_integration_by_parts_twice
    (eta : ℝ) (i : Fin n) {a : Space n → ℂ}
    (ha : ContDiff ℝ 2 a) (hcompact : HasCompactSupport a) :
    frequencyFactor eta ^ 2 * (∫ v, modulation eta i v * a v) =
      ∫ v, modulation eta i v *
        ProductOscillation.coordinateDerivative i (ProductOscillation.coordinateDerivative i a) v := by
  have h1 := modulation_integration_by_parts eta i (ha.of_le (by norm_num)) hcompact
  have h2 := modulation_integration_by_parts eta i
    (ProductOscillation.contDiff_partial i (r := 1) ha)
    (ProductOscillation.hasCompactSupport_partial i hcompact)
  calc
    _ = frequencyFactor eta * (frequencyFactor eta * ∫ v, modulation eta i v * a v) := by ring
    _ = _ := by rw [h1, mul_neg, h2, neg_neg]

@[simp] theorem norm_frequencyFactor (eta : ℝ) :
    ‖frequencyFactor eta‖ = 2 * Real.pi * |eta| := by
  simp only [frequencyFactor, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_I, mul_one]
  norm_num [abs_of_pos Real.pi_pos]

theorem norm_integral_modulation_le (eta : ℝ) (i : Fin n) (a : Space n → ℂ) :
    ‖∫ v, modulation eta i v * a v‖ ≤ ∫ v, ‖a v‖ := by
  simpa only [norm_mul, norm_modulation, one_mul] using
    norm_integral_le_integral_norm (fun v => modulation eta i v * a v)

/-- The second input derivative supplies inverse-square frequency decay. -/
theorem sq_frequency_mul_norm_integral_modulation_le
    (eta : ℝ) (i : Fin n) {a : Space n → ℂ}
    (ha : ContDiff ℝ 2 a) (hcompact : HasCompactSupport a) :
    |eta| ^ 2 * ‖∫ v, modulation eta i v * a v‖ ≤
      ∫ v, ‖ProductOscillation.coordinateDerivative i
        (ProductOscillation.coordinateDerivative i a) v‖ := by
  have hn := congrArg norm (modulation_integration_by_parts_twice eta i ha hcompact)
  simp only [norm_mul, norm_pow] at hn
  have hq : |eta| ≤ ‖frequencyFactor eta‖ := by
    rw [norm_frequencyFactor]
    nlinarith [Real.pi_gt_three, abs_nonneg eta]
  calc
    _ ≤ ‖frequencyFactor eta‖ ^ 2 * ‖∫ v, modulation eta i v * a v‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg eta) hq 2) (norm_nonneg _)
    _ = _ := hn
    _ ≤ _ := norm_integral_modulation_le eta i _

/-- A uniform version valid also at zero frequency. Both quantities on the right
are actual `L¹` norms of the amplitude and its second input derivative. -/
theorem norm_integral_modulation_le_decay
    (eta : ℝ) (i : Fin n) {a : Space n → ℂ}
    (ha : ContDiff ℝ 2 a) (hcompact : HasCompactSupport a) :
    ‖∫ v, modulation eta i v * a v‖ ≤
      4 * ((∫ v, ‖a v‖) +
        ∫ v, ‖ProductOscillation.coordinateDerivative i
          (ProductOscillation.coordinateDerivative i a) v‖) /
        (1 + |eta|) ^ 2 := by
  have h0 := norm_integral_modulation_le eta i a
  have h2 := sq_frequency_mul_norm_integral_modulation_le eta i ha hcompact
  have hN0 : 0 ≤ ∫ v, ‖a v‖ := integral_nonneg fun _ => norm_nonneg _
  have hN2 : 0 ≤ ∫ v, ‖ProductOscillation.coordinateDerivative i
      (ProductOscillation.coordinateDerivative i a) v‖ := integral_nonneg fun _ => norm_nonneg _
  apply (le_div_iff₀ (by positivity : 0 < (1 + |eta|) ^ 2)).2
  rcases le_total |eta| 1 with he | he
  · have hd : (1 + |eta|) ^ 2 ≤ 4 := by nlinarith [abs_nonneg eta]
    calc
      _ ≤ ‖∫ v, modulation eta i v * a v‖ * 4 :=
        mul_le_mul_of_nonneg_left hd (norm_nonneg _)
      _ ≤ _ := by linarith
  · have hd : (1 + |eta|) ^ 2 ≤ 4 * |eta| ^ 2 := by nlinarith
    calc
      _ ≤ ‖∫ v, modulation eta i v * a v‖ * (4 * |eta| ^ 2) :=
        mul_le_mul_of_nonneg_left hd (norm_nonneg _)
      _ ≤ _ := by nlinarith

/-- The same estimate expressed using the integrable frequency-difference profile. -/
theorem norm_integral_modulation_le_frequencyDecay
    (eta : ℝ) (i : Fin n) {a : Space n → ℂ}
    (ha : ContDiff ℝ 2 a) (hcompact : HasCompactSupport a) :
    ‖∫ v, modulation eta i v * a v‖ ≤
      4 * ((∫ v, ‖a v‖) +
        ∫ v, ‖ProductOscillation.coordinateDerivative i
          (ProductOscillation.coordinateDerivative i a) v‖) * frequencyDecay eta := by
  rw [frequencyDecay, Real.rpow_neg (by positivity : 0 ≤ 1 + |eta|),
    Real.rpow_two, ← div_eq_mul_inv]
  exact norm_integral_modulation_le_decay eta i ha hcompact

end StrongSpherical.QuadraticGraph

namespace StrongSpherical.QuadraticGraph
variable {m : ℕ}
/-- The one-dimensional spatial profile in (3.21). -/
def spatialDecay (lambda t : ℝ) : ℝ := (1 + lambda * |t|) ^ (-(1 / 2 : ℝ))

theorem continuous_spatialDecay (lambda : ℝ) (hlambda : 0 ≤ lambda) :
    Continuous (spatialDecay lambda) := by
  apply Continuous.rpow_const
    ((continuous_const.mul continuous_abs).const_add 1)
  intro t
  exact Or.inl (ne_of_gt (by dsimp; positivity))

theorem spatialDecay_nonneg (lambda t : ℝ) (hlambda : 0 ≤ lambda) :
    0 ≤ spatialDecay lambda t := by unfold spatialDecay; positivity

theorem integral_spatialDecay_nonneg (lambda L : ℝ) (hlambda : 0 ≤ lambda) (hL : 0 ≤ L) :
    0 ≤ ∫ t in -L..L, spatialDecay lambda t :=
  intervalIntegral.integral_nonneg (by linarith) fun _ _ => spatialDecay_nonneg _ _ hlambda

/-- Exact one-sided integral, used to obtain (3.22). -/
theorem integral_spatialDecay_zero (lambda L : ℝ) (hlambda : 0 < lambda) (hL : 0 ≤ L) :
    (∫ t in 0..L, spatialDecay lambda t) =
      2 / lambda * (Real.sqrt (1 + lambda * L) - 1) := by
  have hd : ∀ t ∈ uIcc 0 L,
      HasDerivAt (fun s => 2 / lambda * Real.sqrt (1 + lambda * s))
        (spatialDecay lambda t) t := by
    intro t ht
    have ht0 : 0 ≤ t := (by simpa [uIcc_of_le hL] using ht : t ∈ Icc 0 L).1
    have hp : 0 < 1 + lambda * t := by positivity
    convert! (((hasDerivAt_id t).const_mul lambda).const_add 1).sqrt hp.ne' |>.const_mul (2 / lambda) using 1
    rw [spatialDecay, abs_of_nonneg ht0, Real.rpow_neg hp.le, ← Real.sqrt_eq_rpow]
    simp only [id_eq, mul_one]
    field_simp [hlambda.ne', (Real.sqrt_pos.2 hp).ne']
  have hint := (continuous_spatialDecay lambda hlambda.le).intervalIntegrable (μ := volume) 0 L
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint
  calc
    _ = _ := h
    _ = _ := by simp only [mul_zero, add_zero, Real.sqrt_one, mul_one]; ring

/-- Exact symmetric integral of the spatial profile. -/
theorem integral_spatialDecay_symm (lambda L : ℝ) (hlambda : 0 < lambda) (hL : 0 ≤ L) :
    (∫ t in -L..L, spatialDecay lambda t) =
      4 / lambda * (Real.sqrt (1 + lambda * L) - 1) := by
  have hc := continuous_spatialDecay lambda hlambda.le
  have he : (∫ t in -L..0, spatialDecay lambda t) = ∫ t in 0..L, spatialDecay lambda t := by
    have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := L) (spatialDecay lambda)
    simpa only [spatialDecay, abs_neg, neg_zero] using h.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (-L) 0)
    (hc.intervalIntegrable (μ := volume) 0 L), he, integral_spatialDecay_zero lambda L hlambda hL]
  ring

/-- The one-coordinate bound in (3.22), with a uniform explicit constant. -/
theorem integral_spatialDecay_le (lambda L : ℝ) (hlambda : 1 ≤ lambda) (hL : 0 ≤ L) :
    (∫ t in -L..L, spatialDecay lambda t) ≤
      4 * Real.sqrt (L + 1) / Real.sqrt lambda := by
  have hl : 0 < lambda := by linarith
  have hs : 0 < Real.sqrt lambda := Real.sqrt_pos.2 hl
  rw [integral_spatialDecay_symm lambda L hl hL]
  have hroot : Real.sqrt (1 + lambda * L) ≤ Real.sqrt lambda * Real.sqrt (L + 1) := by
    rw [← Real.sqrt_mul hl.le]
    apply Real.sqrt_le_sqrt
    nlinarith
  apply (le_div_iff₀ hs).2
  have hs2 := Real.sq_sqrt hl.le
  have hbase : 0 ≤ Real.sqrt (1 + lambda * L) := Real.sqrt_nonneg _
  have hb : 0 ≤ Real.sqrt (L + 1) := Real.sqrt_nonneg _
  apply (mul_le_mul_iff_left₀ hl).mp
  calc
    (4 / lambda * (Real.sqrt (1 + lambda * L) - 1) * Real.sqrt lambda) * lambda =
      4 * (Real.sqrt (1 + lambda * L) - 1) * Real.sqrt lambda := by field_simp
    _ ≤ 4 * (Real.sqrt lambda * Real.sqrt (L + 1)) * Real.sqrt lambda := by nlinarith
    _ = (4 * Real.sqrt (L + 1)) * lambda := by nlinarith [hs2]

end StrongSpherical.QuadraticGraph

namespace StrongSpherical.QuadraticGraph
variable {m : ℕ}

/-- The compactly supported one-dimensional Schur profile. -/
def localizedSpatialDecay (lambda L : ℝ) : ℝ → ℝ :=
  (Icc (-L) L).indicator (spatialDecay lambda)

theorem localizedSpatialDecay_nonneg (lambda L t : ℝ) (hlambda : 0 ≤ lambda) :
    0 ≤ localizedSpatialDecay lambda L t := by
  exact indicator_nonneg (fun _ _ => spatialDecay_nonneg _ _ hlambda) _

theorem integrable_localizedSpatialDecay (lambda L : ℝ) (hlambda : 0 ≤ lambda) :
    Integrable (localizedSpatialDecay lambda L) := by
  exact (integrable_indicator_iff measurableSet_Icc).2
    ((continuous_spatialDecay lambda hlambda).continuousOn.integrableOn_Icc (μ := volume))

theorem integral_localizedSpatialDecay (lambda L : ℝ) (hL : 0 ≤ L) :
    (∫ t, localizedSpatialDecay lambda L t) = ∫ t in -L..L, spatialDecay lambda t := by
  rw [localizedSpatialDecay, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le (by linarith)]

@[simp] theorem localizedSpatialDecay_neg (lambda L t : ℝ) :
    localizedSpatialDecay lambda L (-t) = localizedSpatialDecay lambda L t := by
  have he : -t ∈ Icc (-L) L ↔ t ∈ Icc (-L) L := by
    simp only [mem_Icc]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith
  simp only [localizedSpatialDecay, indicator_apply, he, spatialDecay, abs_neg]

/-- The product profile in the Gram-kernel bound (3.21), including its support cutoff. -/
def spatialProfile (lambda L : ℝ) (x z : Space m) : ℝ :=
  ∏ i, localizedSpatialDecay lambda L (x i - z i)

theorem spatialProfile_nonneg (lambda L : ℝ) (x z : Space m) (hlambda : 0 ≤ lambda) :
    0 ≤ spatialProfile lambda L x z :=
  Finset.prod_nonneg (fun _ _ => localizedSpatialDecay_nonneg _ _ _ hlambda)

theorem spatialProfile_symm (lambda L : ℝ) (x z : Space m) :
    spatialProfile lambda L x z = spatialProfile lambda L z x := by
  unfold spatialProfile
  apply Finset.prod_congr rfl
  intro i _
  calc
    _ = localizedSpatialDecay lambda L (-(x i - z i)) :=
      (localizedSpatialDecay_neg lambda L (x i - z i)).symm
    _ = _ := by rw [neg_sub]

theorem integrable_spatialProfile (lambda L : ℝ) (x : Space m) (hlambda : 0 ≤ lambda) :
    Integrable (spatialProfile lambda L x) := by
  have hp : Integrable (fun z : Fin m → ℝ =>
      ∏ i, localizedSpatialDecay lambda L (x i - z i)) := by
    exact Integrable.fintype_prod (fun i =>
      (integrable_localizedSpatialDecay lambda L hlambda).comp_sub_left (x i))
  exact ((PiLp.volume_preserving_ofLp (Fin m)).integrable_comp_emb
    (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm.measurableEmbedding).2 hp

/-- Exact factorization of each row integral; the column integral is the same by symmetry. -/
theorem integral_spatialProfile (lambda L : ℝ) (x : Space m) :
    (∫ z, spatialProfile lambda L x z) = (∫ t, localizedSpatialDecay lambda L t) ^ m := by
  calc
    _ = ∫ z : Fin m → ℝ, ∏ i, localizedSpatialDecay lambda L (x i - z i) :=
      (PiLp.volume_preserving_ofLp (Fin m)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm.measurableEmbedding _
    _ = ∏ i : Fin m, ∫ t, localizedSpatialDecay lambda L (x i - t) :=
      integral_fin_nat_prod_volume_eq_prod (E := fun _ : Fin m => ℝ)
        (fun i t => localizedSpatialDecay lambda L (x i - t))
    _ = _ := by
      simp_rw [integral_sub_left_eq_self (localizedSpatialDecay lambda L) volume]
      simp

/-- The row and column mass required by Schur's test, with the correct dimension-dependent power. -/
theorem integral_spatialProfile_le (lambda L : ℝ) (x : Space m)
    (hlambda : 1 ≤ lambda) (hL : 0 ≤ L) :
    (∫ z, spatialProfile lambda L x z) ≤
      (4 * Real.sqrt (L + 1) / Real.sqrt lambda) ^ m := by
  rw [integral_spatialProfile]
  apply pow_le_pow_left₀
    (integral_nonneg fun t => localizedSpatialDecay_nonneg _ _ _ (by linarith))
  rw [integral_localizedSpatialDecay lambda L hL]
  exact integral_spatialDecay_le lambda L hlambda hL

/-- The product of coordinate cutoffs is exactly the box cutoff in (3.21). -/
theorem spatialProfile_eq_cutoff (lambda L : ℝ) (x z : Space m) :
    spatialProfile lambda L x z =
      if (∀ i, |x i - z i| ≤ L) then ∏ i, spatialDecay lambda (x i - z i) else 0 := by
  classical
  by_cases h : ∀ i, |x i - z i| ≤ L
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro i _
    change (Icc (-L) L).indicator (spatialDecay lambda) (x i - z i) = _
    exact indicator_of_mem (show x i - z i ∈ Icc (-L) L from abs_le.mp (h i)) _
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    change (Icc (-L) L).indicator (spatialDecay lambda) (x i - z i) = 0
    exact indicator_of_notMem
      (show x i - z i ∉ Icc (-L) L from fun hm => hi (abs_le.mpr hm)) _

/-- The corresponding column-mass bound, stated explicitly for Schur's test. -/
theorem integral_spatialProfile_column_le (lambda L : ℝ) (x : Space m)
    (hlambda : 1 ≤ lambda) (hL : 0 ≤ L) :
    (∫ z, spatialProfile lambda L z x) ≤
      (4 * Real.sqrt (L + 1) / Real.sqrt lambda) ^ m := by
  calc
    _ = ∫ z, spatialProfile lambda L x z :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => spatialProfile_symm lambda L z x)
    _ ≤ _ := integral_spatialProfile_le lambda L x hlambda hL

end StrongSpherical.QuadraticGraph
