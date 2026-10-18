import FourierMiddle
import ProductSmoothing
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.InnerProductSpace.Adjoint
import MarginalLocalEstimate

/-! # The actual smoothing kernels and their L² Fourier multipliers -/
noncomputable section
open MeasureTheory Set FourierTransform
open scoped FourierTransform SchwartzMap BigOperators ContDiff BoundedContinuousFunction

namespace StrongSpherical.FourierKernel
open FourierCutoff FourierMiddle ProductSmoothing
variable {d : ℕ}

/-- The normalized one-dimensional kernel has the exact dilated cutoff as Fourier transform. -/
theorem fourier_scaledPhi (v : ℝ) (hv : 0 < v) (xi : ℝ) :
    𝓕 (scaledPhi v) xi = (theta (v * xi) : ℂ) := by
  let G : ℝ → ℂ := fun s => 𝐞 (-(s * (v * xi))) • phi s
  have hG : (fun t : ℝ => 𝐞 (-(t * xi)) • phi (v⁻¹ * t)) =
      fun t => G (v⁻¹ * t) := by
    funext t
    dsimp [G]
    congr 2
    field_simp
  have hc : (fun t : ℝ => 𝐞 (-(t * xi)) • scaledPhi v t) =
      fun t => (v⁻¹ : ℂ) * (𝐞 (-(t * xi)) • phi (v⁻¹ * t)) := by
    funext t
    simp only [scaledPhi, Circle.smul_def]
    ring
  rw [Real.fourier_real_eq, hc, integral_const_mul, hG,
    Measure.integral_comp_inv_mul_left, abs_of_pos hv]
  have hf : (∫ s, G s) = (theta (v * xi) : ℂ) := by
    change (∫ s : ℝ, 𝐞 (-(s * (v * xi))) • phi s) = _
    rw [← Real.fourier_real_eq]
    exact congrArg (fun f : 𝓢(ℝ, ℂ) => f (v * xi)) fourier_phi
  rw [hf, Complex.real_smul]
  field_simp [Complex.ofReal_ne_zero.mpr hv.ne']

private theorem char_sum {ι : Type*} (S : Finset ι) (a : ι → ℝ) :
    𝐞 (∑ i ∈ S, a i) = ∏ i ∈ S, 𝐞 (a i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi, Finset.prod_insert hi, AddChar.map_add_eq_mul, ih]

/-- Exact product factorization of the Fourier transform, for the original Euclidean volume. -/
theorem fourier_productPhi (r : Radii d) (xi : Space d) :
    𝓕 (productPhi r) xi = ∏ i, (theta (r.1 i * xi i) : ℂ) := by
  rw [Real.fourier_eq]
  have heq : (fun x : Space d => 𝐞 (-inner ℝ x xi) • productPhi r x) =
      fun x => ∏ i, (𝐞 (-(x i * xi i)) • scaledPhi (r.1 i) (x i)) := by
    funext x
    rw [PiLp.inner_apply]
    simp only [Real.inner_apply, ← Finset.sum_neg_distrib, char_sum]
    change Circle.coeHom (∏ i : Fin d, 𝐞 (-(x i * xi i))) *
      (∏ i, scaledPhi (r.1 i) (x i)) =
        ∏ i, Circle.coeHom (𝐞 (-(x i * xi i))) * scaledPhi (r.1 i) (x i)
    rw [map_prod, Finset.prod_mul_distrib]
  rw [heq, integral_product_functions (fun (i : Fin d) (t : ℝ) =>
    𝐞 (-(t * xi i)) • scaledPhi (r.1 i) t)]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Real.fourier_real_eq, fourier_scaledPhi _ (r.2 i)]

def baseCutoff (x : Space d) : ℂ := ∏ i, (theta (x i) : ℂ)

theorem baseCutoff_contDiff : ContDiff ℝ ∞ (baseCutoff (d := d)) := by
  have ht := theta_contDiff
  unfold baseCutoff
  apply contDiff_prod
  intro i hi
  exact Complex.ofRealCLM.contDiff.comp (theta_contDiff.comp (by fun_prop))

theorem baseCutoff_compact : HasCompactSupport (baseCutoff (d := d)) := by
  apply (GenericKernelRegularity.isCompact_coordinateBox d 2).of_isClosed_subset
    (isClosed_tsupport _)
  apply closure_minimal
  · intro x hx i
    have hn : (theta (x i) : ℂ) ≠ 0 := (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)
    have hr : theta (x i) ≠ 0 := by exact_mod_cast hn
    exact theta_control.support_subset hr
  · exact (GenericKernelRegularity.isCompact_coordinateBox d 2).isClosed

/-- The full product cutoff is a genuine compactly supported smooth Schwartz function. -/
def fullCutoff (r : Radii d) : 𝓢(Space d, ℂ) :=
  (baseCutoff_compact.comp_homeomorph (DilationL2.dilationHomeomorph r)).toSchwartzMap
    (baseCutoff_contDiff.comp (by
      change ContDiff ℝ ∞ (diagonalDilation r.1)
      unfold diagonalDilation
      fun_prop))

@[simp] theorem fullCutoff_apply (r : Radii d) (xi : Space d) :
    fullCutoff r xi = ∏ i, (theta (r.1 i * xi i) : ℂ) := rfl

theorem fourier_productPhi_eq (r : Radii d) :
    𝓕 (productPhi r) = (fullCutoff r : Space d → ℂ) := by
  funext xi
  exact fourier_productPhi r xi

def productPhiSchwartz (r : Radii d) : 𝓢(Space d, ℂ) := 𝓕⁻ (fullCutoff r)

/-- The Schwartz realization is the very same normalized product kernel used for smoothing. -/
theorem productPhiSchwartz_eq (r : Radii d) :
    (productPhiSchwartz r : Space d → ℂ) = productPhi r := by
  have hF : Integrable (𝓕 (productPhi r)) := by
    rw [fourier_productPhi_eq]
    exact (fullCutoff r).integrable
  have hi := (continuous_productPhi r).fourierInv_fourier_eq (integrable_productPhi r) hF
  rw [fourier_productPhi_eq] at hi
  unfold productPhiSchwartz
  rw [SchwartzMap.fourierInv_coe]
  exact hi

def convolutionMass (K : Space d → ℂ) : ℝ := ∫ x, ‖K x‖

theorem convolutionMass_nonneg (K : Space d → ℂ) : 0 ≤ convolutionMass K :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem convolution_row (K : Space d → ℂ) (hK : Continuous K) (hKi : Integrable K)
    (x : Space d) :
    (∫⁻ y, ‖K (x - y)‖ₑ) ≤ ENNReal.ofReal (convolutionMass K) := by
  have h := (Measure.measurePreserving_sub_left (volume : Measure (Space d)) x).lintegral_comp
    (f := fun y : Space d => ‖K y‖ₑ) hK.measurable.enorm
  exact le_of_eq (h.trans (ofReal_integral_norm_eq_lintegral_enorm hKi).symm)

theorem convolution_column (K : Space d → ℂ) (hK : Continuous K) (hKi : Integrable K)
    (y : Space d) :
    (∫⁻ x, ‖K (x - y)‖ₑ) ≤ ENNReal.ofReal (convolutionMass K) := by
  have h := (measurePreserving_sub_right (volume : Measure (Space d)) y).lintegral_comp
    (f := fun x : Space d => ‖K x‖ₑ) hK.measurable.enorm
  exact le_of_eq (h.trans (ofReal_integral_norm_eq_lintegral_enorm hKi).symm)

/-- The actual convolution integral, as a bounded operator on L², obtained by Schur's test. -/
def convolutionCLM (K : Space d → ℂ) (hK : Continuous K) (hKi : Integrable K) :
    L2 d →L[ℂ] L2 d :=
  SchurTest.kernelL2Operator (μ := volume) (ν := volume)
    (fun x y => K (x - y)) (convolutionMass K)
    (hK.comp (continuous_fst.sub continuous_snd)).measurable
    (convolution_row K hK hKi) (convolution_column K hK hKi) (convolutionMass_nonneg K)

theorem convolutionCLM_coe (K : Space d → ℂ) (hK : Continuous K) (hKi : Integrable K)
    (f : L2 d) : (convolutionCLM K hK hKi f : Space d → ℂ) =ᵐ[volume]
      kernelConvolution K f := by
  have h := SchurTest.kernelL2Operator_coe (μ := volume) (ν := volume)
    (fun x y => K (x - y)) (convolutionMass K)
    (hK.comp (continuous_fst.sub continuous_snd)).measurable
    (convolution_row K hK hKi) (convolution_column K hK hKi) (convolutionMass_nonneg K) f
  refine h.trans ?_
  filter_upwards with x
  exact (MarginalLocalEstimate.convolution_eq_centered_integral K f x).symm

/-- On Schwartz inputs, the L² multiplier is exactly the classical Schwartz convolution. -/
theorem multiplier_schwartz (g f : 𝓢(Space d, ℂ)) :
    multiplier (𝓕 g).toBoundedContinuousFunction (f.toLp 2) =
      (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) g f).toLp 2 := by
  have hp : symbolProduct (𝓕 g).toBoundedContinuousFunction ((𝓕 f).toLp 2 volume) =
      (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 g) (𝓕 f)).toLp 2 volume := by
    apply Lp.ext
    filter_upwards [coe_symbolProduct (𝓕 g).toBoundedContinuousFunction ((𝓕 f).toLp 2 volume),
      (𝓕 f).coeFn_toLp 2 volume,
      (SchwartzMap.pairing (ContinuousLinearMap.mul ℂ ℂ) (𝓕 g) (𝓕 f)).coeFn_toLp 2 volume]
        with x h1 h2 h3
    rw [h1, h2, h3]
    rfl
  rw [multiplier_apply, SchwartzMap.toLp_fourier_eq, hp, SchwartzMap.toLp_fourierInv_eq]
  rfl

set_option maxHeartbeats 1000000 in
theorem convolutionCLM_schwartz (g f : 𝓢(Space d, ℂ)) :
    convolutionCLM g g.continuous g.integrable (f.toLp 2) =
      (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) g f).toLp 2 := by
  apply Lp.ext
  filter_upwards [convolutionCLM_coe g g.continuous g.integrable (f.toLp 2),
    (SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) g f).coeFn_toLp 2 volume] with x h1 h2
  rw [h1, h2, SchwartzMap.convolution_apply]
  change kernelConvolution g (f.toLp 2) x = kernelConvolution g f x
  rw [MarginalLocalEstimate.convolution_eq_centered_integral,
    MarginalLocalEstimate.convolution_eq_centered_integral]
  apply integral_congr_ae
  filter_upwards [f.coeFn_toLp 2 volume] with y hy
  rw [hy]

theorem clm_eq_of_schwartz (T S : L2 d →L[ℂ] L2 d)
    (h : ∀ u : 𝓢(Space d, ℂ), T (u.toLp 2 volume) = S (u.toLp 2 volume)) : T = S := by
  apply ContinuousLinearMap.ext
  intro f
  have hd : DenseRange (fun u : 𝓢(Space d, ℂ) => u.toLp 2 volume) :=
    SchwartzMap.denseRange_toLpCLM (E := Space d) (F := ℂ) (p := 2) (μ := volume) (by norm_num)
  exact hd.induction_on f
    (isClosed_eq T.continuous S.continuous) h

/-- Density and the genuine integral bound extend the convolution-multiplier identity to all L². -/
theorem convolutionCLM_eq_multiplier (g : 𝓢(Space d, ℂ)) :
    convolutionCLM g g.continuous g.integrable = multiplier (𝓕 g).toBoundedContinuousFunction :=
  clm_eq_of_schwartz _ _ (fun u =>
    (convolutionCLM_schwartz g u).trans (multiplier_schwartz g u).symm)

/-- The multiplier identity is realized by the original convolution integral on every L² class. -/
theorem multiplier_coe_convolution (g : 𝓢(Space d, ℂ)) (f : L2 d) :
    (multiplier (𝓕 g).toBoundedContinuousFunction f : Space d → ℂ) =ᵐ[volume]
      kernelConvolution g f := by
  rw [← convolutionCLM_eq_multiplier]
  exact convolutionCLM_coe g g.continuous g.integrable f

/-- Full product smoothing, realized by its actual integral, agrees with its actual L² multiplier. -/
theorem full_multiplier_coe_convolution (r : Radii d) (f : L2 d) :
    (multiplier (fullCutoff r).toBoundedContinuousFunction f : Space d → ℂ) =ᵐ[volume]
      kernelConvolution (productPhi r) f := by
  have hg : 𝓕 (productPhiSchwartz r) = fullCutoff r := fourier_fourierInv_eq _
  have h := multiplier_coe_convolution (productPhiSchwartz r) f
  rw [hg, productPhiSchwartz_eq] at h
  exact h

variable {j : ℕ}

/-- A product cutoff in the frequencies dual to a coordinate subspace. -/
def partialFrequency (A : Space j →L[ℝ] Space d) (r : Radii j) (xi : Space d) : ℂ :=
  fullCutoff r (A.adjoint xi)

theorem partialFrequency_temperate (A : Space j →L[ℝ] Space d) (r : Radii j) :
    Function.HasTemperateGrowth (partialFrequency A r) :=
  (fullCutoff r).hasTemperateGrowth.comp A.adjoint.hasTemperateGrowth

def partialSymbol (A : Space j →L[ℝ] Space d) (r : Radii j) : Symbol d :=
  BoundedContinuousFunction.ofNormedAddCommGroup (partialFrequency A r)
    ((fullCutoff r).continuous.comp A.adjoint.continuous)
    ‖(fullCutoff r).toBoundedContinuousFunction‖
    (fun xi => (fullCutoff r).toBoundedContinuousFunction.norm_coe_le_norm (A.adjoint xi))

@[simp] theorem partialSymbol_apply (A : Space j →L[ℝ] Space d) (r : Radii j) (xi : Space d) :
    partialSymbol A r xi = partialFrequency A r xi := rfl

def partialSchwartz (A : Space j →L[ℝ] Space d) (r : Radii j)
    (f : 𝓢(Space d, ℂ)) : 𝓢(Space d, ℂ) :=
  𝓕⁻ (SchwartzMap.smulLeftCLM ℂ (partialFrequency A r) (𝓕 f))

theorem partialSchwartz_toLp (A : Space j →L[ℝ] Space d) (r : Radii j)
    (f : 𝓢(Space d, ℂ)) :
    (partialSchwartz A r f).toLp 2 = multiplier (partialSymbol A r) (f.toLp 2) := by
  have hp : symbolProduct (partialSymbol A r) ((𝓕 f).toLp 2 volume) =
      (SchwartzMap.smulLeftCLM ℂ (partialFrequency A r) (𝓕 f)).toLp 2 volume := by
    apply Lp.ext
    filter_upwards [coe_symbolProduct (partialSymbol A r) ((𝓕 f).toLp 2 volume),
      (𝓕 f).coeFn_toLp 2 volume,
      (SchwartzMap.smulLeftCLM ℂ (partialFrequency A r) (𝓕 f)).coeFn_toLp 2 volume]
      with x h1 h2 h3
    rw [h1, h2, h3, SchwartzMap.smulLeftCLM_apply_apply (partialFrequency_temperate A r)]
    rfl
  rw [multiplier_apply, SchwartzMap.toLp_fourier_eq, hp, SchwartzMap.toLp_fourierInv_eq]
  rfl

private def phase (t : ℝ) : ℂ := 𝐞 t

@[simp] private theorem norm_phase (t : ℝ) : ‖phase t‖ = 1 := Circle.norm_coe _

private theorem phase_add (s t : ℝ) : phase (s + t) = phase s * phase t := by
  exact congrArg ((↑) : Circle → ℂ) (AddChar.map_add_eq_mul 𝐞 s t)

private theorem partialFrequency_integral (A : Space j →L[ℝ] Space d) (r : Radii j)
    (xi : Space d) :
    partialFrequency A r xi = ∫ y, phase (-inner ℝ (A y) xi) * productPhi r y := by
  have h := (fourier_productPhi r (A.adjoint xi)).symm
  change fullCutoff r (A.adjoint xi) = _
  change fullCutoff r (A.adjoint xi) = _ at h
  rw [h, Real.fourier_eq]
  apply integral_congr_ae
  filter_upwards with y
  rw [A.adjoint_inner_right]
  rfl

/-- Physical partial smoothing is the actual Schwartz multiplier, for every coordinate subspace.
The proof uses Fourier inversion and an absolutely integrable Fubini interchange. -/
theorem partialSchwartz_apply (A : Space j →L[ℝ] Space d) (r : Radii j)
    (f : 𝓢(Space d, ℂ)) (x : Space d) :
    partialSchwartz A r f x = ∫ y, productPhi r y * f (x - A y) := by
  let H : Space d × Space j → ℂ := fun p =>
    productPhi r p.2 * (phase (inner ℝ p.1 (x - A p.2)) * (𝓕 f) p.1)
  have hHcont : Continuous H := by
    have hprod := continuous_productPhi r
    dsimp [H, phase]
    fun_prop
  have hH : Integrable H ((volume : Measure (Space d)).prod volume) := by
    have hF : Integrable ((𝓕 f : 𝓢(Space d, ℂ)) : Space d → ℂ) := (𝓕 f).integrable
    have hb : Integrable (fun p : Space d × Space j =>
        ‖(𝓕 f) p.1‖ * ‖productPhi r p.2‖) ((volume : Measure (Space d)).prod volume) :=
      hF.norm.mul_prod (integrable_productPhi r).norm
    apply hb.mono' hHcont.aestronglyMeasurable
    filter_upwards with p
    simp only [H, norm_mul, norm_phase, one_mul]
    exact le_of_eq (mul_comm _ _)
  have hphase (xi : Space d) (y : Space j) :
      phase (inner ℝ xi x) * phase (-inner ℝ (A y) xi) =
        phase (inner ℝ xi (x - A y)) := by
    rw [← phase_add, inner_sub_right, real_inner_comm xi (A y), sub_eq_add_neg]
  have hstart : partialSchwartz A r f x =
      ∫ xi, phase (inner ℝ xi x) * (partialFrequency A r xi * (𝓕 f) xi) := by
    unfold partialSchwartz
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
    apply integral_congr_ae
    filter_upwards with xi
    rw [SchwartzMap.smulLeftCLM_apply_apply (partialFrequency_temperate A r)]
    rfl
  rw [hstart]
  calc
    _ = ∫ xi, ∫ y, H (xi, y) := by
      apply integral_congr_ae
      filter_upwards with xi
      rw [partialFrequency_integral, ← integral_mul_const, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      dsimp [H]
      calc
        _ = (phase (inner ℝ xi x) * phase (-inner ℝ (A y) xi)) *
            (productPhi r y * (𝓕 f) xi) := by ring
        _ = _ := by rw [hphase]; ring
    _ = ∫ y, ∫ xi, H (xi, y) := integral_integral_swap hH
    _ = ∫ y, productPhi r y * f (x - A y) := by
      apply integral_congr_ae
      filter_upwards with y
      dsimp only [H]
      rw [integral_const_mul]
      have hInv : (𝓕⁻ (𝓕 f : 𝓢(Space d, ℂ)) : 𝓢(Space d, ℂ)) = f := fourierInv_fourier_eq f
      have hi := congrArg (fun g : 𝓢(Space d, ℂ) => g (x - A y)) hInv
      rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq] at hi
      have hi' : (∫ xi : Space d, phase (inner ℝ xi (x - A y)) * (𝓕 f) xi) =
          f (x - A y) := by
        simpa only [phase, Circle.smul_def, smul_eq_mul] using hi
      rw [hi']

/-- Coordinate restriction as an actual continuous linear map. -/
def coordinateProjection (e : Fin j ↪ Fin d) : Space d →L[ℝ] Space j :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin j => ℝ)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => EuclideanSpace.proj (e i)))

@[simp] theorem coordinateProjection_apply (e : Fin j ↪ Fin d) (xi : Space d) (i : Fin j) :
    coordinateProjection e xi i = xi (e i) := rfl

/-- The coordinate inclusion is the adjoint of restriction. -/
def coordinateInclusion (e : Fin j ↪ Fin d) : Space j →L[ℝ] Space d :=
  (coordinateProjection e).adjoint

@[simp] theorem coordinateInclusion_adjoint (e : Fin j ↪ Fin d) :
    (coordinateInclusion e).adjoint = coordinateProjection e :=
  ContinuousLinearMap.adjoint_adjoint _

/-- For the initial coordinate block, adjoint inclusion is the familiar zero extension. -/
theorem coordinateInclusion_castAdd (m l : ℕ) (u : Space m) :
    coordinateInclusion (Fin.castAddEmb l) u = (ProductCoordinates.split m l).symm (u, 0) := by
  apply ext_inner_right ℝ
  intro z
  rw [coordinateInclusion, ContinuousLinearMap.adjoint_inner_left]
  simp only [PiLp.inner_apply, Real.inner_apply, coordinateProjection_apply,
    Fin.castAddEmb_apply]
  rw [Fin.sum_univ_add]
  simp only [ProductCoordinates.split_symm_castAdd, ProductCoordinates.split_symm_natAdd,
    WithLp.ofLp_zero, Pi.zero_apply, zero_mul, Finset.sum_const_zero, add_zero]

theorem sub_coordinateInclusion_castAdd (m l : ℕ) (x : Space (m + l)) (u : Space m) :
    x - coordinateInclusion (Fin.castAddEmb l) u =
      (ProductCoordinates.split m l).symm ((ProductCoordinates.split m l x).1 - u,
        (ProductCoordinates.split m l x).2) := by
  rw [coordinateInclusion_castAdd]
  apply (ProductCoordinates.split m l).injective
  simp only [ProductCoordinates.split_sub, MeasurableEquiv.apply_symm_apply,
    Prod.sub_def, sub_zero]

def subsetRadii (M : ℕ) (k : Fin d → ℤ) (e : Fin j ↪ Fin d) : Radii j :=
  ⟨fun i => (2 : ℝ) ^ (k (e i) + (M : ℤ)), fun _ => zpow_pos (by norm_num) _⟩

theorem partialSymbol_eq_lowSubset (M : ℕ) (k : Fin d → ℤ) (e : Fin j ↪ Fin d) :
    partialSymbol (coordinateInclusion e) (subsetRadii M k e) =
      lowSubsetSymbol M k (Finset.univ.image e) := by
  ext xi
  simp only [partialSymbol_apply, partialFrequency, fullCutoff_apply,
    coordinateInclusion_adjoint, coordinateProjection_apply, subsetRadii,
    lowSubsetSymbol, BoundedContinuousFunction.prod_apply, lowSymbol_apply,
    FrequencyDecomposition.lowCoordinate]
  rw [Finset.prod_image]
  exact fun _ _ _ _ h => e.injective h

/-- The actual coordinate-subset low operator preserves Schwartz functions. -/
def lowSubsetSchwartz (M : ℕ) (k : Fin d → ℤ) (e : Fin j ↪ Fin d)
    (f : 𝓢(Space d, ℂ)) : 𝓢(Space d, ℂ) :=
  partialSchwartz (coordinateInclusion e) (subsetRadii M k e) f

/-- This is exactly the pre-existing `lowSubsetOperator`, on an actual Schwartz representative. -/
theorem lowSubsetSchwartz_toLp (M : ℕ) (k : Fin d → ℤ) (e : Fin j ↪ Fin d)
    (f : 𝓢(Space d, ℂ)) :
    (lowSubsetSchwartz M k e f).toLp 2 =
      lowSubsetOperator M k (Finset.univ.image e) (f.toLp 2) := by
  unfold lowSubsetSchwartz lowSubsetOperator
  rw [partialSchwartz_toLp, partialSymbol_eq_lowSubset]

/-- The low-subset projection is its physical partial convolution, with no Fourier oracle. -/
theorem lowSubsetSchwartz_apply (M : ℕ) (k : Fin d → ℤ) (e : Fin j ↪ Fin d)
    (f : 𝓢(Space d, ℂ)) (x : Space d) :
    lowSubsetSchwartz M k e f x =
      ∫ y, productPhi (subsetRadii M k e) y * f (x - coordinateInclusion e y) :=
  partialSchwartz_apply _ _ _ _

theorem multiplier_sub_symbol (a b : Symbol d) (f : L2 d) :
    multiplier (a - b) f = multiplier a f - multiplier b f := by
  have hn : multiplier (-b) f = -multiplier b f := by
    rw [← neg_one_smul ℂ b, multiplier_smul_symbol, neg_one_smul]
  simpa only [sub_eq_add_neg, hn] using multiplier_add_symbol a (-b) f

/-- The actual high-error operator is the signed sum of low projections of the high remainder. -/
theorem error_operator_expansion (M : ℕ) (k : Fin d → ℤ) (f : L2 d) :
    errorOperator M k f =
      ∑ J ∈ Finset.univ.powerset, (-1 : ℂ) ^ J.card •
        lowSubsetOperator M k J (f - multiplier (∏ i, highSymbol M k i) f) := by
  have hp : (∏ i : Fin d, (1 - lowSymbol M k i)) =
      ∑ J ∈ Finset.univ.powerset, (-1 : ℂ) ^ J.card • lowSubsetSymbol M k J := by
    ext xi
    have h := Finset.prod_sub (fun _ : Fin d => (1 : ℂ)) (fun i => lowSymbol M k i xi) Finset.univ
    simpa [lowSubsetSymbol] using h
  unfold errorOperator errorSymbol
  rw [mul_comm, multiplier_mul, multiplier_sub_symbol, multiplier_one, hp, multiplier_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  exact multiplier_smul_symbol _ _ _

def highRadii (M : ℕ) (k : Fin d → ℤ) : Radii d :=
  ⟨fun i => (2 : ℝ) ^ (k i - (M : ℤ)), fun _ => zpow_pos (by norm_num) _⟩

theorem fullCutoff_highRadii (M : ℕ) (k : Fin d → ℤ) :
    (fullCutoff (highRadii M k)).toBoundedContinuousFunction = ∏ i, highSymbol M k i := by
  ext xi
  simp [fullCutoff_apply, highRadii, highSymbol, FrequencyDecomposition.highCoordinate]

def fullSmoothSchwartz (r : Radii d) (f : 𝓢(Space d, ℂ)) : 𝓢(Space d, ℂ) :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) (productPhiSchwartz r) f

theorem fullSmoothSchwartz_toLp (r : Radii d) (f : 𝓢(Space d, ℂ)) :
    (fullSmoothSchwartz r f).toLp 2 = multiplier (fullCutoff r).toBoundedContinuousFunction
      (f.toLp 2) := by
  have h := (multiplier_schwartz (productPhiSchwartz r) f).symm
  have hg : 𝓕 (productPhiSchwartz r) = fullCutoff r := fourier_fourierInv_eq _
  rw [hg] at h
  exact h

theorem fullSmoothSchwartz_apply (r : Radii d) (f : 𝓢(Space d, ℂ)) (x : Space d) :
    fullSmoothSchwartz r f x = kernelConvolution (productPhi r) f x := by
  unfold fullSmoothSchwartz
  rw [SchwartzMap.convolution_apply]
  change kernelConvolution (productPhiSchwartz r) f x = _
  rw [productPhiSchwartz_eq]

def highRemainderSchwartz (M : ℕ) (k : Fin d → ℤ) (f : 𝓢(Space d, ℂ)) :
    𝓢(Space d, ℂ) := f - fullSmoothSchwartz (highRadii M k) f

theorem highRemainderSchwartz_toLp (M : ℕ) (k : Fin d → ℤ) (f : 𝓢(Space d, ℂ)) :
    (highRemainderSchwartz M k f).toLp 2 volume =
      f.toLp 2 volume - multiplier (∏ i, highSymbol M k i) (f.toLp 2 volume) := by
  change (SchwartzMap.toLpCLM ℂ (E := Space d) ℂ 2 volume)
    (f - fullSmoothSchwartz (highRadii M k) f) = _
  rw [map_sub]
  change f.toLp 2 volume - (fullSmoothSchwartz (highRadii M k) f).toLp 2 volume = _
  rw [fullSmoothSchwartz_toLp, fullCutoff_highRadii]

end StrongSpherical.FourierKernel
