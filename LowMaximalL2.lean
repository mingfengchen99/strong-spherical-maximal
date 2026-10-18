import MarginalSmoothing
import MarginalFiberL2
import ErrorMaximalL2
import ConvolutionSmoothing

/-! # Actual low-frequency maximal estimates from lower-dimensional strong estimates -/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Topology SchwartzMap
namespace StrongSpherical.LowMaximalL2
open ProductCoordinates CoordinateMarginals MarginalLocalEstimate
open ProductSmoothing MarginalSmoothing RectangularMaximal ErrorMaximalL2
variable {m j : ℕ}

def lastBlockMaximal (m j : ℕ) (F : Space (m + j) → ℝ≥0∞)
    (x : Space (m + j)) : ℝ≥0∞ :=
  controllingMaximal j (fun z => F ((split m j).symm ((split m j x).1, z))) (split m j x).2

theorem measurable_lastBlockMaximal (m j : ℕ) (F : Space (m + j) → ℝ≥0∞)
    (hF : Measurable F) : Measurable (lastBlockMaximal m j F) := by
  have hH : Measurable (fun p : Space m × Space j => F ((split m j).symm p)) :=
    hF.comp (split m j).symm.measurable
  have h := measurable_controllingMaximal_with_param j _ hH
  exact h.comp (split m j).measurable

theorem lastBlockMaximal_energy (m j : ℕ) (F : Space (m + j) → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ x, lastBlockMaximal m j F x ^ 2) ≤ (40 : ℝ≥0∞) ^ j * ∫⁻ x, F x ^ 2 := by
  have hm := measurable_lastBlockMaximal m j F hF
  have hH : Measurable (fun p : Space m × Space j => F ((split m j).symm p)) :=
    hF.comp (split m j).symm.measurable
  calc
    _ = ∫⁻ u : Space m, ∫⁻ z : Space j,
        controllingMaximal j (fun z => F ((split m j).symm (u, z))) z ^ 2 := by
      simpa only [lastBlockMaximal, MeasurableEquiv.apply_symm_apply] using
        lintegral_split (fun x => lastBlockMaximal m j F x ^ 2) (hm.pow_const 2)
    _ ≤ ∫⁻ u : Space m, (40 : ℝ≥0∞) ^ j * ∫⁻ z : Space j, F ((split m j).symm (u, z)) ^ 2 := by
      apply lintegral_mono
      intro u
      exact controllingMaximal_L2 j _ (hH.comp (measurable_const.prodMk measurable_id))
    _ = (40 : ℝ≥0∞) ^ j * ∫⁻ u : Space m, ∫⁻ z : Space j, F ((split m j).symm (u, z)) ^ 2 :=
      lintegral_const_mul _ (hH.pow_const 2).lintegral_prod_right
    _ = _ := by rw [← lintegral_split _ (hF.pow_const 2)]

theorem eLpNorm_lastBlockMaximal_le (m j : ℕ) (F : Space (m + j) → ℝ≥0∞)
    (hF : Measurable F) :
    eLpNorm (lastBlockMaximal m j F) 2 volume ≤ (8 : ℝ≥0∞) ^ j * eLpNorm F 2 volume := by
  apply (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [mul_pow, MarginalLocalEstimate.eLpNorm_two_sq_ennreal,
    MarginalLocalEstimate.eLpNorm_two_sq_ennreal]
  have hc : (40 : ℝ≥0∞) ^ j ≤ ((8 : ℝ≥0∞) ^ j) ^ 2 := by
    rw [← pow_mul, mul_comm j 2, pow_mul]
    exact pow_le_pow_left' (by norm_num : (40 : ℝ≥0∞) ≤ 8 ^ 2) j
  exact (lastBlockMaximal_energy m j F hF).trans (mul_le_mul' hc le_rfl)

def tensorKernel (H : Space m → ℂ) (r : Radii m) (b : Radii j)
    (v : Space (m + j)) : ℂ :=
  dilatedKernel H r (split m j v).1 * productPhi b (split m j v).2

theorem integrable_dilatedKernel (H : Space m → ℂ) (hH : Continuous H)
    (hc : HasCompactSupport H) (r : Radii m) : Integrable (dilatedKernel H r) :=
  (GenericKernelRegularity.continuous_fixed_kernel H hH r).integrable_of_hasCompactSupport
    ((hc.comp_homeomorph (inverseDilationHomeomorph r)).mul_left)

theorem integrable_tensorKernel (H : Space m → ℂ) (hH : Continuous H)
    (hc : HasCompactSupport H) (r : Radii m) (b : Radii j) : Integrable (tensorKernel H r b) := by
  have hi := (integrable_dilatedKernel H hH hc r).mul_prod (integrable_productPhi b)
  exact ((measurePreserving_split m j).integrable_comp_emb (split m j).measurableEmbedding).2 hi

theorem integrable_tensor_test (H : Space m → ℂ) (hH : Continuous H)
    (hc : HasCompactSupport H) (r : Radii m) (b : Radii j)
    (f : 𝓢(Space (m + j), ℂ)) (x : Space (m + j)) :
    Integrable (fun p : Space m × Space j =>
      (dilatedKernel H r p.1 * productPhi b p.2) * f (x - (split m j).symm p))
      ((volume : Measure (Space m)).prod volume) := by
  apply ((integrable_dilatedKernel H hH hc r).mul_prod (integrable_productPhi b)).mul_bdd
    ((f.continuous.comp (continuous_const.sub (continuous_split_symm m j))).aestronglyMeasurable)
  filter_upwards with p
  exact SchwartzMap.norm_le_seminorm ℝ f _

theorem tensor_convolution_eq (H : Space m → ℂ) (hH : Continuous H)
    (hc : HasCompactSupport H) (r : Radii m) (b : Radii j)
    (f : 𝓢(Space (m + j), ℂ)) (x : Space (m + j)) :
    kernelConvolution (tensorKernel H r b) f x = ∫ z : Space j, productPhi b z *
      kernelConvolution (dilatedKernel H r)
        (fun u => f ((split m j).symm (u, (split m j x).2 - z))) (split m j x).1 := by
  rw [kernelConvolution_eq_product]
  simp only [tensorKernel, MeasurableEquiv.apply_symm_apply, split_symm_sub,
    MeasurableEquiv.symm_apply_apply]
  rw [integral_prod_symm _ (integrable_tensor_test H hH hc r b f x)]
  apply integral_congr_ae
  filter_upwards with z
  rw [kernelConvolution_eq_integral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  have he : x - (split m j).symm (u, z) =
      (split m j).symm ((split m j x).1 - u, (split m j x).2 - z) := by
    apply (split m j).injective
    simp only [split_sub, MeasurableEquiv.apply_symm_apply]
    rfl
  rw [he]
  ring

theorem tensor_convolution_le (H : Space m → ℂ) (hH : Continuous H)
    (hc : HasCompactSupport H) (r : Radii m) (b : Radii j)
    (f : 𝓢(Space (m + j), ℂ))
    (hG : Measurable (MarginalFiberL2.coordinateFiberMaximal H f)) (x : Space (m + j)) :
    ‖kernelConvolution (tensorKernel H r b) f x‖ₑ ≤
      ENNReal.ofReal (ScalarSmoothing.tailConstant ^ j * (16 : ℝ) ^ j) *
        lastBlockMaximal m j (MarginalFiberL2.coordinateFiberMaximal H f) x := by
  let G := MarginalFiberL2.coordinateFiberMaximal H f
  have hGs : Measurable (fun z : Space j => G ((split m j).symm ((split m j x).1, z))) :=
    hG.comp ((split m j).symm.measurable.comp (measurable_const.prodMk measurable_id))
  have hw : Measurable (fun z : Space j => ENNReal.ofReal (productWeight b z) *
      G ((split m j).symm ((split m j x).1, (split m j x).2 - z))) :=
    (ENNReal.measurable_ofReal.comp (continuous_productWeight b).measurable).mul
      (hGs.comp (measurable_const.sub measurable_id))
  calc
    _ ≤ ∫⁻ z : Space j, ‖productPhi b z‖ₑ *
        ‖kernelConvolution (dilatedKernel H r)
          (fun u => f ((split m j).symm (u, (split m j x).2 - z))) (split m j x).1‖ₑ := by
      rw [tensor_convolution_eq H hH hc r b f x]
      simpa only [enorm_mul] using enorm_integral_le_lintegral_enorm
        (fun z : Space j => productPhi b z * kernelConvolution (dilatedKernel H r)
          (fun u => f ((split m j).symm (u, (split m j x).2 - z))) (split m j x).1)
    _ ≤ ∫⁻ z : Space j, ENNReal.ofReal (ScalarSmoothing.tailConstant ^ j) *
        (ENNReal.ofReal (productWeight b z) *
          G ((split m j).symm ((split m j x).1, (split m j x).2 - z))) := by
      apply lintegral_mono
      intro z
      have hphi : ‖productPhi b z‖ₑ ≤ ENNReal.ofReal (ScalarSmoothing.tailConstant ^ j) *
          ENNReal.ofReal (productWeight b z) := by
        rw [← ofReal_norm, ← ENNReal.ofReal_mul (pow_nonneg ScalarSmoothing.tailConstant_pos.le j)]
        exact ENNReal.ofReal_le_ofReal (norm_productPhi_le_weight b z)
      have hconv : ‖kernelConvolution (dilatedKernel H r)
          (fun u => f ((split m j).symm (u, (split m j x).2 - z))) (split m j x).1‖ₑ ≤
          G ((split m j).symm ((split m j x).1, (split m j x).2 - z)) := by
        dsimp only [G, MarginalFiberL2.coordinateFiberMaximal]
        rw [MeasurableEquiv.apply_symm_apply]
        change ‖kernelConvolution (dilatedKernel H r)
          (fun u => f ((split m j).symm (u, (split m j x).2 - z))) (split m j x).1‖ₑ ≤
          strongKernelMaximal H
            (fun u => f ((split m j).symm (u, (split m j x).2 - z))) (split m j x).1
        exact le_maximalOver univ
          (fun t => kernelConvolution (dilatedKernel H t)
            (fun u => f ((split m j).symm (u, (split m j x).2 - z))))
          (split m j x).1 (mem_univ r)
      simpa only [mul_assoc] using mul_le_mul' hphi hconv
    _ = ENNReal.ofReal (ScalarSmoothing.tailConstant ^ j) * ∫⁻ z : Space j,
        ENNReal.ofReal (productWeight b z) *
          G ((split m j).symm ((split m j x).1, (split m j x).2 - z)) := lintegral_const_mul _ hw
    _ ≤ ENNReal.ofReal (ScalarSmoothing.tailConstant ^ j) * ((16 : ℝ≥0∞) ^ j *
        controllingMaximal j (fun z => G ((split m j).symm ((split m j x).1, z))) (split m j x).2) :=
      mul_le_mul' le_rfl (lintegral_productWeight_le j b _ hGs (split m j x).2)
    _ = _ := by
      rw [ENNReal.ofReal_mul (pow_nonneg ScalarSmoothing.tailConstant_pos.le j),
        ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 16)]
      norm_num only [ENNReal.ofReal_ofNat]
      simp only [lastBlockMaximal, G, mul_assoc]

def lastInclusion (m j : ℕ) : Space j →L[ℝ] Space (m + j) :=
  (EuclideanSpace.finAddEquivProd (𝕜 := ℝ) (n := m) (m := j)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.inr ℝ (Space m) (Space j))

theorem lastInclusion_apply (z : Space j) : lastInclusion m j z = (split m j).symm (0, z) := rfl

def smoothedKernel (K : Space (m + j) → ℂ) (r : Radii m) (s b : Radii j)
    (x : Space (m + j)) : ℂ :=
  partialSmoothedKernel (K ∘ (split m j).symm) r s b (split m j x).1 (split m j x).2

theorem smoothedKernel_eq_partialConvolution (K : Space (m + j) → ℂ)
    (r : Radii m) (s b : Radii j) :
    smoothedKernel K r s b = ConvolutionSmoothing.partialConvolution
      (lastInclusion m j) b (dilatedKernel K (joinRadii r s)) := by
  funext x
  unfold smoothedKernel partialSmoothedKernel ConvolutionSmoothing.partialConvolution
  simp_rw [blockDilatedKernel_eq_actual]
  have he : ∀ z : Space j, x - lastInclusion m j z =
      (split m j).symm ((split m j x).1, (split m j x).2 - z) := by
    intro z
    rw [lastInclusion_apply]
    apply (split m j).injective
    simp only [split_sub, MeasurableEquiv.apply_symm_apply]
    simp only [Prod.sub_def, sub_zero]
  simp_rw [he]
  have h := integral_sub_left_eq_self
    (fun z : Space j => dilatedKernel K (joinRadii r s)
      ((split m j).symm ((split m j x).1, z)) * productPhi b ((split m j x).2 - z))
    volume (split m j x).2
  simpa only [sub_sub_cancel, mul_comm] using h.symm

theorem integrable_smoothedKernel (K : Space (m + j) → ℂ) (hK : Continuous K)
    (hc : HasCompactSupport K) (r : Radii m) (s b : Radii j) :
    Integrable (smoothedKernel K r s b) := by
  have hKr := GenericKernelRegularity.continuous_fixed_kernel K hK (joinRadii r s)
  have hKi := integrable_dilatedKernel K hK hc (joinRadii r s)
  rw [smoothedKernel_eq_partialConvolution]
  exact (ConvolutionSmoothing.integrable_partial_kernel_double _ hKr hKi (lastInclusion m j) b).integral_prod_right

def errorKernel (K : Space (m + j) → ℂ) (r : Radii m) (s b : Radii j)
    (x : Space (m + j)) : ℂ :=
  smoothedKernel K r s b x - tensorKernel (marginalKernel K) r b x

theorem errorKernel_eq (K : Space (m + j) → ℂ) (r : Radii m) (s b : Radii j)
    (x : Space (m + j)) :
    errorKernel K r s b x = marginalSmoothingError (K ∘ (split m j).symm)
      r s b (split m j x).1 (split m j x).2 := rfl

theorem productWeight_join (r : Radii m) (b : Radii j) (x : Space (m + j)) :
    productWeight (joinRadii r b) x = productWeight r (split m j x).1 * productWeight b (split m j x).2 := by
  unfold productWeight
  rw [Fin.prod_univ_add]
  simp only [joinRadii_castAdd, joinRadii_natAdd, split_fst, split_snd]

theorem convolution_smoothed_eq_add (K : Space (m + j) → ℂ) (hK : Continuous K)
    (R : ℝ) (hs : Function.support K ⊆ MarginalEnergy.coordinateBox (m + j) R)
    (r : Radii m) (s b : Radii j) (f : 𝓢(Space (m + j), ℂ)) (x : Space (m + j)) :
    kernelConvolution (smoothedKernel K r s b) f x =
      kernelConvolution (tensorKernel (marginalKernel K) r b) f x +
      kernelConvolution (errorKernel K r s b) f x := by
  have hKm := continuous_marginalKernel K hK R hs
  have hcKm : HasCompactSupport (marginalKernel K) :=
    CoordinateMarginals.hasCompactSupport_marginal _
      (hasCompactSupport_product_kernel K (hasCompactSupport_of_box K R hs))
  have hS := integrable_smoothedKernel K hK (hasCompactSupport_of_box K R hs) r s b
  have hT := integrable_tensorKernel _ hKm hcKm r b
  have hE : Integrable (errorKernel K r s b) := hS.sub hT
  have hiT := ConvolutionSmoothing.integrable_convolution_schwartz _ hT f x
  have hiE := ConvolutionSmoothing.integrable_convolution_schwartz _ hE f x
  rw [kernelConvolution_eq_integral, kernelConvolution_eq_integral, kernelConvolution_eq_integral,
    ← integral_add hiT hiE]
  apply integral_congr_ae
  filter_upwards with y
  unfold errorKernel
  ring

abbrev LowParameters (m j : ℕ) (epsilon : ℝ) :=
  {p : Radii m × (Radii j × Radii j) // ∀ i, p.2.1.1 i / p.2.2.1 i ≤ 2 * epsilon}

def lowMaximal (K : Space (m + j) → ℂ) (epsilon : ℝ) (f : Space (m + j) → ℂ)
    (x : Space (m + j)) : ℝ≥0∞ :=
  ⨆ p : LowParameters m j epsilon,
    ‖kernelConvolution (smoothedKernel K p.1.1 p.1.2.1 p.1.2.2) f x‖ₑ

theorem eLpNorm_ennreal_const_mul_le (c : ℝ≥0∞) (F : Space (m + j) → ℝ≥0∞)
    (hF : Measurable F) :
    eLpNorm (fun x => c * F x) 2 volume ≤ c * eLpNorm F 2 volume := by
  apply (ENNReal.pow_le_pow_left_iff (by norm_num : (2 : ℕ) ≠ 0)).mp
  rw [MarginalLocalEstimate.eLpNorm_two_sq_ennreal, mul_pow,
    MarginalLocalEstimate.eLpNorm_two_sq_ennreal]
  simp_rw [mul_pow]
  exact le_of_eq (lintegral_const_mul _ (hF.pow_const 2))

/-- The genuine low-frequency estimate: its lower-dimensional hypothesis
concerns the actual marginal strong maximal operator. -/
theorem exists_lowMaximal_bound (m j : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Space (m + j) → ℂ), Continuous K →
      Function.support K ⊆ MarginalEnergy.coordinateBox (m + j) R →
      ∀ B : ℝ, (∀ x, ‖K x‖ ≤ B) →
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ 1 →
      ∀ D : ℝ≥0∞,
      (∀ g : Space m → ℂ, MemLp g 2 volume →
        eLpNorm (strongKernelMaximal (marginalKernel K) g) 2 volume ≤ D * eLpNorm g 2 volume) →
      ∀ f : 𝓢(Space (m + j), ℂ),
      eLpNorm (lowMaximal K epsilon f) 2 volume ≤
        ENNReal.ofReal C * (D + ENNReal.ofReal (epsilon * B)) * eLpNorm f 2 volume := by
  obtain ⟨Ce, hCe, he⟩ := exists_marginalSmoothingError_bound m j R hR
  let T : ℝ := ScalarSmoothing.tailConstant ^ j * (16 : ℝ) ^ j
  let a : ℝ := T * (8 : ℝ) ^ j
  let b : ℝ := Ce * (16 : ℝ) ^ (m + j) * (8 : ℝ) ^ (m + j)
  let C : ℝ := a + b + 1
  have hT : 0 ≤ T := mul_nonneg (pow_nonneg ScalarSmoothing.tailConstant_pos.le _) (by positivity)
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro K hK hs B hB epsilon heps heps1 D hIH f
  have hB0 : 0 ≤ B := (norm_nonneg (K 0)).trans (hB 0)
  have hKm := continuous_marginalKernel K hK R hs
  have hsKm := marginalKernel_support K R hs
  have hcKm : HasCompactSupport (marginalKernel K) :=
    CoordinateMarginals.hasCompactSupport_marginal _
      (hasCompactSupport_product_kernel K (hasCompactSupport_of_box K R hs))
  let G := MarginalFiberL2.coordinateFiberMaximal (marginalKernel K) f
  obtain ⟨hG, hGnorm⟩ := MarginalFiberL2.coordinateFiberMaximal_L2
    (marginalKernel K) hKm R hR hsKm D hIH f f.continuous (f.memLp 2 volume)
  let MG := lastBlockMaximal m j G
  let MF := controllingMaximal (m + j) (fun x => ‖f x‖ₑ)
  let cE : ℝ≥0∞ := ENNReal.ofReal (Ce * epsilon * B * (16 : ℝ) ^ (m + j))
  let cT : ℝ≥0∞ := ENNReal.ofReal T
  have hMG : Measurable MG := measurable_lastBlockMaximal m j G hG
  have hMF : Measurable MF := measurable_controllingMaximal (m + j) _ f.continuous.measurable.enorm
  have hMGnorm : eLpNorm MG 2 volume ≤ (8 : ℝ≥0∞) ^ j * (D * eLpNorm f 2 volume) :=
    (eLpNorm_lastBlockMaximal_le m j G hG).trans (mul_le_mul' le_rfl hGnorm)
  have hMFnorm : eLpNorm MF 2 volume ≤ (8 : ℝ≥0∞) ^ (m + j) * eLpNorm f 2 volume := by
    simpa only [MF, eLpNorm_enorm] using
      eLpNorm_controllingMaximal_le (m + j) (fun x => ‖f x‖ₑ) f.continuous.measurable.enorm
  have hErr : ∀ p : LowParameters m j epsilon, ∀ v : Space (m + j),
      ‖errorKernel K p.1.1 p.1.2.1 p.1.2.2 v‖ ≤
        (Ce * epsilon * B) * productWeight (joinRadii p.1.1 p.1.2.2) v := by
    intro p v
    have h := he (K ∘ (split m j).symm) (continuous_product_kernel K hK)
      (product_kernel_support K R hs) B (fun _ => hB _)
      epsilon heps heps1 p.1.1 p.1.2.1 p.1.2.2 p.2 (split m j v).1 (split m j v).2
    simpa only [errorKernel_eq, productWeight_join, mul_assoc] using h
  have hLow : ∀ x, lowMaximal K epsilon f x ≤ cT * MG x + cE * MF x := by
    intro x
    apply iSup_le
    intro p
    rw [convolution_smoothed_eq_add K hK R hs]
    apply (enorm_add_le _ _).trans
    apply add_le_add
    · exact tensor_convolution_le _ hKm hcKm p.1.1 p.1.2.2 f hG x
    · exact kernelConvolution_le_weight _ (joinRadii p.1.1 p.1.2.2)
        (Ce * epsilon * B) (by positivity) (hErr p) f f.continuous.measurable x
  have hAM : Measurable (fun x => cT * MG x) := measurable_const.mul hMG
  have hBM : Measurable (fun x => cE * MF x) := measurable_const.mul hMF
  have hNorm : eLpNorm (lowMaximal K epsilon f) 2 volume ≤
      cT * ((8 : ℝ≥0∞) ^ j * (D * eLpNorm f 2 volume)) +
        cE * ((8 : ℝ≥0∞) ^ (m + j) * eLpNorm f 2 volume) := by
    calc
      _ ≤ eLpNorm ((fun x => cT * MG x) + (fun x => cE * MF x)) 2 volume := by
        apply eLpNorm_mono_enorm
        intro x
        simpa only [Pi.add_apply, enorm_eq_self] using hLow x
      _ ≤ eLpNorm (fun x => cT * MG x) 2 volume + eLpNorm (fun x => cE * MF x) 2 volume :=
        eLpNorm_add_le hAM.aestronglyMeasurable hBM.aestronglyMeasurable (by norm_num)
      _ ≤ cT * eLpNorm MG 2 volume + cE * eLpNorm MF 2 volume :=
        add_le_add (eLpNorm_ennreal_const_mul_le cT MG hMG) (eLpNorm_ennreal_const_mul_le cE MF hMF)
      _ ≤ _ := add_le_add (mul_le_mul' le_rfl hMGnorm) (mul_le_mul' le_rfl hMFnorm)
  have he8 : ∀ k : ℕ, ENNReal.ofReal ((8 : ℝ) ^ k) = (8 : ℝ≥0∞) ^ k := by
    intro k
    rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num
  have hFirst : cT * (8 : ℝ≥0∞) ^ j ≤ ENNReal.ofReal C := by
    calc
      _ = ENNReal.ofReal a := by rw [← he8, ← ENNReal.ofReal_mul hT]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by dsimp [C]; linarith)
  have hSecond : cE * (8 : ℝ≥0∞) ^ (m + j) ≤ ENNReal.ofReal C * ENNReal.ofReal (epsilon * B) := by
    calc
      _ = ENNReal.ofReal ((Ce * epsilon * B * (16 : ℝ) ^ (m + j)) * (8 : ℝ) ^ (m + j)) := by
        rw [ENNReal.ofReal_mul (by positivity), he8]
      _ ≤ ENNReal.ofReal (C * (epsilon * B)) := by
        apply ENNReal.ofReal_le_ofReal
        have hbc : b ≤ C := by dsimp [C]; linarith
        have h := mul_le_mul_of_nonneg_right hbc (mul_nonneg heps hB0)
        simpa only [b, mul_assoc, mul_comm, mul_left_comm] using h
      _ = _ := ENNReal.ofReal_mul hC.le
  apply hNorm.trans
  calc
    _ = (cT * (8 : ℝ≥0∞) ^ j * D + cE * (8 : ℝ≥0∞) ^ (m + j)) * eLpNorm f 2 volume := by ring
    _ ≤ (ENNReal.ofReal C * D + ENNReal.ofReal C * ENNReal.ofReal (epsilon * B)) * eLpNorm f 2 volume :=
      mul_le_mul' (add_le_add (mul_le_mul' hFirst le_rfl) hSecond) le_rfl
    _ = _ := by ring

end StrongSpherical.LowMaximalL2
