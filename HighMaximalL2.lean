import ErrorMaximalL2
import CoordinateSubsets
import KernelSmoothing

/-! # Physical high-frequency error sums and their L² maximal envelope -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators

namespace StrongSpherical.HighMaximalL2
open ErrorMaximalL2 RectangularMaximal ProductSmoothing ScalarSmoothing CoordinateSubsets

theorem eLpNorm_const_mul_ennreal {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (G : X → ℝ≥0∞) (hG : Measurable G) (c : ℝ≥0∞) :
    eLpNorm (fun x => c * G x) 2 μ = c * eLpNorm G 2 μ := by
  apply (ENNReal.rpow_left_injective (by norm_num : (2 : ℝ) ≠ 0))
  simp only [ENNReal.rpow_two]
  rw [eLpNorm_two_sq_ennreal, mul_pow, eLpNorm_two_sq_ennreal]
  simp_rw [mul_pow]
  exact lintegral_const_mul _ (hG.pow_const 2)

/-- The positive partial Schwartz kernel is controlled on every measurable
extended-valued input, not just norms of complex functions. -/
theorem lintegral_partial_productPhi_le (m j : ℕ) (b : Radii m)
    (G : Space (m + j) → ℝ≥0∞) (hG : Measurable G) (x : Space (m + j)) :
    (∫⁻ u : Space m, ‖productPhi b u‖ₑ * G ((ProductCoordinates.split m j).symm
      ((ProductCoordinates.split m j x).1 - u, (ProductCoordinates.split m j x).2))) ≤
      ENNReal.ofReal (tailConstant ^ m * (16 : ℝ) ^ m) * partialBlockMaximal m j G x := by
  have hm : Measurable (fun u : Space m => ENNReal.ofReal (productWeight b u) *
      G ((ProductCoordinates.split m j).symm
        ((ProductCoordinates.split m j x).1 - u, (ProductCoordinates.split m j x).2))) := by
    apply (ENNReal.measurable_ofReal.comp (continuous_productWeight b).measurable).mul
    exact hG.comp ((ProductCoordinates.split m j).symm.measurable.comp
      ((measurable_const.sub measurable_id).prodMk measurable_const))
  calc
    _ ≤ ∫⁻ u : Space m, ENNReal.ofReal (tailConstant ^ m) *
        (ENNReal.ofReal (productWeight b u) * G ((ProductCoordinates.split m j).symm
          ((ProductCoordinates.split m j x).1 - u, (ProductCoordinates.split m j x).2))) := by
      apply lintegral_mono
      intro u
      have hk : ‖productPhi b u‖ₑ ≤ ENNReal.ofReal (tailConstant ^ m) *
          ENNReal.ofReal (productWeight b u) := by
        rw [← ofReal_norm, ← ENNReal.ofReal_mul (pow_nonneg tailConstant_pos.le m)]
        exact ENNReal.ofReal_le_ofReal (norm_productPhi_le_weight b u)
      simpa only [mul_assoc] using mul_le_mul' hk (le_rfl : G _ ≤ G _)
    _ = ENNReal.ofReal (tailConstant ^ m) * ∫⁻ u : Space m,
        ENNReal.ofReal (productWeight b u) * G ((ProductCoordinates.split m j).symm
          ((ProductCoordinates.split m j x).1 - u, (ProductCoordinates.split m j x).2)) :=
      lintegral_const_mul _ hm
    _ ≤ ENNReal.ofReal (tailConstant ^ m) *
        ((16 : ℝ≥0∞) ^ m * partialBlockMaximal m j G x) :=
      mul_le_mul' le_rfl (lintegral_partialBlockWeight_le m j b G hG x)
    _ = _ := by
      rw [ENNReal.ofReal_mul (pow_nonneg tailConstant_pos.le m),
        ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 16)]
      norm_num
      ring

theorem partialBlockSmoothing_envelope (m j : ℕ) (b : Radii m)
    (g : Space (m + j) → ℂ) (G : Space (m + j) → ℝ≥0∞) (hG : Measurable G)
    (c : ℝ≥0∞) (hg : ∀ x, ‖g x‖ₑ ≤ c * G x) (x : Space (m + j)) :
    ‖partialBlockSmoothing m j b g x‖ₑ ≤
      c * ENNReal.ofReal (tailConstant ^ m * (16 : ℝ) ^ m) * partialBlockMaximal m j G x := by
  let p : Space m → Space (m + j) := fun u => (ProductCoordinates.split m j).symm
    ((ProductCoordinates.split m j x).1 - u, (ProductCoordinates.split m j x).2)
  have hp : Measurable p := (ProductCoordinates.split m j).symm.measurable.comp
    ((measurable_const.sub measurable_id).prodMk measurable_const)
  have hm : Measurable (fun u : Space m => ‖productPhi b u‖ₑ * G (p u)) :=
    (continuous_productPhi b).measurable.enorm.mul (hG.comp hp)
  calc
    _ ≤ ∫⁻ u : Space m, ‖productPhi b u‖ₑ * ‖g (p u)‖ₑ := by
      simpa only [partialBlockSmoothing, enorm_mul, p] using
        enorm_integral_le_lintegral_enorm (fun u : Space m => productPhi b u * g (p u))
    _ ≤ ∫⁻ u : Space m, c * (‖productPhi b u‖ₑ * G (p u)) := by
      apply lintegral_mono
      intro u
      simpa only [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul' le_rfl (hg (p u))
    _ = c * ∫⁻ u : Space m, ‖productPhi b u‖ₑ * G (p u) := lintegral_const_mul _ hm
    _ ≤ c * (ENNReal.ofReal (tailConstant ^ m * (16 : ℝ) ^ m) * partialBlockMaximal m j G x) :=
      mul_le_mul' le_rfl (lintegral_partial_productPhi_le m j b G hG x)
    _ = _ := by ring

def transportedPartialMaximal {m j d : ℕ} (e : Fin (m + j) ≃ Fin d)
    (G : Space d → ℝ≥0∞) (x : Space d) : ℝ≥0∞ :=
  partialBlockMaximal m j (G ∘ coordinatePermutation e) ((coordinatePermutation e).symm x)

theorem transportedPartialMaximal_eq {m j d : ℕ} (e : Fin (m + j) ≃ Fin d)
    (G : Space d → ℝ≥0∞) :
    transportedPartialMaximal e G =
      partialBlockMaximal m j (G ∘ coordinatePermutation e) ∘ coordinatePermutation e.symm := by
  funext x
  simp only [transportedPartialMaximal, Function.comp_apply, coordinatePermutation_symm]

theorem measurable_transportedPartialMaximal {m j d : ℕ} (e : Fin (m + j) ≃ Fin d)
    (G : Space d → ℝ≥0∞) (hG : Measurable G) : Measurable (transportedPartialMaximal e G) := by
  rw [transportedPartialMaximal_eq]
  exact (measurable_partialBlockMaximal m j _
    (hG.comp (coordinatePermutation e).continuous.measurable)).comp
      (coordinatePermutation e.symm).continuous.measurable

theorem eLpNorm_transportedPartialMaximal_le {m j d : ℕ} (e : Fin (m + j) ≃ Fin d)
    (G : Space d → ℝ≥0∞) (hG : Measurable G) :
    eLpNorm (transportedPartialMaximal e G) 2 volume ≤ (8 : ℝ≥0∞) ^ m * eLpNorm G 2 volume := by
  rw [transportedPartialMaximal_eq, eLpNorm_ennreal_comp_permutation]
  have h := eLpNorm_partialBlockMaximal_le m j (G ∘ coordinatePermutation e)
    (hG.comp (coordinatePermutation e).continuous.measurable)
  rw [eLpNorm_ennreal_comp_permutation] at h
  exact h

/-- A finite signed physical high error: smooth each kernel-error output in
its specified coordinate subset, represented by a coordinate permutation. -/
def physicalHighFamily {ι κ : Type*} {d : ℕ} (S : Finset ι) (m j : ι → ℕ)
    (e : ∀ a, Fin (m a + j a) ≃ Fin d) (b : ∀ a, κ → Radii (m a))
    (sign : ι → ℂ) (g : κ → Space d → ℂ) (i : κ) (x : Space d) : ℂ :=
  ∑ a ∈ S, sign a * partialBlockSmoothing (m a) (j a) (b a i)
    (g i ∘ coordinatePermutation (e a)) ((coordinatePermutation (e a)).symm x)

theorem physicalHighFamily_envelope {ι κ : Type*} {d : ℕ}
    (S : Finset ι) (m j : ι → ℕ) (e : ∀ a, Fin (m a + j a) ≃ Fin d)
    (b : ∀ a, κ → Radii (m a)) (sign : ι → ℂ) (hsign : ∀ a ∈ S, ‖sign a‖ ≤ 1)
    (g : κ → Space d → ℂ) (G : Space d → ℝ≥0∞) (hG : Measurable G)
    (c : ℝ≥0∞) (hg : ∀ i x, ‖g i x‖ₑ ≤ c * G x) (x : Space d) :
    (⨆ i, ‖physicalHighFamily S m j e b sign g i x‖ₑ) ≤
      c * ∑ a ∈ S, ENNReal.ofReal (tailConstant ^ m a * (16 : ℝ) ^ m a) *
        transportedPartialMaximal (e a) G x := by
  apply iSup_le
  intro i
  calc
    _ ≤ ∑ a ∈ S, ‖sign a * partialBlockSmoothing (m a) (j a) (b a i)
        (g i ∘ coordinatePermutation (e a)) ((coordinatePermutation (e a)).symm x)‖ₑ :=
      enorm_sum_le _ _
    _ ≤ ∑ a ∈ S, c * ENNReal.ofReal (tailConstant ^ m a * (16 : ℝ) ^ m a) *
        transportedPartialMaximal (e a) G x := by
      apply Finset.sum_le_sum
      intro a ha
      have hs : ‖sign a‖ₑ ≤ 1 := by
        rw [← ofReal_norm]
        simpa using ENNReal.ofReal_le_ofReal (hsign a ha)
      have he := partialBlockSmoothing_envelope (m a) (j a) (b a i)
        (g i ∘ coordinatePermutation (e a)) (G ∘ coordinatePermutation (e a))
        (hG.comp (coordinatePermutation (e a)).continuous.measurable) c
        (fun y => hg i (coordinatePermutation (e a) y)) ((coordinatePermutation (e a)).symm x)
      rw [enorm_mul]
      exact (mul_le_mul' hs he).trans_eq (one_mul _)
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

theorem eLpNorm_physicalHighFamily_le {ι κ : Type*} {d : ℕ}
    (S : Finset ι) (m j : ι → ℕ) (e : ∀ a, Fin (m a + j a) ≃ Fin d)
    (b : ∀ a, κ → Radii (m a)) (sign : ι → ℂ) (hsign : ∀ a ∈ S, ‖sign a‖ ≤ 1)
    (g : κ → Space d → ℂ) (G : Space d → ℝ≥0∞) (hG : Measurable G)
    (c : ℝ≥0∞) (hg : ∀ i x, ‖g i x‖ₑ ≤ c * G x) :
    eLpNorm (fun x => ⨆ i, ‖physicalHighFamily S m j e b sign g i x‖ₑ) 2 volume ≤
      c * (∑ a ∈ S, ENNReal.ofReal (tailConstant ^ m a * (16 : ℝ) ^ m a) * (8 : ℝ≥0∞) ^ m a) *
        eLpNorm G 2 volume := by
  let D : ι → ℝ≥0∞ := fun a => ENNReal.ofReal (tailConstant ^ m a * (16 : ℝ) ^ m a)
  let P : ι → Space d → ℝ≥0∞ := fun a => transportedPartialMaximal (e a) G
  have hP : ∀ a, Measurable (P a) := fun a => measurable_transportedPartialMaximal (e a) G hG
  have hsum : Measurable (fun x => ∑ a ∈ S, D a * P a x) := by
    exact Finset.measurable_sum S (fun a _ => measurable_const.mul (hP a))
  calc
    _ ≤ eLpNorm (fun x => c * ∑ a ∈ S, D a * P a x) 2 volume := by
      apply eLpNorm_mono_enorm
      intro x
      simpa only [enorm_eq_self, D, P] using physicalHighFamily_envelope S m j e b sign hsign g G hG c hg x
    _ = c * eLpNorm (fun x => ∑ a ∈ S, D a * P a x) 2 volume :=
      eLpNorm_const_mul_ennreal volume _ hsum c
    _ ≤ c * ∑ a ∈ S, eLpNorm (fun x => D a * P a x) 2 volume := by
      apply mul_le_mul' le_rfl
      have hh := eLpNorm_sum_le (μ := (volume : Measure (Space d))) (s := S) (f := fun a x => D a * P a x)
        (fun a _ => (measurable_const.mul (hP a)).aestronglyMeasurable) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      have heq : (∑ a ∈ S, fun x : Space d => D a * P a x) =
          fun x => ∑ a ∈ S, D a * P a x := by funext x; simp
      rw [heq] at hh
      exact hh
    _ ≤ c * ∑ a ∈ S, D a * ((8 : ℝ≥0∞) ^ m a * eLpNorm G 2 volume) := by
      apply mul_le_mul' le_rfl
      apply Finset.sum_le_sum
      intro a _
      rw [eLpNorm_const_mul_ennreal volume _ (hP a)]
      exact mul_le_mul' le_rfl (eLpNorm_transportedPartialMaximal_le (e a) G hG)
    _ = _ := by
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      dsimp only [D]
      ring

theorem physicalHigh_kernel_family_bound {ι κ : Type*} {d : ℕ}
    (S : Finset ι) (m j : ι → ℕ) (e : ∀ a, Fin (m a + j a) ≃ Fin d)
    (b : ∀ a, κ → Radii (m a)) (sign : ι → ℂ) (hsign : ∀ a ∈ S, ‖sign a‖ ≤ 1)
    (H : κ → Space d → ℂ) (rho : κ → Radii d) (C : ℝ) (hC : 0 ≤ C)
    (hH : ∀ i y, ‖H i y‖ ≤ C * productWeight (rho i) y)
    (f : Space d → ℂ) (hf : Measurable f) :
    eLpNorm (fun x => ⨆ i, ‖physicalHighFamily S m j e b sign
      (fun i => kernelConvolution (H i) f) i x‖ₑ) 2 volume ≤
      ENNReal.ofReal (C * (16 : ℝ) ^ d) *
        (∑ a ∈ S, ENNReal.ofReal (tailConstant ^ m a * (16 : ℝ) ^ m a) * (8 : ℝ≥0∞) ^ m a) *
          (8 : ℝ≥0∞) ^ d * eLpNorm f 2 volume := by
  let G : Space d → ℝ≥0∞ := controllingMaximal d (fun y => ‖f y‖ₑ)
  have hG : Measurable G := measurable_controllingMaximal d _ hf.enorm
  have hbound := eLpNorm_physicalHighFamily_le S m j e b sign hsign
    (fun i => kernelConvolution (H i) f) G hG (ENNReal.ofReal (C * (16 : ℝ) ^ d))
    (fun i x => kernelConvolution_le_weight (H i) (rho i) C hC (hH i) f hf x)
  have hN := eLpNorm_controllingMaximal_le d (fun y => ‖f y‖ₑ) hf.enorm
  rw [eLpNorm_enorm] at hN
  apply hbound.trans
  have hh : ENNReal.ofReal (C * (16 : ℝ) ^ d) *
      (∑ a ∈ S, ENNReal.ofReal (tailConstant ^ m a * (16 : ℝ) ^ m a) * (8 : ℝ≥0∞) ^ m a) *
        eLpNorm G 2 volume ≤ ENNReal.ofReal (C * (16 : ℝ) ^ d) *
      (∑ a ∈ S, ENNReal.ofReal (tailConstant ^ m a * (16 : ℝ) ^ m a) * (8 : ℝ≥0∞) ^ m a) *
        ((8 : ℝ≥0∞) ^ d * eLpNorm f 2 volume) := mul_le_mul' le_rfl hN
  simpa only [mul_assoc] using hh

def smallScaleErrorKernel {d : ℕ} (K : Space d → ℂ) (r a : Radii d) : Space d → ℂ :=
  fun y => dilatedKernel K r y - kernelConvolution (dilatedKernel K r) (productPhi a) y

set_option maxHeartbeats 1000000 in
/-- The physical high-frequency maximal estimate for the actual C¹ kernel
error. The factor epsilon*B is proved from the true smoothing error (5.20). -/
theorem exists_physicalHigh_smallScale_bound {ι κ : Type*} (d : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (S : Finset ι) (m j : ι → ℕ) (e : ∀ a, Fin (m a + j a) ≃ Fin d)
    (sign : ι → ℂ) (hsign : ∀ a ∈ S, ‖sign a‖ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : Space d → ℂ, Differentiable ℝ K →
      Function.support K ⊆ MarginalEnergy.coordinateBox d R →
      ∀ B : ℝ, (∀ x, ‖K x‖ ≤ B) → (∀ x, ‖fderiv ℝ K x‖ ≤ B) →
      ∀ (r a : κ → Radii d) (b : ∀ q, κ → Radii (m q)),
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ 1 →
      (∀ i q, (a i).1 q / (r i).1 q ≤ epsilon) →
      ∀ f : Space d → ℂ, Measurable f →
      eLpNorm (fun x => ⨆ i, ‖physicalHighFamily S m j e b sign
        (fun i => kernelConvolution (smallScaleErrorKernel K (r i) (a i)) f) i x‖ₑ) 2 volume ≤
          ENNReal.ofReal (C * epsilon * B) *
            (∑ q ∈ S, ENNReal.ofReal (tailConstant ^ m q * (16 : ℝ) ^ m q) * (8 : ℝ≥0∞) ^ m q) *
              eLpNorm f 2 volume := by
  obtain ⟨C0, hC0, hrow⟩ := KernelSmoothing.exists_small_scale_kernel_bound d R hR
  let C : ℝ := C0 * (16 : ℝ) ^ d * (8 : ℝ) ^ d
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro K hK hs B hb hd r a b epsilon heps0 heps hscale f hf
  have hB : 0 ≤ B := (norm_nonneg (K 0)).trans (hb 0)
  have hCB : 0 ≤ C0 * epsilon * B := by positivity
  have h := physicalHigh_kernel_family_bound S m j e b sign hsign
    (fun i => smallScaleErrorKernel K (r i) (a i)) r (C0 * epsilon * B) hCB
    (fun i y => hrow K hK hs B hb hd (r i) (a i) epsilon heps0 heps (hscale i) y) f hf
  have hc : ENNReal.ofReal (C * epsilon * B) =
      ENNReal.ofReal ((C0 * epsilon * B) * (16 : ℝ) ^ d) * (8 : ℝ≥0∞) ^ d := by
    rw [show C * epsilon * B = ((C0 * epsilon * B) * (16 : ℝ) ^ d) * (8 : ℝ) ^ d by
      dsimp [C]
      ring,
      ENNReal.ofReal_mul (mul_nonneg hCB (pow_nonneg (by norm_num) d)),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 8)]
    norm_num
  rw [hc]
  exact h.trans_eq (by ring)

set_option maxHeartbeats 1000000 in
/-- Absorbing the finite coordinate-subset pattern gives the usual high-piece
estimate C*epsilon*B. For the powerset pattern, C depends only on d and R. -/
theorem exists_physicalHigh_smallScale_L2 {ι κ : Type*} (d : ℕ) (R : ℝ) (hR : 1 ≤ R)
    (S : Finset ι) (m j : ι → ℕ) (e : ∀ a, Fin (m a + j a) ≃ Fin d)
    (sign : ι → ℂ) (hsign : ∀ a ∈ S, ‖sign a‖ ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ K : Space d → ℂ, Differentiable ℝ K →
      Function.support K ⊆ MarginalEnergy.coordinateBox d R →
      ∀ B : ℝ, (∀ x, ‖K x‖ ≤ B) → (∀ x, ‖fderiv ℝ K x‖ ≤ B) →
      ∀ (r a : κ → Radii d) (b : ∀ q, κ → Radii (m q)),
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ 1 →
      (∀ i q, (a i).1 q / (r i).1 q ≤ epsilon) →
      ∀ f : Space d → ℂ, Measurable f →
      eLpNorm (fun x => ⨆ i, ‖physicalHighFamily S m j e b sign
        (fun i => kernelConvolution (smallScaleErrorKernel K (r i) (a i)) f) i x‖ₑ) 2 volume ≤
          ENNReal.ofReal (C * epsilon * B) * eLpNorm f 2 volume := by
  obtain ⟨C0, hC0, hbound⟩ := exists_physicalHigh_smallScale_bound (κ := κ) d R hR S m j e sign hsign
  let D : ℝ≥0∞ := ∑ q ∈ S,
    ENNReal.ofReal (tailConstant ^ m q * (16 : ℝ) ^ m q) * (8 : ℝ≥0∞) ^ m q
  have hD : D ≠ ∞ := by
    apply ENNReal.sum_ne_top.mpr
    intro q _
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.pow_lt_top (by norm_num : (8 : ℝ≥0∞) < ∞)).ne
  have hDle : D ≤ ENNReal.ofReal (D.toReal + 1) := by
    calc
      D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hD).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
  let C : ℝ := C0 * (D.toReal + 1)
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro K hK hs B hb hd r a b epsilon heps0 heps hscale f hf
  have hB : 0 ≤ B := (norm_nonneg (K 0)).trans (hb 0)
  have hreal : 0 ≤ C0 * epsilon * B := by positivity
  have h := hbound K hK hs B hb hd r a b epsilon heps0 heps hscale f hf
  calc
    _ ≤ (ENNReal.ofReal (C0 * epsilon * B) * D) * eLpNorm f 2 volume := h
    _ ≤ (ENNReal.ofReal (C0 * epsilon * B) * ENNReal.ofReal (D.toReal + 1)) *
        eLpNorm f 2 volume := mul_le_mul' (mul_le_mul' le_rfl hDle) le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_mul hreal]
      congr 2
      dsimp [C]
      ring

end StrongSpherical.HighMaximalL2
