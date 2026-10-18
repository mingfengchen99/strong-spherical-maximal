import KernelTruncation
import MaximalChebyshev
import InterpolationLayercake
import InterpolationNorm

/-! # Real-variable interpolation between L² and L∞ for actual kernel maxima -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace StrongSpherical.KernelInterpolationAboveTwo
open KernelTruncation
set_option maxHeartbeats 1000000
variable {n : ℕ}

def thresholdScale (B : ℝ) : ℝ := 1 / (2 * B)
def energyConstant (p : ℝ) : ℝ := p * 4 * (2 : ℝ) ^ (p - 2) / (p - 2)
def normConstant (p : ℝ) : ℝ := energyConstant p ^ (1 / p)

theorem thresholdScale_pos (B : ℝ) (hB : 0 < B) : 0 < thresholdScale B := by
  unfold thresholdScale
  positivity

theorem energyConstant_pos (p : ℝ) (hp : 2 < p) : 0 < energyConstant p := by
  unfold energyConstant
  apply div_pos
  · exact mul_pos (mul_pos (by linarith) (by norm_num)) (Real.rpow_pos_of_pos (by norm_num) _)
  · linarith

theorem normConstant_pos (p : ℝ) (hp : 2 < p) : 0 < normConstant p :=
  Real.rpow_pos_of_pos (energyConstant_pos p hp) _

private theorem threshold_coefficient (p A B : ℝ) (hB : 0 < B) :
    (p * (4 * A ^ 2)) * (thresholdScale B ^ (-(p - 2)) / (p - 2)) =
      energyConstant p * A ^ 2 * B ^ (p - 2) := by
  have h : thresholdScale B ^ (-(p - 2)) = (2 : ℝ) ^ (p - 2) * B ^ (p - 2) := by
    unfold thresholdScale
    rw [one_div, ← Real.rpow_neg_eq_inv_rpow, neg_neg,
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hB.le]
  rw [h]
  unfold energyConstant
  ring

private theorem weight_coefficient (p A t : ℝ) (ht : 0 < t) :
    (A ^ (2 : ℝ) * (t / 2) ^ (-(2 : ℝ))) * t ^ (p - 1) =
      (4 * A ^ 2) * t ^ (p - 2 - 1) := by
  have hpow : t ^ (p - 1) = t ^ (p - 2 - 1) * t ^ (2 : ℕ) := by
    rw [← Real.rpow_two, ← Real.rpow_add ht]
    congr 1
    ring
  rw [Real.rpow_two, Real.rpow_neg (by positivity : 0 ≤ t / 2), Real.rpow_two, hpow]
  field_simp
  ring

/-- A low truncation at t/(2B) contributes at most t/2 pointwise, so the
actual output tail is contained in the tail of the actual high convolution. -/
theorem measure_tail_le_high (K : Space n → ℂ) (hK : Continuous K)
    (hc : HasCompactSupport K) (p : ℝ) (hp : 2 < p)
    (A : ℝ) (hA : 0 < A)
    (hTwo : ∀ g : Space n → ℂ, MemLp g 2 volume →
      eLpNorm (strongKernelMaximal K g) 2 volume ≤ ENNReal.ofReal A * eLpNorm g 2 volume)
    (B : ℝ) (hB : 0 < B)
    (hInfinity : ∀ g : Space n → ℂ, MemLp g ∞ volume → ∀ x,
      strongKernelMaximal K g x ≤ ENNReal.ofReal B * eLpNorm g ∞ volume)
    (f : Space n → ℂ) (hmeas : Measurable f) (hf : MemLp f (ENNReal.ofReal p) volume)
    (t : ℝ) (ht : 0 < t) :
    volume {x | ENNReal.ofReal t < strongKernelMaximal K f x} ≤
      ENNReal.ofReal (A ^ (2 : ℝ) * (t / 2) ^ (-(2 : ℝ))) *
        ∫⁻ x, ‖highPart f (thresholdScale B * t) x‖ₑ ^ (2 : ℝ) := by
  have ha : 0 < thresholdScale B * t := mul_pos (thresholdScale_pos B hB) ht
  have hh : MemLp (highPart f (thresholdScale B * t)) 2 volume := by
    simpa only [ENNReal.ofReal_ofNat] using
      memLp_highPart f hmeas p 2 (by norm_num) hp _ ha hf
  have hl := memLp_lowPart_top f hmeas (thresholdScale B * t) ha.le
  have hlow : ∀ x, strongKernelMaximal K (lowPart f (thresholdScale B * t)) x ≤
      ENNReal.ofReal (t / 2) := by
    intro x
    have h := (hInfinity _ hl x).trans
      (mul_le_mul' le_rfl (eLpNorm_lowPart_top_le f _ ha.le))
    have he : ENNReal.ofReal B * ENNReal.ofReal (thresholdScale B * t) =
        ENNReal.ofReal (t / 2) := by
      rw [← ENNReal.ofReal_mul hB.le]
      congr 1
      unfold thresholdScale
      field_simp
    exact h.trans_eq he
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  have hsub : {x | ENNReal.ofReal t < strongKernelMaximal K f x} ⊆
      {x | ENNReal.ofReal (t / 2) < strongKernelMaximal K (highPart f (thresholdScale B * t)) x} := by
    intro x hx
    change ENNReal.ofReal (t / 2) < strongKernelMaximal K (highPart f (thresholdScale B * t)) x
    by_contra hnot
    have htri := strongKernelMaximal_le_parts K hK hc f hmeas
      (ENNReal.ofReal p) hp1 (thresholdScale B * t) hf x
    have hsum := htri.trans (add_le_add (le_of_not_gt hnot) (hlow x))
    have he : ENNReal.ofReal (t / 2) + ENNReal.ofReal (t / 2) = ENNReal.ofReal t := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    rw [he] at hsum
    exact (not_lt_of_ge hsum) hx
  have hm := KernelMaximalLp.measurable_strongKernelMaximal K hK hc
    (by norm_num : (1 : ℝ≥0∞) ≤ 2) _ hh
  have hnorm : eLpNorm (strongKernelMaximal K (highPart f (thresholdScale B * t)))
      (ENNReal.ofReal (2 : ℝ)) volume ≤
      ENNReal.ofReal A * eLpNorm (highPart f (thresholdScale B * t)) (ENNReal.ofReal (2 : ℝ)) volume := by
    simpa only [ENNReal.ofReal_ofNat] using hTwo _ hh
  exact (measure_mono hsub).trans (MaximalChebyshev.measure_lt_le_of_eLpNorm volume _ hm
    _ 2 (by norm_num) A hA.le (t / 2) (by positivity) hnorm)

/-- The weighted high truncation integral is computed exactly by Tonelli. -/
theorem high_truncation_integral (f : Space n → ℂ) (hmeas : Measurable f)
    (p B : ℝ) (hp : 2 < p) (hB : 0 < B) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 2 - 1)) *
      ∫⁻ x, ‖highPart f (thresholdScale B * t) x‖ₑ ^ (2 : ℝ)) =
      ENNReal.ofReal (thresholdScale B ^ (-(p - 2)) / (p - 2)) *
        ∫⁻ x, ‖f x‖ₑ ^ p := by
  simp_rw [highPart_energy f _ 2 (by norm_num)]
  simpa only [ofReal_norm] using InterpolationLayercake.lintegral_high_tail
    (volume : Measure (Space n)) (fun x => ‖f x‖) hmeas.norm (fun _ => norm_nonneg _)
    2 p (by norm_num) hp (thresholdScale B) (thresholdScale_pos B hB)

/-- The p-energy bound follows from actual endpoint estimates and actual
convolution splitting; no interpolation theorem is assumed. -/
theorem interpolation_energy_measurable (K : Space n → ℂ) (hK : Continuous K)
    (hc : HasCompactSupport K) (p : ℝ) (hp : 2 < p)
    (A : ℝ) (hA : 0 < A)
    (hTwo : ∀ g : Space n → ℂ, MemLp g 2 volume →
      eLpNorm (strongKernelMaximal K g) 2 volume ≤ ENNReal.ofReal A * eLpNorm g 2 volume)
    (B : ℝ) (hB : 0 < B)
    (hInfinity : ∀ g : Space n → ℂ, MemLp g ∞ volume → ∀ x,
      strongKernelMaximal K g x ≤ ENNReal.ofReal B * eLpNorm g ∞ volume)
    (f : Space n → ℂ) (hmeas : Measurable f) (hf : MemLp f (ENNReal.ofReal p) volume) :
    (∫⁻ x, strongKernelMaximal K f x ^ p) ≤
      ENNReal.ofReal (energyConstant p * A ^ 2 * B ^ (p - 2)) * ∫⁻ x, ‖f x‖ₑ ^ p := by
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  have hm := KernelMaximalLp.measurable_strongKernelMaximal K hK hc hp1 f hf
  let tail : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (A ^ (2 : ℝ) * (t / 2) ^ (-(2 : ℝ))) *
    ∫⁻ x, ‖highPart f (thresholdScale B * t) x‖ₑ ^ (2 : ℝ)
  have htail : ∀ t > 0, volume {x | ENNReal.ofReal t < strongKernelMaximal K f x} ≤ tail t :=
    fun t ht => measure_tail_le_high K hK hc p hp A hA hTwo B hB hInfinity f hmeas hf t ht
  have he := InterpolationLayercake.energy_le_of_tail volume (strongKernelMaximal K f) hm p hp0 tail htail
  have hi : (∫⁻ t in Ioi (0 : ℝ), tail t * ENNReal.ofReal (t ^ (p - 1))) =
      ENNReal.ofReal (4 * A ^ 2) *
        (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (p - 2 - 1)) *
          ∫⁻ x, ‖highPart f (thresholdScale B * t) x‖ₑ ^ (2 : ℝ)) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only [tail]
    calc
      _ = (ENNReal.ofReal (A ^ (2 : ℝ) * (t / 2) ^ (-(2 : ℝ))) *
          ENNReal.ofReal (t ^ (p - 1))) *
          ∫⁻ x, ‖highPart f (thresholdScale B * t) x‖ₑ ^ (2 : ℝ) := by ring
      _ = ENNReal.ofReal ((4 * A ^ 2) * t ^ (p - 2 - 1)) *
          ∫⁻ x, ‖highPart f (thresholdScale B * t) x‖ₑ ^ (2 : ℝ) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hA.le _)
          (Real.rpow_nonneg (div_nonneg (show 0 ≤ t from (show 0 < t from ht).le)
            (by norm_num : (0 : ℝ) ≤ 2)) _)), weight_coefficient p A t ht]
      _ = _ := by rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * A ^ 2)]; ring
  calc
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ), tail t * ENNReal.ofReal (t ^ (p - 1)) := he
    _ = ENNReal.ofReal p * (ENNReal.ofReal (4 * A ^ 2) *
        (ENNReal.ofReal (thresholdScale B ^ (-(p - 2)) / (p - 2)) * ∫⁻ x, ‖f x‖ₑ ^ p)) := by
      rw [hi, high_truncation_integral f hmeas p B hp hB]
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hp0.le,
        ← ENNReal.ofReal_mul (mul_nonneg hp0.le (by positivity : 0 ≤ 4 * A ^ 2)),
        threshold_coefficient p A B hB]

private theorem norm_coefficient_rpow (p : ℝ) (hp : 2 < p) (A B : ℝ)
    (hA : 0 < A) (hB : 0 < B) :
    (normConstant p * A ^ (2 / p) * B ^ (1 - 2 / p)) ^ p =
      energyConstant p * A ^ 2 * B ^ (p - 2) := by
  have hp0 : 0 < p := by linarith
  have hd : normConstant p ^ p = energyConstant p := by
    unfold normConstant
    rw [← Real.rpow_mul (energyConstant_pos p hp).le,
      one_div_mul_cancel hp0.ne', Real.rpow_one]
  have ha : (A ^ (2 / p)) ^ p = A ^ 2 := by
    rw [← Real.rpow_mul hA.le, div_mul_cancel₀ _ hp0.ne', Real.rpow_two]
  have hb : (B ^ (1 - 2 / p)) ^ p = B ^ (p - 2) := by
    rw [← Real.rpow_mul hB.le]
    congr 1
    field_simp
  rw [Real.mul_rpow (mul_nonneg (normConstant_pos p hp).le (Real.rpow_nonneg hA.le _))
      (Real.rpow_nonneg hB.le _),
    Real.mul_rpow (normConstant_pos p hp).le (Real.rpow_nonneg hA.le _), hd, ha, hb]

/-- A dimension-independent real-variable interpolation constant. The final
input is the original raw Lᵖ representative. -/
theorem exists_interpolation_above_two (p : ℝ) (hp : 2 < p) :
    ∃ D : ℝ, 0 < D ∧ ∀ (n : ℕ) (K : Space n → ℂ), Continuous K → HasCompactSupport K →
      ∀ A : ℝ, 0 < A →
      (∀ g : Space n → ℂ, MemLp g 2 volume →
        eLpNorm (strongKernelMaximal K g) 2 volume ≤ ENNReal.ofReal A * eLpNorm g 2 volume) →
      ∀ B : ℝ, 0 < B →
      (∀ g : Space n → ℂ, MemLp g ∞ volume → ∀ x,
        strongKernelMaximal K g x ≤ ENNReal.ofReal B * eLpNorm g ∞ volume) →
      ∀ f : Space n → ℂ, MemLp f (ENNReal.ofReal p) volume →
        Measurable (strongKernelMaximal K f) ∧
          eLpNorm (strongKernelMaximal K f) (ENNReal.ofReal p) volume ≤
            ENNReal.ofReal (D * A ^ (2 / p) * B ^ (1 - 2 / p)) *
              eLpNorm f (ENNReal.ofReal p) volume := by
  refine ⟨normConstant p, normConstant_pos p hp, ?_⟩
  intro n K hK hc A hA hTwo B hB hInfinity f hf
  have hp0 : 0 < p := by linarith
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (show (1 : ℝ) ≤ p by linarith)
  refine ⟨KernelMaximalLp.measurable_strongKernelMaximal K hK hc hp1 f hf, ?_⟩
  let g := hf.aestronglyMeasurable.mk f
  have hg : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  have hglp : MemLp g (ENNReal.ofReal p) volume := (memLp_congr_ae hfg).mp hf
  have henergy := interpolation_energy_measurable K hK hc p hp A hA hTwo B hB hInfinity g hg hglp
  have hnorm := InterpolationNorm.eLpNorm_le_of_energy volume (strongKernelMaximal K g) g p hp0
    (normConstant p * A ^ (2 / p) * B ^ (1 - 2 / p))
    (by apply mul_nonneg; apply mul_nonneg; exact (normConstant_pos p hp).le;
        exact Real.rpow_nonneg hA.le _; exact Real.rpow_nonneg hB.le _)
    (by rw [norm_coefficient_rpow p hp A B hA hB]; exact henergy)
  rw [← MaximalAssembly.strongKernelMaximal_congr_ae K f g hfg, ← eLpNorm_congr_ae hfg] at hnorm
  exact hnorm

end StrongSpherical.KernelInterpolationAboveTwo
