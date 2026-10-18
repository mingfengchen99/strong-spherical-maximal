import KernelTruncation
import InterpolationLayercake
import InterpolationScaling
import InterpolationNorm

/-! # Real-variable interpolation between two finite maximal-operator bounds

Amplitude truncation and the distribution formula prove the interpolation
estimate directly for the actual maximal convolution operator.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace StrongSpherical.KernelInterpolationFinite
open KernelTruncation
variable {n : ℕ}
set_option maxHeartbeats 1000000

def interpolationConstant (q p r : ℝ) : ℝ :=
  (p * ((2 : ℝ) ^ q / (p - q) + (2 : ℝ) ^ r / (r - p))) ^ (1 / p)

theorem interpolationConstant_pos (q p r : ℝ) (hq : 0 < q)
    (hqp : q < p) (hpr : p < r) : 0 < interpolationConstant q p r := by
  unfold interpolationConstant
  apply Real.rpow_pos_of_pos
  exact mul_pos (hq.trans hqp) (add_pos
    (div_pos (Real.rpow_pos_of_pos (by norm_num) _) (sub_pos.mpr hqp))
    (div_pos (Real.rpow_pos_of_pos (by norm_num) _) (sub_pos.mpr hpr)))

private theorem half_threshold_coefficient (A s t : ℝ) (hA : 0 ≤ A) (ht : 0 < t) :
    A ^ s * (t / 2) ^ (-s) = (2 * A) ^ s * t ^ (-s) := by
  rw [Real.div_rpow ht.le (by norm_num),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hA]
  ring

private theorem tail_union (K : Space n → ℂ) (hK : Continuous K)
    (hc : HasCompactSupport K) (f : Space n → ℂ) (hmeas : Measurable f)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (hf : MemLp f p volume) (a t : ℝ) (ht : 0 < t) :
    {x | ENNReal.ofReal t < strongKernelMaximal K f x} ⊆
      {x | ENNReal.ofReal (t / 2) < strongKernelMaximal K (highPart f a) x} ∪
        {x | ENNReal.ofReal (t / 2) < strongKernelMaximal K (lowPart f a) x} := by
  intro x hx
  by_cases hh : ENNReal.ofReal (t / 2) < strongKernelMaximal K (highPart f a) x
  · exact Or.inl hh
  · by_cases hl : ENNReal.ofReal (t / 2) < strongKernelMaximal K (lowPart f a) x
    · exact Or.inr hl
    · have hsum := (strongKernelMaximal_le_parts K hK hc f hmeas p hp a hf x).trans
        (add_le_add (le_of_not_gt hh) (le_of_not_gt hl))
      have he : ENNReal.ofReal (t / 2) + ENNReal.ofReal (t / 2) =
          ENNReal.ofReal t := by
        rw [← ENNReal.ofReal_add (by positivity : 0 ≤ t / 2) (by positivity : 0 ≤ t / 2)]
        congr 1
        ring
      rw [he] at hsum
      exact False.elim ((not_le_of_gt hx) hsum)

/-- The two endpoint estimates give the exact two truncated distribution tails. -/
theorem distribution_bound (K : Space n → ℂ) (hK : Continuous K)
    (hc : HasCompactSupport K) (q p r : ℝ) (hq : 1 < q) (hqp : q < p) (hpr : p < r)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hleft : ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal q) volume →
      eLpNorm (strongKernelMaximal K g) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal A * eLpNorm g (ENNReal.ofReal q) volume)
    (hright : ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal r) volume →
      eLpNorm (strongKernelMaximal K g) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal B * eLpNorm g (ENNReal.ofReal r) volume)
    (f : Space n → ℂ) (hmeas : Measurable f) (hf : MemLp f (ENNReal.ofReal p) volume)
    (gamma : ℝ) (hg : 0 < gamma) (t : ℝ) (ht : 0 < t) :
    volume {x | ENNReal.ofReal t < strongKernelMaximal K f x} ≤
      ENNReal.ofReal ((2 * A) ^ q * t ^ (-q)) *
        (∫⁻ x, {x | gamma * t < ‖f x‖}.indicator
          (fun x => ENNReal.ofReal (‖f x‖) ^ q) x) +
      ENNReal.ofReal ((2 * B) ^ r * t ^ (-r)) *
        (∫⁻ x, {x | ‖f x‖ ≤ gamma * t}.indicator
          (fun x => ENNReal.ofReal (‖f x‖) ^ r) x) := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hp0 : 0 < p := hq0.trans hqp
  have hr0 : 0 < r := hp0.trans hpr
  have hpf : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hq.trans hqp).le
  have hqf : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq.le
  have hrf : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ((hq.trans hqp).trans hpr).le
  have hfh := memLp_highPart f hmeas p q hq0 hqp (gamma * t) (mul_pos hg ht) hf
  have hfl := memLp_lowPart f hmeas p r hp0 hpr (gamma * t) (mul_pos hg ht) hf
  have hmH := KernelMaximalLp.measurable_strongKernelMaximal K hK hc hqf _ hfh
  have hmL := KernelMaximalLp.measurable_strongKernelMaximal K hK hc hrf _ hfl
  have hH := MaximalChebyshev.measure_lt_le_of_eLpNorm volume _ hmH
    (highPart f (gamma * t)) q hq0 A hA.le (t / 2) (by positivity) (hleft _ hfh)
  have hL := MaximalChebyshev.measure_lt_le_of_eLpNorm volume _ hmL
    (lowPart f (gamma * t)) r hr0 B hB.le (t / 2) (by positivity) (hright _ hfl)
  rw [highPart_energy f (gamma * t) q hq0, half_threshold_coefficient A q t hA.le ht] at hH
  rw [lowPart_energy f (gamma * t) r hr0, half_threshold_coefficient B r t hB.le ht] at hL
  calc
    _ ≤ volume ({x | ENNReal.ofReal (t / 2) < strongKernelMaximal K (highPart f (gamma * t)) x} ∪
        {x | ENNReal.ofReal (t / 2) < strongKernelMaximal K (lowPart f (gamma * t)) x}) :=
      measure_mono (tail_union K hK hc f hmeas _ hpf hf (gamma * t) t ht)
    _ ≤ volume {x | ENNReal.ofReal (t / 2) < strongKernelMaximal K (highPart f (gamma * t)) x} +
        volume {x | ENNReal.ofReal (t / 2) < strongKernelMaximal K (lowPart f (gamma * t)) x} :=
      measure_union_le _ _
    _ ≤ _ := by simpa only [ofReal_norm] using add_le_add hH hL

/-- Finite-endpoint interpolation, first for Borel measurable raw inputs. -/
theorem strongKernelMaximal_Lp_measurable (K : Space n → ℂ) (hK : Continuous K)
    (hc : HasCompactSupport K) (q p r theta : ℝ) (hq : 1 < q)
    (hqp : q < p) (hpr : p < r)
    (hinterp : 1 / p = (1 - theta) / q + theta / r)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hleft : ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal q) volume →
      eLpNorm (strongKernelMaximal K g) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal A * eLpNorm g (ENNReal.ofReal q) volume)
    (hright : ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal r) volume →
      eLpNorm (strongKernelMaximal K g) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal B * eLpNorm g (ENNReal.ofReal r) volume)
    (f : Space n → ℂ) (hmeas : Measurable f) (hf : MemLp f (ENNReal.ofReal p) volume) :
    eLpNorm (strongKernelMaximal K f) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (interpolationConstant q p r * (A ^ (1 - theta) * B ^ theta)) *
        eLpNorm f (ENNReal.ofReal p) volume := by
  have hq0 : 0 < q := zero_lt_one.trans hq
  have hp0 : 0 < p := hq0.trans hqp
  let gamma := InterpolationScaling.balancingThreshold A B q r
  let C := A ^ (1 - theta) * B ^ theta
  let D := interpolationConstant q p r
  have hg : 0 < gamma := InterpolationScaling.balancingThreshold_pos A B q r hA hB
  have hC : 0 < C := mul_pos (Real.rpow_pos_of_pos hA _) (Real.rpow_pos_of_pos hB _)
  have hD : 0 < D := interpolationConstant_pos q p r hq0 hqp hpr
  have hb := InterpolationScaling.balanced_terms A B q p r theta hA hB hq0 hqp hpr hinterp
  have hb1 : A ^ q * gamma ^ (q - p) = C ^ p := hb.1
  have hb2 : B ^ r * gamma ^ (r - p) = C ^ p := hb.2
  have hbase : 0 < p * ((2 : ℝ) ^ q / (p - q) + (2 : ℝ) ^ r / (r - p)) :=
    mul_pos hp0 (add_pos
      (div_pos (Real.rpow_pos_of_pos (by norm_num) _) (sub_pos.mpr hqp))
      (div_pos (Real.rpow_pos_of_pos (by norm_num) _) (sub_pos.mpr hpr)))
  have hDpow : D ^ p = p * ((2 : ℝ) ^ q / (p - q) + (2 : ℝ) ^ r / (r - p)) := by
    dsimp only [D, interpolationConstant]
    rw [← Real.rpow_mul hbase.le, one_div_mul_cancel hp0.ne', Real.rpow_one]
  have hcoef : p * ((2 * A) ^ q * gamma ^ (-(p - q)) / (p - q) +
      (2 * B) ^ r * gamma ^ (r - p) / (r - p)) = (D * C) ^ p := by
    calc
      _ = p * ((2 : ℝ) ^ q * (A ^ q * gamma ^ (q - p)) / (p - q) +
          (2 : ℝ) ^ r * (B ^ r * gamma ^ (r - p)) / (r - p)) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hA.le,
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hB.le,
          show -(p - q) = q - p by ring]
        ring
      _ = p * ((2 : ℝ) ^ q * C ^ p / (p - q) + (2 : ℝ) ^ r * C ^ p / (r - p)) := by
        rw [hb1, hb2]
      _ = D ^ p * C ^ p := by rw [hDpow]; ring
      _ = _ := (Real.mul_rpow hD.le hC.le).symm
  have hpf : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hq.trans hqp).le
  have hG := KernelMaximalLp.measurable_strongKernelMaximal K hK hc hpf f hf
  have he := InterpolationLayercake.energy_le_of_two_tail volume
    (fun x => ‖f x‖) hmeas.norm (fun _ => norm_nonneg _)
    (strongKernelMaximal K f) hG q p r hq0 hqp hpr gamma hg
    ((2 * A) ^ q) ((2 * B) ^ r) (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (by positivity) _)
    (distribution_bound K hK hc q p r hq hqp hpr A B hA hB hleft hright f hmeas hf gamma hg)
  rw [hcoef] at he
  apply InterpolationNorm.eLpNorm_le_of_energy volume _ f p hp0 (D * C) (mul_pos hD hC).le
  simpa only [ofReal_norm] using he

/-- Both endpoints and the interpolated estimate apply to the original raw
MemLp input; taking a representative preserves every convolution point. -/
theorem strongKernelMaximal_Lp (K : Space n → ℂ) (hK : Continuous K)
    (hc : HasCompactSupport K) (q p r theta : ℝ) (hq : 1 < q)
    (hqp : q < p) (hpr : p < r)
    (hinterp : 1 / p = (1 - theta) / q + theta / r)
    (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hleft : ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal q) volume →
      eLpNorm (strongKernelMaximal K g) (ENNReal.ofReal q) volume ≤
        ENNReal.ofReal A * eLpNorm g (ENNReal.ofReal q) volume)
    (hright : ∀ g : Space n → ℂ, MemLp g (ENNReal.ofReal r) volume →
      eLpNorm (strongKernelMaximal K g) (ENNReal.ofReal r) volume ≤
        ENNReal.ofReal B * eLpNorm g (ENNReal.ofReal r) volume)
    (f : Space n → ℂ) (hf : MemLp f (ENNReal.ofReal p) volume) :
    Measurable (strongKernelMaximal K f) ∧
      eLpNorm (strongKernelMaximal K f) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (interpolationConstant q p r * (A ^ (1 - theta) * B ^ theta)) *
          eLpNorm f (ENNReal.ofReal p) volume := by
  have hpf : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hq.trans hqp).le
  refine ⟨KernelMaximalLp.measurable_strongKernelMaximal K hK hc hpf f hf, ?_⟩
  let g := hf.aestronglyMeasurable.mk f
  have hg : Measurable g := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfg : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  have hgf : MemLp g (ENNReal.ofReal p) volume := (memLp_congr_ae hfg).mp hf
  have h := strongKernelMaximal_Lp_measurable K hK hc q p r theta hq hqp hpr hinterp
    A B hA hB hleft hright g hg hgf
  rw [← MaximalAssembly.strongKernelMaximal_congr_ae K f g hfg,
    ← eLpNorm_congr_ae hfg] at h
  exact h

end StrongSpherical.KernelInterpolationFinite
