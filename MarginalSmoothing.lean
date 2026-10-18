import ProductSmoothing
import CoordinateSubsets
import Mathlib.Analysis.Calculus.MeanValue

/-! # Weighted translations of the actual low-frequency smoothing kernel -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators SchwartzMap
namespace StrongSpherical.MarginalSmoothing
open FourierCutoff ProductSmoothing CoordinateMarginals ProductCoordinates
variable {m j : ℕ}

def scalarWeight (t : ℝ) : ℝ := ((1 + |t|) ^ 3)⁻¹

theorem scalarWeight_pos (t : ℝ) : 0 < scalarWeight t := by
  unfold scalarWeight
  positivity

theorem scalarWeight_eq_zpow (t : ℝ) :
    scalarWeight t = (1 + |t|) ^ (-(3 : ℤ)) := by
  simp only [scalarWeight, zpow_neg, zpow_ofNat]

theorem weighted_decay_shift (F : ℝ → ℝ) (hF : ∀ t, 0 ≤ F t)
    (C H : ℝ) (hH : 0 ≤ H)
    (hdecay : ∀ t, (1 + |t|) ^ 3 * F t ≤ C)
    (t h : ℝ) (hh : |h| ≤ H) :
    F (t - h) ≤ C * (1 + H) ^ 3 * scalarWeight t := by
  have htri : 1 + |t| ≤ (1 + H) * (1 + |t - h|) := by
    have ha : |t| ≤ |t - h| + H := by
      calc
        _ = |t - h + h| := by congr 1; ring
        _ ≤ |t - h| + |h| := abs_add_le _ _
        _ ≤ |t - h| + H := by linarith
    nlinarith [abs_nonneg (t - h)]
  have hp := mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |t|) htri 3) (hF (t - h))
  have hb : (1 + |t|) ^ 3 * F (t - h) ≤ C * (1 + H) ^ 3 := by
    calc
      _ ≤ ((1 + H) * (1 + |t - h|)) ^ 3 * F (t - h) := hp
      _ = (1 + H) ^ 3 * ((1 + |t - h|) ^ 3 * F (t - h)) := by ring
      _ ≤ (1 + H) ^ 3 * C := mul_le_mul_of_nonneg_left (hdecay _) (by positivity)
      _ = _ := mul_comm _ _
  unfold scalarWeight
  apply (le_div_iff₀ (by positivity : 0 < (1 + |t|) ^ 3)).mpr
  simpa only [div_eq_mul_inv, mul_comm] using hb

theorem phi_weighted_translation_control :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 0 ≤ H → ∀ t h : ℝ, |h| ≤ H →
      ‖phi (t - h)‖ ≤ C * (1 + H) ^ 3 * scalarWeight t ∧
      ‖phi (t - h) - phi t‖ ≤ C * (1 + H) ^ 3 * |h| * scalarWeight t := by
  obtain ⟨C0, hC0, h0⟩ := phi_decay 3 0
  obtain ⟨C1, hC1, h1⟩ := phi_decay 3 1
  have h0' : ∀ t, (1 + |t|) ^ 3 * ‖phi t‖ ≤ C0 := by
    intro t
    simpa only [norm_iteratedFDeriv_zero] using h0 t
  have h1' : ∀ t, (1 + |t|) ^ 3 * ‖fderiv ℝ (phi : ℝ → ℂ) t‖ ≤ C1 := by
    intro t
    simpa only [norm_iteratedFDeriv_one] using h1 t
  refine ⟨C0 + C1, by linarith, ?_⟩
  intro H hH t h hh
  have hvalue := weighted_decay_shift (fun s => ‖phi s‖) (fun _ => norm_nonneg _) C0 H hH h0' t h hh
  have hderiv : ∀ x ∈ Metric.closedBall t H,
      ‖fderiv ℝ (phi : ℝ → ℂ) x‖ ≤ C1 * (1 + H) ^ 3 * scalarWeight t := by
    intro x hx
    have hhx : |t - x| ≤ H := by
      simpa only [Metric.mem_closedBall, Real.dist_eq, abs_sub_comm] using hx
    have he := weighted_decay_shift (fun s => ‖fderiv ℝ (phi : ℝ → ℂ) s‖)
      (fun _ => norm_nonneg _) C1 H hH h1' t (t - x) hhx
    simpa only [sub_sub_cancel] using he
  have hm := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun x (_hx : x ∈ Metric.closedBall t H) => phi.differentiableAt)
    hderiv (convex_closedBall t H)
    (Metric.mem_closedBall_self hH)
    (show t - h ∈ Metric.closedBall t H by
      simpa only [Metric.mem_closedBall, Real.dist_eq, sub_sub_cancel_left, abs_neg] using hh)
  have hm' : ‖phi (t - h) - phi t‖ ≤ C1 * (1 + H) ^ 3 * |h| * scalarWeight t := by
    simpa only [sub_sub_cancel_left, Real.norm_eq_abs, abs_neg, mul_assoc, mul_comm, mul_left_comm] using hm
  constructor
  · exact hvalue.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by linarith : C0 ≤ C0 + C1) (by positivity))
      (scalarWeight_pos t).le)
  · exact hm'.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : C1 ≤ C0 + C1) (by positivity))
        (abs_nonneg h)) (scalarWeight_pos t).le)

/-- A finite telescoping estimate with separate weights in every coordinate. -/
theorem product_difference_le {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a b : ι → ℂ) (D : ι → ℝ) (delta : ℝ) (hd : 0 ≤ delta)
    (hD : ∀ i ∈ s, 0 ≤ D i) (ha : ∀ i ∈ s, ‖a i‖ ≤ D i)
    (hb : ∀ i ∈ s, ‖b i‖ ≤ D i)
    (hab : ∀ i ∈ s, ‖a i - b i‖ ≤ delta * D i) :
    ‖(∏ i ∈ s, a i) - ∏ i ∈ s, b i‖ ≤ (s.card : ℝ) * delta * ∏ i ∈ s, D i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
    have hDi := hD i (Finset.mem_insert_self i s)
    have hDs : ∀ q ∈ s, 0 ≤ D q := fun q hq => hD q (Finset.mem_insert_of_mem hq)
    have has : ∀ q ∈ s, ‖a q‖ ≤ D q := fun q hq => ha q (Finset.mem_insert_of_mem hq)
    have hbs : ∀ q ∈ s, ‖b q‖ ≤ D q := fun q hq => hb q (Finset.mem_insert_of_mem hq)
    have habs : ∀ q ∈ s, ‖a q - b q‖ ≤ delta * D q :=
      fun q hq => hab q (Finset.mem_insert_of_mem hq)
    have hi := ih hDs has hbs habs
    have hp : ‖∏ q ∈ s, b q‖ ≤ ∏ q ∈ s, D q := by
      rw [norm_prod]
      exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) hbs
    rw [Finset.prod_insert his, Finset.prod_insert his, Finset.prod_insert his,
      Finset.card_insert_of_notMem his, Nat.cast_add, Nat.cast_one]
    calc
      _ = ‖a i * ((∏ q ∈ s, a q) - ∏ q ∈ s, b q) +
          (a i - b i) * ∏ q ∈ s, b q‖ := by congr 1; ring
      _ ≤ ‖a i‖ * ‖(∏ q ∈ s, a q) - ∏ q ∈ s, b q‖ +
          ‖a i - b i‖ * ‖∏ q ∈ s, b q‖ := by
        simpa only [norm_mul] using norm_add_le
          (a i * ((∏ q ∈ s, a q) - ∏ q ∈ s, b q))
          ((a i - b i) * ∏ q ∈ s, b q)
      _ ≤ D i * ((s.card : ℝ) * delta * ∏ q ∈ s, D q) +
          (delta * D i) * ∏ q ∈ s, D q := by
        apply add_le_add
        · exact mul_le_mul (ha i (Finset.mem_insert_self i s)) hi (norm_nonneg _) hDi
        · exact mul_le_mul (hab i (Finset.mem_insert_self i s)) hp (norm_nonneg _)
            (mul_nonneg hd hDi)
      _ = _ := by ring

theorem scaledPhi_weighted_translation_control :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 0 ≤ H → ∀ v : ℝ, 0 < v → ∀ y z : ℝ,
      |z| / v ≤ H →
      ‖scaledPhi v (y - z)‖ ≤
        (C * (1 + H) ^ 3) * (v⁻¹ * scalarWeight (y / v)) ∧
      ‖scaledPhi v (y - z) - scaledPhi v y‖ ≤
        (C * (1 + H) ^ 3) * (|z| / v) * (v⁻¹ * scalarWeight (y / v)) := by
  obtain ⟨C, hC, hcontrol⟩ := phi_weighted_translation_control
  refine ⟨C, hC, ?_⟩
  intro H hH v hv y z hz
  have hs : |z / v| ≤ H := by simpa only [abs_div, abs_of_pos hv] using hz
  have hc := hcontrol H hH (y / v) (z / v) hs
  have he : v⁻¹ * (y - z) = y / v - z / v := by ring
  constructor
  · rw [norm_scaledPhi v hv, he]
    have hb := mul_le_mul_of_nonneg_left hc.1 (inv_nonneg.mpr hv.le)
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hb
  · have he' : scaledPhi v (y - z) - scaledPhi v y =
        (v⁻¹ : ℂ) * (phi (y / v - z / v) - phi (y / v)) := by
      simp only [scaledPhi, he, show v⁻¹ * y = y / v by ring, mul_sub]
    rw [he', norm_mul]
    have hnorm : ‖(v⁻¹ : ℂ)‖ = v⁻¹ := by
      simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hv]
    rw [hnorm]
    have hb := mul_le_mul_of_nonneg_left hc.2 (inv_nonneg.mpr hv.le)
    simpa only [abs_div, abs_of_pos hv, mul_assoc, mul_comm, mul_left_comm] using hb

theorem productPhi_weighted_translation_control (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ H : ℝ, 0 ≤ H → ∀ delta : ℝ, 0 ≤ delta → delta ≤ H →
      ∀ (b : Radii n) (y z : Space n), (∀ i, |z i| / b.1 i ≤ delta) →
      ‖productPhi b (y - z) - productPhi b y‖ ≤
        (n : ℝ) * delta * (C * (1 + H) ^ 3) ^ n * productWeight b y := by
  obtain ⟨C, hC, hc⟩ := scaledPhi_weighted_translation_control
  refine ⟨C, hC, ?_⟩
  intro H hH delta hd hdH b y z hz
  let D : Fin n → ℝ := fun i => (C * (1 + H) ^ 3) *
    ((b.1 i)⁻¹ * scalarWeight (y i / b.1 i))
  have hD : ∀ i, 0 ≤ D i := by
    intro i
    have hbi := b.2 i
    dsimp [D, scalarWeight]
    positivity
  have ha : ∀ i, ‖scaledPhi (b.1 i) (y i - z i)‖ ≤ D i :=
    fun i => (hc H hH _ (b.2 i) _ _ ((hz i).trans hdH)).1
  have hb : ∀ i, ‖scaledPhi (b.1 i) (y i)‖ ≤ D i := by
    intro i
    have h := (hc H hH _ (b.2 i) (y i) 0 (by simp [hH])).1
    simpa only [sub_zero] using h
  have hab : ∀ i, ‖scaledPhi (b.1 i) (y i - z i) - scaledPhi (b.1 i) (y i)‖ ≤ delta * D i := by
    intro i
    have h := (hc H hH _ (b.2 i) (y i) (z i) ((hz i).trans hdH)).2
    apply h.trans
    calc
      _ = (|z i| / b.1 i) * D i := by dsimp [D]; ring
      _ ≤ delta * D i := mul_le_mul_of_nonneg_right (hz i) (hD i)
  have hp := product_difference_le Finset.univ
    (fun i => scaledPhi (b.1 i) (y i - z i)) (fun i => scaledPhi (b.1 i) (y i))
    D delta hd (fun i _ => hD i) (fun i _ => ha i) (fun i _ => hb i) (fun i _ => hab i)
  have he : (∏ i, D i) = (C * (1 + H) ^ 3) ^ n * productWeight b y := by
    dsimp only [D]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [scalarWeight_eq_zpow]
    simp only [abs_div, abs_of_pos (b.2 i)]
  simpa only [productPhi, PiLp.sub_apply, Finset.card_univ, Fintype.card_fin, he, mul_assoc] using hp

/-- The precise weighted small translation estimate required inside the
actual marginal smoothing error (5.21). The constant is independent of all
kernel radii, smoothing radii, output points, and epsilon. -/
theorem exists_productPhi_difference_le (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ 1 →
      ∀ (r b : Radii n) (y z : Space n),
      (∀ i, |z i| ≤ R * r.1 i) → (∀ i, r.1 i / b.1 i ≤ 2 * epsilon) →
      ‖productPhi b (y - z) - productPhi b y‖ ≤ C * epsilon * productWeight b y := by
  obtain ⟨C, hC, hc⟩ := productPhi_weighted_translation_control n
  let F : ℝ := (n : ℝ) * (2 * R) * (C * (1 + 2 * R) ^ 3) ^ n
  have hF : 0 ≤ F := by dsimp [F]; positivity
  refine ⟨F + 1, by linarith, ?_⟩
  intro epsilon heps heps1 r b y z hz hscale
  have hd : 0 ≤ 2 * R * epsilon := by positivity
  have hdH : 2 * R * epsilon ≤ 2 * R := by nlinarith
  have hs : ∀ i, |z i| / b.1 i ≤ 2 * R * epsilon := by
    intro i
    calc
      _ ≤ (R * r.1 i) / b.1 i := div_le_div_of_nonneg_right (hz i) (b.2 i).le
      _ = R * (r.1 i / b.1 i) := by ring
      _ ≤ R * (2 * epsilon) := mul_le_mul_of_nonneg_left (hscale i) hR
      _ = _ := by ring
  have h := hc (2 * R) (by positivity) (2 * R * epsilon) hd hdH b y z hs
  calc
    _ ≤ (n : ℝ) * (2 * R * epsilon) * (C * (1 + 2 * R) ^ 3) ^ n * productWeight b y := h
    _ = F * epsilon * productWeight b y := by dsimp [F]; ring
    _ ≤ (F + 1) * epsilon * productWeight b y := by
      apply mul_le_mul_of_nonneg_right _ (productWeight_nonneg b y)
      exact mul_le_mul_of_nonneg_right (by linarith) heps

def blockDilatedKernel (K : Space m × Space j → ℂ) (r : Radii m) (s : Radii j)
    (p : Space m × Space j) : ℂ :=
  (dilationJacobian r : ℂ)⁻¹ * (dilationJacobian s : ℂ)⁻¹ *
    K (inverseDilation r p.1, inverseDilation s p.2)

/-- Partial convolution in the integrated coordinate block, with its actual
normalized kernel dilation in both coordinate blocks. -/
def partialSmoothedKernel (K : Space m × Space j → ℂ)
    (r : Radii m) (s b : Radii j) (x : Space m) (y : Space j) : ℂ :=
  ∫ z, blockDilatedKernel K r s (x, z) * productPhi b (y - z)

def marginalSmoothingError (K : Space m × Space j → ℂ)
    (r : Radii m) (s b : Radii j) (x : Space m) (y : Space j) : ℂ :=
  partialSmoothedKernel K r s b x y - dilatedKernel (marginal K) r x * productPhi b y

theorem partialSmoothedKernel_eq_normalized_integral (K : Space m × Space j → ℂ)
    (r : Radii m) (s b : Radii j) (x : Space m) (y : Space j) :
    partialSmoothedKernel K r s b x y = (dilationJacobian r : ℂ)⁻¹ *
      ∫ z, K (inverseDilation r x, z) * productPhi b (y - diagonalDilation s.1 z) := by
  unfold partialSmoothedKernel
  rw [DilationL2.integral_eq_dilation s]
  have he : (fun z : Space j => blockDilatedKernel K r s
      (x, diagonalDilation s.1 z) * productPhi b (y - diagonalDilation s.1 z)) =
      fun z => (dilationJacobian s : ℂ)⁻¹ * ((dilationJacobian r : ℂ)⁻¹ *
        (K (inverseDilation r x, z) * productPhi b (y - diagonalDilation s.1 z))) := by
    funext z
    simp only [blockDilatedKernel, inverseDilation_diagonalDilation]
    ring
  rw [he, integral_const_mul, Complex.real_smul, ← mul_assoc,
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr (dilationJacobian_pos s).ne'), one_mul,
    integral_const_mul]

theorem hasCompactSupport_kernel_slice (K : Space m × Space j → ℂ) (R : ℝ)
    (hs : Function.support K ⊆ coordinateCube m R ×ˢ coordinateCube j R) (u : Space m) :
    HasCompactSupport (fun z : Space j => K (u, z)) := by
  apply (isCompact_coordinateCube j R).of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ (isCompact_coordinateCube j R).isClosed
  intro z hz
  exact (hs hz).2

theorem marginalSmoothingError_eq_integral (K : Space m × Space j → ℂ)
    (hK : Continuous K) (R : ℝ)
    (hs : Function.support K ⊆ coordinateCube m R ×ˢ coordinateCube j R)
    (r : Radii m) (s b : Radii j) (x : Space m) (y : Space j) :
    marginalSmoothingError K r s b x y = (dilationJacobian r : ℂ)⁻¹ *
      ∫ z, K (inverseDilation r x, z) *
        (productPhi b (y - diagonalDilation s.1 z) - productPhi b y) := by
  have hc : Continuous (fun z : Space j => K (inverseDilation r x, z)) :=
    hK.comp (continuous_const.prodMk continuous_id)
  have hs' := hasCompactSupport_kernel_slice K R hs (inverseDilation r x)
  have hi1 : Integrable (fun z : Space j =>
      K (inverseDilation r x, z) * productPhi b (y - diagonalDilation s.1 z)) :=
    (hc.mul ((continuous_productPhi b).comp
      (continuous_const.sub (continuous_diagonalDilation s.1)))).integrable_of_hasCompactSupport hs'.mul_right
  have hi2 : Integrable (fun z : Space j => K (inverseDilation r x, z) * productPhi b y) :=
    (hc.mul continuous_const).integrable_of_hasCompactSupport hs'.mul_right
  unfold marginalSmoothingError
  rw [partialSmoothedKernel_eq_normalized_integral, dilatedKernel, marginal,
    mul_assoc, ← mul_sub, ← integral_mul_const]
  congr 1
  rw [← integral_sub hi1 hi2]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by ring

theorem marginalSmoothingError_eq_zero_of_notMem (K : Space m × Space j → ℂ)
    (hK : Continuous K) (R : ℝ)
    (hs : Function.support K ⊆ coordinateCube m R ×ˢ coordinateCube j R)
    (r : Radii m) (s b : Radii j) (x : Space m) (y : Space j)
    (hx : inverseDilation r x ∉ coordinateCube m R) :
    marginalSmoothingError K r s b x y = 0 := by
  rw [marginalSmoothingError_eq_integral K hK R hs]
  have he : ∀ z : Space j, K (inverseDilation r x, z) = 0 := by
    intro z
    by_contra hne
    exact hx (hs hne).1
  simp only [he, zero_mul, integral_zero, mul_zero]

theorem jacobian_inv_le_productWeight (R : ℝ) (_hR : 0 ≤ R) (r : Radii m) (x : Space m)
    (hx : inverseDilation r x ∈ coordinateCube m R) :
    (dilationJacobian r)⁻¹ ≤ ((1 + R) ^ 3) ^ m * productWeight r x := by
  have hi : ∀ i, (r.1 i)⁻¹ ≤ (1 + R) ^ 3 *
      ((r.1 i)⁻¹ * (1 + |x i| / r.1 i) ^ (-(3 : ℤ))) := by
    intro i
    have hri := r.2 i
    have ht : |x i| / r.1 i ≤ R := by
      simpa only [inverseDilation, diagonalDilation_apply, abs_mul, abs_inv,
        abs_of_pos hri, div_eq_mul_inv, mul_comm] using hx i
    have hp : (1 + |x i| / r.1 i) ^ 3 ≤ (1 + R) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 3
    have hsmall : 1 ≤ (1 + R) ^ 3 * ((1 + |x i| / r.1 i) ^ 3)⁻¹ := by
      change 1 ≤ (1 + R) ^ 3 / (1 + |x i| / r.1 i) ^ 3
      apply (le_div_iff₀ (by positivity)).mpr
      simpa only [one_mul] using hp
    have hh := mul_le_mul_of_nonneg_left hsmall (inv_nonneg.mpr hri.le)
    simpa only [zpow_neg, zpow_ofNat, mul_one, one_mul, mul_assoc, mul_comm, mul_left_comm] using hh
  calc
    _ = ∏ i, (r.1 i)⁻¹ := by simp only [dilationJacobian, Finset.prod_inv_distrib]
    _ ≤ ∏ i, (1 + R) ^ 3 *
        ((r.1 i)⁻¹ * (1 + |x i| / r.1 i) ^ (-(3 : ℤ))) :=
      Finset.prod_le_prod (fun i _ => inv_nonneg.mpr (r.2 i).le) (fun i _ => hi i)
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, productWeight]

/-- The actual partial smoothing error (5.21), in two coordinate blocks.
The constant depends only on the dimensions, the support radius and the
fixed cutoff. It is uniform in every dilation and smoothing radius. -/
theorem exists_marginalSmoothingError_bound (m j : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Space m × Space j → ℂ), Continuous K →
      Function.support K ⊆ coordinateCube m R ×ˢ coordinateCube j R →
      ∀ B : ℝ, (∀ p, ‖K p‖ ≤ B) →
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ 1 →
      ∀ (r : Radii m) (s b : Radii j), (∀ i, s.1 i / b.1 i ≤ 2 * epsilon) →
      ∀ (x : Space m) (y : Space j),
      ‖marginalSmoothingError K r s b x y‖ ≤
        C * epsilon * B * productWeight r x * productWeight b y := by
  obtain ⟨Cphi, hCphi, hphi⟩ := exists_productPhi_difference_le j R hR
  let V : ℝ := (volume : Measure (Space j)).real (coordinateCube j R)
  let A : ℝ := ((1 + R) ^ 3) ^ m
  let F : ℝ := A * V * Cphi
  have hV : 0 ≤ V := ENNReal.toReal_nonneg
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hF : 0 ≤ F := mul_nonneg (mul_nonneg hA hV) hCphi.le
  refine ⟨F + 1, by linarith, ?_⟩
  intro K hK hs B hB epsilon heps heps1 r s b hscale x y
  have hB0 : 0 ≤ B := (norm_nonneg (K (0, 0))).trans (hB _)
  have hWr := productWeight_nonneg r x
  have hWb := productWeight_nonneg b y
  by_cases hx : inverseDilation r x ∈ coordinateCube m R
  · have hcont : Continuous (fun z : Space j => K (inverseDilation r x, z) *
        (productPhi b (y - diagonalDilation s.1 z) - productPhi b y)) := by
      exact (hK.comp (continuous_const.prodMk continuous_id)).mul
        (((continuous_productPhi b).comp
          (continuous_const.sub (continuous_diagonalDilation s.1))).sub continuous_const)
    have he : (∫ z in coordinateCube j R, K (inverseDilation r x, z) *
        (productPhi b (y - diagonalDilation s.1 z) - productPhi b y)) =
        ∫ z, K (inverseDilation r x, z) *
          (productPhi b (y - diagonalDilation s.1 z) - productPhi b y) := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hzero : K (inverseDilation r x, z) = 0 := by
        by_contra hne
        exact hz (hs hne).2
      rw [hzero, zero_mul]
    have hint : ‖∫ z in coordinateCube j R, K (inverseDilation r x, z) *
        (productPhi b (y - diagonalDilation s.1 z) - productPhi b y)‖ ≤
        V * (B * (Cphi * epsilon * productWeight b y)) := by
      calc
        _ ≤ ∫ z in coordinateCube j R, ‖K (inverseDilation r x, z) *
            (productPhi b (y - diagonalDilation s.1 z) - productPhi b y)‖ :=
          norm_integral_le_integral_norm _
        _ ≤ ∫ _z in coordinateCube j R, B * (Cphi * epsilon * productWeight b y) := by
          apply integral_mono_ae
            (hcont.norm.continuousOn.integrableOn_compact (isCompact_coordinateCube j R))
            (integrableOn_const (isCompact_coordinateCube j R).measure_ne_top)
          filter_upwards [ae_restrict_mem (measurableSet_coordinateCube j R)] with z hz
          rw [norm_mul]
          apply mul_le_mul (hB _)
            (hphi epsilon heps heps1 s b y (diagonalDilation s.1 z) (fun i => ?_) hscale)
            (norm_nonneg _) hB0
          simpa only [diagonalDilation_apply, abs_mul, abs_of_pos (s.2 i), mul_comm] using
            mul_le_mul_of_nonneg_left (hz i) (s.2 i).le
        _ = _ := by
          simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, smul_eq_mul, V]
    have hnorm : ‖(dilationJacobian r : ℂ)⁻¹‖ = (dilationJacobian r)⁻¹ := by
      simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (dilationJacobian_pos r)]
    rw [marginalSmoothingError_eq_integral K hK R hs, ← he, norm_mul, hnorm]
    calc
      _ ≤ (dilationJacobian r)⁻¹ * (V * (B * (Cphi * epsilon * productWeight b y))) :=
        mul_le_mul_of_nonneg_left hint (inv_nonneg.mpr (dilationJacobian_pos r).le)
      _ ≤ (A * productWeight r x) * (V * (B * (Cphi * epsilon * productWeight b y))) :=
        mul_le_mul_of_nonneg_right (jacobian_inv_le_productWeight R hR r x hx)
          (by positivity)
      _ = F * epsilon * B * productWeight r x * productWeight b y := by dsimp [F]; ring
      _ ≤ (F + 1) * epsilon * B * productWeight r x * productWeight b y := by
        gcongr
        linarith
  · rw [marginalSmoothingError_eq_zero_of_notMem K hK R hs r s b x y hx, norm_zero]
    positivity

/-- The block kernel is precisely the original normalized Euclidean kernel. -/
theorem blockDilatedKernel_eq_actual (K : Space (m + j) → ℂ)
    (r : Radii m) (s : Radii j) (p : Space m × Space j) :
    blockDilatedKernel (K ∘ (split m j).symm) r s p =
      dilatedKernel K (joinRadii r s) ((split m j).symm p) := by
  have hi : inverseDilation (joinRadii r s) ((split m j).symm p) =
      (split m j).symm (inverseDilation r p.1, inverseDilation s p.2) := by
    apply (split m j).injective
    rw [split_inverseDilation]
    simp only [MeasurableEquiv.apply_symm_apply]
  unfold blockDilatedKernel dilatedKernel
  rw [hi, dilationJacobian_joinRadii]
  simp only [Function.comp_apply, Complex.ofReal_mul, mul_inv_rev]
  ring

/-- Equation (5.21) stated entirely with the original Euclidean dilation and
the actual coordinate marginal. No kernel estimate is an input hypothesis. -/
theorem exists_actual_partial_smoothing_error_bound (m j : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Space (m + j) → ℂ), Continuous K →
      Function.support K ⊆ MarginalEnergy.coordinateBox (m + j) R →
      ∀ B : ℝ, (∀ p, ‖K p‖ ≤ B) →
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ 1 →
      ∀ (r : Radii m) (s b : Radii j), (∀ i, s.1 i / b.1 i ≤ 2 * epsilon) →
      ∀ (x : Space m) (y : Space j),
      ‖(∫ z, dilatedKernel K (joinRadii r s) ((split m j).symm (x, z)) *
          productPhi b (y - z)) -
        dilatedKernel (MarginalLocalEstimate.marginalKernel K) r x * productPhi b y‖ ≤
        C * epsilon * B * productWeight r x * productWeight b y := by
  obtain ⟨C, hC, hc⟩ := exists_marginalSmoothingError_bound m j R hR
  refine ⟨C, hC, ?_⟩
  intro K hK hs B hB epsilon heps heps1 r s b hscale x y
  have h := hc (K ∘ (split m j).symm)
    (MarginalLocalEstimate.continuous_product_kernel K hK)
    (MarginalLocalEstimate.product_kernel_support K R hs) B (fun _ => hB _)
    epsilon heps heps1 r s b hscale x y
  simpa only [marginalSmoothingError, partialSmoothedKernel,
    blockDilatedKernel_eq_actual, MarginalLocalEstimate.marginalKernel] using h

attribute [local instance] Classical.propDecidable

/-- The same error estimate for every subset, transported back to the
original coordinate labels and original normalized kernel. -/
theorem exists_subset_partial_smoothing_error_bound {n : ℕ} (I : Set (Fin n))
    (R : ℝ) (hR : 0 ≤ R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : Space n → ℂ), Continuous K →
      Function.support K ⊆ MarginalEnergy.coordinateBox n R →
      ∀ B : ℝ, (∀ p, ‖K p‖ ≤ B) →
      ∀ epsilon : ℝ, 0 ≤ epsilon → epsilon ≤ 1 →
      ∀ (r : Radii (Fintype.card I))
        (s b : Radii (Fintype.card (↥(Iᶜ : Set (Fin n))))),
      (∀ i, s.1 i / b.1 i ≤ 2 * epsilon) →
      ∀ (x : Space (Fintype.card I))
        (y : Space (Fintype.card (↥(Iᶜ : Set (Fin n))))),
      ‖(∫ z, dilatedKernel K
          (CoordinateSubsets.reindexRadii (CoordinateSubsets.subsetEnumeration I).symm (joinRadii r s))
          (CoordinateSubsets.coordinatePermutation (CoordinateSubsets.subsetEnumeration I)
            ((split _ _).symm (x, z))) * productPhi b (y - z)) -
        dilatedKernel (CoordinateSubsets.subsetMarginal I K) r x * productPhi b y‖ ≤
        C * epsilon * B * productWeight r x * productWeight b y := by
  obtain ⟨C, hC, hc⟩ := exists_actual_partial_smoothing_error_bound
    (Fintype.card I) (Fintype.card (↥(Iᶜ : Set (Fin n)))) R hR
  refine ⟨C, hC, ?_⟩
  intro K hK hs B hB epsilon heps heps1 r s b hscale x y
  let e := CoordinateSubsets.subsetEnumeration I
  have h := hc (CoordinateSubsets.reorderedKernel e K)
    (hK.comp (CoordinateSubsets.coordinatePermutation e).continuous)
    (CoordinateSubsets.reorderedKernel_support e K R hs) B (fun _ => hB _)
    epsilon heps heps1 r s b hscale x y
  have hcov : ∀ p, dilatedKernel (CoordinateSubsets.reorderedKernel e K) (joinRadii r s) p =
      dilatedKernel K (CoordinateSubsets.reindexRadii e.symm (joinRadii r s))
        (CoordinateSubsets.coordinatePermutation e p) := by
    intro p
    have he := CoordinateSubsets.dilatedKernel_reindex e K
      (CoordinateSubsets.reindexRadii e.symm (joinRadii r s)) p
    simpa only [CoordinateSubsets.reindexRadii_symm] using he
  simp_rw [hcov] at h
  exact h

end StrongSpherical.MarginalSmoothing
