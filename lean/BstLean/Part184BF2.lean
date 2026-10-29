import BstLean.Part184Mom
import BstLean.Part150Mom
import BstLean.Part162Gm
import BstLean.Part170Sq

/-!
# Part 184 (file `BF2`): delocalization of the realized centre weights

No proof is left open; no `native_decide` or `axiom` is used.
-/

namespace BstLean.Part184

open MeasureTheory ProbabilityTheory Real Filter
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part150 (binMean binMean_mono binMean_const binMean_affine binMean_add
  binMean_const_mul binMean_sq binMean_pow4)

/-- The centre weight profile `F(y) = E_Z ReLU(y + sZ)` (binomial `Z`). -/
noncomputable def Fw (J : ℕ) (s y : ℝ) : ℝ := binMean J (fun z => relu (y + s * z))

lemma relu_eq_half (x : ℝ) : relu x = (x + |x|) / 2 := by
  unfold relu; rcases le_total 0 x with h | h
  · rw [max_eq_right h, abs_of_nonneg h]; ring
  · rw [max_eq_left h, abs_of_nonpos h]; ring

lemma Fw_ge_relu (J : ℕ) (s y : ℝ) : relu y ≤ Fw J s y := by
  unfold Fw
  have h1 : binMean J (fun z => y + s * z) ≤ binMean J (fun z => relu (y + s * z)) :=
    binMean_mono J fun z => le_max_right _ _
  have h2 : binMean J (fun _ => (0 : ℝ)) ≤ binMean J (fun z => relu (y + s * z)) :=
    binMean_mono J fun z => le_max_left _ _
  rw [binMean_affine] at h1
  rw [binMean_const] at h2
  exact max_le h2 h1

lemma Fw_nonneg (J : ℕ) (s y : ℝ) : 0 ≤ Fw J s y :=
  (le_max_left _ _).trans (Fw_ge_relu J s y)

lemma binMean_abs_ge {J : ℕ} (hJ : 1 ≤ J) : 1 / 2 ≤ binMean J (fun z => |z|) := by
  have hpt : ∀ z : ℝ, z ^ 2 ≤ |z| + 1 / 6 * z ^ 4 := by
    intro z
    have ht : 0 ≤ |z| := abs_nonneg z
    have e2 : z ^ 2 = |z| ^ 2 := (sq_abs z).symm
    have e4 : z ^ 4 = |z| ^ 4 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
    rw [e2, e4]
    nlinarith [sq_nonneg (|z| - 1), sq_nonneg (|z| ^ 2 - 2), mul_nonneg ht (sq_nonneg (|z| - 1)),
      mul_nonneg ht (sq_nonneg (|z| ^ 2 - 2)), mul_nonneg ht (sq_nonneg (|z| - 3 / 2))]
  have h := binMean_mono J hpt
  rw [binMean_add, binMean_const_mul, binMean_sq hJ, binMean_pow4 hJ] at h
  have : 0 ≤ 2 / (J : ℝ) := by positivity
  linarith

lemma binMean_abs_le {J : ℕ} (hJ : 1 ≤ J) : binMean J (fun z => |z|) ≤ 1 := by
  have hpt : ∀ z : ℝ, |z| ≤ 1 / 2 + 1 / 2 * z ^ 2 := by
    intro z; nlinarith [sq_nonneg (|z| - 1), sq_abs z]
  have h := binMean_mono J hpt
  rw [binMean_add, binMean_const, binMean_const_mul, binMean_sq hJ] at h
  linarith

lemma Fw_ge_s {J : ℕ} (hJ : 1 ≤ J) (s : ℝ) {y : ℝ} (hy : 0 ≤ y) : |s| / 4 ≤ Fw J s y := by
  unfold Fw
  have h1 : binMean J (fun z => relu (s * z)) ≤ binMean J (fun z => relu (y + s * z)) :=
    binMean_mono J fun z => max_le_max le_rfl (by linarith)
  have h2 : binMean J (fun z => relu (s * z)) = |s| * binMean J (fun z => |z|) / 2 := by
    simp_rw [relu_eq_half]
    have : (fun z => (s * z + |s * z|) / 2) = fun z => (0 + s * z) * (1 / 2) + (1 / 2 * |s|) * |z| := by
      funext z; rw [abs_mul]; ring
    rw [this, binMean_add]
    have e1 : binMean J (fun z => (0 + s * z) * (1 / 2)) = 0 := by
      have : (fun z : ℝ => (0 + s * z) * (1 / 2)) = fun z => 0 + (s / 2) * z := by funext z; ring
      rw [this, binMean_affine]
    rw [e1, binMean_const_mul]; ring
  have h3 := binMean_abs_ge hJ
  have : |s| / 4 ≤ |s| * binMean J (fun z => |z|) / 2 := by
    have := mul_le_mul_of_nonneg_left h3 (abs_nonneg s); linarith
  linarith

lemma Fw_le {J : ℕ} (hJ : 1 ≤ J) (s y : ℝ) : Fw J s y ≤ |y| + |s| := by
  unfold Fw
  have h1 : binMean J (fun z => relu (y + s * z)) ≤ binMean J (fun z => |y| + |s| * |z|) := by
    refine binMean_mono J fun z => ?_
    unfold relu
    refine max_le (by positivity) ?_
    have := abs_le.mp (abs_add_le y (s * z)) |>.2
    rw [abs_mul] at this
    linarith [le_abs_self (y + s * z), abs_add_le y (s * z), abs_mul s z]
  rw [binMean_add, binMean_const, binMean_const_mul] at h1
  have := mul_le_mul_of_nonneg_left (binMean_abs_le hJ) (abs_nonneg s)
  linarith

/-- The indicator of `0 ≤ y`. -/
noncomputable def ind0 (y : ℝ) : ℝ := if 0 ≤ y then 1 else 0

lemma ind0_nonneg (y : ℝ) : 0 ≤ ind0 y := by unfold ind0; split_ifs <;> norm_num

lemma ind0_le_one (y : ℝ) : ind0 y ≤ 1 := by unfold ind0; split_ifs <;> norm_num

lemma measurable_ind0 : Measurable ind0 := by
  unfold ind0
  exact Measurable.ite measurableSet_Ici measurable_const measurable_const

lemma Fw_sq_ge {J : ℕ} (hJ : 1 ≤ J) (s y : ℝ) :
    (relu y ^ 2 + s ^ 2 / 16 * ind0 y) / 2 ≤ Fw J s y ^ 2 := by
  have h0 := Fw_nonneg J s y
  have hr := Fw_ge_relu J s y
  have hr0 : 0 ≤ relu y := le_max_left _ _
  have h1 : relu y ^ 2 ≤ Fw J s y ^ 2 := pow_le_pow_left₀ hr0 hr 2
  unfold ind0
  split_ifs with hy
  · have h2 := Fw_ge_s hJ s hy
    have h3 : (|s| / 4) ^ 2 ≤ Fw J s y ^ 2 := pow_le_pow_left₀ (by positivity) h2 2
    rw [div_pow, sq_abs] at h3
    nlinarith
  · nlinarith

lemma Fw_pow4_le {J : ℕ} (hJ : 1 ≤ J) (s y : ℝ) : Fw J s y ^ 4 ≤ 8 * (y ^ 4 + s ^ 4) := by
  have h := Fw_le hJ s y
  have h0 := Fw_nonneg J s y
  have h4 : Fw J s y ^ 4 ≤ (|y| + |s|) ^ 4 := pow_le_pow_left₀ h0 h 4
  have ey : y ^ 4 = |y| ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have es : s ^ 4 = |s| ^ 4 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  rw [ey, es]
  have ha := abs_nonneg y
  have hb := abs_nonneg s
  nlinarith [sq_nonneg (|y| - |s|), sq_nonneg (|y| + |s|), mul_nonneg ha hb,
    sq_nonneg (|y| ^ 2 - |s| ^ 2), mul_nonneg (mul_nonneg ha hb) (sq_nonneg (|y| - |s|))]

lemma continuous_Fw (J : ℕ) (s : ℝ) : Continuous (Fw J s) := by
  unfold Fw BstLean.Part150.binMean
  refine continuous_finset_sum _ fun j _ => continuous_const.mul ?_
  exact continuous_relu.comp (continuous_id.add continuous_const)

/-! ## One-dimensional Gaussian facts -/

lemma gabs_pow_int (r : ℕ) : Integrable (fun x : ℝ => |x| ^ r) (gaussianReal 0 1) := by
  have h := memLp_id_gaussianReal (μ := 0) (v := 1) (r : NNReal)
  have e : ((r : NNReal) : ℝ≥0∞) = (r : ℝ≥0∞) := by simp
  rw [e] at h
  simpa using h.integrable_norm_pow'

lemma gpow_int (r : ℕ) : Integrable (fun x : ℝ => x ^ r) (gaussianReal 0 1) := by
  refine (gabs_pow_int r).mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_pow]

lemma g_symm {f : ℝ → ℝ} (hf : Measurable f) :
    ∫ x, f (-x) ∂gaussianReal 0 1 = ∫ x, f x ∂gaussianReal 0 1 := by
  have h := gaussianReal_map_neg (μ := 0) (v := 1)
  rw [neg_zero] at h
  conv_rhs => rw [← h]
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable]

lemma g_relu_sq : ∫ x, relu x ^ 2 ∂gaussianReal 0 1 = 1 / 2 := by
  have hm : Measurable (fun x : ℝ => relu x ^ 2) := (continuous_relu.pow 2).measurable
  have hi : Integrable (fun x : ℝ => relu x ^ 2) (gaussianReal 0 1) := by
    refine (gpow_int 2).mono' hm.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    unfold relu; rcases le_total 0 x with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h]; nlinarith [sq_nonneg x]
  have hi' : Integrable (fun x : ℝ => relu (-x) ^ 2) (gaussianReal 0 1) := by
    refine (gpow_int 2).mono' (hm.comp measurable_neg).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    unfold relu; rcases le_total 0 (-x) with h | h
    · rw [max_eq_right h, neg_sq]
    · rw [max_eq_left h]; nlinarith [sq_nonneg x]
  have hsum : ∀ x : ℝ, relu x ^ 2 + relu (-x) ^ 2 = x ^ 2 := by
    intro x; unfold relu; rcases le_total 0 x with h | h
    · rw [max_eq_right h, max_eq_left (by linarith : -x ≤ 0)]; ring
    · rw [max_eq_left h, max_eq_right (by linarith : 0 ≤ -x)]; ring
  have h2 : ∫ x, x ^ 2 ∂gaussianReal 0 1 = 1 := by
    have := BstLean.Part170.gmom2_eq
    unfold BstLean.Part162.gmom at this
    simpa [sq_abs] using this
  have hs := g_symm (f := fun x => relu x ^ 2) hm
  have := integral_add hi hi'
  simp_rw [hsum] at this
  rw [h2, hs] at this
  linarith

lemma g_ind0 : 1 / 2 ≤ ∫ x, ind0 x ∂gaussianReal 0 1 := by
  have hi : Integrable ind0 (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).mono' measurable_ind0.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (ind0_nonneg x)]; exact ind0_le_one x)
  have hi' : Integrable (fun x => ind0 (-x)) (gaussianReal 0 1) :=
    (integrable_const (1 : ℝ)).mono' (measurable_ind0.comp measurable_neg).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (ind0_nonneg _)]; exact ind0_le_one _)
  have hpt : ∀ x : ℝ, 1 ≤ ind0 x + ind0 (-x) := by
    intro x; unfold ind0
    by_cases h1 : 0 ≤ x
    · rw [if_pos h1]; split_ifs <;> norm_num
    · rw [if_neg h1, if_pos (by linarith)]; norm_num
  have h1 : ∫ _x, (1 : ℝ) ∂gaussianReal 0 1 ≤ ∫ x, (ind0 x + ind0 (-x)) ∂gaussianReal 0 1 :=
    integral_mono (integrable_const _) (hi.add hi') hpt
  rw [integral_add hi hi', g_symm measurable_ind0] at h1
  simp at h1
  linarith

lemma g_pow4 : ∫ x, x ^ 4 ∂gaussianReal 0 1 = 3 := by
  have h : BstLean.Part162.gmom 4 = 3 := by
    rw [show (4 : ℕ) = 2 * 2 by norm_num, BstLean.Part162.gmom_even]
    simp [Finset.prod_range_succ]; norm_num
  unfold BstLean.Part162.gmom at h
  have e : ∀ x : ℝ, |x| ^ 4 = x ^ 4 := fun x => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  simpa [e] using h

/-! ## The delocalization ratio -/

/-- `R₄(x) = Σx_j⁴/(Σx_j²)²`. -/
noncomputable def R4 {m : ℕ} (x : Fin m → ℝ) : ℝ := (∑ j, x j ^ 4) / (∑ j, x j ^ 2) ^ 2

lemma R4_nonneg {m : ℕ} (x : Fin m → ℝ) : 0 ≤ R4 x := by
  unfold R4; positivity

lemma sum4_le_sq {m : ℕ} (x : Fin m → ℝ) : ∑ j, x j ^ 4 ≤ (∑ j, x j ^ 2) ^ 2 := by
  have hD : ∀ j, x j ^ 2 ≤ ∑ i, x i ^ 2 := fun j =>
    Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  rw [sq (∑ j, x j ^ 2), Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [show x j ^ 4 = x j ^ 2 * x j ^ 2 by ring]
  exact mul_le_mul_of_nonneg_left (hD j) (sq_nonneg _)

lemma R4_le_one {m : ℕ} (x : Fin m → ℝ) : R4 x ≤ 1 := by
  unfold R4
  rcases eq_or_lt_of_le (sq_nonneg (∑ j, x j ^ 2)) with h | h
  · rw [← h]; simp
  · rw [div_le_one h]; exact sum4_le_sq x

lemma R4_le_of {m : ℕ} (x : Fin m → ℝ) {T : ℝ} (hT : 0 < T) (hD : T ≤ ∑ j, x j ^ 2) :
    R4 x ≤ (∑ j, x j ^ 4) / T ^ 2 := by
  unfold R4
  exact div_le_div_of_nonneg_left (Finset.sum_nonneg fun j _ => by positivity) (by positivity)
    (pow_le_pow_left₀ hT.le hD 2)

lemma R4_smul_le {m : ℕ} (c : ℝ) (x : Fin m → ℝ) : R4 (c • x) ≤ R4 x := by
  unfold R4
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rcases eq_or_ne c 0 with hc | hc
  · subst hc; simp; exact R4_nonneg x
  · rw [mul_pow, show (c ^ 2) ^ 2 = c ^ 4 by ring, mul_div_mul_left _ _ (pow_ne_zero 4 hc)]

lemma measurable_R4 {m : ℕ} : Measurable (fun x : Fin m → ℝ => R4 x) := by
  unfold R4
  exact (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).pow_const 4).div
    ((Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).pow_const 2).pow_const 2)


lemma R4_pt_abs {m : ℕ} (x : Fin m → ℝ) {SX Sφ μ μb θ M : ℝ} (hM : 0 < M) (hμ : 0 < μ)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hμb : μ ≤ μb) (hD : SX / 2 ≤ ∑ j, x j ^ 2)
    (hS : Sφ = SX - M * μb) :
    R4 x ≤ (∑ j, x j ^ 4) / (θ * M * μ / 2) ^ 2 + Sφ ^ 2 / ((1 - θ) * M * μ) ^ 2 := by
  have hT : 0 < θ * M * μ / 2 := by positivity
  have hC : 0 < (1 - θ) * M * μ := mul_pos (mul_pos (by linarith) hM) hμ
  have hA0 : 0 ≤ (∑ j, x j ^ 4) / (θ * M * μ / 2) ^ 2 := by positivity
  have hB0 : 0 ≤ Sφ ^ 2 / ((1 - θ) * M * μ) ^ 2 := by positivity
  by_cases hTD : θ * M * μ / 2 ≤ ∑ j, x j ^ 2
  · have := R4_le_of x hT hTD
    linarith
  · push_neg at hTD
    have hSX : SX < θ * M * μ := by linarith
    have hneg : (1 - θ) * M * μ ≤ -Sφ := by
      rw [hS]
      have := mul_le_mul_of_nonneg_left hμb hM.le
      nlinarith
    have h1 : 1 ≤ Sφ ^ 2 / ((1 - θ) * M * μ) ^ 2 := by
      rw [le_div_iff₀ (by positivity), one_mul]
      nlinarith
    have := R4_le_one x
    linarith

lemma deloc_arith {M a u μ : ℝ} (hM : 1 ≤ M) (ha : 0 ≤ a) (hu : 0 ≤ u) (hμ : μ = a / 2 + u / 32)
    (hμ0 : 0 < μ) :
    M * (8 * (3 * a ^ 2 + u ^ 2)) / (17 / 20 * M * μ / 2) ^ 2 +
      M * (6 * a ^ 2 + u ^ 2 / 128) / ((1 - 17 / 20) * M * μ) ^ 2 ≤ 47400 / M := by
  have hM0 : 0 < M := by linarith
  have ha2 : a ^ 2 ≤ 4 * μ ^ 2 := by rw [hμ]; nlinarith
  have hu2 : u ^ 2 ≤ 1024 * μ ^ 2 := by rw [hμ]; nlinarith
  have hμ2 : 0 < μ ^ 2 := by positivity
  have e1 : M * (8 * (3 * a ^ 2 + u ^ 2)) / (17 / 20 * M * μ / 2) ^ 2 =
      (8 * (3 * a ^ 2 + u ^ 2)) / μ ^ 2 * (1600 / 289) / M := by
    field_simp; ring
  have e2 : M * (6 * a ^ 2 + u ^ 2 / 128) / ((1 - 17 / 20) * M * μ) ^ 2 =
      (6 * a ^ 2 + u ^ 2 / 128) / μ ^ 2 * (400 / 9) / M := by
    field_simp; ring
  have b1 : (8 * (3 * a ^ 2 + u ^ 2)) / μ ^ 2 ≤ 8288 := by
    rw [div_le_iff₀ hμ2]; nlinarith
  have b2 : (6 * a ^ 2 + u ^ 2 / 128) / μ ^ 2 ≤ 32 := by
    rw [div_le_iff₀ hμ2]; nlinarith
  rw [e1, e2, ← add_div]
  refine div_le_div_of_nonneg_right ?_ hM0.le
  nlinarith

/-- **Delocalization of the centre weights**: for `y_j = σξ_j` with `ξ` standard Gaussian,
`E R₄(F(y)) ≤ 47400/m`. -/
theorem deloc {m J : ℕ} (hJ : 1 ≤ J) (hm : 1 ≤ m) (s : ℝ) {σ : ℝ} (hσ : 0 ≤ σ) :
    ∫⁻ ξ, ENNReal.ofReal (R4 (fun j => Fw J s (σ * ξ j))) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal (47400 / m) := by
  set γ := gaussianReal 0 1 with hγ
  have hP : stdGauss (Fin m) = Measure.pi fun _ : Fin m => γ := rfl
  set a := σ ^ 2 with had
  set u := s ^ 2 with hud
  have ha0 : 0 ≤ a := sq_nonneg σ
  have hu0 : 0 ≤ u := sq_nonneg s
  set μ := a / 2 + u / 32 with hμd
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have cF : Continuous (fun ξ : Fin m → ℝ => fun j => Fw J s (σ * ξ j)) :=
    continuous_pi fun j => (continuous_Fw J s).comp (continuous_const.mul (continuous_apply j))
  have mR : Measurable (fun ξ : Fin m → ℝ => R4 (fun j => Fw J s (σ * ξ j))) :=
    measurable_R4.comp cF.measurable
  have iR : Integrable (fun ξ : Fin m → ℝ => R4 (fun j => Fw J s (σ * ξ j))) (stdGauss (Fin m)) :=
    (integrable_const (1 : ℝ)).mono' mR.aestronglyMeasurable (Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs, abs_of_nonneg (R4_nonneg _)]; exact R4_le_one _)
  rw [← ofReal_integral_eq_lintegral_ofReal iR (Eventually.of_forall fun ξ => R4_nonneg _)]
  refine ENNReal.ofReal_le_ofReal ?_
  rcases eq_or_lt_of_le (show 0 ≤ μ by positivity) with hμ | hμ
  · -- σ = 0 and s = 0
    have ha : a = 0 := by linarith
    have hu : u = 0 := by linarith
    have hσ0 : σ = 0 := by nlinarith
    have hs0 : s = 0 := by nlinarith
    have hz : ∀ ξ : Fin m → ℝ, R4 (fun j => Fw J s (σ * ξ j)) = 0 := by
      intro ξ
      have : ∀ j, Fw J s (σ * ξ j) = 0 := fun j => by
        rw [hσ0, hs0]; unfold Fw; simp [relu, BstLean.Part150.binMean]
      simp [R4, this]
    simp_rw [hz]; simp; positivity
  -- the profile functions
  set X : ℝ → ℝ := fun x => a * relu x ^ 2 + u / 16 * ind0 x with hXd
  have mX : Measurable X :=
    (measurable_const.mul ((continuous_relu.pow 2).measurable)).add
      (measurable_const.mul measurable_ind0)
  have hrelu2 : ∀ x : ℝ, relu x ^ 2 ≤ x ^ 2 := fun x => by
    unfold relu; rcases le_total 0 x with h | h
    · rw [max_eq_right h]
    · rw [max_eq_left h]; nlinarith [sq_nonneg x]
  have hX0 : ∀ x, 0 ≤ X x := fun x => by
    have := ind0_nonneg x; simp only [X]; positivity
  have hXle : ∀ x, X x ≤ a * x ^ 2 + u / 16 := fun x => by
    have := ind0_le_one x
    have := hrelu2 x
    simp only [X]; nlinarith
  have iX2 : Integrable (fun x => X x ^ 2) γ := by
    refine (((gpow_int 4).const_mul (2 * a ^ 2)).add (integrable_const (2 * (u / 16) ^ 2))).mono'
      (mX.pow_const 2).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := hXle x
    have h2 := pow_le_pow_left₀ (hX0 x) h1 2
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (a * x ^ 2 - u / 16)]
  have iX : Integrable X γ := by
    refine (iX2.add (integrable_const 1)).mono' mX.aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hX0 x)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (X x - 1)]
  set μb := ∫ x, X x ∂γ with hμbd
  have hμb : μ ≤ μb := by
    have i1 : Integrable (fun x : ℝ => relu x ^ 2) γ := by
      refine (gpow_int 2).mono' (continuous_relu.pow 2).measurable.aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hrelu2 x
    have i2 : Integrable ind0 γ :=
      (integrable_const (1 : ℝ)).mono' measurable_ind0.aestronglyMeasurable
        (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs, abs_of_nonneg (ind0_nonneg x)]; exact ind0_le_one x)
    simp only [μb, X]
    rw [integral_add (i1.const_mul a) (i2.const_mul _), integral_const_mul, integral_const_mul,
      g_relu_sq]
    have := g_ind0
    simp only [μ]
    nlinarith
  have hX2 : ∫ x, X x ^ 2 ∂γ ≤ 6 * a ^ 2 + u ^ 2 / 128 := by
    have hb : ∀ x, X x ^ 2 ≤ 2 * a ^ 2 * x ^ 4 + 2 * (u / 16) ^ 2 := fun x => by
      have h2 := pow_le_pow_left₀ (hX0 x) (hXle x) 2
      nlinarith [sq_nonneg (a * x ^ 2 - u / 16)]
    have := integral_mono iX2 (((gpow_int 4).const_mul (2 * a ^ 2)).add
      (integrable_const (2 * (u / 16) ^ 2))) hb
    simp only [Pi.add_apply] at this
    rw [integral_add ((gpow_int 4).const_mul _) (integrable_const _), integral_const_mul,
      g_pow4] at this
    simp at this
    nlinarith
  -- the centred row variable
  set φ : ℝ → ℝ := fun x => X x - μb with hφd
  have mφ : Measurable φ := mX.sub_const _
  have iφ8 : Integrable (fun x => φ x ^ 8) γ := by
    set c := u / 16 + |μb|
    refine (((gpow_int 16).const_mul (2 ^ 8 * a ^ 8)).add (integrable_const (2 ^ 8 * c ^ 8))).mono'
      (mφ.pow_const 8).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    have hax : 0 ≤ a * x ^ 2 := by positivity
    have hb : |φ x| ≤ c + a * x ^ 2 := by
      simp only [φ, c]
      have h1 := hXle x; have h2 := hX0 x
      have h3 := le_abs_self μb; have h4 := neg_abs_le μb
      rw [abs_le]; constructor <;> linarith
    have hc0 : 0 ≤ c := by positivity
    rw [Real.norm_eq_abs, abs_pow]
    have h1 : |φ x| ^ 8 ≤ (c + a * x ^ 2) ^ 8 := pow_le_pow_left₀ (abs_nonneg _) hb 8
    have hmx : c + a * x ^ 2 ≤ 2 * max c (a * x ^ 2) := by
      have := le_max_left c (a * x ^ 2); have := le_max_right c (a * x ^ 2); linarith
    have h2 : (c + a * x ^ 2) ^ 8 ≤ (2 * max c (a * x ^ 2)) ^ 8 :=
      pow_le_pow_left₀ (by positivity) hmx 8
    have h3 : (max c (a * x ^ 2)) ^ 8 ≤ c ^ 8 + (a * x ^ 2) ^ 8 := by
      rcases le_total c (a * x ^ 2) with h | h
      · rw [max_eq_right h]; linarith [pow_nonneg hc0 8]
      · rw [max_eq_left h]; linarith [pow_nonneg hax 8]
    simp only [Pi.add_apply]
    calc |φ x| ^ 8 ≤ (2 * max c (a * x ^ 2)) ^ 8 := h1.trans h2
      _ = 2 ^ 8 * (max c (a * x ^ 2)) ^ 8 := mul_pow _ _ _
      _ ≤ 2 ^ 8 * (c ^ 8 + (a * x ^ 2) ^ 8) := by gcongr
      _ = 2 ^ 8 * a ^ 8 * x ^ 16 + 2 ^ 8 * c ^ 8 := by ring
  have hφ0 : ∫ x, φ x ∂γ = 0 := by
    simp only [φ]; rw [integral_sub iX (integrable_const _)]; simp [μb]
  obtain ⟨iS2, hS2⟩ := mom_all γ m (fun _ => φ) (fun _ => mφ) (fun _ => iφ8) (fun _ => hφ0) 2
    (by norm_num)
  have hSm : Smom γ (fun _ : Fin m => φ) 2 ≤ m * (6 * a ^ 2 + u ^ 2 / 128) := by
    unfold Smom
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_left ?_ hm0.le
    have e : ∫ x, |φ x| ^ 2 ∂γ = ∫ x, X x ^ 2 ∂γ - μb ^ 2 := by
      simp_rw [sq_abs]
      simp only [φ]
      have : (fun x => (X x - μb) ^ 2) = fun x => X x ^ 2 - 2 * μb * X x + μb ^ 2 := by
        funext x; ring
      rw [this]
      have h1 := integral_add (f := fun x => X x ^ 2 - 2 * μb * X x) (g := fun _ => μb ^ 2)
        (μ := γ) (iX2.sub (iX.const_mul _)) (integrable_const _)
      have h2 := integral_sub (f := fun x => X x ^ 2) (g := fun x => 2 * μb * X x)
        (μ := γ) iX2 (iX.const_mul _)
      rw [h1, h2, integral_const_mul]
      simp [μb]; ring
    rw [e]; nlinarith [sq_nonneg μb]
  -- the pointwise bound
  set θ : ℝ := 17 / 20
  set T : ℝ := θ * m * μ / 2 with hTd
  set C : ℝ := (1 - θ) * m * μ with hCd
  have hT : 0 < T := by positivity
  have hC : 0 < C := by simp only [C, θ]; positivity
  have hpt : ∀ ξ : Fin m → ℝ, R4 (fun j => Fw J s (σ * ξ j)) ≤
      (∑ j, Fw J s (σ * ξ j) ^ 4) / T ^ 2 + (∑ j, φ (ξ j)) ^ 2 / C ^ 2 := by
    intro ξ
    have hD : (∑ j, X (ξ j)) / 2 ≤ ∑ j, Fw J s (σ * ξ j) ^ 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_le_sum fun j _ => ?_
      have h1 := Fw_sq_ge hJ s (σ * ξ j)
      have hr : relu (σ * ξ j) ^ 2 = a * relu (ξ j) ^ 2 := by
        unfold relu
        rcases le_total 0 (ξ j) with h | h
        · rw [max_eq_right h, max_eq_right (mul_nonneg hσ h)]; ring
        · rw [max_eq_left h, max_eq_left (mul_nonpos_of_nonneg_of_nonpos hσ h)]; ring
      have hi : ind0 (ξ j) ≤ ind0 (σ * ξ j) := by
        unfold ind0
        by_cases h1 : 0 ≤ ξ j
        · rw [if_pos h1, if_pos (mul_nonneg hσ h1)]
        · rw [if_neg h1]; split_ifs <;> norm_num
      rw [hr] at h1
      simp only [X]
      have : u / 16 * ind0 (ξ j) ≤ s ^ 2 / 16 * ind0 (σ * ξ j) := by
        simp only [u]; gcongr
      linarith
    have hsum : ∑ j, φ (ξ j) = ∑ j, X (ξ j) - m * μb := by
      simp only [φ, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
    exact R4_pt_abs (fun j => Fw J s (σ * ξ j)) hm0 hμ (by norm_num) (by norm_num) hμb hD hsum
  -- integrate
  have iN : ∀ j : Fin m, Integrable (fun ξ : Fin m → ℝ => Fw J s (σ * ξ j) ^ 4) (stdGauss (Fin m)) := by
    intro j
    have i1 : Integrable (fun x : ℝ => Fw J s (σ * x) ^ 4) γ := by
      refine (((gpow_int 4).const_mul (8 * σ ^ 4)).add (integrable_const (8 * s ^ 4))).mono'
        (((continuous_Fw J s).comp (continuous_const.mul continuous_id)).measurable.pow_const 4
          |>.aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Fw_nonneg _ _ _) 4)]
      have := Fw_pow4_le hJ s (σ * x)
      simp only [Pi.add_apply]; rw [mul_pow] at this; linarith
    rw [hP]
    exact (measurePreserving_eval (fun _ : Fin m => γ) j).integrable_comp_of_integrable i1
  have hN : ∫ ξ, ∑ j, Fw J s (σ * ξ j) ^ 4 ∂stdGauss (Fin m) ≤ m * (8 * (3 * a ^ 2 + u ^ 2)) := by
    rw [integral_finset_sum _ fun j _ => iN j]
    have hj : ∀ j : Fin m, ∫ ξ, Fw J s (σ * ξ j) ^ 4 ∂stdGauss (Fin m) ≤ 8 * (3 * a ^ 2 + u ^ 2) := by
      intro j
      have hb : ∀ ξ : Fin m → ℝ, Fw J s (σ * ξ j) ^ 4 ≤ 8 * σ ^ 4 * ξ j ^ 4 + 8 * s ^ 4 := by
        intro ξ; have := Fw_pow4_le hJ s (σ * ξ j); rw [mul_pow] at this; linarith
      have ic : Integrable (fun ξ : Fin m → ℝ => 8 * σ ^ 4 * ξ j ^ 4 + 8 * s ^ 4) (stdGauss (Fin m)) :=
        ((BstLean.Part108.coordPow_int j 4).const_mul _).add (integrable_const _)
      refine (integral_mono (iN j) ic hb).trans (le_of_eq ?_)
      rw [integral_add ((BstLean.Part108.coordPow_int j 4).const_mul _) (integrable_const _),
        integral_const_mul]
      have e4 : ∫ ξ : Fin m → ℝ, ξ j ^ 4 ∂stdGauss (Fin m) = 3 := by
        rw [hP]
        have := integral_comp_eval (μ := fun _ : Fin m => γ) (i := j) (f := fun x : ℝ => x ^ 4)
          (gpow_int 4).aestronglyMeasurable
        exact this.trans g_pow4
      rw [e4]; simp [a, u]; ring
    calc ∑ j, ∫ ξ, Fw J s (σ * ξ j) ^ 4 ∂stdGauss (Fin m) ≤ ∑ _j : Fin m, 8 * (3 * a ^ 2 + u ^ 2) :=
          Finset.sum_le_sum fun j _ => hj j
      _ = _ := by simp
  have iB : Integrable (fun ξ : Fin m → ℝ => (∑ j, φ (ξ j)) ^ 2) (stdGauss (Fin m)) := by
    rw [hP]; exact iS2
  have hB : ∫ ξ, (∑ j, φ (ξ j)) ^ 2 ∂stdGauss (Fin m) ≤ m * (6 * a ^ 2 + u ^ 2 / 128) := by
    rw [hP]
    have : (∫ ξ, (∑ j, φ (ξ j)) ^ 2 ∂Measure.pi fun _ : Fin m => γ) ≤ Ek (Smom γ (fun _ => φ)) 2 :=
      (le_abs_self _).trans hS2
    simp only [Ek] at this
    linarith
  have iA : Integrable (fun ξ : Fin m → ℝ => ∑ j, Fw J s (σ * ξ j) ^ 4) (stdGauss (Fin m)) :=
    integrable_finset_sum _ fun j _ => iN j
  calc ∫ ξ, R4 (fun j => Fw J s (σ * ξ j)) ∂stdGauss (Fin m)
      ≤ ∫ ξ, ((∑ j, Fw J s (σ * ξ j) ^ 4) / T ^ 2 + (∑ j, φ (ξ j)) ^ 2 / C ^ 2)
          ∂stdGauss (Fin m) :=
        integral_mono iR ((iA.div_const _).add (iB.div_const _)) hpt
    _ = (∫ ξ, ∑ j, Fw J s (σ * ξ j) ^ 4 ∂stdGauss (Fin m)) / T ^ 2 +
          (∫ ξ, (∑ j, φ (ξ j)) ^ 2 ∂stdGauss (Fin m)) / C ^ 2 := by
        rw [integral_add (iA.div_const _) (iB.div_const _), integral_div, integral_div]
    _ ≤ m * (8 * (3 * a ^ 2 + u ^ 2)) / T ^ 2 + m * (6 * a ^ 2 + u ^ 2 / 128) / C ^ 2 := by
        gcongr
    _ ≤ 47400 / m := deloc_arith (by exact_mod_cast hm) ha0 hu0 rfl hμ

end BstLean.Part184
