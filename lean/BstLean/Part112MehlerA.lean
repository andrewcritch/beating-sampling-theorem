import BstLean.Part112Defs

/-!
# Part 112, helper H1: the second-order Gebelein inequality, given the first-chaos limit

* `chaos1Bessel : Chaos1Bessel` (Bessel for the coordinate functions).
* `prodContract`: `N(c) − 2N(κc) ≤ c⁴ (N(1) − 2N(κ))` for bounded `h` of mean zero.
* `mehler2_of (hB : ChaosLimit) : Mehler2`.

No `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part112

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part48 (rotX rotY rot_preserving)
open BstLean.Part105
open BstLean.Part107 (gauss_pair107 gauss_pair_integrable107 lin_sq_integrable107
  lin_sq_integral107)

variable {ι : Type} [Fintype ι]

/-! ## The coordinate functions -/

lemma coord_integrable (i : ι) : Integrable (fun z : ι → ℝ => z i) (stdGauss ι) := by
  classical
  have h := BstLean.Part35.stdGauss_prod_integrable (ι := ι) 1 ![i]
  simpa using h

lemma coord_integral (i : ι) : ∫ z, z i ∂stdGauss ι = 0 := by
  classical
  have h := BstLean.Part35.stdGauss_wick_step i 0 (Fin.elim0 : Fin 0 → ι)
  simpa using h

variable {f g h : (ι → ℝ) → ℝ}

lemma bm_mul_coord_integrable (hh : BM h) (i : ι) :
    Integrable (fun x => h x * x i) (stdGauss ι) := by
  obtain ⟨M, hM⟩ := hh.bdd
  refine Integrable.mono' ((coord_integrable i).norm.const_mul M)
    (hh.meas.mul (measurable_pi_apply i)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right ((Real.norm_eq_abs _).le.trans (hM x)) (norm_nonneg _)

/-- The first-chaos coefficient `E[h(x) x_i]`. -/
noncomputable def lc (h : (ι → ℝ) → ℝ) (i : ι) : ℝ := ∫ x, h x * x i ∂stdGauss ι

lemma mul_lin_eq (h : (ι → ℝ) → ℝ) (a : ι → ℝ) (x : ι → ℝ) :
    h x * ∑ i, x i * a i = ∑ i, a i * (h x * x i) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma mul_lin_integrable (hh : BM h) (a : ι → ℝ) :
    Integrable (fun x => h x * ∑ i, x i * a i) (stdGauss ι) := by
  simp_rw [mul_lin_eq]
  exact integrable_finsetSum _ fun i _ => (bm_mul_coord_integrable hh i).const_mul _

lemma int_mul_lin (hh : BM h) (a : ι → ℝ) :
    ∫ x, h x * ∑ i, x i * a i ∂stdGauss ι = ∑ i, a i * lc h i := by
  simp_rw [mul_lin_eq]
  rw [integral_finsetSum _ fun i _ => (bm_mul_coord_integrable hh i).const_mul _]
  simp_rw [integral_const_mul]
  rfl

/-- Bessel for the coordinate functions: `Σ_i (E h x_i)² ≤ E h²`. -/
lemma bessel_core (hh : BM h) : ∑ i, lc h i ^ 2 ≤ ∫ x, h x ^ 2 ∂stdGauss ι := by
  classical
  set a : ι → ℝ := fun i => lc h i with ha
  have hpos : 0 ≤ ∫ x, (h x - ∑ i, x i * a i) ^ 2 ∂stdGauss ι :=
    integral_nonneg fun _ => sq_nonneg _
  have e : (fun x : ι → ℝ => (h x - ∑ i, x i * a i) ^ 2) = fun x =>
      h x ^ 2 - 2 * (h x * ∑ i, x i * a i) + (∑ i, x i * a i) ^ 2 := by
    funext x; ring
  have I1 := hh.sq.integrable (stdGauss ι)
  have I2 := (mul_lin_integrable hh a).const_mul 2
  have I3 := lin_sq_integrable107 a
  have I12 : Integrable (fun x : ι → ℝ => h x ^ 2 - 2 * (h x * ∑ i, x i * a i)) (stdGauss ι) :=
    I1.sub I2
  rw [e, integral_add I12 I3, integral_sub I1 I2, integral_const_mul, int_mul_lin hh,
    lin_sq_integral107] at hpos
  have : ∑ i, a i * lc h i = ∑ i, a i ^ 2 := Finset.sum_congr rfl fun i _ => by simp [ha, sq]
  rw [this] at hpos
  linarith

lemma lc_sub_const (hf : BM f) (m : ℝ) (i : ι) : lc (fun x => f x - m) i = lc f i := by
  unfold lc
  have : (fun x : ι → ℝ => (f x - m) * x i) = fun x => f x * x i - m * x i := by
    funext x; ring
  rw [this, integral_sub (bm_mul_coord_integrable hf i) ((coord_integrable i).const_mul m),
    integral_const_mul, coord_integral]
  simp

/-- **Bessel for the first chaos.** -/
theorem chaos1Bessel : Chaos1Bessel := by
  intro ι _ f hf
  have h := bessel_core (hf.sub (BM.const (∫ y, f y ∂stdGauss ι)))
  simp_rw [lc_sub_const hf] at h
  exact h

/-- `E[(T_c h)(x) x_i] = c E[h(x) x_i]`. -/
lemma lc_Tou {c : ℝ} (hc : |c| ≤ 1) (hh : BM h) (i : ι) : lc (Tou c h) i = c * lc h i := by
  obtain ⟨M, hM⟩ := hh.bdd
  have bA : BM (fun w : (ι → ℝ) × (ι → ℝ) => h (c • w.1 + sC c • w.2)) :=
    hh.comp (meas_comb c (sC c))
  have I0 : Integrable (fun w : (ι → ℝ) × (ι → ℝ) => h (c • w.1 + sC c • w.2) * w.1 i)
      ((stdGauss ι).prod (stdGauss ι)) := by
    refine Integrable.mono' (((coord_integrable i).comp_fst (stdGauss ι)).norm.const_mul M)
      (bA.meas.mul ((measurable_pi_apply i).comp measurable_fst)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun w => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right ((Real.norm_eq_abs _).le.trans (hM _)) (norm_nonneg _)
  have e1 : lc (Tou c h) i =
      ∫ w, h (c • w.1 + sC c • w.2) * w.1 i ∂((stdGauss ι).prod (stdGauss ι)) := by
    rw [integral_prod _ I0]
    simp only [lc, Tou, integral_mul_const]
  rw [e1]
  set θ := Real.arccos c with hθ
  have hcos : Real.cos θ = c := Real.cos_arccos (abs_le.mp hc).1 (abs_le.mp hc).2
  have hsin : Real.sin θ = sC c := by rw [hθ, Real.sin_arccos]; rfl
  have hmp := rot_preserving (ι := ι) θ
  set H : (ι → ℝ) × (ι → ℝ) → ℝ := fun v => h v.1 * (c * v.1 i - sC c * v.2 i) with hH
  have hHm : Measurable H := by
    have := hh.meas
    simp only [hH]
    fun_prop
  have key : ∀ w : (ι → ℝ) × (ι → ℝ), h (c • w.1 + sC c • w.2) * w.1 i =
      H (rotX θ w.1 w.2, rotY θ w.1 w.2) := by
    intro w
    simp only [hH]
    have e2 : rotX θ w.1 w.2 = c • w.1 + sC c • w.2 := by
      funext j
      simp [rotX, hcos, hsin]
    have e3 : c * rotX θ w.1 w.2 i - sC c * rotY θ w.1 w.2 i = w.1 i := by
      simp only [rotX, rotY, hcos, hsin]
      have := sC_sq hc
      linear_combination (w.1 i) * this
    rw [e3, e2]
  simp_rw [key]
  rw [mp_integral hmp H hHm]
  have J1 : Integrable (fun v : (ι → ℝ) × (ι → ℝ) => h v.1 * v.1 i)
      ((stdGauss ι).prod (stdGauss ι)) := (bm_mul_coord_integrable hh i).comp_fst (stdGauss ι)
  have J2 : Integrable (fun v : (ι → ℝ) × (ι → ℝ) => h v.1 * v.2 i)
      ((stdGauss ι).prod (stdGauss ι)) :=
    (hh.integrable (stdGauss ι)).mul_prod (coord_integrable i)
  have e4 : H = fun v => c * (h v.1 * v.1 i) - sC c * (h v.1 * v.2 i) := by
    funext v; simp only [hH]; ring
  have e5 : ∫ v : (ι → ℝ) × (ι → ℝ), h v.1 * v.2 i ∂((stdGauss ι).prod (stdGauss ι)) = 0 := by
    rw [integral_prod_mul (fun x : ι → ℝ => h x) (fun z : ι → ℝ => z i), coord_integral]
    simp
  have e6 : ∫ v : (ι → ℝ) × (ι → ℝ), h v.1 * v.1 i ∂((stdGauss ι).prod (stdGauss ι)) =
      lc h i := by
    rw [integral_fun_fst (fun x : ι → ℝ => h x * x i)]
    simp [lc]
  rw [e4, integral_sub (J1.const_mul c) (J2.const_mul (sC c)), integral_const_mul,
    integral_const_mul, e5, e6]
  simp

/-! ## The product contraction -/

/-- Contraction in the first variable of a function that is centred in that variable. -/
lemma part_contract {H : (ι → ℝ) × (ι → ℝ) → ℝ} (hH : BM H) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hcent : ∀ z, ∫ x, H (x, z) ∂stdGauss ι = 0) :
    ∫ w, (∫ x', H (c • w.1 + sC c • x', w.2) ∂stdGauss ι) ^ 2
        ∂((stdGauss ι).prod (stdGauss ι)) ≤
      c ^ 2 * ∫ w, H w ^ 2 ∂((stdGauss ι).prod (stdGauss ι)) := by
  have bH1 : BM (fun w : (ι → ℝ) × (ι → ℝ) =>
      ∫ x', H (c • w.1 + sC c • x', w.2) ∂stdGauss ι) := by
    have : BM (fun p : ((ι → ℝ) × (ι → ℝ)) × (ι → ℝ) => H (c • p.1.1 + sC c • p.2, p.1.2)) :=
      hH.comp (by fun_prop)
    exact this.integral_right (stdGauss ι)
  rw [integral_prod_symm _ (bH1.sq.integrable _), integral_prod_symm _ (hH.sq.integrable _),
    ← integral_const_mul]
  refine integral_mono ((bH1.sq.integral_left (stdGauss ι)).integrable _)
    (((BM.const (c ^ 2)).mul (hH.sq.integral_left (stdGauss ι))).integrable _) fun z => ?_
  have hz : BM (fun x => H (x, z)) := hH.comp (measurable_id.prodMk measurable_const)
  exact Nou_le hz (hcent z) hc0 hc1

/-- The part of `h(κx + κz)` that is centred in each variable. -/
noncomputable def mH (h : (ι → ℝ) → ℝ) (w : (ι → ℝ) × (ι → ℝ)) : ℝ :=
  h (cc 1 • w.1 + cc 1 • w.2) - Tou (cc 1) h w.1 - Tou (cc 1) h w.2

lemma bm_mH (hh : BM h) : BM (mH h) :=
  ((hh.comp (meas_comb (cc 1) (cc 1))).sub ((Tou_BM (cc 1) hh).comp measurable_fst)).sub
    ((Tou_BM (cc 1) hh).comp measurable_snd)

lemma mH_swap (h : (ι → ℝ) → ℝ) (x z : ι → ℝ) : mH h (z, x) = mH h (x, z) := by
  simp only [mH]
  rw [add_comm (cc 1 • z) (cc 1 • x)]
  ring

lemma mH_sq (hh : BM h) (h0 : ∫ x, h x ∂stdGauss ι = 0) :
    ∫ w, mH h w ^ 2 ∂((stdGauss ι).prod (stdGauss ι)) =
      ∫ x, h x ^ 2 ∂stdGauss ι - 2 * Nou (cc 1) h := by
  set κ := cc 1 with hκ
  set T := Tou κ h with hT
  have bT : BM T := Tou_BM κ hh
  set A : (ι → ℝ) × (ι → ℝ) → ℝ := fun w => h (κ • w.1 + κ • w.2) with hA
  have bA : BM A := hh.comp (meas_comb κ κ)
  have bA1 : BM (fun w : (ι → ℝ) × (ι → ℝ) => T w.1) := bT.comp measurable_fst
  have bA2 : BM (fun w : (ι → ℝ) × (ι → ℝ) => T w.2) := bT.comp measurable_snd
  have iAA : ∫ w, A w ^ 2 ∂((stdGauss ι).prod (stdGauss ι)) = ∫ x, h x ^ 2 ∂stdGauss ι := by
    have h1 := gauss_comb κ κ (cc_pos 1).le (fun y => h y ^ 2) hh.sq.meas
    have h2 : Real.sqrt (κ ^ 2 + κ ^ 2) = 1 := by rw [cc_one_sq]; norm_num
    rw [h2] at h1
    simpa using h1
  have i11 : ∫ w, T w.1 ^ 2 ∂((stdGauss ι).prod (stdGauss ι)) = Nou κ h := by
    rw [integral_fun_fst (fun x => T x ^ 2)]; simp [Nou, hT]
  have i22 : ∫ w, T w.2 ^ 2 ∂((stdGauss ι).prod (stdGauss ι)) = Nou κ h := by
    rw [integral_fun_snd (fun x => T x ^ 2)]; simp [Nou, hT]
  have iA1 : ∫ w, A w * T w.1 ∂((stdGauss ι).prod (stdGauss ι)) = Nou κ h := by
    have h1 := integral_mul_Tou κ bT hh
    rw [sC_cc_one] at h1
    calc ∫ w, A w * T w.1 ∂((stdGauss ι).prod (stdGauss ι))
        = ∫ w, T w.1 * h (κ • w.1 + κ • w.2) ∂((stdGauss ι).prod (stdGauss ι)) := by
          congr 1; funext w; simp only [hA]; ring
      _ = ∫ x, T x * Tou κ h x ∂stdGauss ι := h1.symm
      _ = Nou κ h := by simp only [Nou, pow_two, hT]
  have iA2 : ∫ w, A w * T w.2 ∂((stdGauss ι).prod (stdGauss ι)) = Nou κ h := by
    rw [← iA1, ← integral_prod_swap]
    congr 1
    funext w
    simp only [hA, Prod.fst_swap, Prod.snd_swap, add_comm]
  have i12 : ∫ w, T w.1 * T w.2 ∂((stdGauss ι).prod (stdGauss ι)) = 0 := by
    rw [integral_prod_mul, hT, integral_Tou (cc_abs zero_le_one) hh, h0]
    simp
  have b1 := bA.sq
  have b2 := bA1.sq
  have b3 := bA2.sq
  have b4 := (BM.const (α := (ι → ℝ) × (ι → ℝ)) 2).mul (bA.mul bA1)
  have b5 := (BM.const (α := (ι → ℝ) × (ι → ℝ)) 2).mul (bA.mul bA2)
  have b6 := (BM.const (α := (ι → ℝ) × (ι → ℝ)) 2).mul (bA1.mul bA2)
  have e : (fun w : (ι → ℝ) × (ι → ℝ) => mH h w ^ 2) = fun w =>
      A w ^ 2 + T w.1 ^ 2 + T w.2 ^ 2 - 2 * (A w * T w.1) - 2 * (A w * T w.2) +
        2 * (T w.1 * T w.2) := by
    funext w; simp only [mH, hA, hT, hκ]; ring
  rw [e, integral_add (((((b1.add b2).add b3).sub b4).sub b5).integrable _) (b6.integrable _),
    integral_sub ((((b1.add b2).add b3).sub b4).integrable _) (b5.integrable _),
    integral_sub (((b1.add b2).add b3).integrable _) (b4.integrable _),
    integral_add ((b1.add b2).integrable _) (b3.integrable _),
    integral_add (b1.integrable _) (b2.integrable _),
    integral_const_mul, integral_const_mul, integral_const_mul,
    iAA, i11, i22, iA1, iA2, i12]
  ring

lemma mH_cent (hh : BM h) (h0 : ∫ x, h x ∂stdGauss ι = 0) (z : ι → ℝ) :
    ∫ x, mH h (x, z) ∂stdGauss ι = 0 := by
  have b1 : BM (fun x : ι → ℝ => h (cc 1 • x + cc 1 • z)) :=
    hh.comp ((measurable_const_smul (cc 1)).add measurable_const)
  have bT := Tou_BM (ι := ι) (cc 1) hh
  have e1 : ∫ x, h (cc 1 • x + cc 1 • z) ∂stdGauss ι = Tou (cc 1) h z := by
    simp only [Tou, sC_cc_one]
    congr 1
    funext x
    rw [add_comm]
  simp only [mH]
  rw [integral_sub (b1.sub bT |>.integrable _) (integrable_const _),
    integral_sub (b1.integrable _) (bT.integrable _), e1,
    integral_Tou (cc_abs zero_le_one) hh, h0]
  simp

/-- `(T_c ⊗ T_c) m_h = m_{T_c h}`. -/
lemma mH_Tou (hh : BM h) {c : ℝ} (hc : |c| ≤ 1) (x z : ι → ℝ) :
    ∫ z', (∫ x', mH h (c • x + sC c • x', c • z + sC c • z') ∂stdGauss ι) ∂stdGauss ι =
      mH (Tou c h) (x, z) := by
  set κ := cc 1 with hκ
  set s := sC c with hs
  have hκabs : |κ| ≤ 1 := cc_abs zero_le_one
  have bT := Tou_BM (ι := ι) κ hh
  set G : (ι → ℝ) × (ι → ℝ) → ℝ := fun p =>
    h (κ • (c • x + s • p.2) + κ • (c • z + s • p.1)) with hG
  have bG : BM G := hh.comp (by fun_prop)
  have bG2 : ∀ z', BM (fun x' : ι → ℝ => G (z', x')) := fun z' =>
    bG.comp (measurable_const.prodMk measurable_id)
  have bTx : BM (fun x' : ι → ℝ => Tou κ h (c • x + s • x')) :=
    bT.comp (measurable_const.add (measurable_const_smul s))
  have bTz : BM (fun z' : ι → ℝ => Tou κ h (c • z + s • z')) :=
    bT.comp (measurable_const.add (measurable_const_smul s))
  have A : ∀ z', ∫ x', mH h (c • x + s • x', c • z + s • z') ∂stdGauss ι =
      (∫ x', G (z', x') ∂stdGauss ι) - Tou c (Tou κ h) x - Tou κ h (c • z + s • z') := by
    intro z'
    simp only [mH]
    rw [integral_sub (((bG2 z').sub bTx).integrable _) (integrable_const _),
      integral_sub ((bG2 z').integrable _) (bTx.integrable _)]
    simp [Tou, hs, hG, hκ]
  simp_rw [A]
  rw [integral_sub (((bG.integral_right (stdGauss ι)).sub (BM.const _)).integrable _)
      (bTz.integrable _),
    integral_sub ((bG.integral_right (stdGauss ι)).integrable _) (integrable_const _)]
  have e1 : ∫ z', ∫ x', G (z', x') ∂stdGauss ι ∂stdGauss ι = Tou c h (κ • x + κ • z) := by
    rw [← integral_prod _ (bG.integrable _)]
    have h1 := gauss_comb (ι := ι) (s * κ) (s * κ) (mul_nonneg (sC_nonneg c) (cc_pos 1).le)
      (fun v => h (c • (κ • x + κ • z) + v)) (hh.meas.comp (measurable_const.add measurable_id))
    have h2 : Real.sqrt ((s * κ) ^ 2 + (s * κ) ^ 2) = s := by
      rw [mul_pow, hκ, cc_one_sq, show s ^ 2 * (1 / 2) + s ^ 2 * (1 / 2) = s ^ 2 by ring]
      exact Real.sqrt_sq (sC_nonneg c)
    rw [h2] at h1
    simp only [Tou]
    rw [← hs, ← h1]
    congr 1
    funext p
    simp only [hG]
    congr 1
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have e2 : ∫ z', Tou κ h (c • z + s • z') ∂stdGauss ι = Tou c (Tou κ h) z := rfl
  rw [e1, e2]
  simp only [mH, integral_const, probReal_univ, one_smul]
  rw [Tou_Tou hc hκabs hh, Tou_Tou hκabs hc hh, mul_comm c κ]

/-- **The product contraction**: `N(c) − 2N(κc) ≤ c⁴ (N(1) − 2N(κ))` for bounded `h` of mean
zero. -/
theorem prodContract {ι : Type} [Fintype ι] {h : (ι → ℝ) → ℝ} (hh : BM h)
    (h0 : ∫ x, h x ∂stdGauss ι = 0) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Nou c h - 2 * Nou (cc 1 * c) h ≤ c ^ 4 * (Nou 1 h - 2 * Nou (cc 1) h) := by
  have hc : |c| ≤ 1 := by rw [abs_of_nonneg hc0]; exact hc1
  have hκabs : |cc 1| ≤ 1 := cc_abs zero_le_one
  set s := sC c with hs
  have bm := bm_mH hh
  have bg : BM (Tou c h) := Tou_BM c hh
  have g0 : ∫ x, Tou c h x ∂stdGauss ι = 0 := by rw [integral_Tou hc hh, h0]
  -- first variable
  set H1 : (ι → ℝ) × (ι → ℝ) → ℝ := fun w => ∫ x', mH h (c • w.1 + s • x', w.2) ∂stdGauss ι
    with hH1
  have bH1 : BM H1 := by
    have : BM (fun p : ((ι → ℝ) × (ι → ℝ)) × (ι → ℝ) => mH h (c • p.1.1 + s • p.2, p.1.2)) :=
      bm.comp (by fun_prop)
    exact this.integral_right (stdGauss ι)
  have step1 : ∫ w, H1 w ^ 2 ∂((stdGauss ι).prod (stdGauss ι)) ≤
      c ^ 2 * ∫ w, mH h w ^ 2 ∂((stdGauss ι).prod (stdGauss ι)) :=
    part_contract bm hc0 hc1 (mH_cent hh h0)
  -- second variable
  set H1s : (ι → ℝ) × (ι → ℝ) → ℝ := fun w => H1 (w.2, w.1) with hH1s
  have bH1s : BM H1s := bH1.comp (measurable_snd.prodMk measurable_fst)
  have cent2 : ∀ x, ∫ z, H1s (z, x) ∂stdGauss ι = 0 := by
    intro x
    simp only [hH1s, hH1]
    have bq : BM (fun p : (ι → ℝ) × (ι → ℝ) => mH h (c • x + s • p.2, p.1)) :=
      bm.comp (by fun_prop)
    rw [integral_integral_swap (bq.integrable ((stdGauss ι).prod (stdGauss ι)))]
    have : ∀ x' : ι → ℝ, ∫ z, mH h (c • x + s • x', z) ∂stdGauss ι = 0 := by
      intro x'
      rw [show (fun z : ι → ℝ => mH h (c • x + s • x', z)) =
        fun z => mH h (z, c • x + s • x') from funext fun z => mH_swap h z _]
      exact mH_cent hh h0 _
    simp [this]
  have step2 := part_contract bH1s hc0 hc1 cent2
  have e2 : ∫ w, H1s w ^ 2 ∂((stdGauss ι).prod (stdGauss ι)) =
      ∫ w, H1 w ^ 2 ∂((stdGauss ι).prod (stdGauss ι)) := by
    rw [← integral_prod_swap]
    rfl
  have e3 : ∀ w : (ι → ℝ) × (ι → ℝ),
      ∫ z', H1s (c • w.1 + sC c • z', w.2) ∂stdGauss ι = mH (Tou c h) w := by
    intro w
    simp only [hH1s, hH1]
    rw [mH_Tou hh hc w.2 w.1, mH_swap]
  simp_rw [e3] at step2
  rw [e2, mH_sq bg g0] at step2
  rw [mH_sq hh h0] at step1
  have hN1 : Nou (cc 1) (Tou c h) = Nou (cc 1 * c) h := by
    simp only [Nou]; rw [Tou_Tou hκabs hc hh]
  have hN2 : ∫ x, Tou c h x ^ 2 ∂stdGauss ι = Nou c h := rfl
  rw [hN1, hN2] at step2
  rw [Nou_one]
  have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
  calc Nou c h - 2 * Nou (cc 1 * c) h
      ≤ c ^ 2 * ∫ w, H1 w ^ 2 ∂((stdGauss ι).prod (stdGauss ι)) := step2
    _ ≤ c ^ 2 * (c ^ 2 * (∫ x, h x ^ 2 ∂stdGauss ι - 2 * Nou (cc 1) h)) :=
        mul_le_mul_of_nonneg_left step1 hc2
    _ = c ^ 4 * (∫ x, h x ^ 2 ∂stdGauss ι - 2 * Nou (cc 1) h) := by ring

/-! ## The part above the first chaos -/

/-- `|c_h|² = Σ_i (E h x_i)²`. -/
noncomputable def asq (h : (ι → ℝ) → ℝ) : ℝ := ∑ i, lc h i ^ 2

/-- `ñ(c) = N(c) − c² |c_h|²`. -/
noncomputable def nt (c : ℝ) (h : (ι → ℝ) → ℝ) : ℝ := Nou c h - c ^ 2 * asq h

lemma Nou_ge {c : ℝ} (hc : |c| ≤ 1) (hh : BM h) : c ^ 2 * asq h ≤ Nou c h := by
  have h1 := bessel_core (Tou_BM c hh)
  simp_rw [lc_Tou hc hh, mul_pow] at h1
  rw [← Finset.mul_sum] at h1
  exact h1

lemma nt_nonneg {c : ℝ} (hc : |c| ≤ 1) (hh : BM h) : 0 ≤ nt c h := by
  have := Nou_ge hc hh
  unfold nt; linarith

lemma cc_one_four : cc 1 ^ 4 = 1 / 4 := by
  rw [show cc 1 ^ 4 = (cc 1 ^ 2) ^ 2 by ring, cc_one_sq]; norm_num

section meanzero

variable (hh : BM h) (h0 : ∫ x, h x ∂stdGauss ι = 0)
include hh h0

lemma E_nonneg : 0 ≤ Nou 1 h - 2 * Nou (cc 1) h := by
  have := bessel_half hh h0
  rw [Nou_one]; linarith

omit h0 in
lemma E_le : Nou 1 h - 2 * Nou (cc 1) h ≤ nt 1 h := by
  have := Nou_ge (cc_abs zero_le_one) hh
  rw [cc_one_sq] at this
  unfold nt; linarith

lemma phi_step {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    nt c h - 2 * c ^ 4 * (Nou 1 h - 2 * Nou (cc 1) h) ≤
      2 * (nt (cc 1 * c) h - 2 * (cc 1 * c) ^ 4 * (Nou 1 h - 2 * Nou (cc 1) h)) := by
  have h1 := prodContract hh h0 hc0 hc1
  have e2 : (cc 1 * c) ^ 2 = c ^ 2 / 2 := by rw [mul_pow, cc_one_sq]; ring
  have e4 : (cc 1 * c) ^ 4 = c ^ 4 / 4 := by rw [mul_pow, cc_one_four]; ring
  unfold nt
  rw [e2, e4]
  linarith

lemma phi_step2 {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    nt c h - 2 * c ^ 4 * (Nou 1 h - 2 * Nou (cc 1) h) ≤
      4 * (nt (c / 2) h - 2 * (c / 2) ^ 4 * (Nou 1 h - 2 * Nou (cc 1) h)) := by
  have hκ0 : 0 ≤ cc 1 := (cc_pos 1).le
  have hκ1 : cc 1 ≤ 1 := by have := cc_abs (t := 1) zero_le_one; rwa [abs_of_nonneg hκ0] at this
  have h1 := phi_step hh h0 hc0 hc1
  have h2 := phi_step hh h0 (mul_nonneg hκ0 hc0) (by nlinarith : cc 1 * c ≤ 1)
  have e : cc 1 * (cc 1 * c) = c / 2 := by
    rw [← mul_assoc, ← pow_two, cc_one_sq]; ring
  rw [e] at h2
  linarith

lemma phi_iter {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (m : ℕ) :
    nt c h - 2 * c ^ 4 * (Nou 1 h - 2 * Nou (cc 1) h) ≤
      4 ^ m * (nt (c / 2 ^ m) h - 2 * (c / 2 ^ m) ^ 4 * (Nou 1 h - 2 * Nou (cc 1) h)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hp : (0 : ℝ) < 2 ^ m := by positivity
    have hp1 : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    have hc0' : 0 ≤ c / 2 ^ m := div_nonneg hc0 hp.le
    have hc1' : c / 2 ^ m ≤ 1 := by
      rw [div_le_one hp]; linarith
    have h1 := phi_step2 hh h0 hc0' hc1'
    have e : c / 2 ^ m / 2 = c / 2 ^ (m + 1) := by rw [pow_succ]; field_simp
    rw [e] at h1
    have h4 : (0 : ℝ) ≤ 4 ^ m := by positivity
    calc _ ≤ 4 ^ m * (nt (c / 2 ^ m) h - 2 * (c / 2 ^ m) ^ 4 *
          (Nou 1 h - 2 * Nou (cc 1) h)) := ih
      _ ≤ 4 ^ m * (4 * (nt (c / 2 ^ (m + 1)) h - 2 * (c / 2 ^ (m + 1)) ^ 4 *
          (Nou 1 h - 2 * Nou (cc 1) h))) := mul_le_mul_of_nonneg_left h1 h4
      _ = _ := by rw [pow_succ]; ring

/-- `ñ(c) ≤ 2 c⁴ ñ(1)` for bounded `h` of mean zero, given the first-chaos limit. -/
lemma nt_le (hB : ChaosLimit) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    nt c h ≤ 2 * c ^ 4 * nt 1 h := by
  obtain ⟨K, hK⟩ := hB ι h hh
  set E := Nou 1 h - 2 * Nou (cc 1) h with hE
  have hE0 : 0 ≤ E := E_nonneg hh h0
  have hbound : ∀ m : ℕ, nt c h - 2 * c ^ 4 * E ≤ |K| * c ^ 4 * (1 / 4) ^ (m + 1) := by
    intro m
    have h1 := phi_iter hh h0 hc0 hc1 (m + 1)
    have hp : (0 : ℝ) < 2 ^ (m + 1) := by positivity
    have hp2 : (2 : ℝ) ≤ 2 ^ (m + 1) := by
      rw [pow_succ]; nlinarith [one_le_pow₀ (M₀ := ℝ) (a := 2) (n := m) (by norm_num)]
    have hc0' : 0 ≤ c / 2 ^ (m + 1) := div_nonneg hc0 hp.le
    have hc1' : c / 2 ^ (m + 1) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ hp (by norm_num)]; nlinarith
    have h2 := hK _ hc0' hc1'
    rw [h0] at h2
    have h3 : nt (c / 2 ^ (m + 1)) h ≤ K * (c / 2 ^ (m + 1)) ^ 4 := by
      have : nt (c / 2 ^ (m + 1)) h = Nou (c / 2 ^ (m + 1)) h - 0 ^ 2 -
          (c / 2 ^ (m + 1)) ^ 2 * ∑ i, (∫ x, h x * x i ∂stdGauss ι) ^ 2 := by
        simp [nt, asq, lc]
      rw [this]; exact h2
    have h4 : (0 : ℝ) ≤ 4 ^ (m + 1) := by positivity
    have h5 : 0 ≤ 2 * (c / 2 ^ (m + 1)) ^ 4 * E := by positivity
    have h6 : (4 : ℝ) ^ (m + 1) * (K * (c / 2 ^ (m + 1)) ^ 4) = K * c ^ 4 * (1 / 4) ^ (m + 1) := by
      rw [div_pow, ← pow_mul, show (2 : ℝ) ^ ((m + 1) * 4) = 4 ^ (m + 1) * 4 ^ (m + 1) by
        rw [← mul_pow, pow_mul']; norm_num, one_div, inv_pow]
      field_simp
    calc nt c h - 2 * c ^ 4 * E
        ≤ 4 ^ (m + 1) * (nt (c / 2 ^ (m + 1)) h - 2 * (c / 2 ^ (m + 1)) ^ 4 * E) := h1
      _ ≤ 4 ^ (m + 1) * (K * (c / 2 ^ (m + 1)) ^ 4) :=
          mul_le_mul_of_nonneg_left (by linarith) h4
      _ = K * c ^ 4 * (1 / 4) ^ (m + 1) := h6
      _ ≤ |K| * c ^ 4 * (1 / 4) ^ (m + 1) := by
          have : 0 ≤ c ^ 4 * (1 / 4 : ℝ) ^ (m + 1) := by positivity
          nlinarith [le_abs_self K]
  have hlim : Filter.Tendsto (fun m : ℕ => |K| * c ^ 4 * (1 / 4 : ℝ) ^ (m + 1)) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun m : ℕ => (1 / 4 : ℝ) ^ (m + 1)) Filter.atTop (nhds 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp
        (Filter.tendsto_add_atTop_nat 1)
    simpa using h1.const_mul (|K| * c ^ 4)
  have h7 : nt c h - 2 * c ^ 4 * E ≤ 0 := ge_of_tendsto' hlim hbound
  have h8 := E_le hh
  have h9 : 0 ≤ 2 * c ^ 4 := by positivity
  nlinarith

end meanzero

/-! ## The bilinear form -/

/-- `B_r(f, g) = E[T_r f · T_r g] − r² c_f·c_g`. -/
noncomputable def Bf (r : ℝ) (f g : (ι → ℝ) → ℝ) : ℝ :=
  ∫ x, Tou r f x * Tou r g x ∂stdGauss ι - r ^ 2 * ∑ i, lc f i * lc g i

lemma Tou_lin (r t : ℝ) (hf : BM f) (hg : BM g) (x : ι → ℝ) :
    Tou r (fun y => f y + t * g y) x = Tou r f x + t * Tou r g x := by
  simp only [Tou]
  have m : Measurable (fun z : ι → ℝ => r • x + sC r • z) :=
    measurable_const.add (measurable_const_smul (sC r))
  rw [integral_add ((hf.comp m).integrable _) (((BM.const t).mul (hg.comp m)).integrable _),
    integral_const_mul]

lemma lc_lin (t : ℝ) (hf : BM f) (hg : BM g) (i : ι) :
    lc (fun y => f y + t * g y) i = lc f i + t * lc g i := by
  unfold lc
  have : (fun x : ι → ℝ => (f x + t * g x) * x i) = fun x => f x * x i + t * (g x * x i) := by
    funext x; ring
  rw [this, integral_add (bm_mul_coord_integrable hf i)
    ((bm_mul_coord_integrable hg i).const_mul t), integral_const_mul]

lemma nt_lin (r t : ℝ) (hf : BM f) (hg : BM g) :
    nt r (fun y => f y + t * g y) = nt r g * (t * t) + 2 * Bf r f g * t + nt r f := by
  have bF := Tou_BM (ι := ι) r hf
  have bG := Tou_BM (ι := ι) r hg
  have e1 : Nou r (fun y => f y + t * g y) =
      Nou r f + 2 * t * ∫ x, Tou r f x * Tou r g x ∂stdGauss ι + t * t * Nou r g := by
    simp only [Nou]
    simp_rw [Tou_lin r t hf hg]
    have : (fun x => (Tou r f x + t * Tou r g x) ^ 2) = fun x =>
        Tou r f x ^ 2 + (2 * t) * (Tou r f x * Tou r g x) + (t * t) * Tou r g x ^ 2 := by
      funext x; ring
    rw [this, integral_add ((bF.sq.add ((BM.const _).mul (bF.mul bG))).integrable _)
      (((BM.const _).mul bG.sq).integrable _),
      integral_add (bF.sq.integrable _) (((BM.const _).mul (bF.mul bG)).integrable _),
      integral_const_mul, integral_const_mul]
  have e2 : asq (fun y => f y + t * g y) =
      asq f + 2 * t * ∑ i, lc f i * lc g i + t * t * asq g := by
    simp only [asq]
    simp_rw [lc_lin t hf hg]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  unfold nt Bf
  rw [e1, e2]
  ring

/-- Cauchy–Schwarz for the form `B_r`. -/
lemma Bf_sq_le {r : ℝ} (hr : |r| ≤ 1) (hf : BM f) (hg : BM g) :
    Bf r f g ^ 2 ≤ nt r f * nt r g := by
  have key : ∀ t : ℝ, 0 ≤ nt r g * (t * t) + 2 * Bf r f g * t + nt r f := by
    intro t
    rw [← nt_lin r t hf hg]
    exact nt_nonneg hr (hf.add ((BM.const t).mul hg))
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

/-- The covariance as an inner product of two images of the Ornstein–Uhlenbeck operator. -/
lemma cov_eq {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hf : BM f) (hg : BM g) :
    ∫ w, f w.1 * g (ρ • w.1 + sC ρ • w.2) ∂((stdGauss ι).prod (stdGauss ι)) -
        (∫ x, f x ∂stdGauss ι) * ∫ x, g x ∂stdGauss ι =
      ∫ x, Tou (Real.sqrt ρ) (fun x => f x - ∫ y, f y ∂stdGauss ι) x *
        Tou (Real.sqrt ρ) (fun x => g x - ∫ y, g y ∂stdGauss ι) x ∂stdGauss ι := by
  set mf := ∫ y, f y ∂stdGauss ι with hmf
  set mg := ∫ y, g y ∂stdGauss ι with hmg
  set f' : (ι → ℝ) → ℝ := fun x => f x - mf with hf'
  set g' : (ι → ℝ) → ℝ := fun x => g x - mg with hg'
  have bf' : BM f' := hf.sub (BM.const mf)
  have bg' : BM g' := hg.sub (BM.const mg)
  have hρ : |ρ| ≤ 1 := by rw [abs_of_nonneg hρ0]; exact hρ1
  have mg' : ∫ x, g' x ∂stdGauss ι = 0 := by
    simp only [hg']
    rw [integral_sub (hg.integrable _) (integrable_const _)]
    simp [hmg]
  have hTg : ∀ x, Tou ρ g x = Tou ρ g' x + mg := by
    intro x
    simp only [Tou, hg']
    rw [integral_sub (f := fun z : ι → ℝ => g (ρ • x + sC ρ • z))
      ((hg.comp (g := fun z : ι → ℝ => ρ • x + sC ρ • z)
        (measurable_const.add (measurable_const_smul (sC ρ)))).integrable _)
      (integrable_const _)]
    simp
  have e1 : ∫ w, f w.1 * g (ρ • w.1 + sC ρ • w.2) ∂((stdGauss ι).prod (stdGauss ι)) - mf * mg =
      ∫ x, f' x * Tou ρ g' x ∂stdGauss ι := by
    rw [← integral_mul_Tou ρ hf hg]
    have bT := Tou_BM (ι := ι) ρ bg'
    have hT0 : ∫ x, Tou ρ g' x ∂stdGauss ι = 0 := by rw [integral_Tou hρ bg', mg']
    have : (fun x => f x * Tou ρ g x) =
        fun x => f' x * Tou ρ g' x + (mf * Tou ρ g' x + mg * f x) := by
      funext x; rw [hTg x]; simp only [hf']; ring
    rw [this, integral_add ((bf'.mul bT).integrable _)
      ((((BM.const mf).mul bT).add ((BM.const mg).mul hf)).integrable _),
      integral_add (((BM.const mf).mul bT).integrable _) (((BM.const mg).mul hf).integrable _),
      integral_const_mul, integral_const_mul, hT0]
    rw [← hmf]; ring
  rw [e1]
  set r := Real.sqrt ρ with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrr : r * r = ρ := Real.mul_self_sqrt hρ0
  have hr1 : r ≤ 1 := by rw [hr]; exact Real.sqrt_le_one.mpr hρ1
  have hrabs : |r| ≤ 1 := by rw [abs_of_nonneg hr0]; exact hr1
  rw [← hrr, ← Tou_Tou hrabs hrabs bg']
  exact Tou_selfadj hrabs bf' (Tou_BM r bg')

/-- The second-order Gebelein inequality for `0 ≤ ρ ≤ 1`. -/
theorem mehler2_nonneg (hB : ChaosLimit) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hf : BM f)
    (hg : BM g) :
    |∫ w, f w.1 * g (ρ • w.1 + sC ρ • w.2) ∂((stdGauss ι).prod (stdGauss ι)) -
        (∫ x, f x ∂stdGauss ι) * (∫ x, g x ∂stdGauss ι) -
        ρ * ∑ i, (∫ x, f x * x i ∂stdGauss ι) * (∫ x, g x * x i ∂stdGauss ι)| ≤
      2 * ρ ^ 2 *
        Real.sqrt (∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι -
          ∑ i, (∫ x, f x * x i ∂stdGauss ι) ^ 2) *
        Real.sqrt (∫ x, (g x - ∫ y, g y ∂stdGauss ι) ^ 2 ∂stdGauss ι -
          ∑ i, (∫ x, g x * x i ∂stdGauss ι) ^ 2) := by
  set mf := ∫ y, f y ∂stdGauss ι with hmf
  set mg := ∫ y, g y ∂stdGauss ι with hmg
  set f' : (ι → ℝ) → ℝ := fun x => f x - mf with hf'
  set g' : (ι → ℝ) → ℝ := fun x => g x - mg with hg'
  have bf' : BM f' := hf.sub (BM.const mf)
  have bg' : BM g' := hg.sub (BM.const mg)
  have mf' : ∫ x, f' x ∂stdGauss ι = 0 := by
    simp only [hf']
    rw [integral_sub (hf.integrable _) (integrable_const _)]
    simp [hmf]
  have mg' : ∫ x, g' x ∂stdGauss ι = 0 := by
    simp only [hg']
    rw [integral_sub (hg.integrable _) (integrable_const _)]
    simp [hmg]
  set r := Real.sqrt ρ with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = ρ := Real.sq_sqrt hρ0
  have hr4 : r ^ 4 = ρ ^ 2 := by rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr2]
  have hr1 : r ≤ 1 := by rw [hr]; exact Real.sqrt_le_one.mpr hρ1
  have hrabs : |r| ≤ 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have lf : ∀ i, lc f' i = ∫ x, f x * x i ∂stdGauss ι := fun i => lc_sub_const hf mf i
  have lg : ∀ i, lc g' i = ∫ x, g x * x i ∂stdGauss ι := fun i => lc_sub_const hg mg i
  have eB : ∫ w, f w.1 * g (ρ • w.1 + sC ρ • w.2) ∂((stdGauss ι).prod (stdGauss ι)) -
        mf * mg - ρ * ∑ i, (∫ x, f x * x i ∂stdGauss ι) * (∫ x, g x * x i ∂stdGauss ι) =
      Bf r f' g' := by
    rw [cov_eq hρ0 hρ1 hf hg]
    simp only [Bf, lf, lg, hr2]
    rfl
  have eF : ∫ x, (f x - mf) ^ 2 ∂stdGauss ι - ∑ i, (∫ x, f x * x i ∂stdGauss ι) ^ 2 =
      nt 1 f' := by
    simp only [nt, asq, lf, Nou_one]; ring
  have eG : ∫ x, (g x - mg) ^ 2 ∂stdGauss ι - ∑ i, (∫ x, g x * x i ∂stdGauss ι) ^ 2 =
      nt 1 g' := by
    simp only [nt, asq, lg, Nou_one]; ring
  rw [eB, eF, eG]
  have h1 := Bf_sq_le hrabs bf' bg'
  have h2 := nt_le bf' mf' hB hr0 hr1
  have h3 := nt_le bg' mg' hB hr0 hr1
  rw [hr4] at h2 h3
  have a0 : 0 ≤ nt 1 f' := nt_nonneg (by simp) bf'
  have b0 : 0 ≤ nt 1 g' := nt_nonneg (by simp) bg'
  have h4 : Bf r f' g' ^ 2 ≤ (2 * ρ ^ 2) ^ 2 * (nt 1 f' * nt 1 g') := by
    calc _ ≤ nt r f' * nt r g' := h1
      _ ≤ (2 * ρ ^ 2 * nt 1 f') * (2 * ρ ^ 2 * nt 1 g') :=
          mul_le_mul h2 h3 (nt_nonneg hrabs bg') (by positivity)
      _ = _ := by ring
  have h5 := Real.abs_le_sqrt h4
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), Real.sqrt_mul a0] at h5
  linarith

/-- **The second-order Gebelein inequality**, given the first-chaos limit. -/
theorem mehler2_of (hB : ChaosLimit) : Mehler2 := by
  intro ι _ ρ f g hρ hf hg
  rcases le_or_gt 0 ρ with h0 | h0
  · exact mehler2_nonneg hB h0 (by rw [abs_of_nonneg h0] at hρ; exact hρ) hf hg
  · have hρ' : -ρ ≤ 1 := by rw [abs_of_neg h0] at hρ; exact hρ
    set gn : (ι → ℝ) → ℝ := fun y => g (-y) with hgn
    have bgn : BM gn := hg.comp measurable_neg
    have h1 := mehler2_nonneg (ι := ι) hB (by linarith : 0 ≤ -ρ) hρ' hf bgn
    have hs : sC (-ρ) = sC ρ := by simp [sC]
    have e1 : ∫ w, f w.1 * gn ((-ρ) • w.1 + sC (-ρ) • w.2) ∂((stdGauss ι).prod (stdGauss ι)) =
        ∫ w, f w.1 * g (ρ • w.1 + sC ρ • w.2) ∂((stdGauss ι).prod (stdGauss ι)) := by
      rw [hs]
      have bL : BM (fun w : (ι → ℝ) × (ι → ℝ) => f w.1 * gn ((-ρ) • w.1 + sC ρ • w.2)) :=
        (hf.comp measurable_fst).mul (bgn.comp (meas_comb (-ρ) (sC ρ)))
      have bR : BM (fun w : (ι → ℝ) × (ι → ℝ) => f w.1 * g (ρ • w.1 + sC ρ • w.2)) :=
        (hf.comp measurable_fst).mul (hg.comp (meas_comb ρ (sC ρ)))
      rw [integral_prod _ (bL.integrable _), integral_prod _ (bR.integrable _)]
      congr 1
      funext x
      simp only [integral_const_mul]
      congr 1
      have := gauss_neg (ι := ι) (fun z => g (ρ • x + sC ρ • z))
        (hg.meas.comp (measurable_const.add (measurable_const_smul (sC ρ))))
      rw [← this]
      congr 1
      funext z
      simp only [hgn]
      congr 1
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      ring
    have e2 : ∫ x, gn x ∂stdGauss ι = ∫ x, g x ∂stdGauss ι := gauss_neg g hg.meas
    have e3 : ∫ x, (gn x - ∫ y, g y ∂stdGauss ι) ^ 2 ∂stdGauss ι =
        ∫ x, (g x - ∫ y, g y ∂stdGauss ι) ^ 2 ∂stdGauss ι :=
      gauss_neg (fun x => (g x - ∫ y, g y ∂stdGauss ι) ^ 2) (hg.sub (BM.const _)).sq.meas
    have e4 : ∀ i, ∫ x, gn x * x i ∂stdGauss ι = -∫ x, g x * x i ∂stdGauss ι := by
      intro i
      have := gauss_neg (ι := ι) (fun z => g z * (-(z i)))
        (hg.meas.mul (measurable_pi_apply i).neg)
      simp only [Pi.neg_apply, neg_neg] at this
      rw [show (fun x => gn x * x i) = fun z : ι → ℝ => g (-z) * z i from rfl, this,
        ← integral_neg]
      congr 1
      funext z
      ring
    simp_rw [e4] at h1
    rw [e1, e2, e3] at h1
    have e5 : (-ρ) * ∑ i, (∫ x, f x * x i ∂stdGauss ι) * -(∫ x, g x * x i ∂stdGauss ι) =
        ρ * ∑ i, (∫ x, f x * x i ∂stdGauss ι) * (∫ x, g x * x i ∂stdGauss ι) := by
      simp only [mul_neg, Finset.sum_neg_distrib]; ring
    simp only [neg_sq] at h1
    rw [e5] at h1
    exact h1

#print axioms chaos1Bessel
#print axioms prodContract
#print axioms mehler2_of

end BstLean.Part112
