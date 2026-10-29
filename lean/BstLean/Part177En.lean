import BstLean.Part176All

/-!
# Part 177 (file `En`): the energy event `SEn`, its charge, and its consequences

No proof is left open; no `native_decide` or `axiom` is used.

* `ptK ĉ τ a v`: the latitude point of `sgA`/`wbR` written through `(ĉ, τ₀)` (`ptK_eq`, by `rfl`);
  `omK θ x = |h₂(x)|²/n`; `YEn = ∫_a∫_v ω¹²`.
* **`SEn n`**: `YEn ≤ 1.1` (a family of Agent events; `measurableSet_SEn`).
* `HMom n`: the moment hypothesis `E(|h₂(x)|²/n)^q ≤ exp(8q²/n²)` for `|x| ≤ 1` (file `EnMom`).
* **`SEn_charge`**: for every `(ĉ, τ₀)`, `ν_A{θ ∉ SEn} ≤ 10⁻⁶` (`n ≥ 16 384`, no upper end), from
  `HMom n`: Jensen `Y²⁰⁰ ≤ ∫∫ω²⁴⁰⁰`, Tonelli, Markov; `exp(8·2400²/n²)/1.1²⁰⁰ ≤ 10⁻⁶`.
* **`SEn_ret_charge`**: the same charge for the retained data of `paperDesign`.
* **`sg8_of_SEn`**: on `SEn`, `∫∫σ⁸ ≤ (1.005·√γ_A)⁸` (`σ² ≤ γ_A ω`, `ω⁴ ≤ (2 + ω¹²)/3`); this
  replaces `E0 n ≈ 4.06·√γ_A`.
* **`fb_of_SEn`** (`fb24_of_SEn`, `fb4_of_SEn`): on `SEn`, `∫_{KR} f̄²⁴ ≤ 1.005²⁴`,
  `∫_{KR} f̄⁴ ≤ 1.005⁴` (`f² ≤ ω`, Jensen, `x⁴ ≤ (5 + x²⁴)/6`): the inputs `hf24`, `hf4` of
  `MomX` with `H_f = 1.005` (Part 169 has `HfN ≈ 4.04`).
-/

namespace BstLean.Part177

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg hid2 mA)
open BstLean.Part157
open BstLean.Part161 (Ix muI xLat latC hhMat consV uHat)
open BstLean.Part160 (AgFam agKey agentEv)
open BstLean.Part153 (nuA)
open BstLean.Part53 (unitF53)

variable {n : ℕ}

/-- The latitude point of `sgA`/`wbR`, written through `(ĉ, τ₀)` only. -/
noncomputable def ptK (ch : Fin n → ℝ) (τ : ℝ) (a : Ix n) (v : Fin (n - 1) → ℝ) : Fin n → ℝ :=
  (hhMat ((√(normSq ch))⁻¹ • ch)).mulVec
    (consV (BstLean.Part157.latitude (√(normSq ch)) τ a)
      (√(1 - BstLean.Part157.latitude (√(normSq ch)) τ a ^ 2) • unitF53 v))

lemma ptK_eq (D : Design n) (c : Ret n) (a : Ix n) (v : Fin (n - 1) → ℝ) :
    xLat c (latC D c a) (unitF53 v) = ptK c.1.2 (D.tau0 c) a v := rfl

/-- The normalized energy `ω(x) = |h₂(x)|²/n`. -/
noncomputable def omK (θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (x : Fin n → ℝ) : ℝ :=
  normSq (hid2 θ.1 θ.2 x) / (n : ℝ)

/-- `Y = ∫_a ∫_v ω(x(a, v))¹²`. -/
noncomputable def YEn (x : AgFam n) : ℝ :=
  ∫ a, ∫ v, omK x.2 (ptK x.1.1 x.1.2 a v) ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n

/-- **The energy event**: `∫_a ∫_v (|h₂(x)|²/n)¹² ≤ 1.1`. -/
def SEn (n : ℕ) : Set (AgFam n) := {x | YEn x ≤ 11 / 10}

lemma measurable_hhMat_comp {α : Type*} [MeasurableSpace α] {u : α → Fin n → ℝ}
    (hu : Measurable u) : Measurable (fun x => hhMat (u x)) := by
  unfold hhMat
  have hw : Measurable (fun x => BstLean.Part130.e0 n - u x) := measurable_const.sub hu
  have hs : Measurable (fun x => 2 * (normSq (BstLean.Part130.e0 n - u x))⁻¹) :=
    measurable_const.mul ((BstLean.Part130.continuous_normSq.measurable.comp hw).inv)
  refine measurable_const.sub ?_
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  exact hs.mul (((measurable_pi_apply i).comp hw).mul ((measurable_pi_apply j).comp hw))

lemma measurable_ptK_comp {α : Type*} [MeasurableSpace α] {ch : α → Fin n → ℝ} {τ : α → ℝ}
    {a : α → Ix n} {v : α → Fin (n - 1) → ℝ} (hc : Measurable ch) (ht : Measurable τ)
    (ha : Measurable a) (hv : Measurable v) :
    Measurable (fun x => ptK (ch x) (τ x) (a x) (v x)) := by
  unfold ptK
  have hr : Measurable (fun x => √(normSq (ch x))) :=
    (BstLean.Part130.continuous_normSq.measurable.comp hc).sqrt
  have hl : Measurable (fun x => BstLean.Part157.latitude (√(normSq (ch x))) (τ x) (a x)) :=
    BstLean.Part157.measurable_latitude_comp hr ht ha
  have hH := measurable_hhMat_comp (hr.inv.smul hc)
  have hC : Measurable (fun x =>
      consV (n := n) (BstLean.Part157.latitude (√(normSq (ch x))) (τ x) (a x))
        (√(1 - BstLean.Part157.latitude (√(normSq (ch x))) (τ x) (a x) ^ 2) • unitF53 (v x))) :=
    BstLean.Part161.measurable_consV.comp (hl.prodMk
      (((measurable_const.sub (hl.pow_const 2)).sqrt).smul
        (BstLean.Part53.measurable_unitF.comp hv)))
  exact (Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp (hH.prodMk hC)

lemma measurable_omK_joint :
    Measurable (fun p : (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) ×
      (Fin n → ℝ) => omK p.1 p.2) := by
  unfold omK
  have hc : Continuous (fun p : (Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × (Fin n → ℝ) => hid2 p.1.1 p.1.2 p.2) := by
    unfold hid2
    exact BstLean.Part130.continuous_reluV.comp (Continuous.matrix_mulVec (by fun_prop)
      (BstLean.Part130.continuous_reluV.comp (Continuous.matrix_mulVec (by fun_prop) (by fun_prop))))
  exact ((BstLean.Part130.continuous_normSq.comp hc).measurable).div_const _

abbrev TH (n : ℕ) : Type := Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ

lemma measurable_omK_comp {α : Type} [MeasurableSpace α]
    {θ : α → TH n} {y : α → Fin n → ℝ} (hθ : Measurable θ) (hy : Measurable y) :
    Measurable (fun x => omK (θ x) (y x)) := by
  unfold omK
  have hc : Continuous (fun p : TH n × (Fin n → ℝ) => hid2 p.1.1 p.1.2 p.2) := by
    unfold hid2
    exact BstLean.Part130.continuous_reluV.comp (Continuous.matrix_mulVec (by fun_prop)
      (BstLean.Part130.continuous_reluV.comp (Continuous.matrix_mulVec (by fun_prop) (by fun_prop))))
  have h2 : Measurable (fun x => hid2 (θ x).1 (θ x).2 (y x)) := hc.measurable.comp (hθ.prodMk hy)
  exact (BstLean.Part130.continuous_normSq.measurable.comp h2).div_const _

lemma measurable_YEn_integrand :
    Measurable (fun p : (AgFam n × Ix n) × (Fin (n - 1) → ℝ) =>
      omK p.1.1.2 (ptK p.1.1.1.1 p.1.1.1.2 p.1.2 p.2) ^ 12) := by
  have h1 : Measurable (fun p : (AgFam n × Ix n) × (Fin (n - 1) → ℝ) =>
      ptK p.1.1.1.1 p.1.1.1.2 p.1.2 p.2) :=
    measurable_ptK_comp (measurable_fst.comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))
      (measurable_snd.comp (measurable_fst.comp (measurable_fst.comp measurable_fst)))
      (measurable_snd.comp measurable_fst) measurable_snd
  have hg2 : Measurable (fun p : (AgFam n × Ix n) × (Fin (n - 1) → ℝ) =>
      (p.1.1.2, ptK p.1.1.1.1 p.1.1.1.2 p.1.2 p.2)) :=
    (measurable_snd.comp (measurable_fst.comp measurable_fst)).prodMk h1
  exact (measurable_omK_joint.comp hg2).pow_const 12

lemma measurable_YEn : Measurable (fun x : AgFam n => YEn x) := by
  have h2 : Measurable (fun p : AgFam n × Ix n =>
      ∫ v, omK p.1.2 (ptK p.1.1.1 p.1.1.2 p.2 v) ^ 12 ∂stdGauss (Fin (n - 1))) :=
    (measurable_YEn_integrand.stronglyMeasurable.integral_prod_right'
      (ν := stdGauss (Fin (n - 1)))).measurable
  unfold YEn
  exact (h2.stronglyMeasurable.integral_prod_right' (ν := muI n)).measurable

theorem measurableSet_SEn (n : ℕ) : MeasurableSet (SEn n) :=
  measurableSet_le measurable_YEn measurable_const


lemma normSq_ptK_le (hn : 1 ≤ n) (ch : Fin n → ℝ) (τ : ℝ) (a : Ix n) (v : Fin (n - 1) → ℝ) :
    normSq (ptK ch τ a v) ≤ 1 := by
  unfold ptK
  set s := BstLean.Part157.latitude (√(normSq ch)) τ a
  have hs : s ^ 2 ≤ 1 := BstLean.Part162.latitude_sq_le _ _ _
  rw [BstLean.Part161.hh_normSq, BstLean.Part161.normSq_consV hn]
  have h1 : normSq (√(1 - s ^ 2) • unitF53 v) = (1 - s ^ 2) * normSq (unitF53 v) := by
    unfold normSq
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [Real.sq_sqrt (by linarith), Finset.mul_sum]
  have h2 : normSq (unitF53 v) ≤ 1 := by
    have h := BstLean.Part162.radF_unitF_le v
    have h3 : normSq (unitF53 v) = BstLean.Part53.radF53 (unitF53 v) ^ 2 :=
      (BstLean.Part162.radF_sq _).symm
    rw [h3]
    have := BstLean.Part162.radF_nonneg (unitF53 v)
    nlinarith
  rw [h1]
  nlinarith

lemma omK_nonneg (θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (x : Fin n → ℝ) : 0 ≤ omK θ x := by
  unfold omK; exact div_nonneg (normSq_nonneg _) (Nat.cast_nonneg n)

lemma omK_le (hn : 1 ≤ n) (θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    {x : Fin n → ℝ} (hx : normSq x ≤ 1) :
    omK θ x ≤ BstLean.Part131.frob θ.2 * BstLean.Part131.frob θ.1 / n := by
  unfold omK
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h := BstLean.Part131.normSq_hid2_le θ.1 θ.2 x
  have h1 := BstLean.Part131.frob_nonneg θ.1
  have h2 := BstLean.Part131.frob_nonneg θ.2
  refine div_le_div_of_nonneg_right (h.trans ?_) hn0.le
  calc BstLean.Part131.frob θ.2 * (BstLean.Part131.frob θ.1 * normSq x)
      ≤ BstLean.Part131.frob θ.2 * (BstLean.Part131.frob θ.1 * 1) := by gcongr
    _ = _ := by ring

/-- A bounded measurable function is integrable for a finite measure. -/
lemma intOfBdd {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) : Integrable f μ :=
  Integrable.mono' (integrable_const M) hf.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)

/-- The moment hypothesis (proved by fork E1): `E(|h₂(x)|²/n)^q ≤ exp(8q²/n²)` for `|x| ≤ 1`. -/
def HMom (n : ℕ) : Prop :=
  ∀ x : Fin n → ℝ, normSq x ≤ 1 → ∀ q : ℕ,
    Integrable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      (normSq (hid2 θ.1 θ.2 x) / (n : ℝ)) ^ q) (nuA n) ∧
    ∫ θ, (normSq (hid2 θ.1 θ.2 x) / (n : ℝ)) ^ q ∂(nuA n) ≤ Real.exp (8 * (q : ℝ) ^ 2 / (n : ℝ) ^ 2)

lemma charge_num {n : ℕ} (hn : 16384 ≤ n) :
    Real.exp (8 * ((2400 : ℕ) : ℝ) ^ 2 / (n : ℝ) ^ 2) / (11 / 10) ^ 200 ≤ 1 / 10 ^ 6 := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 8 * ((2400 : ℕ) : ℝ) ^ 2 / (n : ℝ) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    have : (16384 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnR 2
    push_cast; nlinarith
  have h2 : Real.exp (8 * ((2400 : ℕ) : ℝ) ^ 2 / (n : ℝ) ^ 2) ≤ 3 :=
    (Real.exp_le_exp.2 h1).trans (by have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith)
  rw [div_le_iff₀ (by positivity)]
  calc _ ≤ (3 : ℝ) := h2
    _ ≤ 1 / 10 ^ 6 * (11 / 10) ^ 200 := by norm_num

/-- The integrand `ω(x(a, v))` for fixed `(ĉ, τ₀)`. -/
noncomputable def fK (ch : Fin n → ℝ) (τ : ℝ)
    (θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (a : Ix n)
    (v : Fin (n - 1) → ℝ) : ℝ := omK θ (ptK ch τ a v)

lemma measurable_fK (ch : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun p : ((Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × Ix n) × (Fin (n - 1) → ℝ) => fK ch τ p.1.1 p.1.2 p.2) := by
  have h1 : Measurable (fun p : ((Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × Ix n) × (Fin (n - 1) → ℝ) => ptK ch τ p.1.2 p.2) :=
    measurable_ptK_comp measurable_const measurable_const (measurable_snd.comp measurable_fst)
      measurable_snd
  unfold fK
  exact measurable_omK_comp (measurable_fst.comp measurable_fst) h1

lemma measurable_fK_v (ch : Fin n → ℝ) (τ : ℝ) (θ : TH n) (a : Ix n) :
    Measurable (fun v => fK ch τ θ a v) := by
  unfold fK
  exact measurable_omK_comp measurable_const
    (measurable_ptK_comp measurable_const measurable_const measurable_const measurable_id)

lemma measurable_fK_av (ch : Fin n → ℝ) (τ : ℝ) (θ : TH n) :
    Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => fK ch τ θ p.1 p.2) := by
  unfold fK
  exact measurable_omK_comp measurable_const
    (measurable_ptK_comp measurable_const measurable_const measurable_fst measurable_snd)

lemma YEn_eq (ch : Fin n → ℝ) (τ : ℝ) (θ : TH n) :
    YEn ((ch, τ), θ) = ∫ a, ∫ v, fK ch τ θ a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n := rfl

lemma measurable_fK_θv (ch : Fin n → ℝ) (τ : ℝ) (a : Ix n) :
    Measurable (fun p : TH n × (Fin (n - 1) → ℝ) => fK ch τ p.1 a p.2) := by
  unfold fK
  exact measurable_omK_comp measurable_fst
    (measurable_ptK_comp measurable_const measurable_const measurable_const measurable_snd)

attribute [irreducible] fK

/-- **The charge of the energy event**: at most `10⁻⁶` for every `(ĉ, τ₀)` (`n ≥ 16 384`, no upper
end), from the moment hypothesis `HMom n` (Markov at order 200 on `Y`, Jensen, Tonelli). -/
theorem SEn_charge (hn : 16384 ≤ n) (hmom : HMom n) (ch : Fin n → ℝ) (τ : ℝ) :
    (nuA n).real {θ | ((ch, τ), θ) ∉ SEn n} ≤ 1 / 10 ^ 6 := by
  have hn1 : 1 ≤ n := by omega
  have mf := measurable_fK (n := n) ch τ
  have f0 : ∀ θ a v, 0 ≤ fK ch τ θ a v := fun θ a v => by unfold fK; exact omK_nonneg _ _
  have fb : ∀ θ a v, fK ch τ θ a v ≤ BstLean.Part131.frob θ.2 * BstLean.Part131.frob θ.1 / n :=
    fun θ a v => by unfold fK; exact omK_le hn1 θ (normSq_ptK_le hn1 ch τ a v)
  -- measurability in (a, v) for fixed θ
  have mfθ : ∀ θ, Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => fK ch τ θ p.1 p.2) := fun θ =>
    measurable_fK_av ch τ θ
  -- Jensen: `Y^200 ≤ ∫∫ f^2400`
  have hJ : ∀ θ, YEn ((ch, τ), θ) ^ 200 ≤ ∫ a, ∫ v, fK ch τ θ a v ^ 2400 ∂stdGauss (Fin (n - 1)) ∂muI n := by
    intro θ
    set B := BstLean.Part131.frob θ.2 * BstLean.Part131.frob θ.1 / n
    have hB0 : 0 ≤ B := le_trans (f0 θ 0 0) (fb θ 0 0)
    have bnd : ∀ a v, |fK ch τ θ a v ^ 12| ≤ B ^ 12 := fun a v => by
      rw [abs_of_nonneg (pow_nonneg (f0 θ a v) _)]; exact pow_le_pow_left₀ (f0 θ a v) (fb θ a v) _
    have bnd2 : ∀ a v, |fK ch τ θ a v ^ 2400| ≤ B ^ 2400 := fun a v => by
      rw [abs_of_nonneg (pow_nonneg (f0 θ a v) _)]; exact pow_le_pow_left₀ (f0 θ a v) (fb θ a v) _
    have mF : Measurable (fun a => ∫ v, fK ch τ θ a v ^ 12 ∂stdGauss (Fin (n - 1))) :=
      (((mfθ θ).pow_const 12).stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin (n - 1)))).measurable
    have mG : Measurable (fun a => ∫ v, fK ch τ θ a v ^ 2400 ∂stdGauss (Fin (n - 1))) :=
      (((mfθ θ).pow_const 2400).stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin (n - 1)))).measurable
    have iv : ∀ a, Integrable (fun v => fK ch τ θ a v ^ 12) (stdGauss (Fin (n - 1))) := fun a =>
      intOfBdd ((measurable_fK_v ch τ θ a).pow_const 12) (bnd a)
    have iv2 : ∀ a, Integrable (fun v => fK ch τ θ a v ^ 2400) (stdGauss (Fin (n - 1))) := fun a =>
      intOfBdd ((measurable_fK_v ch τ θ a).pow_const 2400) (bnd2 a)
    have Fb : ∀ a, |∫ v, fK ch τ θ a v ^ 12 ∂stdGauss (Fin (n - 1))| ≤ B ^ 12 := fun a => by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ v, |fK ch τ θ a v ^ 12| ∂stdGauss (Fin (n - 1)) ≤ ∫ v, B ^ 12 ∂stdGauss (Fin (n - 1)) :=
            integral_mono (iv a).abs (integrable_const _) (bnd a)
        _ = B ^ 12 := by simp
    have F0 : ∀ a, 0 ≤ ∫ v, fK ch τ θ a v ^ 12 ∂stdGauss (Fin (n - 1)) := fun a =>
      integral_nonneg fun v => pow_nonneg (f0 θ a v) _
    have Gb : ∀ a, |∫ v, fK ch τ θ a v ^ 2400 ∂stdGauss (Fin (n - 1))| ≤ B ^ 2400 := fun a => by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ v, |fK ch τ θ a v ^ 2400| ∂stdGauss (Fin (n - 1)) ≤ ∫ v, B ^ 2400 ∂stdGauss (Fin (n - 1)) :=
            integral_mono (iv2 a).abs (integrable_const _) (bnd2 a)
        _ = B ^ 2400 := by simp
    have iF : Integrable (fun a => ∫ v, fK ch τ θ a v ^ 12 ∂stdGauss (Fin (n - 1))) (muI n) := intOfBdd mF Fb
    have iF2 : Integrable (fun a => (∫ v, fK ch τ θ a v ^ 12 ∂stdGauss (Fin (n - 1))) ^ 200) (muI n) :=
      intOfBdd (mF.pow_const 200) (fun a => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (Fb a) _)
    have iG : Integrable (fun a => ∫ v, fK ch τ θ a v ^ 2400 ∂stdGauss (Fin (n - 1))) (muI n) := intOfBdd mG Gb
    have hout := (convexOn_pow 200).map_integral_le (μ := muI n)
      (f := fun a => ∫ v, fK ch τ θ a v ^ 12 ∂stdGauss (Fin (n - 1))) (continuous_pow 200).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun a => Set.mem_Ici.mpr (F0 a)) iF iF2
    rw [YEn_eq]
    refine hout.trans (integral_mono iF2 iG fun a => ?_)
    have hin := (convexOn_pow 200).map_integral_le (μ := stdGauss (Fin (n - 1)))
      (f := fun v => fK ch τ θ a v ^ 12) (continuous_pow 200).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun v => Set.mem_Ici.mpr (pow_nonneg (f0 θ a v) _)) (iv a)
      (by simpa only [Function.comp_def, ← pow_mul] using iv2 a)
    simpa only [Function.comp_def, ← pow_mul] using hin
  -- integrability for each `θ`
  have hint : ∀ θ : TH n, (∀ a, Integrable (fun v => fK ch τ θ a v ^ 2400) (stdGauss (Fin (n - 1))))
      ∧ Integrable (fun a => ∫ v, fK ch τ θ a v ^ 2400 ∂stdGauss (Fin (n - 1))) (muI n) := by
    intro θ
    set B := BstLean.Part131.frob θ.2 * BstLean.Part131.frob θ.1 / n
    have bnd2 : ∀ a v, |fK ch τ θ a v ^ 2400| ≤ B ^ 2400 := fun a v => by
      rw [abs_of_nonneg (pow_nonneg (f0 θ a v) _)]; exact pow_le_pow_left₀ (f0 θ a v) (fb θ a v) _
    have iv2 : ∀ a, Integrable (fun v => fK ch τ θ a v ^ 2400) (stdGauss (Fin (n - 1))) := fun a =>
      intOfBdd ((measurable_fK_v ch τ θ a).pow_const 2400) (bnd2 a)
    refine ⟨iv2, intOfBdd (M := B ^ 2400) (((mfθ θ).pow_const 2400).stronglyMeasurable.integral_prod_right'
      (ν := stdGauss (Fin (n - 1)))).measurable fun a => ?_⟩
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |fK ch τ θ a v ^ 2400| ∂stdGauss (Fin (n - 1))
        ≤ ∫ v, B ^ 2400 ∂stdGauss (Fin (n - 1)) :=
          integral_mono (iv2 a).abs (integrable_const _) (bnd2 a)
      _ = B ^ 2400 := by simp
  -- the lintegral form
  have hL : ∀ θ : TH n, ENNReal.ofReal (∫ a, ∫ v, fK ch τ θ a v ^ 2400 ∂stdGauss (Fin (n - 1)) ∂muI n)
      = ∫⁻ a, ∫⁻ v, ENNReal.ofReal (fK ch τ θ a v ^ 2400) ∂stdGauss (Fin (n - 1)) ∂muI n := by
    intro θ
    rw [ofReal_integral_eq_lintegral_ofReal (hint θ).2 (Filter.Eventually.of_forall fun a =>
      integral_nonneg fun v => pow_nonneg (f0 θ a v) _)]
    refine lintegral_congr fun a => ?_
    exact ofReal_integral_eq_lintegral_ofReal ((hint θ).1 a)
      (Filter.Eventually.of_forall fun v => pow_nonneg (f0 θ a v) _)
  -- joint measurability
  have mJ : Measurable (fun p : (TH n × Ix n) × (Fin (n - 1) → ℝ) =>
      ENNReal.ofReal (fK ch τ p.1.1 p.1.2 p.2 ^ 2400)) :=
    ENNReal.measurable_ofReal.comp (mf.pow_const 2400)
  have mI : Measurable (fun p : TH n × Ix n =>
      ∫⁻ v, ENNReal.ofReal (fK ch τ p.1 p.2 v ^ 2400) ∂stdGauss (Fin (n - 1))) :=
    mJ.lintegral_prod_right'
  have mO : Measurable (fun θ : TH n =>
      ∫⁻ a, ∫⁻ v, ENNReal.ofReal (fK ch τ θ a v ^ 2400) ∂stdGauss (Fin (n - 1)) ∂muI n) :=
    mI.lintegral_prod_right'
  -- the total
  set E : ℝ := Real.exp (8 * ((2400 : ℕ) : ℝ) ^ 2 / (n : ℝ) ^ 2) with hE
  have hpt : ∀ a v, ∫⁻ θ, ENNReal.ofReal (fK ch τ θ a v ^ 2400) ∂nuA n ≤ ENNReal.ofReal E := by
    intro a v
    obtain ⟨hi, hb⟩ := hmom (ptK ch τ a v) (normSq_ptK_le hn1 ch τ a v) 2400
    have e : ∀ θ : TH n, fK ch τ θ a v ^ 2400 =
        (normSq (hid2 θ.1 θ.2 (ptK ch τ a v)) / (n : ℝ)) ^ 2400 := fun θ => by
      unfold fK omK; rfl
    simp_rw [e]
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun θ =>
      pow_nonneg (div_nonneg (normSq_nonneg _) (Nat.cast_nonneg n)) _)]
    exact ENNReal.ofReal_le_ofReal hb
  have htot : ∫⁻ θ, ∫⁻ a, ∫⁻ v, ENNReal.ofReal (fK ch τ θ a v ^ 2400) ∂stdGauss (Fin (n - 1))
      ∂muI n ∂nuA n ≤ ENNReal.ofReal E := by
    rw [lintegral_lintegral_swap mI.aemeasurable]
    calc ∫⁻ a, ∫⁻ θ, ∫⁻ v, ENNReal.ofReal (fK ch τ θ a v ^ 2400) ∂stdGauss (Fin (n - 1)) ∂nuA n
          ∂muI n
        = ∫⁻ a, ∫⁻ v, ∫⁻ θ, ENNReal.ofReal (fK ch τ θ a v ^ 2400) ∂nuA n
          ∂stdGauss (Fin (n - 1)) ∂muI n := by
          refine lintegral_congr fun a => ?_
          have ma : Measurable (fun p : TH n × (Fin (n - 1) → ℝ) =>
              ENNReal.ofReal (fK ch τ p.1 a p.2 ^ 2400)) :=
            ENNReal.measurable_ofReal.comp ((measurable_fK_θv ch τ a).pow_const 2400)
          exact lintegral_lintegral_swap ma.aemeasurable
      _ ≤ ∫⁻ a, ∫⁻ v, ENNReal.ofReal E ∂stdGauss (Fin (n - 1)) ∂muI n :=
          lintegral_mono fun a => lintegral_mono fun v => hpt a v
      _ = ENNReal.ofReal E := by
          have hρ : IsProbabilityMeasure (stdGauss (Fin (n - 1))) := by
            unfold stdGauss; infer_instance
          simp
  -- Markov
  set T : ℝ := (11 / 10) ^ 200 with hT
  have hT0 : 0 < T := by positivity
  have hsub : {θ | ((ch, τ), θ) ∉ SEn n} ⊆ {θ : TH n | ENNReal.ofReal T ≤
      ∫⁻ a, ∫⁻ v, ENNReal.ofReal (fK ch τ θ a v ^ 2400) ∂stdGauss (Fin (n - 1)) ∂muI n} := by
    intro θ hθ
    simp only [SEn, Set.mem_ofPred_eq, not_le] at hθ
    simp only [Set.mem_ofPred_eq]
    rw [← hL θ]
    refine ENNReal.ofReal_le_ofReal ?_
    exact (pow_le_pow_left₀ (by norm_num) hθ.le 200).trans (hJ θ)
  have hM := meas_ge_le_lintegral_div mO.aemeasurable (μ := nuA n)
    (ε := ENNReal.ofReal T) (by simpa using hT0) ENNReal.ofReal_ne_top
  have hfin : (nuA n) {θ | ((ch, τ), θ) ∉ SEn n} ≤ ENNReal.ofReal (E / T) := by
    refine (measure_mono hsub).trans (hM.trans ?_)
    rw [ENNReal.ofReal_div_of_pos hT0]
    exact ENNReal.div_le_div_right htot _
  refine (ENNReal.toReal_le_of_le_ofReal (by positivity) hfin).trans ?_
  exact charge_num hn

/-- **The charge of the energy event under the distribution of the retained data.** -/
theorem SEn_ret_charge (hn : 16384 ≤ n) (hmom : HMom n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real (agentEv (paperDesign n fT wT hf hw) (SEn n))ᶜ ≤
      1 / 10 ^ 6 := by
  rw [BstLean.Part160.agentEv_compl]
  exact BstLean.Part160.retDist_agent_charge (paperDesign n fT wT hf hw)
    (BstLean.Part160.paperDesign_tauWorld fT wT hf hw) (measurableSet_SEn n) (by norm_num)
    (fun c τ _ => SEn_charge hn hmom c τ)

/-- On the energy event: `Y ≤ 1.1` for the retained data. -/
lemma YEn_le {D : Design n} {c : Ret n} (hc : c ∈ agentEv D (SEn n)) (hτ : 0 < D.tau0 c) :
    ∫ a, ∫ v, omK c.2.1.1 (xLat c (latC D c a) (unitF53 v)) ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n
      ≤ 11 / 10 := hc hτ

/-- Iterated integrals are monotone for bounded measurable integrands. -/
lemma iint_mono {F G : Ix n → (Fin (n - 1) → ℝ) → ℝ}
    (mF : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => F p.1 p.2))
    (mG : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => G p.1 p.2)) {MF MG : ℝ}
    (bF : ∀ a v, |F a v| ≤ MF) (bG : ∀ a v, |G a v| ≤ MG) (h : ∀ a v, F a v ≤ G a v) :
    ∫ a, ∫ v, F a v ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      ∫ a, ∫ v, G a v ∂stdGauss (Fin (n - 1)) ∂muI n := by
  have hρ : IsProbabilityMeasure (stdGauss (Fin (n - 1))) := by unfold stdGauss; infer_instance
  have iF : ∀ a, Integrable (fun v => F a v) (stdGauss (Fin (n - 1))) := fun a =>
    intOfBdd (mF.comp measurable_prodMk_left) (bF a)
  have iG : ∀ a, Integrable (fun v => G a v) (stdGauss (Fin (n - 1))) := fun a =>
    intOfBdd (mG.comp measurable_prodMk_left) (bG a)
  have oF : Integrable (fun a => ∫ v, F a v ∂stdGauss (Fin (n - 1))) (muI n) :=
    intOfBdd (M := MF) (mF.stronglyMeasurable.integral_prod_right'
      (ν := stdGauss (Fin (n - 1)))).measurable fun a => (abs_integral_le_integral_abs).trans
        ((integral_mono (iF a).abs (integrable_const MF) (bF a)).trans (by simp))
  have oG : Integrable (fun a => ∫ v, G a v ∂stdGauss (Fin (n - 1))) (muI n) :=
    intOfBdd (M := MG) (mG.stronglyMeasurable.integral_prod_right'
      (ν := stdGauss (Fin (n - 1)))).measurable fun a => (abs_integral_le_integral_abs).trans
        ((integral_mono (iG a).abs (integrable_const MG) (bG a)).trans (by simp))
  exact integral_mono oF oG fun a => integral_mono (iF a) (iG a) (h a)

/-- Iterated integral of `α·(β + γ·H)`. -/
lemma iint_affine {H : Ix n → (Fin (n - 1) → ℝ) → ℝ}
    (mH : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => H p.1 p.2)) {M : ℝ}
    (bH : ∀ a v, |H a v| ≤ M) (α β γ : ℝ) :
    ∫ a, ∫ v, α * (β + γ * H a v) ∂stdGauss (Fin (n - 1)) ∂muI n =
      α * (β + γ * ∫ a, ∫ v, H a v ∂stdGauss (Fin (n - 1)) ∂muI n) := by
  have hρ : IsProbabilityMeasure (stdGauss (Fin (n - 1))) := by unfold stdGauss; infer_instance
  have iH : ∀ a, Integrable (fun v => H a v) (stdGauss (Fin (n - 1))) := fun a =>
    intOfBdd (mH.comp measurable_prodMk_left) (bH a)
  have oH : Integrable (fun a => ∫ v, H a v ∂stdGauss (Fin (n - 1))) (muI n) :=
    intOfBdd (M := M) (mH.stronglyMeasurable.integral_prod_right'
      (ν := stdGauss (Fin (n - 1)))).measurable fun a => (abs_integral_le_integral_abs).trans
        ((integral_mono (iH a).abs (integrable_const M) (bH a)).trans (by simp))
  have e1 : ∀ a, ∫ v, α * (β + γ * H a v) ∂stdGauss (Fin (n - 1)) =
      α * (β + γ * ∫ v, H a v ∂stdGauss (Fin (n - 1))) := fun a => by
    rw [integral_const_mul, integral_add (integrable_const β) ((iH a).const_mul γ),
      integral_const_mul]
    simp
  simp_rw [e1]
  rw [integral_const_mul, integral_add (integrable_const β) (oH.const_mul γ), integral_const_mul]
  simp

lemma pow4_le_12 {y : ℝ} (_hy : 0 ≤ y) : y ^ 4 ≤ (2 + y ^ 12) / 3 := by
  have h : 0 ≤ (y ^ 4 - 1) ^ 2 * (y ^ 4 + 2) := by positivity
  nlinarith [h]

lemma pow4_le_24 {y : ℝ} : y ^ 4 ≤ (5 + y ^ 24) / 6 := by
  set z := y ^ 4 with hz
  have hz0 : 0 ≤ z := by positivity
  have e : y ^ 24 = z ^ 6 := by rw [hz, ← pow_mul]
  rw [e]
  have h : 0 ≤ (z - 1) ^ 2 * (z ^ 4 + 2 * z ^ 3 + 3 * z ^ 2 + 4 * z + 5) := by positivity
  nlinarith [h]

/-- `σ² ≤ γ_A·ω` pointwise. -/
lemma sgA_sq_le (hn : 1 ≤ n) (D : Design n) (c : Ret n) (a : Ix n) (v : Fin (n - 1) → ℝ) :
    BstLean.Part162.sgA D c a v ^ 2 ≤ 2 / (n : ℝ) * omK c.2.1.1 (xLat c (latC D c a) (unitF53 v)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : (0 : ℝ) ≤ 2 / (mA n : ℝ) := by positivity
  show BstLean.Part161.sigX D c (xLat c (latC D c a) (unitF53 v)) ^ 2 ≤ _
  unfold BstLean.Part161.sigX BstLean.Part134.sig omK
  rw [mul_pow, Real.sq_sqrt hm, Real.sq_sqrt (normSq_nonneg _)]
  have hres := BstLean.Part162.normSq_res_le (D.bA c.1 c.2.1.1)
    (hid2 c.2.1.1.1 c.2.1.1.2 (xLat c (latC D c a) (unitF53 v)))
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  rw [hmA]
  have e : 2 / (n : ℝ) * (normSq (hid2 c.2.1.1.1 c.2.1.1.2 (xLat c (latC D c a) (unitF53 v))) / n)
      = 2 / (n : ℝ) ^ 2 * normSq (hid2 c.2.1.1.1 c.2.1.1.2 (xLat c (latC D c a) (unitF53 v))) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left hres (by positivity)

/-- **The eighth moment of `σ` on the energy event**: `∫∫ σ⁸ ≤ (1.005·√γ_A)⁸`. -/
theorem sg8_of_SEn (hn : 2 ≤ n) (D : Design n) {c : Ret n} (hc : c ∈ agentEv D (SEn n))
    (hτ : 0 < D.tau0 c) :
    ∫ a, ∫ v, BstLean.Part162.sgA D c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      (1005 / 1000 * √(2 / (n : ℝ))) ^ 8 := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set θ := c.2.1.1
  set w : Ix n → (Fin (n - 1) → ℝ) → ℝ := fun a v => omK θ (xLat c (latC D c a) (unitF53 v))
    with hw
  have mw : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => w p.1 p.2) := by
    have h := measurable_omK_comp (θ := fun _ : Ix n × (Fin (n - 1) → ℝ) => θ) measurable_const
      (measurable_ptK_comp (ch := fun _ => c.1.2) (τ := fun _ => D.tau0 c) measurable_const
        measurable_const measurable_fst measurable_snd)
    exact h
  set B := BstLean.Part131.frob θ.2 * BstLean.Part131.frob θ.1 / n
  have w0 : ∀ a v, 0 ≤ w a v := fun a v => omK_nonneg _ _
  have wb : ∀ a v, w a v ≤ B := fun a v =>
    omK_le hn1 θ (BstLean.Part162.normSq_xLat_le hn1 c (BstLean.Part162.latC_sq_le D c a) v)
  have hB0 : 0 ≤ B := (w0 0 0).trans (wb 0 0)
  have hY := YEn_le hc hτ
  have hpt : ∀ a v, BstLean.Part162.sgA D c a v ^ 8 ≤
      (2 / (n : ℝ)) ^ 4 * (2 / 3 + 1 / 3 * w a v ^ 12) := fun a v => by
    have h1 := sgA_sq_le hn1 D c a v
    have h0 : 0 ≤ BstLean.Part162.sgA D c a v ^ 2 := sq_nonneg _
    calc BstLean.Part162.sgA D c a v ^ 8 = (BstLean.Part162.sgA D c a v ^ 2) ^ 4 := by ring
      _ ≤ (2 / (n : ℝ) * w a v) ^ 4 := pow_le_pow_left₀ h0 h1 4
      _ = (2 / (n : ℝ)) ^ 4 * w a v ^ 4 := by ring
      _ ≤ (2 / (n : ℝ)) ^ 4 * (2 / 3 + 1 / 3 * w a v ^ 12) := by
          have := pow4_le_12 (w0 a v)
          gcongr; linarith
  have ms : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => BstLean.Part162.sgA D c p.1 p.2 ^ 8) :=
    (BstLean.Part162.measurable_sgA D c).pow_const 8
  have bs : ∀ a v, |BstLean.Part162.sgA D c a v ^ 8| ≤ (2 / (n : ℝ) * B) ^ 4 := fun a v => by
    rw [abs_of_nonneg (by positivity)]
    have h1 := (sgA_sq_le hn1 D c a v).trans (mul_le_mul_of_nonneg_left (wb a v) (by positivity))
    calc BstLean.Part162.sgA D c a v ^ 8 = (BstLean.Part162.sgA D c a v ^ 2) ^ 4 := by ring
      _ ≤ _ := pow_le_pow_left₀ (sq_nonneg _) h1 4
  have bw : ∀ a v, |w a v ^ 12| ≤ B ^ 12 := fun a v => by
    rw [abs_of_nonneg (pow_nonneg (w0 a v) _)]; exact pow_le_pow_left₀ (w0 a v) (wb a v) _
  have bg : ∀ a v, |(2 / (n : ℝ)) ^ 4 * (2 / 3 + 1 / 3 * w a v ^ 12)| ≤
      (2 / (n : ℝ)) ^ 4 * (2 / 3 + 1 / 3 * B ^ 12) := fun a v => by
    rw [abs_of_nonneg (by have := w0 a v; positivity)]
    have := pow_le_pow_left₀ (w0 a v) (wb a v) 12
    gcongr
  refine (iint_mono ms ((mw.pow_const 12).const_mul (1 / 3) |>.const_add (2 / 3) |>.const_mul _)
    bs bg hpt).trans ?_
  rw [iint_affine (mw.pow_const 12) bw]
  have hY' : ∫ a, ∫ v, w a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ 11 / 10 := hY
  have e : (1005 / 1000 * √(2 / (n : ℝ))) ^ 8 = (1005 / 1000) ^ 8 * (2 / (n : ℝ)) ^ 4 := by
    rw [mul_pow, show (8 : ℕ) = 2 * 4 from rfl, pow_mul √(2 / (n : ℝ)),
      Real.sq_sqrt (by positivity)]
  rw [e, mul_comm ((1005 / 1000 : ℝ) ^ 8)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  nlinarith

open BstLean.Part169 (fbR eR KR measurable_fbR measurableSet_KR paperDesignP) in
/-- `f = √e_b·λ` is bounded by `√ω` pointwise: `f² ≤ ω`. -/
lemma fv_sq_le (hn : 1 ≤ n) (c : Ret n) (a : Ix n) (v : Fin (n - 1) → ℝ) :
    (√(eR c) * BstLean.Part161.lA (paperDesignP n) c a v) ^ 2 ≤
      omK c.2.1.1 (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set b := BstLean.Part169.bR c
  set h := hid2 c.2.1.1.1 c.2.1.1.2 (xLat c (latC (paperDesignP n) c a) (unitF53 v))
  have e1 : BstLean.Part161.lA (paperDesignP n) c a v = BstLean.Part134.lam b h := rfl
  have e2 : eR c = normSq b / n := rfl
  rw [e1, e2, mul_pow, Real.sq_sqrt (div_nonneg (normSq_nonneg _) hn0.le)]
  unfold BstLean.Part134.lam omK
  by_cases hb : normSq b = 0
  · rw [hb]; simp only [zero_div, zero_mul]; exact div_nonneg (normSq_nonneg _) hn0.le
  have hb0 : 0 < normSq b := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hb)
  have hcs : (∑ j, h j * b j) ^ 2 ≤ normSq h * normSq b := by
    unfold normSq
    exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  rw [div_pow, div_mul_div_comm, div_le_div_iff₀ (by positivity) hn0]
  have : normSq b * (∑ j, h j * b j) ^ 2 * n ≤ normSq b * (normSq h * normSq b) * n := by gcongr
  nlinarith [this]

open BstLean.Part169 (fbR eR KR measurable_fbR measurableSet_KR paperDesignP) in
/-- **The location means on the energy event**: `∫_K f̄²⁴ ≤ 1.005²⁴` and `∫_K f̄⁴ ≤ 1.005⁴` on
the kept indices `K = KR c` (the inputs `hf24`, `hf4` of `MomX` with `H_f = 1.005`). -/
theorem fb_of_SEn (hn : 2 ≤ n) {c : Ret n} (hc : c ∈ agentEv (paperDesignP n) (SEn n))
    (hτ : 0 < (paperDesignP n).tau0 c) :
    ∫ a in KR c, fbR c a ^ 24 ∂muI n ≤ (1005 / 1000) ^ 24 ∧
      ∫ a in KR c, fbR c a ^ 4 ∂muI n ≤ (1005 / 1000) ^ 4 := by
  have hn1 : 1 ≤ n := by omega
  have hρ : IsProbabilityMeasure (stdGauss (Fin (n - 1))) := by unfold stdGauss; infer_instance
  set D := paperDesignP n
  set θ := c.2.1.1
  set w : Ix n → (Fin (n - 1) → ℝ) → ℝ := fun a v => omK θ (xLat c (latC D c a) (unitF53 v))
    with hw
  have mw : Measurable (fun p : Ix n × (Fin (n - 1) → ℝ) => w p.1 p.2) :=
    measurable_omK_comp (θ := fun _ : Ix n × (Fin (n - 1) → ℝ) => θ) measurable_const
      (measurable_ptK_comp (ch := fun _ => c.1.2) (τ := fun _ => D.tau0 c) measurable_const
        measurable_const measurable_fst measurable_snd)
  set B := BstLean.Part131.frob θ.2 * BstLean.Part131.frob θ.1 / n
  have w0 : ∀ a v, 0 ≤ w a v := fun a v => omK_nonneg _ _
  have wb : ∀ a v, w a v ≤ B := fun a v =>
    omK_le hn1 θ (BstLean.Part162.normSq_xLat_le hn1 c (BstLean.Part162.latC_sq_le D c a) v)
  have hB0 : 0 ≤ B := (w0 0 0).trans (wb 0 0)
  have hY : ∫ a, ∫ v, w a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ 11 / 10 := YEn_le hc hτ
  set f : Ix n → (Fin (n - 1) → ℝ) → ℝ := fun a v => √(eR c) * BstLean.Part161.lA D c a v
    with hfd
  have mf : ∀ a, Measurable (fun v => f a v) := fun a =>
    (BstLean.Part161.measurable_lA_left D c a).const_mul _
  have f2 : ∀ a v, f a v ^ 2 ≤ w a v := fun a v => fv_sq_le hn1 c a v
  have fbd : ∀ a v, |f a v| ≤ √B := fun a v => by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt ((f2 a v).trans (wb a v))
  have iv : ∀ a, Integrable (fun v => f a v) (stdGauss (Fin (n - 1))) := fun a =>
    intOfBdd (mf a) (fbd a)
  have efb : ∀ a, fbR c a = ∫ v, f a v ∂stdGauss (Fin (n - 1)) := fun a => by
    simp only [hfd]
    rw [integral_const_mul]; rfl
  -- `f̄²⁴ ≤ ∫ ω¹²`
  have h24 : ∀ a, fbR c a ^ 24 ≤ ∫ v, w a v ^ 12 ∂stdGauss (Fin (n - 1)) := fun a => by
    rw [efb a]
    have hJ := (Even.convexOn_pow (𝕜 := ℝ) (n := 24) (by decide)).map_integral_le
      (μ := stdGauss (Fin (n - 1))) (f := fun v => f a v) (continuous_pow 24).continuousOn
      isClosed_univ (Filter.Eventually.of_forall fun v => Set.mem_univ _) (iv a)
      (intOfBdd (M := √B ^ 24) ((mf a).pow_const 24) fun v => by
        simp only [Function.comp_def]; rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (fbd a v) _)
    refine hJ.trans (integral_mono ?_ ?_ fun v => ?_)
    · exact intOfBdd (M := √B ^ 24) ((mf a).pow_const 24) fun v => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (fbd a v) _
    · exact intOfBdd (M := B ^ 12) ((mw.comp measurable_prodMk_left).pow_const 12) fun v => by
        rw [abs_of_nonneg (pow_nonneg (w0 a v) _)]; exact pow_le_pow_left₀ (w0 a v) (wb a v) _
    · show f a v ^ 24 ≤ w a v ^ 12
      rw [show (24 : ℕ) = 2 * 12 from rfl, pow_mul]
      exact pow_le_pow_left₀ (sq_nonneg _) (f2 a v) 12
  have fbb : ∀ a, |fbR c a| ≤ √B := fun a => by
    rw [efb a]
    refine (abs_integral_le_integral_abs).trans ((integral_mono (iv a).abs
      (integrable_const _) (fbd a)).trans (by simp))
  have mfb := measurable_fbR c
  have i24 : Integrable (fun a => fbR c a ^ 24) (muI n) :=
    intOfBdd (M := √B ^ 24) (mfb.pow_const 24) fun a => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (fbb a) _
  have i4 : Integrable (fun a => fbR c a ^ 4) (muI n) :=
    intOfBdd (M := √B ^ 4) (mfb.pow_const 4) fun a => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (fbb a) _
  have iW : Integrable (fun a => ∫ v, w a v ^ 12 ∂stdGauss (Fin (n - 1))) (muI n) :=
    intOfBdd (M := B ^ 12) ((mw.pow_const 12).stronglyMeasurable.integral_prod_right'
      (ν := stdGauss (Fin (n - 1)))).measurable fun a => by
        rw [abs_of_nonneg (integral_nonneg fun v => pow_nonneg (w0 a v) _)]
        calc ∫ v, w a v ^ 12 ∂stdGauss (Fin (n - 1)) ≤ ∫ v, B ^ 12 ∂stdGauss (Fin (n - 1)) :=
              integral_mono (intOfBdd (M := B ^ 12) ((mw.comp measurable_prodMk_left).pow_const 12)
                fun v => by
                  rw [abs_of_nonneg (pow_nonneg (w0 a v) _)]
                  exact pow_le_pow_left₀ (w0 a v) (wb a v) _)
                (integrable_const _) fun v => pow_le_pow_left₀ (w0 a v) (wb a v) _
          _ = B ^ 12 := by simp
  have hall24 : ∫ a, fbR c a ^ 24 ∂muI n ≤ 11 / 10 :=
    (integral_mono i24 iW h24).trans hY
  have hK24 : ∫ a in KR c, fbR c a ^ 24 ∂muI n ≤ ∫ a, fbR c a ^ 24 ∂muI n :=
    setIntegral_le_integral i24 (Filter.Eventually.of_forall fun a => by positivity)
  have hK4 : ∫ a in KR c, fbR c a ^ 4 ∂muI n ≤ ∫ a, fbR c a ^ 4 ∂muI n :=
    setIntegral_le_integral i4 (Filter.Eventually.of_forall fun a => by positivity)
  refine ⟨hK24.trans (hall24.trans (by norm_num)), hK4.trans ?_⟩
  have i5 : Integrable (fun a => (5 + fbR c a ^ 24) / 6) (muI n) :=
    ((integrable_const 5).add i24).div_const 6
  calc ∫ a, fbR c a ^ 4 ∂muI n ≤ ∫ a, (5 + fbR c a ^ 24) / 6 ∂muI n :=
        integral_mono i4 i5 fun a => pow4_le_24
    _ = (5 + ∫ a, fbR c a ^ 24 ∂muI n) / 6 := by
        rw [integral_div, integral_add (integrable_const 5) i24]; simp
    _ ≤ (1005 / 1000) ^ 4 := by linarith [hall24]

open BstLean.Part169 (fbR KR paperDesignP) in
theorem fb24_of_SEn (hn : 2 ≤ n) {c : Ret n} (hc : c ∈ agentEv (paperDesignP n) (SEn n))
    (hτ : 0 < (paperDesignP n).tau0 c) :
    ∫ a in KR c, fbR c a ^ 24 ∂muI n ≤ (1005 / 1000) ^ 24 := (fb_of_SEn hn hc hτ).1

open BstLean.Part169 (fbR KR paperDesignP) in
theorem fb4_of_SEn (hn : 2 ≤ n) {c : Ret n} (hc : c ∈ agentEv (paperDesignP n) (SEn n))
    (hτ : 0 < (paperDesignP n).tau0 c) :
    ∫ a in KR c, fbR c a ^ 4 ∂muI n ≤ (1005 / 1000) ^ 4 := (fb_of_SEn hn hc hτ).2

end BstLean.Part177
