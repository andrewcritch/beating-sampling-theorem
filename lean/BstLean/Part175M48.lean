import BstLean.Part175Cert

/-!
# Part 175 (file `M48`): the floor mass and the root sum at `n ≥ 48 000`

No proof is left open; no `native_decide` or `axiom` is used.

Files `Mass` and `Root` again, for `n ≥ 48 000`, namespace `BstLean.Part175.N48`. Changes:
* `W20_le_528_48`: `W₂₀ ≤ (1.0622·θ/n)²⁰` (`ε = 0.0295`).
* Lemma PP at order `P = 400` with `η = 0.0015` (file `Mass`: `P = 200`, `η = 0.006`):
  `gaussMomConst_400_le` (`𝔪₄₀₀ ≤ 17.5`), `jS_400_le_48000` (`jS ≤ 1.0241`); the event
  `SXM48 n` (`X₂₀ ≤ (1.0755·n)²⁰·W₂₀`), **`SXM48_charge`** (`≤ 5·10⁻⁵`; Markov at order 800).
* `tX20_le_W48`: `t_A²⁰·X₂₀ ≤ (0.6032·γ_A/n)²⁰`; `betaMW48` with `0.6032`; `mass_order40W48`,
  `mass_of_goodCW48`, **`classifier_paper_free23_massW48`**.
* Root sum: `887 + 474 + 659 ≤ 2159` (units `10⁻⁶`), mass budget `1.12·10⁻¹¹`
  (`betaMW48 n 0.4691 ≤ 1.12·10⁻¹¹` for `n ≥ 48 000`); **`classifier_paper_root48k`**.
The docstrings of the copied lemmas can carry older numbers; the Lean statements are authoritative.
-/

namespace BstLean.Part175.N48

section SMass
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part165
open BstLean.Part161 (muI sigX lamX BIAS_hyp)
open BstLean.Part162 (sgA gmom gmom_nonneg psiA rootFL latMomOfPsi12e eps0 dPaper)
open BstLean.Part153 (XiS Xi4 N2 hid2Mean_cr nuA jS)
open BstLean.Part134 (res sig)
open BstLean.Part164 (goodA window_goodA goodC16_of_goodA hE8_of_good CAn E0 E0_nonneg roomB roomB_ge)

open BstLean.Part175 (win528_goodA s0W s0W_cond)

variable {n : ℕ}

/-! ## The radius moment `W₂₀` in the window `θ ≤ 0.528` -/

/-- **`E[(τ²/|y|²)²⁰] ≤ (1.0622·θ/n)²⁰`** for `n ≥ 48 000`, `0.46 ≤ θ ≤ 0.528`. -/
theorem W20_le_528_48 (hn : 48000 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000) :
    WqN 20 c τ ≤ (10622 / 10000 * (thetaC c τ / n)) ^ 20 := by
  have hnR : (48000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := WqN_le (q := 20) (by omega) c hτ (ε := 295 / 10000) (by norm_num) (by norm_num)
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = τ ^ 2 := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = normSq c + (n : ℝ) * τ ^ 2 := ⟨_, rfl⟩
  have hR0 : 0 < R := by
    have := normSq_nonneg c
    rw [hR]; nlinarith [sq_pos_of_pos hτ]
  have hθ : thetaC c τ = (n : ℝ) * T / R := by
    unfold thetaC rhoC
    rw [Real.sq_sqrt (by rw [← hR]; exact hR0.le), ← hR, ← hT]
  rw [hθ] at hθ0 hθ1 ⊢
  rw [le_div_iff₀ hR0] at hθ0
  rw [div_le_iff₀ hR0] at hθ1
  rw [← hT, show normSq c + (n : ℝ) * T - T = R - T by rw [hR, hT]] at h
  have hT23 : 48000 * T ≤ 528 / 1000 * R := by nlinarith
  have hQ0 : 0 < R - T := by nlinarith
  have e : (n : ℝ) * T / R / n = T / R := by field_simp
  rw [e]
  have hTR0 : 0 ≤ T / R := by positivity
  -- the first term
  have h1 : T / ((1 - 295 / 10000) ^ 2 * (R - T)) ≤ 10618 / 10000 * (T / R) := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hR0]
    have : R ≤ 10618 / 10000 * ((1 - 295 / 10000) ^ 2 * (R - T)) := by nlinarith
    calc T * R ≤ T * (10618 / 10000 * ((1 - 295 / 10000) ^ 2 * (R - T))) :=
          mul_le_mul_of_nonneg_left this hT0.le
      _ = 10618 / 10000 * T * ((1 - 295 / 10000) ^ 2 * (R - T)) := by ring
  have h1' := pow_le_pow_left₀ (by positivity) h1 20
  -- the second term
  have hexp : exp (-((295 / 10000 : ℝ) ^ 2 * (R - T)) / (2 * T)) ≤ exp (-13) ^ 3 := by
    rw [← Real.exp_nat_mul]
    apply exp_le_exp.mpr
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  have hE4 : exp (-13) ^ 3 ≤ ((1504 / 10 ^ 6 : ℝ) ^ 3) ^ 2 := by
    have := pow_le_pow_left₀ (exp_pos _).le exp_neg_13_le 3
    calc exp (-13) ^ 3 ≤ ((1504 / 10 ^ 6 : ℝ) ^ 2) ^ 3 := this
      _ = ((1504 / 10 ^ 6 : ℝ) ^ 3) ^ 2 := by ring
  have hsq : √(exp (-((295 / 10000 : ℝ) ^ 2 * (R - T)) / (2 * T))) ≤ (1504 / 10 ^ 6 : ℝ) ^ 3 := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ (1504 / 10 ^ 6) ^ 3 by norm_num)]
    exact Real.sqrt_le_sqrt (hexp.trans hE4)
  have hd0 : (0 : ℝ) < (n : ℝ) - 1 - 4 * (20 : ℕ) := by push_cast; linarith
  have hTR : 46 / 100 / (n : ℝ) ≤ T / R := by
    rw [div_le_div_iff₀ hn0 hR0]
    linarith
  have hinv : ((n : ℝ) - 1 - 4 * (20 : ℕ))⁻¹ ≤ 219 / 100 * (T / R) := by
    have h4 : ((n : ℝ) - 1 - 4 * (20 : ℕ))⁻¹ ≤ 219 / 100 * (46 / 100 / (n : ℝ)) := by
      rw [inv_eq_one_div, mul_div_assoc', div_le_div_iff₀ hd0 hn0]
      push_cast
      nlinarith
    exact h4.trans (mul_le_mul_of_nonneg_left hTR (by norm_num))
  have h2' := pow_le_pow_left₀ (inv_nonneg.mpr hd0.le) hinv 20
  have h2 : √(exp (-((295 / 10000 : ℝ) ^ 2 * (R - T)) / (2 * T))) *
      (((n : ℝ) - 1 - 4 * (20 : ℕ))⁻¹) ^ 20 ≤
      (1504 / 10 ^ 6 : ℝ) ^ 3 * (219 / 100 * (T / R)) ^ 20 :=
    mul_le_mul hsq h2' (by positivity) (by norm_num)
  have hfin : (10618 / 10000 * (T / R)) ^ 20 + (1504 / 10 ^ 6 : ℝ) ^ 3 * (219 / 100 * (T / R)) ^ 20 ≤
      (10622 / 10000 * (T / R)) ^ 20 := by
    have e2 : (10622 / 10000 * (T / R)) ^ 20 - ((10618 / 10000 * (T / R)) ^ 20 +
        (1504 / 10 ^ 6 : ℝ) ^ 3 * (219 / 100 * (T / R)) ^ 20) =
        ((10622 / 10000 : ℝ) ^ 20 - (10618 / 10000) ^ 20 - (1504 / 10 ^ 6) ^ 3 * (219 / 100) ^ 20) *
          (T / R) ^ 20 := by ring
    have : 0 ≤ ((10622 / 10000 : ℝ) ^ 20 - (10618 / 10000) ^ 20 - (1504 / 10 ^ 6) ^ 3 *
          (219 / 100) ^ 20) * (T / R) ^ 20 := mul_nonneg (by norm_num) (by positivity)
    linarith
  push_cast at h h2
  linarith

/-! ## The event `SXM48` with the sharper Lemma PP constant -/

/-- **The event of the gradient moment of order 40 with `M = 1.0755`** (`n ≥ 48 000`): `X₂₀ ≤ (1.0755·n)²⁰·W₂₀`. -/
def SXM48 (n : ℕ) : Set (AgFam n) :=
  {x | XqN 20 x.2.1 x.2.2 x.1.1 x.1.2 ≤ (10755 / 10000 * (n : ℝ)) ^ 20 * WqN 20 x.1.1 x.1.2}

theorem measurableSet_SXM48 (n : ℕ) : MeasurableSet (SXM48 n) :=
  measurableSet_le (measurable_XqN_fam 20) ((measurable_WqN_fam 20).const_mul _)

/-- `𝔪₄₀₀ ≤ 17.5`: `2⁴⁰⁰·400! ≤ 17.5⁸⁰⁰`. -/
lemma gaussMomConst_400_le : BstLean.Part152.gaussMomConst 400 ≤ 35 / 2 := by
  have hp := BstLean.Part152.gaussMomConst_pow (P := 400) (by norm_num)
  have hN : (2 ^ 200) ^ 2 * Nat.factorial 400 * (2 ^ 200) ^ 4 ≤ (35 ^ 200) ^ 4 := by
    norm_num [Nat.factorial]
  have h1 : BstLean.Part152.gaussMomConst 400 ^ (2 * 400) ≤ (35 / 2 : ℝ) ^ (2 * 400) := by
    rw [hp]
    have e1 : (2 : ℝ) ^ 400 = (2 ^ 200) ^ 2 := by rw [← pow_mul]
    have e2 : (35 / 2 : ℝ) ^ (2 * 400) = ((35 : ℝ) ^ 200) ^ 4 / ((2 : ℝ) ^ 200) ^ 4 := by
      rw [div_pow, ← pow_mul, ← pow_mul]
    rw [e1, e2, le_div_iff₀ (by positivity)]
    exact_mod_cast hN
  by_contra hlt
  have := pow_lt_pow_left₀ (not_le.mp hlt) (by norm_num : (0 : ℝ) ≤ 35 / 2)
    (by norm_num : (2 * 400 : ℕ) ≠ 0)
  exact absurd h1 (not_le.mpr this)

lemma sqrt_eta15_le : √(1 + 2 * (15 / 10000) : ℝ) ≤ 10015 / 10000 := by
  rw [Real.sqrt_le_iff]
  constructor <;> norm_num

lemma epsS_400_le {n : ℕ} (hn : 48000 ≤ n) :
    BstLean.Part153.epsS n 400 (15 / 10000) ≤ 7 / 10 ^ 6 := by
  have hnr : (48000 : ℝ) ≤ n := by exact_mod_cast hn
  refine le_trans ?_ BstLean.Part153.exp_neg_12_le
  unfold BstLean.Part153.epsS
  rw [show ((400 : ℕ) : ℝ) = 400 by norm_num]
  refine Real.exp_le_exp.2 ?_
  have : (48000 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnr 2
  have h12 : (12 : ℝ) ≤ (15 / 10000) ^ 2 * (n : ℝ) ^ 2 / 400 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  linarith

/-- `jS n 400 (15/10000) ≤ 1.0241` for `n ≥ 48 000`. -/
lemma jS_400_le_48000 (hn : 48000 ≤ n) : jS n 400 (15 / 10000) ≤ 10241 / 10000 := by
  have hnr : (48000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : (219 : ℝ) ≤ √(n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hg0 := BstLean.Part152.gaussMomConst_nonneg 400
  have hg := gaussMomConst_400_le
  have hu : 1 / √(n : ℝ) ≤ 1 / 219 := one_div_le_one_div_of_le (by norm_num) hs
  have hw : BstLean.Part152.gaussMomConst 400 / (n : ℝ) ≤ (35 / 2) / 48000 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    nlinarith
  have hgu : BstLean.Part152.gaussMomConst 400 / √(n : ℝ) ≤ (35 / 2) / 219 := by
    rw [div_le_div_iff₀ hs0 (by norm_num)]
    nlinarith
  refine (BstLean.Part153.jS_le_atoms n 400 (15 / 10000) BstLean.Part153.sqrt_two_le
    sqrt_eta15_le hu hw hgu (epsS_400_le hn)).trans ?_
  norm_num

lemma pow_9755_le : (9755 / 10000 : ℝ) ^ 400 ≤ 5 / 100000 := by
  have : (9755 / 10000 : ℝ) ^ 400 = ((9755 / 10000 : ℝ) ^ 100) ^ 4 := by rw [← pow_mul]
  rw [this]
  norm_num

/-- **The charge of `SXM48 n`**: at most `5·10⁻⁵` (`n ≥ 48 000`, `τ > 0`; Markov over the
weights at order `800`: `q = 20`, `P' = 20`, Lemma PP with `P = 400`, `η = 0.0015`). -/
theorem SXM48_charge (hn : 48000 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SXM48 n} ≤ 5 / 100000 := by
  have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      ((c, τ), θ) ∉ SXM48 n} =
      {θ | (10755 / 10000 * (n : ℝ)) ^ 20 * WqN 20 c τ < XqN 20 θ.1 θ.2 c τ} := by
    ext θ
    change ¬ (XqN 20 θ.1 θ.2 c τ ≤ (10755 / 10000 * (n : ℝ)) ^ 20 * WqN 20 c τ) ↔ _
    exact not_le
  rw [e]
  have h := markov_XqN (n := n) (q := 20) (P' := 20) (by norm_num) (by omega) c hτ
    (BstLean.Part153.jS_nonneg n 400 (15 / 10000))
    (fun _ hx => by
      exact BstLean.Part153.lemmaPP_i_sharp (by omega) (by norm_num)
        (by norm_num : (0 : ℝ) ≤ 15 / 10000) hx) (M := 10755 / 10000) (by norm_num)
  refine h.trans ?_
  have hj0 := BstLean.Part153.jS_nonneg n 400 (15 / 10000)
  have hj := jS_400_le_48000 hn
  have hj2 : jS n 400 (15 / 10000) ^ 2 ≤ (10241 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hj0 hj 2
  have hratio : jS n 400 (15 / 10000) ^ 2 / (10755 / 10000) ≤ 9755 / 10000 := by
    rw [div_le_iff₀ (by norm_num)]
    refine hj2.trans (by norm_num)
  exact (pow_le_pow_left₀ (by positivity) hratio (20 * 20)).trans pow_9755_le

theorem SXM48_ret_charge (hn : 48000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real (agentEv (paperDesign n fT wT hf hw) (SXM48 n))ᶜ ≤
      5 / 100000 := by
  rw [agentEv_compl]
  exact retDist_agent_charge (paperDesign n fT wT hf hw) (paperDesign_tauWorld fT wT hf hw)
    (measurableSet_SXM48 n) (by norm_num) (fun c τ hτ => SXM48_charge hn c τ hτ)

/-- **The gradient moment of order 40 on `SXM48` in the window `θ ≤ 0.528`**:
`t_A²⁰·X₂₀ ≤ (0.6032·γ_A/n)²⁰` (`1.0755·1.0622·0.528 ≤ 0.6032`), for `n ≥ 48 000`. -/
theorem tX20_le_W48 (hn : 48000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXM48 n) :
    (2 / (mA n : ℝ)) ^ 20 * XqN 20 A₁ A₂ c τ ≤ (6032 / 10000 * (2 / (n : ℝ)) / n) ^ 20 := by
  have hnR : (48000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have h1 : XqN 20 A₁ A₂ c τ ≤ (10755 / 10000 * (n : ℝ)) ^ 20 * WqN 20 c τ := h
  have h2 := W20_le_528_48 hn c hτ hθ0 hθ1
  have hθn : (0 : ℝ) ≤ thetaC c τ := by linarith
  have h3 : XqN 20 A₁ A₂ c τ ≤ (10755 / 10000 * (10622 / 10000) * thetaC c τ) ^ 20 := by
    refine h1.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq ?_))
    rw [← mul_pow]; congr 1; field_simp
  have hB : 10755 / 10000 * (10622 / 10000) * thetaC c τ ≤ 6032 / 10000 := by nlinarith
  have h4 := pow_le_pow_left₀ (by positivity) hB 20
  rw [hmA]
  calc (2 / (n : ℝ) ^ 2) ^ 20 * XqN 20 A₁ A₂ c τ ≤ (2 / (n : ℝ) ^ 2) ^ 20 * (6032 / 10000) ^ 20 :=
        mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
    _ = (6032 / 10000 * (2 / (n : ℝ)) / n) ^ 20 := by rw [← mul_pow]; congr 1; field_simp


/-- **The mass bound of order 40 at `n ≥ 48 000`**:
`β(n, sd) = (π/2)⁴⁰·E|g|⁴⁰·(0.6032/(n(s0W − sd)²))²⁰`. -/
noncomputable def betaMW48 (n : ℕ) (sd : ℝ) : ℝ :=
  (π / 2) ^ 40 * gmom 40 * (6032 / 10000 / ((n : ℝ) * (s0W - sd) ^ 2)) ^ 20

lemma betaMW48_nonneg (n : ℕ) (sd : ℝ) : 0 ≤ betaMW48 n sd := by
  unfold betaMW48
  have := gmom_nonneg 40
  have h : 0 ≤ (6032 / 10000 / ((n : ℝ) * (s0W - sd) ^ 2)) ^ 20 := by
    rw [show (20 : ℕ) = 2 * 10 by norm_num, pow_mul]; positivity
  positivity

/-- **The mass below the floor from the moment of order 40 of `σ`**, for one retained value:
with the quantities of the frame events and the event `SXM48 n`, in the window `θ ≤ 0.528`,
`∫_a ν{σ < √γ_A·sd} ≤ betaMW48 n sd` for `0 ≤ sd < s0W`, `n ≥ 23 000`. -/
theorem mass_order40W48 (hn : 48000 ≤ n) (D : Design n) (c : Ret n) (hτ : 0 < D.tau0 c)
    (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c)) (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100)
    (hθ2 : thetaC c.1.2 (D.tau0 c) ≤ 528 / 1000)
    (hb : 0 < normSq (D.bA c.1 c.2.1.1))
    (hXi : XiS c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ 11911 / 10000 * (2 / (n : ℝ)) / n)
    (heb : 2 / (mA n : ℝ) * normSq (D.bA c.1 c.2.1.1) ≤ 2 / (n : ℝ) * (7315 / 10000))
    (hxi : 2 / (mA n : ℝ) * normSq (hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) -
      D.bA c.1 c.2.1.1) ≤ 485 / 1000 * (2 / (n : ℝ)) / n)
    (hN22 : N2 2 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ 18334 / 1000 / (n : ℝ))
    (hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM48 n)
    {sd : ℝ} (hsd0 : 0 ≤ sd) (hsd : sd < s0W) :
    ∫ a', (stdGauss (Fin (n - 1))).real {v | sgA D c a' v < √(2 / (n : ℝ)) * sd} ∂muI n ≤
      betaMW48 n sd := by
  have hnR : (48000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hc : c.1.2 ≠ 0 := c_ne_of_theta (by omega) hτ hθ1
  rw [BstLean.Part162.mass_eq_stand (by omega) D c hc hτ]
  -- the tail bound of order 40
  set A₁ := c.2.1.1.1
  set A₂ := c.2.1.1.2
  set b := D.bA c.1 c.2.1.1
  set τ := D.tau0 c
  have hX := tX20_le_W48 hn hτ hθ0 hθ2 hS
  set K : ℝ := (π / 2) ^ 40 * (gmom 40 * (6032 / 10000 * (2 / (n : ℝ)) / n) ^ 20) with hK
  have hT : ∀ g : ℝ, 0 < g → (stdGauss (Fin n)).real
      {ξ | g ≤ |sigD A₁ A₂ c.1.2 τ b ξ - ∫ ζ, sigD A₁ A₂ c.1.2 τ b ζ ∂stdGauss (Fin n)|} ≤
        K / g ^ 40 := by
    intro g hg
    have h := sigD_tail (q := 20) (by norm_num) (by omega) A₁ A₂ c.1.2 hτ hb hg
    refine h.trans (div_le_div_of_nonneg_right ?_ (by positivity))
    rw [hK]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hX (gmom_nonneg _)) (by positivity)
  have hXi' : XiS A₁ A₂ c.1.2 τ ≤ 11911 / 10000 * (2 / (n : ℝ)) / n := hXi
  have hm := mass_bound_gen (by omega) A₁ A₂ c.1.2 hτ hb hXi' heb hxi hN22
    (e1 := 8553 / 10000) (e2 := 46 / 10000) (by norm_num) (by norm_num) (by norm_num)
    (by rw [div_le_iff₀ hn0]; nlinarith) hsd0 hsd (by
      have := s0W_cond (by omega : 45000 ≤ n)
      unfold s0W at this ⊢
      linarith) hT
  have hset : {ξ : Fin n → ℝ | sigX D c (sphPt (c.1.2 + D.tau0 c • ξ)) < √(2 / (n : ℝ)) * sd} =
      {ξ | 2 / (mA n : ℝ) * normSq (res (D.bA c.1 c.2.1.1)
        (hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ)))) < 2 / (n : ℝ) * sd ^ 2} := by
    ext ξ
    simp only [Set.mem_ofPred_eq]
    set R := normSq (res (D.bA c.1 c.2.1.1) (hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ))))
    have hR : 0 ≤ R := normSq_nonneg _
    have hsig : sigX D c (sphPt (c.1.2 + D.tau0 c • ξ)) = √(2 / (mA n : ℝ)) * √R := rfl
    rw [hsig, ← Real.sqrt_mul (by positivity)]
    have e : √(2 / (n : ℝ)) * sd = √(2 / (n : ℝ) * sd ^ 2) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hsd0]
    rw [e]
    exact Real.sqrt_lt_sqrt_iff (by positivity)
  rw [hset]
  refine hm.trans (le_of_eq ?_)
  -- the value of `K / (√γ_A (s0W − sd))⁴⁰`
  have hd : 0 < s0W - sd := by linarith
  have hγ : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hs40 : (√(2 / (n : ℝ)) * (s0W - sd)) ^ 40 = (2 / (n : ℝ)) ^ 20 * ((s0W - sd) ^ 2) ^ 20 := by
    rw [mul_pow, show (40 : ℕ) = 2 * 20 by norm_num, pow_mul, pow_mul, Real.sq_sqrt hγ.le]
  unfold s0W at hs40 hd ⊢
  rw [hs40, hK]
  unfold betaMW48 s0W
  field_simp

/-- **The mass below the floor on the good set**: `∫_a ν{σ < √γ_A·sd} ≤ betaMW48 n sd`. -/
theorem mass_of_goodCW48 (hn : 48000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodC n (paperDesign n fT wT hf hw) (EA ∩ agentEv (paperDesign n fT wT hf hw) (SXM48 n)))
    {sd : ℝ} (hsd0 : 0 ≤ sd) (hsd : sd < s0W) :
    ∫ a, (stdGauss (Fin (n - 1))).real
        {v | sgA (paperDesign n fT wT hf hw) c a v < √(2 / (n : ℝ)) * sd} ∂muI n ≤
      betaMW48 n sd := by
  set D := paperDesign n fT wT hf hw
  have hn16 : 16384 ≤ n := by omega
  obtain ⟨hτ, hθ0, hθ1⟩ := window_goodA hn16 fT wT hf hw _ c hc
  have hG := goodC16_of_goodA hn16 fT wT hf hw hc
  have hSc : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n := hc.2.2.1.1.2 hτ
  have hS20 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXM48 n := hc.2.1.2.1.1.1.2 hτ
  have hθ2 := (win528_goodA hn16 fT wT hf hw _ hc).2.2
  obtain ⟨hxi, -, -, hpos, hX4, hN22, -⟩ := centre16 hn16 hτ hθ0 hθ1 hG
  have heb := eb16_sharp hn16 hτ hθ0 hθ1 hG hSc
  have hb : D.bA c.1 c.2.1.1 =
      (1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) :=
    paperDesign_agentCentre fT wT hf hw c
  rw [← hb] at hxi hpos heb
  have hXi := (BstLean.Part153.XiS_le_Xi4 (by omega) c.2.1.1.1 c.2.1.1.2 c.1.2 hτ).trans hX4
  exact mass_order40W48 hn D c hτ hθ0 hθ1 hθ2 hpos hXi heb hxi hN22 hS20 hsd0 hsd

/-- **The free-event classifier theorem with the sharper floor mass (every `n ≥ 48 000`).**
Part 174's `classifier_paper_free23_mass40P` with `s0W`, `betaMW48` and `mass_of_goodCW48`. The caller
event `E_A` is intersected with `agentEv D (SXM48 n)`, whose charge `5·10⁻⁵` is paid here: the room
for `E_A` is `roomC − 5·10⁻⁵`. -/
theorem classifier_paper_free23_massW48 (hn : 48000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomC - 5 / 100000)
    (hM : ∀ (c : Ret n) (hc : c ∈ goodC n (paperDesign n fT wT hf hw)
        (EA ∩ agentEv (paperDesign n fT wT hf hw) (SXM48 n))),
      ∃ (wl ws sd η CL CS : ℝ) (h0 : 0 < η) (h1 : η < 1) (hCL : 0 < CL)
        (hCS : 0 < CS) (hsd0 : 0 < sd) (hsd : sd < s0W)
        (hL12 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 12)
        (hS12 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 12),
        0 < wl ∧ 0 < ws ∧ eps0 ws (√(2 / (n : ℝ)) * sd) < 1 ∧
        rootFL wl ws η (CAn n) (latMomOfPsi12e (by omega) (paperDesign n fT wT hf hw) c hCL hCS
          (E0_nonneg n) (betaMW48_nonneg n sd) hL12 hS12 (hE8_of_good (by omega) fT wT hf hw hc)
          (mass_of_goodCW48 hn fT wT hf hw hc hsd0.le hsd)) ≤ 2159 / 10 ^ 6 ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws (√(2 / (n : ℝ)) * sd) η h0 h1)
          (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  set D := paperDesign n fT wT hf hw
  set S := BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
    BstLean.Part159.Ethp (paperCentres n)
  set E1 := EA ∩ agentEv D (SXM48 n) with hE1
  have hE1m : MeasurableSet E1 := hEA.inter (measurableSet_agentEv D (measurableSet_SXM48 n))
  have hEA' : MeasurableSet (E1 ∩ agentEv D (SXqN n 20)) :=
    hE1m.inter (measurableSet_agentEv D (measurableSet_SXqN n 20))
  have hA' : (retDist (paperCentres n)).real (S ∩ (E1 ∩ agentEv D (SXqN n 20))ᶜ) ≤
      δA + 5 / 100000 + 5 / 100000 := by
    have hsub : S ∩ (E1 ∩ agentEv D (SXqN n 20))ᶜ ⊆
        ((S ∩ EAᶜ) ∪ (agentEv D (SXM48 n))ᶜ) ∪ (agentEv D (SXqN n 20))ᶜ := by
      intro c hc
      by_cases h1 : c ∈ EA
      · by_cases h2 : c ∈ agentEv D (SXM48 n)
        · exact Or.inr fun h3 => hc.2 ⟨⟨h1, h2⟩, h3⟩
        · exact Or.inl (Or.inr h2)
      · exact Or.inl (Or.inl ⟨hc.1, h1⟩)
    refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
    have c1 := SX20_ret_charge (by omega) fT wT hf hw
    have c2 := SXM48_ret_charge hn fT wT hf hw
    have c3 := (measureReal_union_le (μ := retDist (paperCentres n)) (S ∩ EAᶜ)
      (agentEv D (SXM48 n))ᶜ)
    linarith
  have hroom' : δA + 5 / 100000 + 5 / 100000 ≤ roomB := by unfold roomC at hroom; linarith
  refine BstLean.Part164.classifier_paper_free23_cA8 (by omega) fT wT hf hw t hEA' hA' hroom'
    fun c hc => ?_
  obtain ⟨wl, ws, sd, η, CL, CS, h0, h1, hCL, hCS, hsd0, hsd, hL12, hS12, hwl, hws, hε, hroot,
    hbias⟩ := hM c hc
  have hσl : 0 < √(2 / (n : ℝ)) * sd := by
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  exact ⟨wl, ws, √(2 / (n : ℝ)) * sd, η, CL, CS, betaMW48 n sd, h0, h1, hCL, hCS, betaMW48_nonneg n sd,
    hL12, hS12, mass_of_goodCW48 hn fT wT hf hw hc hsd0.le hsd, hwl, hws, hσl, hε, hroot, hbias⟩


end SMass

section SRoot
open BstLean.Part175 (s0W)
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part148 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part165
open BstLean.Part161 (muI lamX sigX BIAS_hyp)
open BstLean.Part162 (sgA psiA rootFL latMomOfPsi12e eps0 dPaper cLS kLSs gmom gmom_even LatMom)
open BstLean.Part162 (tK tK_nonneg priceC Bpap Dpap cVw cEw iotaP c2η c3η)
open BstLean.Part164 (goodA hE8_of_good CAn E0 E0_nonneg CAn_le E0_le)

section core2

variable {g s : ℝ}

lemma rc_price48 {n : ℕ} {κ L ε E A D e4 d4 e6 d6 : ℝ} (hg : 0 < g) (hgn : (n : ℝ) * g ^ 2 = 2)
    (hg0 : g ^ 2 ≤ 2 / 48000) (h0κ : 0 ≤ κ) (h0L : 0 ≤ L) (h0ε : 0 ≤ ε) (h0E : 0 ≤ E)
    (h0A : 0 ≤ A) (h0D : 0 ≤ D) (h0e4 : 0 ≤ e4) (h0d4 : 0 ≤ d4) (h0e6 : 0 ≤ e6) (h0d6 : 0 ≤ d6)
    (hκ : κ ≤ 1000203 / 1000000) (hL : L ≤ 12666 / 100 * g) (hε : ε ≤ 1421 / 100000)
    (hE : E ≤ 55) (hA : A ≤ 1776 / 100 * (g ^ 2) ^ 2) (hD : D ≤ 10567 / 1000 * g ^ 2)
    (he4 : e4 ≤ 1199 / 100 * g ^ 2) (hd4 : d4 ≤ 924 / 100 * g) (he6 : e6 ≤ 1449 / 100 * g ^ 2)
    (hd6 : d6 ≤ 1116 / 100 * g) :
    √(priceC κ n L ε E A D e4 d4 e6 d6) ≤ 887 / 10 ^ 6 := by
  have h1 := priceC_mono h0κ (Nat.cast_nonneg n) h0L h0ε h0E h0A h0D h0e4 h0d4 h0e6 h0d6 hκ hL hε
    hE hA hD he4 hd4 he6 hd6
  rw [priceC_scale hg hgn (by norm_num) (by norm_num)] at h1
  have hs : √((1776 / 100 : ℝ) * (10567 / 1000)) ≤ 1370 / 100 :=
    sqrt_le_of_sq (by norm_num) (by norm_num)
  have hs0 : 0 ≤ √((1776 / 100 : ℝ) * (10567 / 1000)) := Real.sqrt_nonneg _
  have hu : 0 ≤ g ^ 2 := sq_nonneg g
  have hg0' : g ^ 2 ≤ 2 / 23000 := hg0.trans (by norm_num)
  have hF : (1000203 / 1000000 : ℝ) * g ^ 2 * ((1776 / 100) ^ 2 / 2 + (1 + 1421 / 100000) *
        (1776 / 100) * (10567 / 1000)) +
      (1000203 / 1000000 * (1776 / 100 + 10567 / 1000 + 12666 / 100 *
        √((1776 / 100 : ℝ) * (10567 / 1000)) * g ^ 2)) ^ 2 / 2 +
      g ^ 2 * (1000203 / 1000000 * (1776 / 100 + 10567 / 1000 + 12666 / 100 *
        √((1776 / 100 : ℝ) * (10567 / 1000)) * g ^ 2)) *
        (1000203 / 1000000 * ((1199 / 100) ^ 2 + (924 / 100) ^ 2 + 12666 / 100 * (924 / 100) *
          (1199 / 100) * g ^ 2)) ^ 2 / 6 +
      (g ^ 2) ^ 2 * (1000203 / 1000000 * ((1199 / 100) ^ 2 + (924 / 100) ^ 2 + 12666 / 100 *
        (924 / 100) * (1199 / 100) * g ^ 2)) ^ 4 / 24 +
      (g ^ 2) ^ 3 * (1000203 / 1000000 * ((1199 / 100) ^ 2 + (924 / 100) ^ 2 + 12666 / 100 *
        (924 / 100) * (1199 / 100) * g ^ 2)) ^ 2 *
        (1000203 / 1000000 * ((1449 / 100) ^ 2 + (1116 / 100) ^ 2 + 12666 / 100 * (1116 / 100) *
          (1449 / 100) * g ^ 2)) ^ 3 / 120 +
      55 * (g ^ 2) ^ 4 * (1000203 / 1000000 * ((1449 / 100) ^ 2 + (1116 / 100) ^ 2 +
        12666 / 100 * (1116 / 100) * (1449 / 100) * g ^ 2)) ^ 6 / 720 ≤ 452 := by
    calc _ ≤ (1000203 / 1000000 : ℝ) * (2 / 23000) * ((1776 / 100) ^ 2 / 2 + (1 + 1421 / 100000) *
            (1776 / 100) * (10567 / 1000)) +
          (1000203 / 1000000 * (1776 / 100 + 10567 / 1000 + 12666 / 100 * (1370 / 100) *
            (2 / 23000))) ^ 2 / 2 +
          (2 / 23000) * (1000203 / 1000000 * (1776 / 100 + 10567 / 1000 + 12666 / 100 *
            (1370 / 100) * (2 / 23000))) *
            (1000203 / 1000000 * ((1199 / 100) ^ 2 + (924 / 100) ^ 2 + 12666 / 100 * (924 / 100) *
              (1199 / 100) * (2 / 23000))) ^ 2 / 6 +
          (2 / 23000) ^ 2 * (1000203 / 1000000 * ((1199 / 100) ^ 2 + (924 / 100) ^ 2 +
            12666 / 100 * (924 / 100) * (1199 / 100) * (2 / 23000))) ^ 4 / 24 +
          (2 / 23000) ^ 3 * (1000203 / 1000000 * ((1199 / 100) ^ 2 + (924 / 100) ^ 2 +
            12666 / 100 * (924 / 100) * (1199 / 100) * (2 / 23000))) ^ 2 *
            (1000203 / 1000000 * ((1449 / 100) ^ 2 + (1116 / 100) ^ 2 + 12666 / 100 *
              (1116 / 100) * (1449 / 100) * (2 / 23000))) ^ 3 / 120 +
          55 * (2 / 23000) ^ 4 * (1000203 / 1000000 * ((1449 / 100) ^ 2 + (1116 / 100) ^ 2 +
            12666 / 100 * (1116 / 100) * (1449 / 100) * (2 / 23000))) ^ 6 / 720 := by
          gcongr
      _ ≤ 452 := by norm_num
  have h2 : priceC κ n L ε E A D e4 d4 e6 d6 ≤ (g ^ 2) ^ 2 * 452 :=
    h1.trans (mul_le_mul_of_nonneg_left hF (by positivity))
  calc √(priceC κ n L ε E A D e4 d4 e6 d6) ≤ √((g ^ 2) ^ 2 * 452) := Real.sqrt_le_sqrt h2
    _ = g ^ 2 * √452 := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hu]
    _ ≤ (2 / 48000) * (2127 / 100) := by
        gcongr
        exact sqrt_le_of_sq (by norm_num) (by norm_num)
    _ ≤ 887 / 10 ^ 6 := by norm_num

lemma rc_B48 {tlq tsq βl : ℝ} (hg : 0 < g) (h0tlq : 0 ≤ tlq) (htlq : tlq ≤ 53493 / 10000 * g ^ 2)
    (h0tsq : 0 ≤ tsq) (htsq : tsq ≤ 42768 / 10000 * (g ^ 2 * g)) (h0β : 0 ≤ βl)
    (hβ : βl ≤ 112 / 10 ^ 13) :
    0 ≤ Bpap (22 * g ^ 2) (35 / 2 * (g ^ 2 * g)) tlq tsq βl (2 * 12) ∧
    Bpap (22 * g ^ 2) (35 / 2 * (g ^ 2 * g)) tlq tsq βl (2 * 12) ≤ 1121 / 10 ^ 14 := by
  unfold Bpap
  have hu : 0 < g ^ 2 := by positivity
  have h1 : tlq / (22 * g ^ 2) ≤ 53493 / 10000 / 22 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h2 : tsq / (35 / 2 * (g ^ 2 * g)) ≤ 42768 / 10000 / (35 / 2) := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [mul_pos hu hg]
  have h10 : 0 ≤ tlq / (22 * g ^ 2) := by positivity
  have h20 : 0 ≤ tsq / (35 / 2 * (g ^ 2 * g)) := by positivity
  refine ⟨by positivity, ?_⟩
  calc (tlq / (22 * g ^ 2)) ^ (2 * 12) + (tsq / (35 / 2 * (g ^ 2 * g))) ^ (2 * 12) + βl
      ≤ (53493 / 10000 / 22) ^ (2 * 12) + (42768 / 10000 / (35 / 2)) ^ (2 * 12) + 112 / 10 ^ 13 := by
        gcongr
    _ ≤ 1121 / 10 ^ 14 := by norm_num

lemma rc_R1_48 {B : ℝ} (h0B : 0 ≤ B) (hB : B ≤ 1121 / 10 ^ 14) :
    √(2 * (1 + (1 / 10000 : ℝ)⁻¹) * B) ≤ 474 / 10 ^ 6 := by
  apply sqrt_le_of_sq (by norm_num)
  calc 2 * (1 + (1 / 10000 : ℝ)⁻¹) * B ≤ 2 * (1 + (1 / 10000 : ℝ)⁻¹) * (1121 / 10 ^ 14) := by gcongr
    _ ≤ (474 / 10 ^ 6) ^ 2 := by norm_num

lemma rc_Dp48 {n : ℕ} {B CA Vl VS : ℝ} (hg : 0 < g) (hgn : (n : ℝ) * g ^ 2 = 2)
    (hg0 : g ^ 2 ≤ 2 / 48000) (hs : 43 / 100 ≤ s) (h0B : 0 ≤ B) (hB : B ≤ 1121 / 10 ^ 14)
    (h0CA : 0 ≤ CA) (hCA : CA ≤ 1532 / 1000) (h0Vl : 0 ≤ Vl)
    (hVl : Vl ≤ 127512 / 100000 * (g ^ 2) ^ 2)
    (h0VS : 0 ≤ VS) (hVS : VS ≤ 4247 / 10 * (g ^ 2) ^ 4) :
    √(Dpap n B CA Vl VS (1 / 10000) (g * s)) ≤ 659 / 10 ^ 6 := by
  unfold Dpap
  have hn' : (n : ℝ) = 2 / g ^ 2 := by field_simp; linarith
  have hsB : √B ≤ 3349 / 10 ^ 9 := (Real.sqrt_le_sqrt hB).trans
    (sqrt_le_of_sq (by norm_num) (by norm_num))
  have hsB0 : 0 ≤ √B := Real.sqrt_nonneg _
  have hu : 0 < g ^ 2 := by positivity
  have hT1 : CA * Vl / (2 * (1 - 1 / 10000) * (g * s) ^ 2) ≤
      1532 / 1000 * (127512 / 100000) / (2 * (1 - 1 / 10000) * (43 / 100) ^ 2) * g ^ 2 := by
    calc CA * Vl / (2 * (1 - 1 / 10000) * (g * s) ^ 2)
        ≤ 1532 / 1000 * (127512 / 100000 * (g ^ 2) ^ 2) /
          (2 * (1 - 1 / 10000) * (g * (43 / 100)) ^ 2) := by gcongr
      _ = _ := by field_simp
  have hT2 : (n : ℝ) * VS / (8 * (1 - 1 / 10000) ^ 2 * (g * s) ^ 4) ≤
      2 * (4247 / 10) / (8 * (1 - 1 / 10000) ^ 2 * (43 / 100) ^ 4) * g ^ 2 := by
    rw [hn']
    calc 2 / g ^ 2 * VS / (8 * (1 - 1 / 10000) ^ 2 * (g * s) ^ 4)
        ≤ 2 / g ^ 2 * (4247 / 10 * (g ^ 2) ^ 4) /
          (8 * (1 - 1 / 10000) ^ 2 * (g * (43 / 100)) ^ 4) := by gcongr
      _ = _ := by field_simp
  have hsum : CA * Vl / (2 * (1 - 1 / 10000) * (g * s) ^ 2) +
      (n : ℝ) * VS / (8 * (1 - 1 / 10000) ^ 2 * (g * s) ^ 4) ≤ 3112 * g ^ 2 := by
    have e : 1532 / 1000 * (127512 / 100000) / (2 * (1 - 1 / 10000) * (43 / 100) ^ 2) +
        2 * (4247 / 10) / (8 * (1 - 1 / 10000) ^ 2 * (43 / 100) ^ 4) ≤ (3112 : ℝ) := by norm_num
    nlinarith
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hS0 : 0 ≤ CA * Vl / (2 * (1 - 1 / 10000) * (g * s) ^ 2) +
      (n : ℝ) * VS / (8 * (1 - 1 / 10000) ^ 2 * (g * s) ^ 4) := by positivity
  apply sqrt_le_of_sq (by norm_num)
  calc √B * (CA * Vl / (2 * (1 - 1 / 10000) * (g * s) ^ 2) +
        (n : ℝ) * VS / (8 * (1 - 1 / 10000) ^ 2 * (g * s) ^ 4))
      ≤ 3349 / 10 ^ 9 * (3112 * (2 / 48000)) := by
        gcongr
        exact hsum.trans (by gcongr)
    _ ≤ (659 / 10 ^ 6) ^ 2 := by norm_num

theorem root_core48 {n : ℕ} (hg : 0 < g) (hgn : (n : ℝ) * g ^ 2 = 2) (hg0 : g ^ 2 ≤ 2 / 48000)
    (hs : 43 / 100 ≤ s) {CA Vs Vl VS ts8 ts12 tl8 tl12 tlq tsq βl : ℝ}
    (h0CA : 0 ≤ CA) (hCA : CA ≤ 1532 / 1000)
    (h0Vs : 0 ≤ Vs) (hVs : Vs ≤ 81508 / 100000 * (g ^ 2) ^ 3)
    (h0Vl : 0 ≤ Vl) (hVl : Vl ≤ 127512 / 100000 * (g ^ 2) ^ 2)
    (h0VS : 0 ≤ VS) (hVS : VS ≤ 4247 / 10 * (g ^ 2) ^ 4)
    (h0ts8 : 0 ≤ ts8) (hts8 : ts8 ≤ 25379 / 10000 * (g ^ 2 * g))
    (h0tl8 : 0 ≤ tl8) (htl8 : tl8 ≤ 31743 / 10000 * g ^ 2)
    (h0ts12 : 0 ≤ ts12) (hts12 : ts12 ≤ 30661 / 10000 * (g ^ 2 * g))
    (h0tl12 : 0 ≤ tl12) (htl12 : tl12 ≤ 38350 / 10000 * g ^ 2)
    (h0tlq : 0 ≤ tlq) (htlq : tlq ≤ 53493 / 10000 * g ^ 2)
    (h0tsq : 0 ≤ tsq) (htsq : tsq ≤ 42768 / 10000 * (g ^ 2 * g))
    (h0β : 0 ≤ βl) (hβ : βl ≤ 112 / 10 ^ 13) :
    rootE n (22 * g ^ 2) (35 / 2 * (g ^ 2 * g)) (1 / 10000) CA (g * s)
      Vs Vl VS ts8 ts12 tl8 tl12 tlq tsq βl ≤ 2159 / 10 ^ 6 := by
  have hg0' : g ^ 2 ≤ 2 / 23000 := hg0.trans (by norm_num)
  obtain ⟨-, hε0, hε1⟩ := rc_eps hg hg0' hs
  obtain ⟨hκd, hκ1⟩ := rc_kappa hε0 hε1
  have hκ0 := (inv_pos.2 hκd).le
  obtain ⟨hL0, hL1⟩ := rc_L hg hs h0CA hCA
  have hnε := rc_neps (n := n) hg hgn hg0' hs
  have hEE := rc_EE hg hg0' hκ0 hκ1 hε0 hε1 hnε hL0 hL1
  obtain ⟨hA0, hA⟩ := rc_A hg hg0' hs h0Vs hVs
  obtain ⟨hD0, hD⟩ := rc_D hg hs h0CA hCA h0Vl hVl
  obtain ⟨he40, he4⟩ := rc_e (p := 8) hg hg0' hs (by norm_num) h0ts8 hts8
  obtain ⟨he60, he6⟩ := rc_e (p := 12) hg hg0' hs (by norm_num) h0ts12 hts12
  obtain ⟨hd40, hd4⟩ := rc_d (p := 8) hg hs h0CA hCA (by norm_num) h0tl8 htl8
  obtain ⟨hd60, hd6⟩ := rc_d (p := 12) hg hs h0CA hCA (by norm_num) h0tl12 htl12
  have hP := rc_price48 (n := n) hg hgn hg0 hκ0 hL0 hε0 (exp_pos _).le hA0 hD0 he40 hd40 he60 hd60
    hκ1 hL1 hε1 hEE hA hD (he4.trans (by gcongr; norm_num)) (hd4.trans (by gcongr; norm_num))
    (he6.trans (by gcongr; norm_num)) (hd6.trans (by gcongr; norm_num))
  obtain ⟨hB0, hB⟩ := rc_B48 hg h0tlq htlq h0tsq htsq h0β hβ
  have hR1 := rc_R1_48 hB0 hB
  have hR3 := rc_Dp48 (n := n) hg hgn hg0 hs hB0 hB h0CA hCA h0Vl hVl h0VS hVS
  unfold rootE
  linarith

end core2

variable {n : ℕ}

theorem rootFL_fixed48 (hn : 48000 ≤ n) {sd : ℝ} (hsd : 43 / 100 ≤ sd)
    (hβ : betaMW48 n sd ≤ 112 / 10 ^ 13) (D : Design n) (c : Ret n)
    (hCL : (0 : ℝ) < 51 / 10) (hCS : (0 : ℝ) < 326 / 100 * (2 / n))
    (hL12 : ∫ a, ∫ v, psiA (lamX D c) D c a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (51 / 10 / n) ^ 12)
    (hS12 : ∫ a, ∫ v, psiA (sigX D c) D c a v ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      (326 / 100 * (2 / n) / n) ^ 12)
    (hE8 : ∫ a, ∫ v, sgA D c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ E0 n ^ 8)
    (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA D c a v < √(2 / (n : ℝ)) * sd}
      ∂muI n ≤ betaMW48 n sd) :
    rootFL (22 * √(2 / (n : ℝ)) ^ 2) (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (1 / 10000)
      (CAn n) (latMomOfPsi12e (by omega) D c hCL hCS (E0_nonneg n) (betaMW48_nonneg n sd)
        hL12 hS12 hE8 hmass) ≤ 2159 / 10 ^ 6 := by
  have hnR : (48000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set g := √(2 / (n : ℝ)) with hgdef
  have hg2 : g ^ 2 = 2 / n := Real.sq_sqrt (by positivity)
  have hg : 0 < g := Real.sqrt_pos.mpr (by positivity)
  have hgn : (n : ℝ) * g ^ 2 = 2 := by rw [hg2]; field_simp
  have hg0 : g ^ 2 ≤ 2 / 48000 := by
    rw [hg2]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hnR
  set P := latMomOfPsi12e (by omega) D c hCL hCS (E0_nonneg n) (betaMW48_nonneg n sd)
    hL12 hS12 hE8 hmass with hP
  -- the two square roots
  have hCSn : √(326 / 100 * (2 / (n : ℝ)) / n) = √(163 / 100) * g ^ 2 := by
    rw [hg2, show 326 / 100 * (2 / (n : ℝ)) / n = 163 / 100 * (2 / n) ^ 2 by ring,
      Real.sqrt_mul (by norm_num), Real.sqrt_sq (by positivity)]
  have hCLn : √(51 / 10 / (n : ℝ)) = √(255 / 100) * g := by
    rw [hgdef, ← Real.sqrt_mul (by norm_num)]; congr 1; ring
  have hs1 : √(163 / 100 : ℝ) ≤ 1276715 / 1000000 := sqrt_le_of_sq (by norm_num) (by norm_num)
  have hs2 : √(255 / 100 : ℝ) ≤ 1596872 / 1000000 := sqrt_le_of_sq (by norm_num) (by norm_num)
  have hs10 : 0 ≤ √(163 / 100 : ℝ) := Real.sqrt_nonneg _
  have hs20 : 0 ≤ √(255 / 100 : ℝ) := Real.sqrt_nonneg _
  -- the factors `kLSs`
  have hk4 : kLSs n 4 ≤ 198779 / 100000 * g :=
    kLSs_le (by omega) (by norm_num) cLS4_le (by norm_num) (by norm_num)
  have hk6 : kLSs n 6 ≤ 240152 / 100000 * g :=
    kLSs_le (by omega) (by norm_num) cLS6_le (by norm_num) (by norm_num)
  have hk12 : kLSs n 12 ≤ 334984 / 100000 * g :=
    kLSs_le (by omega) (by norm_num) cLS12_le (by norm_num) (by norm_num)
  have hk40 : 0 ≤ kLSs n 4 := (BstLean.Part162.kLSs_pos' (by omega) (by norm_num) (by norm_num)).le
  have hk60 : 0 ≤ kLSs n 6 := (BstLean.Part162.kLSs_pos' (by omega) (by norm_num) (by norm_num)).le
  have hk120 : 0 ≤ kLSs n 12 :=
    (BstLean.Part162.kLSs_pos' (by omega) (by norm_num) (by norm_num)).le
  have hu : 0 ≤ g ^ 2 := sq_nonneg g
  -- the fields
  have fS : ∀ {k K : ℝ}, 0 ≤ k → k ≤ K * g → ∀ {M : ℝ}, K * (1276715 / 1000000) ≤ M →
      k * √(326 / 100 * (2 / (n : ℝ)) / n) ≤ M * (g ^ 2 * g) := by
    intro k K hk0 hk M hM
    rw [hCSn]
    have hK0 : 0 ≤ K := by
      by_contra h
      have : K * g < 0 := mul_neg_of_neg_of_pos (not_le.mp h) hg
      linarith
    calc k * (√(163 / 100) * g ^ 2) ≤ (K * g) * (1276715 / 1000000 * g ^ 2) := by gcongr
      _ = K * (1276715 / 1000000) * (g ^ 2 * g) := by ring
      _ ≤ M * (g ^ 2 * g) := by gcongr
  have fL : ∀ {k K : ℝ}, 0 ≤ k → k ≤ K * g → ∀ {M : ℝ}, K * (1596872 / 1000000) ≤ M →
      k * √(51 / 10 / (n : ℝ)) ≤ M * g ^ 2 := by
    intro k K hk0 hk M hM
    rw [hCLn]
    have hK0 : 0 ≤ K := by
      by_contra h
      have : K * g < 0 := mul_neg_of_neg_of_pos (not_le.mp h) hg
      linarith
    calc k * (√(255 / 100) * g) ≤ (K * g) * (1596872 / 1000000 * g) := by gcongr
      _ = K * (1596872 / 1000000) * g ^ 2 := by ring
      _ ≤ M * g ^ 2 := by gcongr
  have hts8 : P.ts8 ≤ 25379 / 10000 * (g ^ 2 * g) := fS hk40 hk4 (by norm_num)
  have hts12 : P.ts12 ≤ 30661 / 10000 * (g ^ 2 * g) := fS hk60 hk6 (by norm_num)
  have htsq : P.tsq ≤ 42768 / 10000 * (g ^ 2 * g) := fS hk120 hk12 (by norm_num)
  have htl8 : P.tl8 ≤ 31743 / 10000 * g ^ 2 := fL hk40 hk4 (by norm_num)
  have htl12 : P.tl12 ≤ 38350 / 10000 * g ^ 2 := fL hk60 hk6 (by norm_num)
  have htlq : P.tlq ≤ 53493 / 10000 * g ^ 2 := fL hk120 hk12 (by norm_num)
  have hVs : P.Vs ≤ 81508 / 100000 * (g ^ 2) ^ 3 := by
    change 326 / 100 * (2 / (n : ℝ)) / n / ((n : ℝ) - 2) ≤ _
    rw [hg2]
    have hd : (0 : ℝ) < n - 2 := by linarith
    rw [div_le_iff₀ hd]
    have e : 81508 / 100000 * (2 / (n : ℝ)) ^ 3 * (n - 2) = 652064 / 100000 * (n - 2) / n ^ 3 := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have e2 : 326 / 100 * (2 / (n : ℝ)) / n * n ^ 3 = 652 / 100 * n := by field_simp; ring
    rw [e2]
    nlinarith
  have hVl : P.Vl ≤ 127512 / 100000 * (g ^ 2) ^ 2 := by
    change 51 / 10 / (n : ℝ) / ((n : ℝ) - 2) ≤ _
    rw [hg2]
    have hd : (0 : ℝ) < n - 2 := by linarith
    rw [div_le_iff₀ hd]
    have e : 127512 / 100000 * (2 / (n : ℝ)) ^ 2 * (n - 2) = 510048 / 100000 * (n - 2) / n ^ 2 := by
      field_simp; ring
    rw [e, le_div_iff₀ (by positivity)]
    have e2 : 51 / 10 / (n : ℝ) * n ^ 2 = 51 / 10 * n := by field_simp
    rw [e2]
    nlinarith
  have hVS : P.VS ≤ 4247 / 10 * (g ^ 2) ^ 4 := by
    change 4 * (kLSs n 4 * √(326 / 100 * (2 / (n : ℝ)) / n)) ^ 2 * E0 n ^ 2 ≤ _
    have h1 := fS hk40 hk4 (M := 25379 / 10000) (by norm_num)
    have h10 : 0 ≤ kLSs n 4 * √(326 / 100 * (2 / (n : ℝ)) / n) := by positivity
    have h2 := E0_le (by omega : 23000 ≤ n)
    rw [← hgdef] at h2
    calc 4 * (kLSs n 4 * √(326 / 100 * (2 / (n : ℝ)) / n)) ^ 2 * E0 n ^ 2
        ≤ 4 * (25379 / 10000 * (g ^ 2 * g)) ^ 2 * (406 / 100 * g) ^ 2 := by
          gcongr
          exact E0_nonneg n
      _ = 4 * (25379 / 10000) ^ 2 * (406 / 100) ^ 2 * (g ^ 2) ^ 4 := by ring
      _ ≤ 4247 / 10 * (g ^ 2) ^ 4 := by gcongr; norm_num
  have hβ' : P.βlow ≤ 112 / 10 ^ 13 := hβ
  have hCA := CAn_le (by omega : 23000 ≤ n)
  have hCA0 : 0 ≤ CAn n := by unfold CAn BstLean.Part164.chiUp; positivity
  exact root_core48 hg hgn hg0 hsd hCA0 hCA P.hVs0 hVs P.hVl0 hVl P.hVS0 hVS P.hts8.le hts8 P.htl8.le
    htl8 P.hts12.le hts12 P.htl12.le htl12 P.htlq htlq P.htsq htsq P.hβl hβ'

theorem classifier_paper_root_gen48 (hn : 48000 ≤ n) {sd : ℝ} (hsd : 43 / 100 ≤ sd)
    (hsd' : sd < BstLean.Part175.s0W) (hβ : betaMW48 n sd ≤ 112 / 10 ^ 13) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomC - 5 / 100000)
    (hM : ∀ c ∈ goodC n (paperDesign n fT wT hf hw)
        (EA ∩ agentEv (paperDesign n fT wT hf hw) (SXM48 n)),
      (∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (51 / 10 / n) ^ 12) ∧
      (∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (326 / 100 * (2 / n) / n) ^ 12) ∧
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * sd)
          (1 / 10000) (by norm_num) (by norm_num)) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  have hnR : (48000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hsd0 : 0 < sd := lt_of_lt_of_le (by norm_num) hsd
  refine classifier_paper_free23_massW48 (by omega) fT wT hf hw t hEA hA hroom fun c hc => ?_
  obtain ⟨hL12, hS12, hbias⟩ := hM c hc
  have hCS : (0 : ℝ) < 326 / 100 * (2 / n) := by positivity
  refine ⟨22 * √(2 / (n : ℝ)) ^ 2, 35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ))), sd,
    1 / 10000, 51 / 10, 326 / 100 * (2 / n), by norm_num, by norm_num, by norm_num, hCS,
    hsd0, hsd', hL12, hS12, by positivity, by positivity, eps0_fixed_lt (by omega) hsd, ?_, hbias⟩
  exact rootFL_fixed48 hn hsd hβ _ c (by norm_num) hCS hL12 hS12 _ _

theorem betaMP_4691_48 (hn : 48000 ≤ n) : betaMW48 n (4691 / 10000) ≤ 112 / 10 ^ 13 := by
  have hnR : (48000 : ℝ) ≤ n := by exact_mod_cast hn
  unfold betaMW48 BstLean.Part175.s0W
  rw [gmom_40]
  have h1 : (π / 2) ^ 40 ≤ (15708 / 10000 : ℝ) ^ 40 := pow_le_pow_left₀ (by positivity) pi_half_le 40
  have h2 : 6032 / 10000 / ((n : ℝ) * (5096 / 10000 - 4691 / 10000) ^ 2) ≤
      6032 / 10000 / ((48000 : ℝ) * (5096 / 10000 - 4691 / 10000) ^ 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right hnR (by norm_num))
  have h3 := pow_le_pow_left₀ (by positivity) h2 20
  calc (π / 2) ^ 40 * 319830986772877770815625 *
        (6032 / 10000 / ((n : ℝ) * (5096 / 10000 - 4691 / 10000) ^ 2)) ^ 20
      ≤ (15708 / 10000 : ℝ) ^ 40 * 319830986772877770815625 *
        (6032 / 10000 / ((48000 : ℝ) * (5096 / 10000 - 4691 / 10000) ^ 2)) ^ 20 :=
        mul_le_mul (mul_le_mul_of_nonneg_right h1 (by norm_num)) h3 (by positivity)
          (by positivity)
    _ ≤ 112 / 10 ^ 13 := by norm_num

theorem classifier_paper_root48k (hn : 48000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomC - 5 / 100000)
    (hM : ∀ c ∈ goodC n (paperDesign n fT wT hf hw)
        (EA ∩ agentEv (paperDesign n fT wT hf hw) (SXM48 n)),
      (∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (51 / 10 / n) ^ 12) ∧
      (∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (326 / 100 * (2 / n) / n) ^ 12) ∧
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (4691 / 10000))
          (1 / 10000) (by norm_num) (by norm_num)) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_root_gen48 hn (by norm_num) (by unfold BstLean.Part175.s0W; norm_num)
    (betaMP_4691_48 hn) fT wT hf hw t hEA hA hroom hM


end SRoot

end BstLean.Part175.N48
