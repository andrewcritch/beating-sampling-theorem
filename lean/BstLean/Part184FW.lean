import BstLean.Part181Jen
import BstLean.Part182Ew
import BstLean.Part183D19
import BstLean.Part184Def

/-!
# Part 184 (file `FW`): `W₂₀`, Lemma PP at order 800 and the event `SXM185` at `n ≥ 18 500`
(copy of Part 182 `W21`)

No proof is left open; no `native_decide` or `axiom` is used. Constants (single-process python;
Lean checks every inequality):
* `W20_le_F185`: `E[(τ²/|y|²)²⁰] ≤ (1.0198·θ/n)²⁰` for `n ≥ 18 500`, `0.46 ≤ θ ≤ 0.528` (levels
  `ε_k = 0.0048·min(k, 10)`).
* `SXM185 n = {X₂₀ ≤ (1.111·n)²⁰·W₂₀}`; `jS(n, 800, 0.0049) ≤ 1.04704`, `jS²/1.111 ≤ 0.98760`,
  charge `≤ 5·10⁻⁵`.
* `Xi4_SXM185`, `Xi8_SXM185`, `XiS_SXM185`: `Ξ, Ξ₄, Ξ₈ ≤ 1.111·1.0198·θh·γ_A/n` on `SXM185`.
Docstrings of copied lemmas can carry older numbers; the Lean statements are authoritative.
-/

namespace BstLean.Part183.F185
open BstLean.Part182

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part160 (WqN)
open BstLean.Part176 (fL fL_mono fL_eq WqN_le_layer exp_neg_quart')

variable {n : ℕ}

/-- The levels `ε_k = 0.0036·min(k, 10)`. -/
noncomputable def epsF185 (k : ℕ) : ℝ := 48 / 10000 * ((min k 10 : ℕ) : ℝ)

lemma epsF185_mono (k : ℕ) : epsF185 k ≤ epsF185 (k + 1) := by
  unfold epsF185
  have : ((min k 10 : ℕ) : ℝ) ≤ ((min (k + 1) 10 : ℕ) : ℝ) := by
    exact_mod_cast min_le_min_right 10 (Nat.le_succ k)
  linarith

lemma epsF185_lt (k : ℕ) : epsF185 k < 1 := by
  unfold epsF185
  have : ((min k 10 : ℕ) : ℝ) ≤ 10 := by exact_mod_cast min_le_right k 10
  linarith

/-- `C(e) = ((1 − e)²)^{−20}`. -/
lemma fL_eqF185 {τ Q e : ℝ} (hQ : 0 < Q) (he : e < 1) :
    fL 20 τ Q e = (τ ^ 2 / Q) ^ 20 * (1 / ((1 - e) ^ 2) ^ 20) := by
  unfold fL
  have h1 : 0 < 1 - e := by linarith
  have : (1 - e) ^ 2 ≠ 0 := by positivity
  rw [show (1 : ℝ) / ((1 - e) ^ 2) ^ 20 = (1 / (1 - e) ^ 2) ^ 20 by rw [div_pow, one_pow],
    ← mul_pow]
  congr 1
  field_simp


/-- `C(e) = ((1 − e)²)^{−20}`. -/
noncomputable def CF185 (e : ℝ) : ℝ := 1 / ((1 - e) ^ 2) ^ 20

/-- The tail bound `P(e) = (1 + x/4 + (x/4)²/2)^{−4}` at `x = 32 196·e²`. -/
noncomputable def PF185 (e : ℝ) : ℝ := 1 / (1 + e ^ 2 * 17518 / 4 + (e ^ 2 * 17518 / 4) ^ 2 / 2) ^ 4

lemma sumF185_le : ∑ k ∈ Finset.range 10, (CF185 (epsF185 (k + 1)) - CF185 (epsF185 k)) * PF185 (epsF185 k) ≤
    4657 / 10000 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, epsF185, CF185, PF185]
  norm_num


open BstLean.Part150 (thetaC rhoC) in
/-- **`E[(τ²/|y|²)²⁰] ≤ (1.0146·θ/n)²⁰`** for `n ≥ 34 000`, `0.46 ≤ θ ≤ 0.528` (the layered bound
with the ten levels `ε_k = 0.0036k`). -/
theorem W20_le_F185 (hn : 18500 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000) :
    WqN 20 c τ ≤ (10198 / 10000 * (thetaC c τ / n)) ^ 20 := by
  have hnR : (18500 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := WqN_le_layer (q := 20) (by omega) c hτ epsF185 10 (by unfold epsF185; norm_num)
    epsF185_mono epsF185_lt
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
  rw [show normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2 = R - T by rw [hR, hT]] at h
  rw [← hT] at h
  have hT45 : 18500 * T ≤ 528 / 1000 * R := by nlinarith
  have hQ0 : 0 < R - T := by nlinarith
  set w := T / (R - T) with hw
  have hw0 : 0 < w := div_pos hT0 hQ0
  -- `Q/(2T) ≥ 42 613`
  have hlam : 17518 ≤ (R - T) / (2 * T) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hE : ∀ k, exp (-(epsF185 k ^ 2 * (R - T)) / (2 * T)) ≤ PF185 (epsF185 k) := by
    intro k
    rw [neg_div]
    refine exp_neg_quart' (by positivity) ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hlam (sq_nonneg _)
  have hfL : ∀ k, fL 20 τ (R - T) (epsF185 k) = w ^ 20 * CF185 (epsF185 k) := fun k => by
    rw [fL_eqF185 hQ0 (epsF185_lt k), CF185, hw, ← hT]
  have hsum : ∑ k ∈ Finset.range 10, (fL 20 τ (R - T) (epsF185 (k + 1)) - fL 20 τ (R - T) (epsF185 k)) *
      exp (-(epsF185 k ^ 2 * (R - T)) / (2 * T)) ≤ w ^ 20 * (4657 / 10000) := by
    calc _ ≤ ∑ k ∈ Finset.range 10, (fL 20 τ (R - T) (epsF185 (k + 1)) - fL 20 τ (R - T) (epsF185 k)) *
          PF185 (epsF185 k) := Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (hE k)
              (by linarith [fL_mono (q := 20) (τ := τ) hQ0 (epsF185_mono k) (epsF185_lt (k + 1))])
      _ = w ^ 20 * ∑ k ∈ Finset.range 10, (CF185 (epsF185 (k + 1)) - CF185 (epsF185 k)) * PF185 (epsF185 k) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hfL, hfL]; ring
      _ ≤ w ^ 20 * (4657 / 10000) := mul_le_mul_of_nonneg_left sumF185_le (by positivity)
  have h0 : fL 20 τ (R - T) (epsF185 0) = w ^ 20 := by
    rw [hfL]; unfold CF185 epsF185; norm_num
  -- the tail
  have he10 : epsF185 10 = 48 / 1000 := by unfold epsF185; norm_num
  have htl : √(exp (-(epsF185 10 ^ 2 * (R - T)) / (2 * T))) ≤ (36788 / 100000) ^ 20 := by
    have h40 : exp (-(epsF185 10 ^ 2 * (R - T)) / (2 * T)) ≤ exp (-1) ^ 40 := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      rw [he10, neg_div, mul_div_assoc]
      have : (40 : ℝ) ≤ (48 / 1000) ^ 2 * ((R - T) / (2 * T)) := by nlinarith
      push_cast; linarith
    have h1 : exp (-1) ≤ 36788 / 100000 := by
      have := Real.exp_neg_one_lt_d9; norm_num at this ⊢; linarith
    have h2 : exp (-1) ^ 40 ≤ ((36788 / 100000 : ℝ) ^ 20) ^ 2 := by
      rw [← pow_mul]; exact pow_le_pow_left₀ (exp_pos _).le h1 _
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ (36788 / 100000) ^ 20 by positivity)]
    exact Real.sqrt_le_sqrt (h40.trans h2)
  have hd0 : (0 : ℝ) < (n : ℝ) - 1 - 4 * (20 : ℕ) := by push_cast; linarith
  have hinv : ((n : ℝ) - 1 - 4 * (20 : ℕ))⁻¹ ≤ 21900 / 10000 * w := by
    have hTR : 46 / 100 / (n : ℝ) ≤ w := by
      rw [hw, div_le_div_iff₀ hn0 hQ0]; nlinarith
    have h4 : ((n : ℝ) - 1 - 4 * (20 : ℕ))⁻¹ ≤ 21900 / 10000 * (46 / 100 / (n : ℝ)) := by
      rw [inv_eq_one_div, mul_div_assoc', div_le_div_iff₀ hd0 hn0]
      push_cast
      nlinarith
    exact h4.trans (mul_le_mul_of_nonneg_left hTR (by norm_num))
  have h2' := pow_le_pow_left₀ (inv_nonneg.mpr hd0.le) hinv 20
  have htail : √(exp (-(epsF185 10 ^ 2 * (R - T)) / (2 * T))) * (((n : ℝ) - 1 - 4 * (20 : ℕ))⁻¹) ^ 20 ≤
      (36788 / 100000 : ℝ) ^ 20 * (21900 / 10000 * w) ^ 20 :=
    mul_le_mul htl h2' (by positivity) (by positivity)
  -- `w ≤ 1.0000118·T/R`
  have hwu : w ≤ 1000029 / 1000000 * (T / R) := by
    rw [hw, div_le_iff₀ hQ0]
    have e : 1000029 / 1000000 * (T / R) * (R - T) = T * (1000029 / 1000000 * (1 - T / R)) := by
      field_simp
    rw [e]
    have hTR : T / R ≤ 528 / 1000 / 18500 := by
      rw [div_le_iff₀ hR0]; nlinarith
    have : 1 ≤ 1000029 / 1000000 * (1 - T / R) := by nlinarith
    nlinarith
  have hfin : w ^ 20 + w ^ 20 * (4657 / 10000) + (36788 / 100000 : ℝ) ^ 20 * (21900 / 10000 * w) ^ 20 ≤
      w ^ 20 * (14791 / 10000) := by
    have e : (36788 / 100000 : ℝ) ^ 20 * (21900 / 10000 * w) ^ 20 =
        ((36788 / 100000 : ℝ) ^ 20 * (21900 / 10000) ^ 20) * w ^ 20 := by ring
    rw [e]
    have : (36788 / 100000 : ℝ) ^ 20 * (21900 / 10000) ^ 20 ≤ 134 / 10000 := by norm_num
    nlinarith [pow_pos hw0 20]
  have hwf : w ^ 20 * (14791 / 10000) ≤ (10198 / 10000 * ((n : ℝ) * T / R / n)) ^ 20 := by
    have e : (n : ℝ) * T / R / n = T / R := by field_simp
    rw [e]
    have h1 : w ^ 20 ≤ (1000029 / 1000000 * (T / R)) ^ 20 := pow_le_pow_left₀ hw0.le hwu 20
    have hu0 : 0 ≤ T / R := by positivity
    calc w ^ 20 * (14791 / 10000) ≤ (1000029 / 1000000 * (T / R)) ^ 20 * (14791 / 10000) :=
          mul_le_mul_of_nonneg_right h1 (by norm_num)
      _ = ((1000029 / 1000000) ^ 20 * (14791 / 10000)) * (T / R) ^ 20 := by ring
      _ ≤ (10198 / 10000) ^ 20 * (T / R) ^ 20 :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (10198 / 10000 * (T / R)) ^ 20 := by ring
  rw [h0] at h
  push_cast at h htail
  linarith


section SXM
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160
open BstLean.Part153 (XiS Xi4 N2 hid2Mean_cr nuA jS)

/-! ## The event `SXM185` with the sharper Lemma PP constant -/

/-- **The event of the gradient moment of order 40 with `M = 1.0670`** (`n ≥ 40 000`): `X₂₀ ≤ (1.0670·n)²⁰·W₂₀`. -/
def SXM185 (n : ℕ) : Set (AgFam n) :=
  {x | XqN 20 x.2.1 x.2.2 x.1.1 x.1.2 ≤ (1111 / 1000 * (n : ℝ)) ^ 20 * WqN 20 x.1.1 x.1.2}

theorem measurableSet_SXM185 (n : ℕ) : MeasurableSet (SXM185 n) :=
  measurableSet_le (measurable_XqN_fam 20) ((measurable_WqN_fam 20).const_mul _)

/-- `𝔪₈₀₀ ≤ 24.33`: `2⁸⁰⁰·800! ≤ 24.33¹⁶⁰⁰`. -/
lemma gaussMomConst_800_leF185 : BstLean.Part152.gaussMomConst 800 ≤ 2433 / 100 := by
  have hp := BstLean.Part152.gaussMomConst_pow (P := 800) (by norm_num)
  have hN : (2 ^ 200) ^ 4 * Nat.factorial 800 * (100 ^ 200) ^ 8 ≤ (2433 ^ 200) ^ 8 := by
    norm_num [Nat.factorial]
  have h1 : BstLean.Part152.gaussMomConst 800 ^ (2 * 800) ≤ (2433 / 100 : ℝ) ^ (2 * 800) := by
    rw [hp]
    have e1 : (2 : ℝ) ^ 800 = (2 ^ 200) ^ 4 := by rw [← pow_mul]
    have e2 : (2433 / 100 : ℝ) ^ (2 * 800) = ((2433 : ℝ) ^ 200) ^ 8 / ((100 : ℝ) ^ 200) ^ 8 := by
      rw [div_pow, ← pow_mul, ← pow_mul]
    rw [e1, e2, le_div_iff₀ (by positivity)]
    exact_mod_cast hN
  by_contra hlt
  have := pow_lt_pow_left₀ (not_le.mp hlt) (by norm_num : (0 : ℝ) ≤ 2433 / 100)
    (by norm_num : (2 * 800 : ℕ) ≠ 0)
  exact absurd h1 (not_le.mpr this)

lemma sqrt_eta_leF185 : √(1 + 2 * (49 / 10000) : ℝ) ≤ 10049 / 10000 := by
  rw [Real.sqrt_le_iff]
  constructor <;> norm_num

lemma epsS_800_leF185 {n : ℕ} (hn : 18500 ≤ n) :
    BstLean.Part153.epsS n 800 (49 / 10000) ≤ 46 / 10 ^ 6 := by
  have hnr : (18500 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : exp (-1) ≤ 36788 / 100000 := by
    have := Real.exp_neg_one_lt_d9; norm_num at this ⊢; linarith
  have h10 : exp (-10) ≤ 46 / 10 ^ 6 := by
    have e : exp (-10) = exp (-1) ^ 10 := by rw [← Real.exp_nat_mul]; norm_num
    rw [e]
    calc exp (-1) ^ 10 ≤ (36788 / 100000 : ℝ) ^ 10 := pow_le_pow_left₀ (exp_pos _).le h1 10
      _ ≤ 46 / 10 ^ 6 := by norm_num
  refine le_trans ?_ h10
  unfold BstLean.Part153.epsS
  rw [show ((800 : ℕ) : ℝ) = 800 by norm_num]
  refine Real.exp_le_exp.2 ?_
  have : (18500 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnr 2
  have h12 : (10 : ℝ) ≤ (49 / 10000) ^ 2 * (n : ℝ) ^ 2 / 800 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  linarith

/-- `jS n 800 (2/1000) ≤ 1.02654` for `n ≥ 40 000`. -/
lemma jS_800_le_18500 (hn : 18500 ≤ n) : jS n 800 (49 / 10000) ≤ 104704 / 100000 := by
  have hnr : (18500 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : (136 : ℝ) ≤ √(n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hg0 := BstLean.Part152.gaussMomConst_nonneg 800
  have hg := gaussMomConst_800_leF185
  have hu : 1 / √(n : ℝ) ≤ 1 / (136) := one_div_le_one_div_of_le (by norm_num) hs
  have hw : BstLean.Part152.gaussMomConst 800 / (n : ℝ) ≤ (2433 / 100) / 18500 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    nlinarith
  have hgu : BstLean.Part152.gaussMomConst 800 / √(n : ℝ) ≤ (2433 / 100) / (136) := by
    rw [div_le_div_iff₀ hs0 (by norm_num)]
    nlinarith
  refine (BstLean.Part153.jS_le_atoms n 800 (49 / 10000) BstLean.Part153.sqrt_two_le
    sqrt_eta_leF185 hu hw hgu (epsS_800_leF185 hn)).trans ?_
  norm_num

lemma pow_98760_leF185 : (98760 / 100000 : ℝ) ^ 800 ≤ 5 / 100000 := by
  have : (98760 / 100000 : ℝ) ^ 800 = ((98760 / 100000 : ℝ) ^ 100) ^ 8 := by rw [← pow_mul]
  rw [this]
  norm_num

/-- **The charge of `SXM185 n`**: at most `5·10⁻⁵` (`n ≥ 40 000`, `τ > 0`; Markov over the
weights at order `1600`: `q = 20`, `P' = 40`, Lemma PP with `P = 800`, `η = 0.002`). -/
theorem SXM185_charge (hn : 18500 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SXM185 n} ≤ 5 / 100000 := by
  have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      ((c, τ), θ) ∉ SXM185 n} =
      {θ | (1111 / 1000 * (n : ℝ)) ^ 20 * WqN 20 c τ < XqN 20 θ.1 θ.2 c τ} := by
    ext θ
    change ¬ (XqN 20 θ.1 θ.2 c τ ≤ (1111 / 1000 * (n : ℝ)) ^ 20 * WqN 20 c τ) ↔ _
    exact not_le
  rw [e]
  have h := markov_XqN (n := n) (q := 20) (P' := 40) (by norm_num) (by omega) c hτ
    (BstLean.Part153.jS_nonneg n 800 (49 / 10000))
    (fun _ hx => by
      exact BstLean.Part153.lemmaPP_i_sharp (by omega) (by norm_num)
        (by norm_num : (0 : ℝ) ≤ 49 / 10000) hx) (M := 1111 / 1000) (by norm_num)
  refine h.trans ?_
  have hj0 := BstLean.Part153.jS_nonneg n 800 (49 / 10000)
  have hj := jS_800_le_18500 hn
  have hj2 : jS n 800 (49 / 10000) ^ 2 ≤ (104704 / 100000 : ℝ) ^ 2 := pow_le_pow_left₀ hj0 hj 2
  have hratio : jS n 800 (49 / 10000) ^ 2 / (1111 / 1000) ≤ 98760 / 100000 := by
    rw [div_le_iff₀ (by norm_num)]
    refine hj2.trans (by norm_num)
  exact (pow_le_pow_left₀ (by positivity) hratio (20 * 40)).trans pow_98760_leF185

theorem SXM185_ret_charge (hn : 18500 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real (agentEv (paperDesign n fT wT hf hw) (SXM185 n))ᶜ ≤
      5 / 100000 := by
  rw [agentEv_compl]
  exact retDist_agent_charge (paperDesign n fT wT hf hw) (paperDesign_tauWorld fT wT hf hw)
    (measurableSet_SXM185 n) (by norm_num) (fun c τ hτ => SXM185_charge hn c τ hτ)

/-- **The gradient moment of order 40 on `SXM185` in the window `θ ≤ 0.528`**:
`t_A²⁰·X₂₀ ≤ (0.5737·γ_A/n)²⁰` (`1.067·1.013·0.528 ≤ 0.5737`), for `n ≥ 40 000`. -/
theorem tX20_le_WF185 (hn : 18500 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXM185 n) :
    (2 / (mA n : ℝ)) ^ 20 * XqN 20 A₁ A₂ c τ ≤ (5983 / 10000 * (2 / (n : ℝ)) / n) ^ 20 := by
  have hnR : (18500 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have h1 : XqN 20 A₁ A₂ c τ ≤ (1111 / 1000 * (n : ℝ)) ^ 20 * WqN 20 c τ := h
  have h2 := W20_le_F185 hn c hτ hθ0 hθ1
  have hθn : (0 : ℝ) ≤ thetaC c τ := by linarith
  have h3 : XqN 20 A₁ A₂ c τ ≤ (1111 / 1000 * (10198 / 10000) * thetaC c τ) ^ 20 := by
    refine h1.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq ?_))
    rw [← mul_pow]; congr 1; field_simp
  have hB : 1111 / 1000 * (10198 / 10000) * thetaC c τ ≤ 5983 / 10000 := by nlinarith
  have h4 := pow_le_pow_left₀ (by positivity) hB 20
  rw [hmA]
  calc (2 / (n : ℝ) ^ 2) ^ 20 * XqN 20 A₁ A₂ c τ ≤ (2 / (n : ℝ) ^ 2) ^ 20 * (5983 / 10000) ^ 20 :=
        mul_le_mul_of_nonneg_left (h3.trans h4) (by positivity)
    _ = (5983 / 10000 * (2 / (n : ℝ)) / n) ^ 20 := by rw [← mul_pow]; congr 1; field_simp



end SXM


open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160
open BstLean.Part181 (xq_pt integrable_xq Xq_le_of_X20)
open BstLean.Part153 (XiS Xi4 jacT)
open BstLean.Part152 (opN opN_nonneg)


/-- On `SXM185` in the window `0.46 ≤ θ_in ≤ 0.528`: `X₂₀ ≤ (1.1·1.0182·θ_in)²⁰`. -/
lemma X20_SXM185 (hn : 18500 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXM185 n) :
    XqN 20 A₁ A₂ c τ ≤ (1111 / 1000 * (10198 / 10000) * thetaC c τ) ^ 20 := by
  have hn0 : (0 : ℝ) < n := by
    have : (18500 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h1 : XqN 20 A₁ A₂ c τ ≤ (1111 / 1000 * (n : ℝ)) ^ 20 * WqN 20 c τ := h
  have h2 := W20_le_F185 hn c hτ hθ0 hθ1
  refine h1.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq ?_))
  rw [← mul_pow]; congr 1; field_simp

/-- **`Ξ₄ ≤ 1.1·1.0182·θh·γ_A/n` on `SXM185`** (`n ≥ 22 000`, `0.46 ≤ θ_in ≤ θh ≤ 0.528`). -/
theorem Xi4_SXM185 (hn : 18500 ≤ n) {c : Fin n → ℝ} {τ θh : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θh) (hθh : θh ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXM185 n) :
    Xi4 A₁ A₂ c τ ≤ 1111 / 1000 * (10198 / 10000) * θh * (2 / (n : ℝ)) / n := by
  have hn0 : (0 : ℝ) < n := by
    have : (18500 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 1111 / 1000 * (10198 / 10000) * thetaC c τ := ⟨_, rfl⟩
  have hBp : 0 < B := by rw [hB]; nlinarith
  have h20 := X20_SXM185 hn hτ hθ0 (hθ1.trans hθh) h
  rw [← hB] at h20
  have h2 := Xq_le_of_X20 (q := 2) (by norm_num) (by omega) A₁ A₂ c hτ hBp h20
  have h4 : √(XqN 2 A₁ A₂ c τ) ≤ B := by
    rw [← Real.sqrt_sq hBp.le]; exact Real.sqrt_le_sqrt h2
  rw [Xi4_eq_XqN A₁ A₂ c τ, hmA]
  have hB' : B ≤ 1111 / 1000 * (10198 / 10000) * θh := by
    rw [hB]; exact mul_le_mul_of_nonneg_left hθ1 (by norm_num)
  have h5 : 2 / (n : ℝ) ^ 2 * √(XqN 2 A₁ A₂ c τ) ≤
      2 / (n : ℝ) ^ 2 * (1111 / 1000 * (10198 / 10000) * θh) :=
    mul_le_mul_of_nonneg_left (h4.trans hB') (by positivity)
  refine h5.trans (le_of_eq ?_)
  field_simp

/-- **`Ξ₈ ≤ 1.1·1.0182·θh·γ_A/n` on `SXM185`**. -/
theorem Xi8_SXM185 (hn : 18500 ≤ n) {c : Fin n → ℝ} {τ θh : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θh) (hθh : θh ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXM185 n) :
    Xi8 A₁ A₂ c τ ≤ 1111 / 1000 * (10198 / 10000) * θh * (2 / (n : ℝ)) / n := by
  have hn0 : (0 : ℝ) < n := by
    have : (18500 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 1111 / 1000 * (10198 / 10000) * thetaC c τ := ⟨_, rfl⟩
  have hBp : 0 < B := by rw [hB]; nlinarith
  have h20 := X20_SXM185 hn hτ hθ0 (hθ1.trans hθh) h
  rw [← hB] at h20
  have h3 : XqN 4 A₁ A₂ c τ ≤ (B ^ 2) ^ 2 := by
    rw [← pow_mul]; exact Xq_le_of_X20 (q := 4) (by norm_num) (by omega) A₁ A₂ c hτ hBp h20
  have h4 : √(XqN 4 A₁ A₂ c τ) ≤ B ^ 2 := by
    rw [← Real.sqrt_sq (sq_nonneg B)]; exact Real.sqrt_le_sqrt h3
  have h4' : √(√(XqN 4 A₁ A₂ c τ)) ≤ B := by
    rw [← Real.sqrt_sq hBp.le]; exact Real.sqrt_le_sqrt h4
  rw [Xi8_eq_XqN A₁ A₂ c τ, hmA]
  have hB' : B ≤ 1111 / 1000 * (10198 / 10000) * θh := by
    rw [hB]; exact mul_le_mul_of_nonneg_left hθ1 (by norm_num)
  have h5 : 2 / (n : ℝ) ^ 2 * √(√(XqN 4 A₁ A₂ c τ)) ≤
      2 / (n : ℝ) ^ 2 * (1111 / 1000 * (10198 / 10000) * θh) :=
    mul_le_mul_of_nonneg_left (h4'.trans hB') (by positivity)
  refine h5.trans (le_of_eq ?_)
  field_simp

/-- **`Ξ ≤ 1.1·1.0182·θh·γ_A/n` on `SXM185`** (`Ξ ≤ Ξ₄`). -/
theorem XiS_SXM185 (hn : 18500 ≤ n) {c : Fin n → ℝ} {τ θh : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θh) (hθh : θh ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXM185 n) :
    XiS A₁ A₂ c τ ≤ 1111 / 1000 * (10198 / 10000) * θh * (2 / (n : ℝ)) / n :=
  (BstLean.Part153.XiS_le_Xi4 (by omega) A₁ A₂ c hτ).trans (Xi4_SXM185 hn hτ hθ0 hθ1 hθh h)

end BstLean.Part183.F185

open BstLean.Part183.F185 in
#print axioms SXM185_ret_charge
open BstLean.Part183.F185 in
#print axioms XiS_SXM185
open BstLean.Part183.F185 in
#print axioms Xi8_SXM185
open BstLean.Part183.F185 in
#print axioms tX20_le_WF185
