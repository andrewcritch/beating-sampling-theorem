import BstLean.Part153PPs3
import Mathlib.Tactic.NormNum.NatFactorial

/-!
# Part 153, Lemma PP: the numeric corollaries with the paper's budget constants `M_P`

Paper source: `proofs/option-n/theorem5-05-covariance.tex`, Lemma PP (the script values
`M_P ≤ 1.257833734831` at `n = 8192` and `M_P ≤ 1.191132745625` at `n = 16384`).
Here `P = 200`, `η = 6/1000` in `lemmaPP_Xi4_sharp`.

* §1 `gaussMomConst_200_le`: `𝔪_200 ≤ 25/2`; `jS_le_atoms`; `jS_200_le_8192`, `jS_200_le_16384`.
* §2 **`lemmaPP_numeric_8192`** (`M_P = 12578/10000`), **`lemmaPP_numeric_16384`**
  (`M_P = 11911/10000`).
* §3 `cov_le_on_event_8192`, `var_lip_le_on_event_8192`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part148 (EuLip)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (jac mask)

/-! ## §1 Numeric bounds -/

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 1000 in
/-- `𝔪_200 ≤ 25/2`. -/
lemma gaussMomConst_200_le : gaussMomConst 200 ≤ 25 / 2 := by
  have hp := gaussMomConst_pow (P := 200) (by norm_num)
  have hN : 2 ^ 200 * Nat.factorial 200 * 2 ^ 400 ≤ 25 ^ 400 := by
    norm_num
  have h1 : gaussMomConst 200 ^ (2 * 200) ≤ (25 / 2 : ℝ) ^ (2 * 200) := by
    rw [hp, div_pow, le_div_iff₀ (by positivity)]
    exact_mod_cast hN
  by_contra hlt
  have := pow_lt_pow_left₀ (not_le.mp hlt) (by norm_num : (0 : ℝ) ≤ 25 / 2)
    (by norm_num : (2 * 200 : ℕ) ≠ 0)
  linarith

lemma exp_neg_12_le : Real.exp (-12) ≤ 7 / 10 ^ 6 := by
  have h1 : (2.7 : ℝ) ^ 12 ≤ Real.exp 12 := by
    have e : Real.exp 12 = Real.exp 1 ^ 12 := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [e]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.exp_one_gt_d9]) 12
  rw [Real.exp_neg]
  calc (Real.exp 12)⁻¹ ≤ ((2.7 : ℝ) ^ 12)⁻¹ := inv_anti₀ (by positivity) h1
    _ ≤ 7 / 10 ^ 6 := by norm_num

/-- `jS` is at most its value at upper bounds of its atoms. -/
lemma jS_le_atoms (n P : ℕ) (η : ℝ) {R Q U Wb GU E : ℝ} (hr : √(2 : ℝ) ≤ R)
    (hq : √(1 + 2 * η) ≤ Q) (hu : 1 / √(n : ℝ) ≤ U) (hw : gaussMomConst P / (n : ℝ) ≤ Wb)
    (hgu : gaussMomConst P / √(n : ℝ) ≤ GU) (he : epsS n P η ≤ E) :
    jS n P η ≤ (Q + R * U + R * Wb + E * (R * (1 + U + Wb))) ^ 2 +
      (1 + R * Wb) * (R * (1 + GU)) * U := by
  have hg0 := gaussMomConst_nonneg P
  have hr0 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have hq0 : (0 : ℝ) ≤ √(1 + 2 * η) := Real.sqrt_nonneg _
  have hu0 : (0 : ℝ) ≤ 1 / √(n : ℝ) := by positivity
  have hw0 : (0 : ℝ) ≤ gaussMomConst P / n := by positivity
  have hgu0 : (0 : ℝ) ≤ gaussMomConst P / √(n : ℝ) := by positivity
  have he0 : 0 ≤ epsS n P η := (Real.exp_pos _).le
  obtain ⟨r2, hr2⟩ : ∃ r2, r2 = √(2 : ℝ) := ⟨_, rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q, q = √(1 + 2 * η) := ⟨_, rfl⟩
  obtain ⟨u, hud⟩ : ∃ u, u = 1 / √(n : ℝ) := ⟨_, rfl⟩
  obtain ⟨w, hwd⟩ : ∃ w, w = gaussMomConst P / (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨gu, hgud⟩ : ∃ gu, gu = gaussMomConst P / √(n : ℝ) := ⟨_, rfl⟩
  obtain ⟨e, hed⟩ : ∃ e, e = epsS n P η := ⟨_, rfl⟩
  have key : jS n P η = (q + r2 * u + r2 * w + e * (r2 * (1 + u + w))) ^ 2 +
      (1 + r2 * w) * (r2 * (1 + gu)) * u := by
    unfold jS n2S n1S b2S rcS rchiS
    rw [← hed, hqd, hr2, hud, hwd, hgud]
    ring
  rw [key]
  rw [← hr2] at hr0 hr
  rw [← hqd] at hq0 hq
  rw [← hud] at hu0 hu
  rw [← hwd] at hw0 hw
  rw [← hgud] at hgu0 hgu
  rw [← hed] at he0 he
  have hR0 : 0 ≤ R := hr0.trans hr
  have hU0 : 0 ≤ U := hu0.trans hu
  have hW0 : 0 ≤ Wb := hw0.trans hw
  have hGU0 : 0 ≤ GU := hgu0.trans hgu
  have hE0 : 0 ≤ E := he0.trans he
  have h1 : r2 * u ≤ R * U := mul_le_mul hr hu hu0 hR0
  have h2 : r2 * w ≤ R * Wb := mul_le_mul hr hw hw0 hR0
  have hb0 : 0 ≤ r2 * (1 + u + w) := mul_nonneg hr0 (by linarith)
  have hb : r2 * (1 + u + w) ≤ R * (1 + U + Wb) :=
    mul_le_mul hr (by linarith) (by linarith) hR0
  have heb : e * (r2 * (1 + u + w)) ≤ E * (R * (1 + U + Wb)) := mul_le_mul he hb hb0 hE0
  have hn20 : 0 ≤ q + r2 * u + r2 * w + e * (r2 * (1 + u + w)) :=
    add_nonneg (add_nonneg (add_nonneg hq0 (mul_nonneg hr0 hu0)) (mul_nonneg hr0 hw0))
      (mul_nonneg he0 hb0)
  have hn2 : q + r2 * u + r2 * w + e * (r2 * (1 + u + w)) ≤
      Q + R * U + R * Wb + E * (R * (1 + U + Wb)) := by linarith
  have hn2sq := pow_le_pow_left₀ hn20 hn2 2
  have hrc0 : 0 ≤ 1 + r2 * w := add_nonneg zero_le_one (mul_nonneg hr0 hw0)
  have hrc : 1 + r2 * w ≤ 1 + R * Wb := by linarith
  have hrchi0 : 0 ≤ r2 * (1 + gu) := mul_nonneg hr0 (by linarith)
  have hrchi : r2 * (1 + gu) ≤ R * (1 + GU) := mul_le_mul hr (by linarith) (by linarith) hR0
  have hprod : (1 + r2 * w) * (r2 * (1 + gu)) ≤ (1 + R * Wb) * (R * (1 + GU)) :=
    mul_le_mul hrc hrchi hrchi0 (by linarith [mul_nonneg hR0 hW0])
  have hpu : (1 + r2 * w) * (r2 * (1 + gu)) * u ≤ (1 + R * Wb) * (R * (1 + GU)) * U :=
    mul_le_mul hprod hu hu0
      (mul_nonneg (by linarith [mul_nonneg hR0 hW0]) (mul_nonneg hR0 (by linarith)))
  linarith

lemma sqrt_two_le : √(2 : ℝ) ≤ 141422 / 100000 := by
  rw [Real.sqrt_le_iff]
  constructor <;> norm_num

lemma sqrt_eta_le : √(1 + 2 * (6 / 1000) : ℝ) ≤ 100599 / 100000 := by
  rw [Real.sqrt_le_iff]
  constructor <;> norm_num

lemma epsS_200_le {n : ℕ} (hn : 8192 ≤ n) : epsS n 200 (6 / 1000) ≤ 7 / 10 ^ 6 := by
  have hnr : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  refine le_trans ?_ exp_neg_12_le
  unfold epsS
  rw [show ((200 : ℕ) : ℝ) = 200 by norm_num]
  refine Real.exp_le_exp.2 ?_
  have : (8192 : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := pow_le_pow_left₀ (by norm_num) hnr 2
  have h12 : (12 : ℝ) ≤ (6 / 1000) ^ 2 * (n : ℝ) ^ 2 / 200 := by
    rw [le_div_iff₀ (by norm_num)]
    nlinarith
  linarith

/-- `jS n 200 (6/1000) ≤ 1.066` for `n ≥ 8192`. -/
lemma jS_200_le_8192 {n : ℕ} (hn : 8192 ≤ n) : jS n 200 (6 / 1000) ≤ 1066 / 1000 := by
  have hnr : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : (905 / 10 : ℝ) ≤ √(n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hg0 := gaussMomConst_nonneg 200
  have hg := gaussMomConst_200_le
  have hu : 1 / √(n : ℝ) ≤ 1 / (905 / 10) := one_div_le_one_div_of_le (by norm_num) hs
  have hw : gaussMomConst 200 / (n : ℝ) ≤ (25 / 2) / 8192 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    nlinarith
  have hgu : gaussMomConst 200 / √(n : ℝ) ≤ (25 / 2) / (905 / 10) := by
    rw [div_le_div_iff₀ hs0 (by norm_num)]
    nlinarith
  refine (jS_le_atoms n 200 (6 / 1000) sqrt_two_le sqrt_eta_le hu hw hgu
    (epsS_200_le hn)).trans ?_
  norm_num

/-- `jS n 200 (6/1000) ≤ 1.0488` for `n ≥ 16384`. -/
lemma jS_200_le_16384 {n : ℕ} (hn : 16384 ≤ n) : jS n 200 (6 / 1000) ≤ 10488 / 10000 := by
  have hnr : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : (128 : ℝ) ≤ √(n : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    norm_num
    linarith
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  have hg0 := gaussMomConst_nonneg 200
  have hg := gaussMomConst_200_le
  have hu : 1 / √(n : ℝ) ≤ 1 / 128 := one_div_le_one_div_of_le (by norm_num) hs
  have hw : gaussMomConst 200 / (n : ℝ) ≤ (25 / 2) / 16384 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    nlinarith
  have hgu : gaussMomConst 200 / √(n : ℝ) ≤ (25 / 2) / 128 := by
    rw [div_le_div_iff₀ hs0 (by norm_num)]
    nlinarith
  refine (jS_le_atoms n 200 (6 / 1000) sqrt_two_le sqrt_eta_le hu hw hgu
    (epsS_200_le (by omega))).trans ?_
  norm_num

/-! ## §2 The numeric corollaries -/

set_option exponentiation.threshold 1000 in
lemma pow_951_le : (951 / 1000 : ℝ) ^ 200 ≤ 5 / 100000 := by norm_num

/-- The Markov step at `P = 200`, `η = 6/1000`, from a bound `J` of `jS` and a bound `951/1000`
of the ratio. -/
lemma lemmaPP_numeric_aux {n : ℕ} (hn : 8192 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {J M : ℝ} (hM : 0 < M) (hj : jS n 200 (6 / 1000) ≤ J)
    (hJ : J ^ 2 * n ≤ 951 / 1000 * (((n : ℝ) - 1 - 2 * 200) * M)) :
    (nuA n).real {θ | M * (2 / (n : ℝ)) / n < Xi4 θ.1 θ.2 c τ} ≤ 5 / 100000 := by
  have hnr : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  have h := lemmaPP_Xi4_sharp (n := n) (P := 200) (by norm_num) (by omega) c hτ hM
    (η := 6 / 1000) (by norm_num)
  refine h.trans ?_
  rw [show ((200 : ℕ) : ℝ) = 200 by norm_num]
  have hj0 := jS_nonneg n 200 (6 / 1000)
  have hj2 : jS n 200 (6 / 1000) ^ 2 ≤ J ^ 2 := pow_le_pow_left₀ hj0 hj 2
  have hd : (0 : ℝ) < ((n : ℝ) - 1 - 2 * 200) * M := by
    have : (0 : ℝ) < (n : ℝ) - 1 - 2 * 200 := by linarith
    positivity
  have hratio : jS n 200 (6 / 1000) ^ 2 * n / (((n : ℝ) - 1 - 2 * 200) * M) ≤ 951 / 1000 := by
    rw [div_le_iff₀ hd]
    exact (mul_le_mul_of_nonneg_right hj2 (by linarith)).trans hJ
  have hr0 : 0 ≤ jS n 200 (6 / 1000) ^ 2 * n / (((n : ℝ) - 1 - 2 * 200) * M) :=
    div_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) hd.le
  exact (pow_le_pow_left₀ hr0 hratio 200).trans pow_951_le

/-- **Lemma PP, numeric corollary with the paper's `M_P` at `n = 8192`** (`P = 200`,
`η = 6/1000`): for `n ≥ 8192`, `Pr(Ξ₄ > (12578/10000)·γ_A/n) ≤ 5·10⁻⁵`. -/
theorem lemmaPP_numeric_8192 {n : ℕ} (hn : 8192 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real {θ | (12578 / 10000 : ℝ) * (2 / (n : ℝ)) / n < Xi4 θ.1 θ.2 c τ} ≤
      5 / 100000 := by
  have hnr : (8192 : ℝ) ≤ n := by exact_mod_cast hn
  refine lemmaPP_numeric_aux hn c hτ (by norm_num) (jS_200_le_8192 hn) ?_
  norm_num
  linarith

/-- **Lemma PP, numeric corollary with the paper's `M_P` at `n = 16384`** (`P = 200`,
`η = 6/1000`): for `n ≥ 16384`, `Pr(Ξ₄ > (11911/10000)·γ_A/n) ≤ 5·10⁻⁵`. -/
theorem lemmaPP_numeric_16384 {n : ℕ} (hn : 16384 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    (nuA n).real {θ | (11911 / 10000 : ℝ) * (2 / (n : ℝ)) / n < Xi4 θ.1 θ.2 c τ} ≤
      5 / 100000 := by
  have hnr : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  refine lemmaPP_numeric_aux (by omega) c hτ (by norm_num) (jS_200_le_16384 hn) ?_
  norm_num
  linarith

/-! ## §3 The covariance bound on the event, with the constant `12578/10000` -/

section cov

variable {n : ℕ}

/-- For `n ≥ 8192` and every `θ` outside the set of `lemmaPP_numeric_8192`:
`t_A·Var_ξ ⟨w, h₂(x)⟩ ≤ (12578/10000)·(2/n)/n·|w|²`. -/
theorem cov_le_on_event_8192 (hn : 8192 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (hθ : θ ∉ {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      (12578 / 10000 : ℝ) * (2 / (n : ℝ)) / n < Xi4 θ.1 θ.2 c τ}) (w : Fin (mA n) → ℝ) :
    2 / ((mA n : ℕ) : ℝ) * ∫ ξ, (w ⬝ᵥ hid2 θ.1 θ.2 (sphPt (c + τ • ξ)) -
      ∫ ξ', w ⬝ᵥ hid2 θ.1 θ.2 (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
      (12578 / 10000 : ℝ) * (2 / (n : ℝ)) / n * normSq w :=
  cov_le_of_Xi4 (by omega) θ.1 θ.2 c hτ (not_lt.mp hθ) w

/-- For `n ≥ 8192` and every `θ` outside the set of `lemmaPP_numeric_8192`:
`Var_ξ φ(√t_A·h₂(x)) ≤ Lφ²·(12578/10000)·(2/n)/n`. -/
theorem var_lip_le_on_event_8192 (hn : 8192 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (hθ : θ ∉ {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      (12578 / 10000 : ℝ) * (2 / (n : ℝ)) / n < Xi4 θ.1 θ.2 c τ})
    {φ : (Fin (mA n) → ℝ) → ℝ} {Lφ : ℝ} (hL : 0 ≤ Lφ) (hφ : EuLip φ Lφ) :
    ∫ ξ, (φ (√(2 / ((mA n : ℕ) : ℝ)) • hid2 θ.1 θ.2 (sphPt (c + τ • ξ))) -
      ∫ ξ', φ (√(2 / ((mA n : ℕ) : ℝ)) • hid2 θ.1 θ.2 (sphPt (c + τ • ξ'))) ∂stdGauss (Fin n)) ^ 2
        ∂stdGauss (Fin n) ≤ Lφ ^ 2 * ((12578 / 10000 : ℝ) * (2 / (n : ℝ)) / n) :=
  var_lip_le_of_Xi4 (by omega) θ.1 θ.2 c hτ (not_lt.mp hθ) hL hφ

end cov

end BstLean.Part153

open BstLean.Part153 in
#print axioms gaussMomConst_200_le
open BstLean.Part153 in
#print axioms lemmaPP_numeric_8192
open BstLean.Part153 in
#print axioms lemmaPP_numeric_16384
open BstLean.Part153 in
#print axioms cov_le_on_event_8192
open BstLean.Part153 in
#print axioms var_lip_le_on_event_8192
