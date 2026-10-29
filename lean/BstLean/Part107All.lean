import BstLean.Part107Final
import BstLean.Part107Poincare
import BstLean.Part107Aux
import BstLean.Part107P1
import BstLean.Part107P3
import BstLean.Part107P4
import BstLean.Part107Sph
import BstLean.Part107Law
import BstLean.Part107Wick
import BstLean.Part107Num
import BstLean.Part107P5
import BstLean.Part107S
import BstLean.Part107E

/-!
# Part 107: the spread of the linear part — headline theorems, with no hypothesis left

Role: `delegations/statements/p107-spec.md`. Report: `delegations/answers/p107-spec-opus.md`.

* Item 1: `poincare107` (`Part107Poincare.lean`).
* Item 2: `p1`, `p3`, `p4`, `p5` (Lemma P).
* Item 3: `agent_kernel`, `part107_spread`, `part107_spread_num` (Lemma S, Corollary S).
* Item 4: `cantelli` (`Part107Final.lean`), `part107_tail`, `part107_tail_num`.
* Item 5: `lemmaE`, `part107_lemmaA_dA3`, `part107_lemmaA_dA4` (Lemma E, Lemma A, linear part).
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

/-- (P1). -/
theorem p1 : P1_107 := p1_107 nonZero107

/-- (P3). -/
theorem p3 : P3_107 := p3_107 poincare107 invMom107 nullPar107

/-- (P4). -/
theorem p4 : P4_107 := p4_107'

/-- (P2) and (P5) for the Gaussian version of `W`. -/
theorem p5 : P5_107 := p5_107 twoPoint107 p1 p3 p4 sphStat107 kapFacts107

/-- Lemma S and Corollary S from two-point bounds. -/
theorem corS : CorS107 := corS107 wick107 qDom107 (onePoint107 nonZero107)

/-- Lemma E for the linear part. -/
theorem lemmaE : LemmaE107 := lemmaE107 qDom107

/-- **The kernel of the Gaussian version of `A` with unit coefficient variance**:
`E A_i(x) A_j(x′) = δ_ij κ(x·x′)`. -/
theorem agent_kernel (n dA : ℕ) (x y : Fin n → ℝ) (i j : Fin n) :
    ∫ A, bwEval A x i * bwEval A y j ∂bwGauss n n dA 1 =
      if i = j then kap dA (dot x y) else 0 := by
  rw [bwGauss_cov]
  simp [kap]

/-- **Item 3 (Lemma S, Corollary S)**, `n ≥ 4 096`, `d_A ∈ {3, 4}`, Gaussian versions:
`X₁ ∈ L²`, `E X₁ ≥ n (K − v̄) > 0`, `n · Var X₁ ≤ a_L (E X₁)²`. -/
theorem part107_spread (n dA : ℕ) (σ : ℝ) (hn : 4096 ≤ n) (hdA : dA = 3 ∨ dA = 4) (hσ : σ ≠ 0) :
    MemLp (fun ω => X1 ω.1 ω.2.1 ω.2.2) 2 (PP (2 * n) n (2 * dA) dA σ) ∧
    vbar dA n < (dA : ℝ) + 1 ∧
    (n : ℝ) * ((dA : ℝ) + 1 - vbar dA n) ≤ ∫ ω, X1 ω.1 ω.2.1 ω.2.2 ∂PP (2 * n) n (2 * dA) dA σ ∧
    (n : ℝ) * Var[fun ω => X1 ω.1 ω.2.1 ω.2.2; PP (2 * n) n (2 * dA) dA σ] ≤
      aL dA n * (∫ ω, X1 ω.1 ω.2.1 ω.2.2 ∂PP (2 * n) n (2 * dA) dA σ) ^ 2 := by
  have hv : vbar dA n < (dA : ℝ) + 1 := by
    obtain ⟨⟨h3, -, -⟩, ⟨h4, -, -⟩⟩ := numeric107 n hn
    rcases hdA with rfl | rfl
    · norm_num; linarith
    · norm_num; linarith
  obtain ⟨h1, h2, h3⟩ := spread_var corS p5 n dA σ (by omega) hdA hσ hv
  exact ⟨h1, hv, h2, h3⟩

/-- The numeric bounds of `a_L`: `a_L ≤ 10.5` (`d_A = 3`), `a_L ≤ 10.7` (`d_A = 4`), `n ≥ 4 096`. -/
theorem aL_num (n : ℕ) (hn : 4096 ≤ n) : aL 3 n ≤ 105 / 10 ∧ aL 4 n ≤ 107 / 10 :=
  ⟨(numeric107 n hn).1.2.2, (numeric107 n hn).2.2.2⟩

/-- Item 3 with the numeric constant: `n · Var X₁ ≤ 10.7 (E X₁)²` for both degrees
(`10.5` for `d_A = 3`). -/
theorem part107_spread_num (n dA : ℕ) (σ : ℝ) (hn : 4096 ≤ n) (hdA : dA = 3 ∨ dA = 4)
    (hσ : σ ≠ 0) :
    (n : ℝ) * Var[fun ω => X1 ω.1 ω.2.1 ω.2.2; PP (2 * n) n (2 * dA) dA σ] ≤
      (if dA = 3 then 105 / 10 else 107 / 10) *
        (∫ ω, X1 ω.1 ω.2.1 ω.2.2 ∂PP (2 * n) n (2 * dA) dA σ) ^ 2 := by
  obtain ⟨-, -, -, h⟩ := part107_spread n dA σ hn hdA hσ
  refine le_trans h (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  rcases hdA with rfl | rfl
  · simpa using (aL_num n hn).1
  · simpa using (aL_num n hn).2

/-- **Item 4 (the lower tail of the spread)**:
`Pr(X₁ < (1 − θ) E X₁) ≤ a_L/(a_L + n θ²)`. -/
theorem part107_tail (n dA : ℕ) (σ : ℝ) (hn : 4096 ≤ n) (hdA : dA = 3 ∨ dA = 4) (hσ : σ ≠ 0)
    {θ : ℝ} (hθ : 0 < θ) :
    (PP (2 * n) n (2 * dA) dA σ).real
        {ω | X1 ω.1 ω.2.1 ω.2.2 < (1 - θ) * ∫ ω, X1 ω.1 ω.2.1 ω.2.2 ∂PP (2 * n) n (2 * dA) dA σ} ≤
      aL dA n / (aL dA n + (n : ℝ) * θ ^ 2) :=
  spread_tail corS p5 n dA σ (by omega) hdA hσ (part107_spread n dA σ hn hdA hσ).2.1 hθ

/-- Item 4 with the numeric constant. -/
theorem part107_tail_num (n dA : ℕ) (σ : ℝ) (hn : 4096 ≤ n) (hdA : dA = 3 ∨ dA = 4) (hσ : σ ≠ 0)
    {θ : ℝ} (hθ : 0 < θ) :
    (PP (2 * n) n (2 * dA) dA σ).real
        {ω | X1 ω.1 ω.2.1 ω.2.2 < (1 - θ) * ∫ ω, X1 ω.1 ω.2.1 ω.2.2 ∂PP (2 * n) n (2 * dA) dA σ} ≤
      (107 / 10) / (107 / 10 + (n : ℝ) * θ ^ 2) := by
  refine le_trans (part107_tail n dA σ hn hdA hσ hθ) ?_
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have ha : 0 ≤ aL dA n := le_trans (by norm_num) (aL_ge_two_of p5 n dA σ (by omega) hdA hσ)
  refine frac_mono ha ?_ (by positivity)
  rcases hdA with rfl | rfl
  · linarith [(aL_num n hn).1]
  · exact (aL_num n hn).2

/-- `λ_0 < 1` at `d_W = 6`. -/
theorem lam6_lt_one (n : ℕ) (hn : 4096 ≤ n) : lam0 (2 * n) (2 * 3) < 1 := by
  have h := lam0_bound n (by omega)
  have hn0 : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 / (10 * (n : ℝ)) ≤ 1 / 40960 := by
    apply one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h2 : 2 / (n : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have : 1 / (10 * (n : ℝ)) * (1 + 2 / (n : ℝ)) ≤ 1 / 40960 * 2 :=
    mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
  show lam0 (2 * n) 6 < 1
  linarith

/-- `λ_0 < 1` at `d_W = 8`. -/
theorem lam8_lt_one (n : ℕ) (hn : 4096 ≤ n) : lam0 (2 * n) (2 * 4) < 1 := by
  have h := lam8_107 n (by omega)
  have hn0 : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 1 / (14 * (n : ℝ)) ≤ 1 / 57344 := by
    apply one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h2 : 2 / (n : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have : 1 / (14 * (n : ℝ)) * (1 + 2 / (n : ℝ)) ≤ 1 / 57344 * 2 :=
    mul_le_mul h1 (by linarith) (by positivity) (by norm_num)
  show lam0 (2 * n) 8 < 1
  linarith

/-- **Item 5 (Lemma A for the linear part)**, `n ≥ 4 096`, `d_A ∈ {3, 4}`, `k ≥ 1`,
`0 < θ < 1`: the probability over `(W, A₁, ℓ)` and the `k` draws of `|g − B| > √X₁/2` is at most
`a_L/(a_L + n θ²) + 4(λ_0 + 1/k)/((1 − θ)(1 − λ_0))`. -/
theorem part107_lemmaA (n dA k : ℕ) (σ : ℝ) (hn : 4096 ≤ n) (hdA : dA = 3 ∨ dA = 4) (hσ : σ ≠ 0)
    (hk : 1 ≤ k) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1) :
    (Full (2 * n) n (2 * dA) dA k σ).real
        {ω | Real.sqrt (X1 ω.1.1 ω.1.2.1 ω.1.2.2) / 2 <
          |gErr (N := 2 * n) (n := n) (dW := 2 * dA) (dA := dA) (k := k) σ ω|} ≤
      aL dA n / (aL dA n + (n : ℝ) * θ ^ 2) +
        4 * (lam0 (2 * n) (2 * dA) + 1 / (k : ℝ)) / ((1 - θ) * (1 - lam0 (2 * n) (2 * dA))) := by
  have hlam : lam0 (2 * n) (2 * dA) < 1 := by
    rcases hdA with rfl | rfl
    · exact lam6_lt_one n hn
    · exact lam8_lt_one n hn
  exact lemmaA corS p5 lemmaE n dA k σ (by omega) hdA hσ hk
    (part107_spread n dA σ hn hdA hσ).2.1 hlam hθ hθ1

end BstLean.Part107

open BstLean.Part107 in
#print axioms poincare107
open BstLean.Part107 in
#print axioms p5
open BstLean.Part107 in
#print axioms agent_kernel
open BstLean.Part107 in
#print axioms part107_spread
open BstLean.Part107 in
#print axioms part107_spread_num
open BstLean.Part107 in
#print axioms cantelli
open BstLean.Part107 in
#print axioms part107_tail_num
open BstLean.Part107 in
#print axioms lemmaE
open BstLean.Part107 in
#print axioms part107_lemmaA
