import BstLean.Part59Main
import BstLean.Part59CostCmp
import BstLean.Part59T2
import BstLean.Part59Horner
import BstLean.Part59Prog
import BstLean.Part59Coef
import BstLean.Part59LemmaQ
import BstLean.Part59Error
import BstLean.Part59Floor
import BstLean.Part59RPlus
import BstLean.Part59LemmaV
import BstLean.Part59LemmaH
import BstLean.Part59Radial
import BstLean.Part59T1
import BstLean.Part53Remez
import BstLean.Part53Polar
import BstLean.Part48SmallBall
import BstLean.Part53Laws

/-!
# Part 59: Theorem DL2-G — the constant-column program `g₀(m) = (P_a f)(m(0))` beats the charged
baseline for every output degree

Role: `delegations/statements/p59-spec.md`. Specification: `delegations/answers/p59-spec-opus.md`.
Source: `delegations/answers/omDL2-opus-prover.md` lines 25–247, with the repairs of `chDL2-opus.md`
and `chDL2-codex.md`.

* `part59_baseline_honest`: the baseline's `f`-program exists, from `0` and `1`, with cost exactly
  `costF n k = 2C(n+k,k) − 2` (Dev's A9 charge is the cost of a real program).
* `part59_fail_g0`: for every `d ≥ 1`, `k ≥ 1`, `K`, `ε > 0`, `δ > 0`: failure probability `≤ δ` for the
  function `g₀` (tensor form), every law with `dD/dσ ≤ K` and every `f` of degree `k`, from `n₀` on.
* `part59_general`: the headline. No relation between `k` and `d` is assumed.

Do not use `native_decide` or `axiom`.
-/

namespace BstLean.Part59

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (Mono frob Tens TSymm heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part48 (SBLevel sb_level_exists)
open BstLean.Part53 (g0 lemmaR53 gaussPolar53 DensLaw lawE_dens)
open BstLean.Part51 (lawE OscLE)

/-- **The charged baseline is honest**: one program from `0` and `1` evaluates every polynomial of
degree `≤ k` at every point, at cost exactly `costF n k`. -/
theorem part59_baseline_honest (n k : ℕ) :
    ∃ pg : Prog (InH n k) Unit, heavyCount pg = 0 ∧
      (∀ v : InH n k → ℝ, pg.eval v () = polyEval k (fun α => v (Sum.inl α)) (fun i => v (Sum.inr i))) ∧
      (pg.cost : ℝ) = costF n k := by
  obtain ⟨pg, h0, hev, hc⟩ := horner59_exists n k
  refine ⟨pg, h0, hev, ?_⟩
  have h1 : 1 ≤ (n + k).choose k := Nat.choose_pos (by omega)
  rw [hc, costF, Nat.cast_sub (by omega)]
  push_cast
  ring

/-- **The error and the floor** for the function `g₀` (tensor form), every `d ≥ 1`, `k ≥ 1`. -/
theorem part59_fail_g0 (k d : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (K ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ μ : Measure (Fin n → ℝ), UpLaw n μ K →
      ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ μ k f0 T (unitOfD Z) <
            (BofQ μ k f0 T (unitOfD Z) - g0 n d k f0 T (unitOfD Z)) ^ 2} ≤ ENNReal.ofReal δ := by
  obtain ⟨CE, nE, hE⟩ := propE59_of d k hd hk K
  obtain ⟨nF, hF⟩ := propF59_of d k hd hk K
  obtain ⟨C1, n1, h1⟩ := propT1s_of d k hd hk K CE nE hE (lemmaR53 k) gaussPolar53
  obtain ⟨CV, nV, hV⟩ := lemmaV59_of d k hd hk K
  obtain ⟨CR, nR, hCR, hRT⟩ :=
    radialTail59_of d k hd hk K CV nV hV (lemmaH59 d k hk) (lemmaRp59 k) gaussPolar53
  obtain ⟨t, ht, hSB⟩ := sb_level_exists (2 * k) (δ / 2) (by positivity)
  have h2 := propT2s_of d k hk K nF hF CR nR hCR hRT (δ / 2) t hSB ht
  exact fail59 d k K ε δ (δ / 2) (t / 32) C1 CR n1 _ hε (by positivity) (by positivity)
    (by linarith) h1 h2

/-- **Theorem DL2-G** (headline). For every `d_M ≥ 1`, every `d_f ≥ 1` (no relation between them),
every `K` and every `ε > 0` there is `n₀ ≥ 100` such that for every `n ≥ n₀` one straight-line program
`pg` from the constants `0` and `1` reads only the constant column of `m` and the coefficients of `f`,
computes `g₀ = (P_a f)(m(0))` by the nested tree with the weights of Lemma Q, costs less than the
charged baseline `max(2P′, 0.91P′/ε²)`, `P′ = P + 2C(n+k,k) − 2`, and, for every law `μ` on the sphere
with `dμ/dσ ≤ K` and every `f` of degree `d_f`, fails with probability `≤ 1/100` over `m` uniform on
the coefficient sphere. -/
theorem part59_general (k d : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (K ε : ℝ) (hε : 0 < ε) :
    ∃ n0 : ℕ, 100 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n → ∃ pg : Prog (In59 n d k) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d k → ℝ, pg.eval v () = g0Q n d k (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d k ε ∧
      ∀ μ : Measure (Fin n → ℝ), UpLaw n μ K →
        ∀ c : Mono n k → ℝ, TopNZ k c →
          stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
            ε ^ 2 * varP μ k c (unitOfD Z) <
              (BP μ k c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) := by
  obtain ⟨nf, hfail⟩ := part59_fail_g0 k d hd hk K ε (1 / 100) hε (by norm_num)
  obtain ⟨nc, hc⟩ := costG59_lt d k hd ε
  refine ⟨max (max nf nc) 100, le_max_right _ _, fun n hn => ?_⟩
  have hnf : nf ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnc : nc ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn1 : 1 ≤ n := le_trans (by norm_num) (le_trans (le_max_right _ _) hn)
  obtain ⟨pg, h0, hread, hspec, hcost⟩ := prog59_exists n d k hn1 hd hk
  refine ⟨pg, h0, hread, hspec, cost_lt_baselineF59 k ε pg.cost hcost (hc n hnc), ?_⟩
  intro μ hμ c hc
  have hCT := coefTens59
  obtain ⟨hTs, -, htop⟩ := hCT n k c
  have heval : ∀ M : CoefIdxD n d → ℝ,
      pg.eval (inp59 c M) () = g0 n d k (c default) (tensOf k c) M := by
    intro M
    rw [hspec, (cv59_inp k c M).1, (cv59_inp k c M).2, lemmaQ59]
  simp only [heval, BP_eq59 hCT, varP_eq59 hCT]
  exact hfail n hnf μ hμ (c default) (tensOf k c) hTs (htop hc)

/-- A law with density ratio in `[e^{−Λ}, e^Λ]` has `dD/dσ ≤ e^Λ`. -/
theorem densLaw_upLaw59 {n : ℕ} {μ : Measure (Fin n → ℝ)} {Λ : ℝ} (h : DensLaw n μ Λ) :
    UpLaw n μ (Real.exp Λ) := by
  obtain ⟨hp, ρ, hm, h0, hμ, hb⟩ := h
  exact ⟨hp, ρ, hm, h0, hμ, fun x hx => (hb x hx).2⟩

/-- **Theorem DL2-G for the exponential families** `D ∝ e^U`, `U` continuous with oscillation `≤ Λ`
on the sphere (for example `U = polR b` of Part 51), every `d ≥ 1`, `k ≥ 1`. -/
theorem part59_lawE (k d : ℕ) (hd : 1 ≤ d) (hk : 1 ≤ k) (Λ ε : ℝ) (hε : 0 < ε) :
    ∃ n0 : ℕ, 100 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n → ∃ pg : Prog (In59 n d k) Unit,
      heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d k → ℝ, pg.eval v () = g0Q n d k (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) < baselineF n d k ε ∧
      ∀ U : (Fin n → ℝ) → ℝ, Continuous U → OscLE U Λ →
        ∀ c : Mono n k → ℝ, TopNZ k c →
          stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
            ε ^ 2 * varP (lawE n U) k c (unitOfD Z) <
              (BP (lawE n U) k c (unitOfD Z) - pg.eval (inp59 c (unitOfD Z)) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) := by
  obtain ⟨n0, h100, h⟩ := part59_general k d hd hk (Real.exp Λ) ε hε
  refine ⟨n0, h100, fun n hn => ?_⟩
  obtain ⟨pg, h0, hread, hspec, hcost, hfail⟩ := h n hn
  have hn1 : 1 ≤ n := le_trans (by omega) hn
  exact ⟨pg, h0, hread, hspec, hcost, fun U hU hosc =>
    hfail (lawE n U) (densLaw_upLaw59 (lawE_dens hn1 U hU Λ hosc))⟩

end BstLean.Part59

#print axioms BstLean.Part59.part59_general
#print axioms BstLean.Part59.part59_baseline_honest
#print axioms BstLean.Part59.part59_lawE
