import BstLean.Part56MomProg_Card
import BstLean.Part56MomProg_CostBound

/-!
# Part 56, wave 1: the moment program and its cost

Specification: `delegations/answers/p56-spec-opus.md` §3 (`Part56MomProg`).
This file imports `Part56Defs` (and existing Parts ≤ 55) only; it must not import another Part 56
wave-1 file. Do not use `native_decide` or `axiom` anywhere. Do not edit the statement below.

Construction (`omRK-opus-prover.md` §5): the `s`-moments `E_{Q̃} s^{2a}` as ratios of
`Σ_{i ≤ K} (t^i/i!) E_σ s^{2a+2i}` (rational recurrences `E_σ s^{2m+2}/E_σ s^{2m} = (2m+1)/(n+2m)`,
`n` built from `1`); the `w`-moments `E_w[w_{l_1}⋯w_{l_{2q}}] = c_q Σ_{pairings} Π(δ_{ll'} − v_l v_{l'})`,
`c_q = 1/((n−1)(n+1)⋯(n+2q−3))`; `E_{Q̃} x^α` for `|α| ≤ dk` by `x = s v + ϱ w`; the coefficients of
`τ^l Π_r β_{j_r}` (polynomial products, division by `k_j(v,v) > 0`); the contraction; the factor
`wickC i l σ^{2l}` (`σ² = 1/𝒟`, `𝒟` built from `1`). Only `0`, `1`; nonzero divisors at `t ≥ 0`, unit `v`.
The bound `onceCost56` is generous: any construction polynomial of degree `≤ 8dk + 8` in `n` fits.
-/

namespace BstLean.Part56

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono frob Tens TSymm Pn NN baseline heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (LemmaR53 GaussPolar53)
open BstLean.Part48 (SBLevel)

/-- **The moment program.** -/
theorem momProg56_exists (n d k K : ℕ) (hn : 2 ≤ n) :
    ∃ pm : Prog (InM56 n) (KeyRK k d), heavyCount pm = 0 ∧ MomSpec56 pm K ∧
      (pm.cost : ℝ) ≤ onceCost56 n d k K := by
  by_cases hd : d = 0
  · subst d
    exact MomProg.exists_d_zero n k K hn
  by_cases hk : k = 0
  · subst k
    exact MomProg.exists_k_zero n d K hn
  have hn1 : 1 ≤ n := by omega
  let a : Fin n := ⟨0, by omega⟩
  obtain ⟨p, hcl, hev, hco⟩ := MomProg.hp_full hn1 a d k K
  refine ⟨p, MomProg.clean_heavyCount hcl, ?_, ?_⟩
  · intro t v ht hv κ
    rw [hev]
    exact MomProg.fullF_eq hn1 a K k t ht v hv κ
  · calc (p.cost : ℝ) ≤ (MomProg.costAll n d k K (Fintype.card (MomProg.Idx n (2 * d * k)))
          (Fintype.card (Mono n d)) (Fintype.card (KeyRK k d)) : ℝ) := by exact_mod_cast hco
      _ ≤ onceCost56 n d k K :=
        MomProg.costAll_le n d k K _ _ _ hn (by omega) (by omega)
          (MomProg.card_Idx_le n _) (MomProg.card_mono_le n d) (MomProg.card_key_le k d)

end BstLean.Part56
