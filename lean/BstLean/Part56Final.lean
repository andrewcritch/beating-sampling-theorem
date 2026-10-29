import BstLean.Part56Main
import BstLean.Part56MC
import BstLean.Part56Split
import BstLean.Part56Weights
import BstLean.Part56Orth
import BstLean.Part56RKGErr
import BstLean.Part56RKGFloor
import BstLean.Part56Key
import BstLean.Part56PropD
import BstLean.Part56Surr
import BstLean.Part56T1
import BstLean.Part56Low
import BstLean.Part56T2
import BstLean.Part56LineProg
import BstLean.Part56MomProg
import BstLean.Part56Cost
import BstLean.Part53Remez
import BstLean.Part53Polar
import BstLean.Part48SmallBall

/-!
# Part 56: Theorem RK — the line program for dense rank-one Bingham laws `D ∝ exp(t (v·x)²)`

Role: `delegations/statements/p56-spec.md`. Specification: `delegations/answers/p56-spec-opus.md`.
Source: `delegations/answers/omRK-opus-prover.md` (Theorem RK), with the repairs of `chRK-codex.md`
and `chRK-opus.md`.

* `part56_fail`: the failure bound `≤ 1/100` for the function `gLineW` of the surrogate, uniformly in
  the unit vector `v`, `t ∈ [0, C n]`, `ε ∈ [ε_lo, ε_hi]` and admissible `f`.
* `part56_general`: the headline. For `2 ≤ k ≤ d`, `0 < ε_lo ≤ ε_hi`, `ε_hi² < 91/200` and every `C`,
  there are `η > 0` and `n₀ ≥ 100` such that for every `n ≥ n₀` there are a moment program `pm`
  (input `t`, `v`; output one weight per key; cost `≤ onceCost56`, polynomial in `n`) and a line
  program `pg` (input `M`, `f`, `v`, the weights), both with the constants `0` and `1` only, such that
  for every unit `v`, `t ∈ [0, C n]`, `ε ∈ [ε_lo, ε_hi]` and admissible `f`: the failure probability
  over `M` uniform on the coefficient sphere is `≤ 1/100`, and for every counter `k′ ≥ k₀`,
  `cost(pm)/k′ + cost(pg) < baseline n d ε`.

The proof is complete: all 10 wave-1 files (`Part56MC`, `Part56Split`, `Part56Orth`, `Part56RKGErr`,
`Part56RKGFloor`, `Part56Key`, `Part56PropD`, `Part56Low`, `Part56LineProg`, `Part56MomProg`) are proved, and
`#print axioms part56_general` lists only `propext`, `Classical.choice`, `Quot.sound` (audited 2026-10-02).
Do not use `native_decide` or `axiom`.
-/

namespace BstLean.Part56

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD unitOfD)
open BstLean.Part41 (frob Tens TSymm baseline heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part48 (SBLevel sb_level_exists)
open BstLean.Part53 (lemmaR53 gaussPolar53)

/-- **The failure bound** of Theorem RK for the function `gLineW` of the surrogate at
`K = KRK C n (eRK k s ε_lo)`, for some small-ball level `4s > 0`. -/
theorem part56_fail (k d : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) (C εlo εhi : ℝ) (hlo : 0 < εlo) :
    ∃ (s : ℝ) (n0 : ℕ), 0 < s ∧
      ∀ n : ℕ, n0 ≤ n → ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
      ∀ ε : ℝ, εlo ≤ ε → ε ≤ εhi →
      ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
        stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
          ε ^ 2 * varFQ (lawRK n t v) k f0 T (unitOfD Z) <
            (BofQ (lawRK n t v) k f0 T (unitOfD Z) -
              gLineW (surrRK n (KRK C n (eRK k s εlo)) t v) k f0 T v (unitOfD Z)) ^ 2} ≤
          ENNReal.ofReal (1 / 100) := by
  have hd : 1 ≤ d := by omega
  have hk1 : 1 ≤ k := by omega
  obtain ⟨tsb, htsb_pos, hSB⟩ := sb_level_exists (2 * k) (1 / 200) (by norm_num)
  set s : ℝ := tsb / 4 with hs
  have hs0 : 0 < s := by positivity
  have he0 : 0 < eRK k s εlo := by
    unfold eRK etaRK BstLean.Part43.xi43; positivity
  obtain ⟨CK, -, hK⟩ := keyLemma56 d
  obtain ⟨CD, -, hD⟩ := propD56_of d hd CK hK
  have hMC := lemmaMC56
  have hW := propWeights56 d k
  have hSp := propSplit56 d
  have hO := propOrth56 d k hSp
  have hE := propRKGErr56_of d k hMC hSp
  have hF := propRKGFloor56_of d k hE hO hSp
  have hS := propSurr56_of d k C (eRK k s εlo) he0 hO hW
  obtain ⟨Cerr, n1, h1⟩ := propT1_56_of d k hd hk1 C (eRK k s εlo) CD (lemmaR53 k) gaussPolar53
    hW hE hF hD hS
  obtain ⟨cL, nL, hcL, hL⟩ := propLow56 d k hk1 hkd C
  obtain ⟨C2, n2, h2⟩ := propT2_56_of d k hk1 hkd C (1 / 200) tsb hSB htsb_pos gaussPolar53 hE hF
    CD hD cL nL hcL hL
  obtain ⟨n0, hfail⟩ := fail56 d k C εlo εhi s Cerr C2 n1 n2 hlo hs0 h1 h2
  exact ⟨s, n0, hs0, hfail⟩

/-- **Theorem RK** (headline): for `2 ≤ d_f = k ≤ d_M = d`, `0 < ε_lo ≤ ε_hi`, `ε_hi² < 91/200` and
every `C`, there are `η > 0` and `n₀ ≥ 100` such that for every `n ≥ n₀` a charged moment program `pm`
(constants `0`, `1`; it reads `t` and `v` and returns the weights of the surrogate `Q̃ ∝ p_K(t(v·x)²)`,
`K = KRK C n η`) and a line program `pg` (constants `0`, `1`; it reads `M`, `f`, `v` and the weights,
and computes the anchors `u_j = M_j φ_j(v)` and the degree-`k` polynomial `E[B | u]`) satisfy, for
every unit `v ∈ ℝⁿ`, every `t ∈ [0, C n]`, every `ε ∈ [ε_lo, ε_hi]` and every `f` of degree `k` with
`TSymm` and `T_k ≠ 0`:
* `Pr_M{|g(M) − B_{D_{t,v}}(M)| > ε sd_{D_{t,v}} f(m(x))} ≤ 1/100` (`M` uniform on the coefficient
  sphere), and
* `cost(pm)/k′ + cost(pg) < baseline n d ε` for every counter `k′ ≥ k₀ = ⌈cost(pm)/(ν 𝔅(ε))⌉`. -/
theorem part56_general (k d : ℕ) (hk : 2 ≤ k) (hkd : k ≤ d) (C εlo εhi : ℝ) (hlo : 0 < εlo)
    (hlh : εlo ≤ εhi) (hhi : εhi ^ 2 < 91 / 200) :
    ∃ (η : ℝ) (n0 : ℕ), 0 < η ∧ 100 ≤ n0 ∧ ∀ n : ℕ, n0 ≤ n →
      ∃ (pm : Prog (InM56 n) (KeyRK k d)) (pg : Prog (In56 n d k) Unit),
        heavyCount pm = 0 ∧ heavyCount pg = 0 ∧ MomSpec56 pm (KRK C n η) ∧ GSpec56 pg ∧
        (pm.cost : ℝ) ≤ onceCost56 n d k (KRK C n η) ∧
        ∀ v : Fin n → ℝ, UnitV v → ∀ t : ℝ, 0 ≤ t → t ≤ C * n →
        ∀ ε : ℝ, εlo ≤ ε → ε ≤ εhi →
        ∀ (f0 : ℝ) (T : Tens n), TSymm k T → 0 < frob (T k) →
          stdGauss (CoefIdxD n d) {Z | Z ≠ 0 ∧
            ε ^ 2 * varFQ (lawRK n t v) k f0 T (unitOfD Z) <
              (BofQ (lawRK n t v) k f0 T (unitOfD Z) -
                pg.eval (inp56 f0 T (unitOfD Z) v (pm.eval (inRK t v))) ()) ^ 2} ≤
            ENNReal.ofReal (1 / 100) ∧
          ∀ k' : ℕ, k0RK n d pm.cost ε εhi ≤ k' → (pm.cost : ℝ) / k' + pg.cost < baseline n d ε := by
  obtain ⟨s, nf, hs0, hfail⟩ := part56_fail k d hk hkd C εlo εhi hlo
  have hεhi : 0 < εhi := lt_of_lt_of_le hlo hlh
  obtain ⟨nc, hc⟩ := costLine56_lt d k (by omega) hkd εhi hεhi hhi
  have hη0 : 0 < eRK k s εlo := by unfold eRK etaRK BstLean.Part43.xi43; positivity
  refine ⟨eRK k s εlo, max (max nf nc) 100, hη0, le_max_right _ _, fun n hn => ?_⟩
  have hnf : nf ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hnc : nc ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hn100 : 100 ≤ n := le_trans (le_max_right _ _) hn
  obtain ⟨pg, hpg0, hpgs, hpgc⟩ := lineProg56_exists n d k (by omega)
  obtain ⟨pm, hpm0, hpms, hpmc⟩ := momProg56_exists n d k (KRK C n (eRK k s εlo)) (by omega)
  refine ⟨pm, pg, hpm0, hpg0, hpms, hpgs, hpmc, fun v hv t ht0 ht ε hε1 hε2 f0 T hT hTk => ⟨?_, ?_⟩⟩
  · have heval : ∀ M : CoefIdxD n d → ℝ,
        pg.eval (inp56 f0 T M v (pm.eval (inRK t v))) () =
          gLineW (surrRK n (KRK C n (eRK k s εlo)) t v) k f0 T v M :=
      fun M => eval56 pm pg _ hpms hpgs t v ht0 hv f0 T hT M
    simp only [heval]
    exact hfail n hnf v hv t ht0 ht ε hε1 hε2 f0 T hT hTk
  · intro k' hk'
    exact cost56 k (by omega) εhi ε (lt_of_lt_of_le hlo hε1) hε2 hhi pm.cost pg.cost hpgc (hc n hnc) k' hk'

end BstLean.Part56

#print axioms BstLean.Part56.part56_general
