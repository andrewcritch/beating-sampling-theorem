import BstLean.Part59Defs
import BstLean.Part59Prog_Existence
import BstLean.Part59Prog_Tree
import BstLean.Part59Prog_Constants
import BstLean.Part59Prog_Table

/-!
# Part 59, wave 1: The program `g₀` by the nested tree with heat-adjusted weights (Prop C)

Specification: `delegations/answers/p59-spec-opus.md` §3.2. Source: `omDL2-opus-prover.md` §2, Prop C.

Suggested route (the source's four steps).
1. Constants from `0` and `1` (no other constant may appear: `heavyCount pg = 0`): `n` by doubling
   (`≤ 2⌊log₂ n⌋` operations), the integers `j ≤ d` (`j = (j−1) + 1`), `N = Π_{j≤d}(n+j)/j`,
   `𝒟 = nN` (equal to `DD n d = card (CoefIdxD n d)`; use Part 36/41/53 card lemmas, for example the
   ones behind `Part53Cost_Constants.lean`), `c₀ − 1 = Σ_{1≤j≤d} 1/j!`, `a = (c₀−1)/𝒟 = aH n d`, and
   `e·a` for `1 ≤ e ≤ k−1`. Within `2⌊log₂ n⌋ + 6d + 3k + 10`.
2. Table `q_e(y_i; a)`, `1 ≤ i ≤ n`, `2 ≤ e ≤ k` by `q_{e+1} = y_i q_e + (e·a) q_{e−1}`
   (3 operations each; `y_i = M_{(0, ∅, i)}`, an input of the constant column): `3n(k−1)`.
3. The nested tree on `Mono n k`: the parent of `α ≠ 0` removes **all** of its last variable
   (`α′ = α − α_j e_j`, `j = max{i : α_i > 0}`), the edge weight is `q_{α_j}(y_j)`. `S(β) = c_β +
   Σ_children q_{γ_j}(y_j) S(γ)`, `S(0) = g0Q`. `C(n+k,k) − 1` edges, 2 operations each.
   An induction on `n` as in `Part59Horner` works: `G_{n+1,k} = Σ_{e=0}^{k} q_e(y_n) G_{n,k−e}(c|_{α_n = e})`.
4. Output `S(0)`.
* `ConstColOnly59 pg`: the only `M`-inputs used are `y_i = M ⟨0, (Sym.nil, i)⟩`.
* `qH 0 = 1`, so absent variables contribute the factor `1` in `g0Q`.
* Part 53's `Part53Cost_Program.lean`, `Part53Cost_Constants.lean` build similar constants from `0` and
  `1`; reuse them where possible.

Replace each `sorry` by a proof. Do not edit the statements or `Part59Defs.lean`. Do not use
`native_decide` or `axiom` anywhere. This file imports `Part59Defs` only; a prover may also import
finished files of Parts 29–58, but no other Part 59 wave-1 file. Name private helpers with the suffix
`59x` or make them `private`, so that `Part59Final` does not see a name clash.
-/

namespace BstLean.Part59

set_option backward.isDefEq.respectTransparency false

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM contr trL frob IsSymmT Tens TSymm fval Pn varU sdU heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (sg c0 aH g0 heatA fvA Ncirc LemmaR53 GaussPolar53)

variable {n d : ℕ}

/-- **Prop C** (program and cost): one program from `0` and `1` reads the constant column of `M` and the
coefficients of `f`, computes `g0Q`, and costs at most `costG59`. -/
theorem prog59_exists (n d k : ℕ) (hn : 1 ≤ n) (hd : 1 ≤ d) (hk : 1 ≤ k) :
    ∃ pg : Prog (In59 n d k) Unit, heavyCount pg = 0 ∧ ConstColOnly59 pg ∧
      (∀ v : In59 n d k → ℝ, pg.eval v () = g0Q n d k (cv59 v) (Mv59 v)) ∧
      (pg.cost : ℝ) ≤ costG59 n d k := by
  classical
  let ι := ProgAux59x.SmallIn59x n k
  obtain ⟨pa, hpa, hea, hca⟩ := ConstantAux59x.a_constant59x ι n d hn
  let pm : Prog ι (Fin (k + 1)) := pa.bind ((TableAux59x.muls59x k k).mapIn Sum.inr)
  have hpm : BstLean.Part53.CostAux.Clean pm :=
    BstLean.Part53.CostAux.clean_bind hpa
      (BstLean.Part53.CostAux.clean_mapIn _ (TableAux59x.muls_clean59x k k))
  have hem : ∀ v e, pm.eval v e = (e.val : ℝ) * aH n d := by
    intro v e
    rw [eval_bind, eval_mapIn]
    change (TableAux59x.muls59x k k).eval (fun _ => pa.eval v ()) e = _
    rw [hea, TableAux59x.muls_eval59x k k _ e (by have := e.isLt; omega)]
  have hcm : pm.cost ≤ 2 * Nat.log 2 n + 6 * d + 2 + k := by
    rw [cost_bind, cost_mapIn]
    have := TableAux59x.muls_cost59x k k
    omega
  let pq := pm.bind (TableAux59x.table59x n k (k - 1))
  have hpq : BstLean.Part53.CostAux.Clean pq :=
    BstLean.Part53.CostAux.clean_bind hpm (TableAux59x.table_clean59x n k (k - 1))
  have heq : ∀ v (s : TableAux59x.TableKey59x n k), pq.eval v s =
      qH s.2.val (v (.inl s.1)) (aH n d) := by
    intro v s
    rw [eval_bind]
    exact TableAux59x.table_eval59x n k (k - 1) _ (aH n d)
      (fun e => hem v e) s (by have := s.2.isLt; omega)
  obtain ⟨pt, hpt, hct, het⟩ := TreeAux59x.weighted_monomials_exists59x n k
  let toTree : TreeAux59x.WeightIn59x n k → ι ⊕ TableAux59x.TableKey59x n k :=
    Sum.elim Sum.inr (fun α => Sum.inl (Sum.inr α))
  let p : Prog ι Unit := pq.bind (pt.mapIn toTree)
  have hp : BstLean.Part53.CostAux.Clean p :=
    BstLean.Part53.CostAux.clean_bind hpq (BstLean.Part53.CostAux.clean_mapIn _ hpt)
  have hep : ∀ v : ι → ℝ, p.eval v () =
      ∑ α : Mono n k, v (.inr α) *
        ∏ i : Fin n, qH (α.2.val.count i) (v (.inl i)) (aH n d) := by
    intro v
    rw [eval_bind, eval_mapIn]
    rw [het _ (by
      intro i
      change pq.eval v (i, 0) = 1
      rw [heq]
      rfl)]
    apply Finset.sum_congr rfl
    intro α hα
    change v (.inr α) * TreeAux59x.weight59x
      (fun i e => pq.eval v (i, e)) α = _
    simp only [TreeAux59x.weight59x, heq]
  have hcp : p.cost ≤ 2 * Nat.log 2 n + 6 * d + 2 + k +
      3 * n * (k - 1) + 2 * ((n + k).choose k - 1) := by
    rw [cost_bind, cost_mapIn, hct]
    have hcq := TableAux59x.table_cost59x n k (k - 1)
    have hbind : pq.cost = pm.cost + (TableAux59x.table59x n k (k - 1)).cost := cost_bind _ _
    omega
  refine ⟨p.mapIn (ProgAux59x.embed59x n d k), ?_,
    ProgAux59x.mapIn_constCol59x n d k p, ?_, ?_⟩
  · rw [BstLean.Part53.CostAux.heavy_mapIn]
    exact BstLean.Part53.CostAux.clean_heavy hp
  · intro v
    rw [eval_mapIn, hep]
    rfl
  · rw [cost_mapIn]
    have hchoose : 1 ≤ (n + k).choose k := Nat.choose_pos (by omega)
    have hcpR : (p.cost : ℝ) ≤ 2 * (Nat.log 2 n : ℝ) + 6 * (d : ℝ) + 2 + (k : ℝ) +
        3 * (n : ℝ) * ((k - 1 : ℕ) : ℝ) + 2 * (((n + k).choose k : ℝ) - 1) := by
      exact_mod_cast hcp
    unfold costG59
    nlinarith

end BstLean.Part59
