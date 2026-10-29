import BstLean.Part288Search
import BstLean.Part282JoinCost

/-!
# Part 288: the joined program with the full search cost

`drawRun'` replaces the Part 282 search with `selectNode'`. All setup blocks, table reads,
latitude and hit blocks, and the output block are the same. `run'` sums the new draw costs.
The Part 189 search reserve pays for the real arithmetic and index/control operations.
`progOut_run'` gives the value equality and strict cost bound for every `n ≥ 8000` and input.
-/

namespace BstLean.Part288

open BstLean.Cost BstLean.Part130 BstLean.Part157 BstLean.Part189 BstLean.Part272
open BstLean.Part282 BstLean.Part279

noncomputable section

/-- One draw with the fully counted search. The setup outputs are retained registers. -/
def drawRun' (n : ℕ) (hM : 0 < mA n) (θ : Net3 n) (t : ℝ) (d : DrawSp n) : Cm ℝ :=
  Cm.bind (blk1 (latProg (n - 1)) (latVal (rdOut n θ (rIx n)) (tOut n θ) (t2Out n θ) d.1.1 d.1.2))
    fun s => Cm.bind (selectNode' (Js n) (gOut n θ (Sum.inl 0)) (gOut n θ (Sum.inl 1)) s)
    fun g => Cm.bind (tread (fun g => tabOut n hM θ g 0) g)
    fun f => Cm.bind (tread (fun g => tabOut n hM θ g 1) g)
    fun ω => blk1 (hitProg n (mF n)) (hitVal f ω (ebOut n hM θ) t (cAOut n hM θ) d.2 θ.2.2)

/-- The composed program, with the existing setup and the fully counted draws. -/
def run' (n : ℕ) (hM : 0 < mA n) (t a : ℝ) (k : ℕ) (θ : Net3 n)
    (σ : Fin k → DrawSp n) : Cm ℝ :=
  ((outProg k).eval (oVal a (fun i => (drawRun' n hM θ t (σ i)).1)) (),
    setupCost n hM + ∑ i, (drawRun' n hM θ t (σ i)).2 + (outProg k).cost)

theorem drawRun'_eq_old {n : ℕ} (hM : 0 < mA n) (θ : Net3 n) (t : ℝ) (d : DrawSp n) :
    (drawRun' n hM θ t d).1 = (drawRun n hM θ t d).1 := by
  simp only [drawRun', drawRun, Cm.bind, srch, selectNode'_eq_selectNode]

theorem progOut_eq_run' {n : ℕ} (hn : 8000 ≤ n) (hM : 0 < mA n)
    (t a : ℝ) (k : ℕ) (θ : Net3 n) (σ : Fin k → DrawSp n) :
    (run' n hM t a k θ σ).1 = progOut (statedDesign n) t a k θ σ := by
  have he : (run' n hM t a k θ σ).1 = (Part282.run n hM t a k θ σ).1 := by
    simp only [run', Part282.run, drawRun'_eq_old]
  exact he.trans (progOut_eq_run hM θ hn t a k σ)

/-- The search term is its full cost, bounded by the named Part 189 reserve. -/
theorem drawRun'_cost_le {n : ℕ} (hn : 8000 ≤ n) (hM : 0 < mA n)
    (θ : Net3 n) (t : ℝ) (d : DrawSp n) :
    (drawRun' n hM θ t d).2 ≤ (latProg (n - 1)).cost + searchPrice n + 2 +
      (hitProg n (mF n)).cost := by
  simp only [drawRun', Cm.bind, blk1, tread]
  have := selectNode'_le_searchPrice hn (gOut n θ (Sum.inl 0)) (gOut n θ (Sum.inl 1))
    ((latProg (n - 1)).eval (latVal (rdOut n θ (rIx n)) (tOut n θ) (t2Out n θ) d.1.1 d.1.2) ())
  omega

/-- The counted draws retain the five-operation slack used to pay for final output work. -/
theorem draws'_cost_le {n : ℕ} (hn : 8000 ≤ n) (hM : 0 < mA n) (t : ℝ) (θ : Net3 n)
    (σ : Fin draws → DrawSp n) :
    ∑ i, (drawRun' n hM θ t (σ i)).2 + draws * 5 ≤ draws * drawAllowance n := by
  have hn1 : 1 ≤ n := by omega
  have hdc : ∀ i, (drawRun' n hM θ t (σ i)).2 + 5 ≤ drawAllowance n := by
    intro i
    have h := drawRun'_cost_le hn hM θ t (σ i)
    have hs := searchPrice_le hn
    have hc := classifierReference_cost (n := n) hn1
    rw [latProg_cost, hitProg_cost] at h
    rw [mlpProg_cost_eq] at hc
    unfold drawAllowance
    omega
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hdc i)
  rw [Finset.sum_add_distrib] at this
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using this

/-- The cost of the composed program is the sum of the executed blocks and counted draws. -/
theorem run'_cost_eq {n : ℕ} (hM : 0 < mA n) (t a : ℝ) (k : ℕ) (θ : Net3 n)
    (σ : Fin k → DrawSp n) :
    (run' n hM t a k θ σ).2 = (worldP n).cost + (chatProg n (mW n)).cost + (agent2 n hM).cost +
      (chatProg n (mA n)).cost + (rdProg n).cost + (gridProg n).cost + (nbProg n).cost +
      (ebProg n).cost + tauSqProg.cost + Js n * (nodeAny n).cost +
      ∑ i, (drawRun' n hM θ t (σ i)).2 + (outProg k).cost := rfl

/-- The existing setup estimates and the repaired draw estimate fit the same schedule. -/
theorem run'_cost_le {n : ℕ} (hn : 8000 ≤ n) (hM : 0 < mA n) (t a : ℝ) (θ : Net3 n)
    (σ : Fin draws → DrawSp n) : (run' n hM t a draws θ σ).2 ≤ (orderedWork n).cost := by
  have h1 := draws'_cost_le hn hM t θ σ
  have h2 := setup_cost_le hn hM
  have h3 := nodes_cost_le hn
  have h4 := world_chat_le (by omega : 2 ≤ n)
  have h5 := orderedWork_entries n
  have h6 := outProg_cost draws
  have hd : 8 ≤ draws := by unfold draws; norm_num
  rw [run'_cost_eq]
  generalize ∑ i, (drawRun' n hM θ t (σ i)).2 = D at h1 ⊢
  generalize (worldP n).cost = a1 at h4 ⊢
  generalize (chatProg n (mW n)).cost = a2 at h4 ⊢
  generalize (agent2 n hM).cost = a3 at h2 ⊢
  generalize (chatProg n (mA n)).cost = a4 at h2 ⊢
  generalize (rdProg n).cost = a5 at h2 ⊢
  generalize (gridProg n).cost = a6 at h2 ⊢
  generalize (nbProg n).cost = a7 at h2 ⊢
  generalize (ebProg n).cost = a8 at h2 ⊢
  generalize tauSqProg.cost = a9 at h2 ⊢
  generalize Js n * (nodeAny n).cost = a10 at h3 ⊢
  generalize (outProg draws).cost = a11 at h6 ⊢
  generalize (orderedWork n).cost = W at h5 ⊢
  generalize (worldTail n).cost = b1 at h4 h5
  generalize (agentWork n).cost = b2 at h2 h5
  generalize setupAllowance n = b3 at h2 h5
  generalize (gridWork n).cost = b4 at h3 h5
  generalize draws * drawAllowance n = b5 at h1 h5
  generalize draws = K at h1 h5 h6 hd ⊢
  omega

theorem run'_cost_lt {n : ℕ} (hn : 8000 ≤ n) (hM : 0 < mA n) (t a : ℝ) (θ : Net3 n)
    (σ : Fin draws → DrawSp n) :
    ((run' n hM t a draws θ σ).2 : ℝ) < 1.0003 * (2 * (n : ℝ) ^ 7) := by
  have h : ((run' n hM t a draws θ σ).2 : ℝ) ≤ ((orderedWork n).cost : ℝ) := by
    exact_mod_cast run'_cost_le hn hM t a θ σ
  have h2 := orderedWork_lt_8000 hn
  have h3 : (1.0003 : ℝ) = 10003 / 10000 := by norm_num
  rw [h3]
  exact lt_of_le_of_lt h h2

/-- For every dimension at least 8000 and every input, the program returns the stated output
and costs less than `1.0003 * 2n^7`, including the search arithmetic and control operations. -/
theorem progOut_run' {n : ℕ} (hn : 8000 ≤ n) (t a : ℝ) (θ : Net3 n)
    (σ : Fin draws → DrawSp n) :
    ∃ hM : 0 < mA n, (run' n hM t a draws θ σ).1 = progOut (statedDesign n) t a draws θ σ ∧
      ((run' n hM t a draws θ σ).2 : ℝ) < 1.0003 * (2 * (n : ℝ) ^ 7) := by
  have hM : 0 < mA n := by unfold mA; positivity
  exact ⟨hM, progOut_eq_run' hn hM t a draws θ σ, run'_cost_lt hn hM t a θ σ⟩

end
end BstLean.Part288
