import BstLean.Part282Next
import BstLean.Part282TotalBound

/-!
# Part 282 (C2), the joining theorem

## The model

The straight-line model `RProg` has no indirect addressing. The composed program uses three
kinds of steps, each with a cost:

* a **block**: one `RProg` run on values that are raw inputs (weights, `t`, `a`, draws) or
  outputs of earlier blocks; it costs `RProg.cost`;
* the **node search** `srch = selectNode`: comparisons only; it costs the number of comparisons;
* a **table read** `tread tab g`: the entry `g` of a table that an earlier block computed; it
  costs one operation.

`Cm α = α × ℕ` holds a value and its cost; `Cm.bind` adds the costs.

## The program

`wOut`, `chOut`, `tOut`, `bOut`, `cAOut`, `rdOut`, `gOut`, `nbOut`, `ebOut`, `t2Out`, `tabOut`:
the setup blocks (World pass, `ĉ = W₃b_W`, Agent pass, `c_A = A₃b`, row data, grid, `|b|²`, `√e_b`,
`τ₀²`, and `J_s` node passes). `drawRun`: one draw (latitude block, node search, two table
reads, hit block). `run`: all of these and the output block. Its cost `(run …).2` is the sum of
the costs of the blocks it runs, the comparisons and the reads.

## The theorem

`progOut_eq_run` (every `n ≥ 8000`, every input): `(run …).1 = progOut (statedDesign n) t a k θ σ`.
`run_cost_lt` (every `n ≥ 8000`, `k = draws`): `(run …).2 < 1.0003·2n⁷`.
-/

namespace BstLean.Part282

open BstLean.Cost BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part189 BstLean.Part279
open BstLean.Part272
open BstLean.Part169 (A2 bR nodeS nodeL nodeH Jz tauR)

noncomputable section

/-! ## The model -/

abbrev Cm (α : Type) : Type := α × ℕ

def Cm.bind {α β : Type} (x : Cm α) (f : α → Cm β) : Cm β := ((f x.1).1, x.2 + (f x.1).2)

/-- A block with one output: value and cost. -/
def blk1 {ι : Type} (p : RProg ι Unit) (v : ι → ℝ) : Cm ℝ := (p.eval v (), p.cost)

/-- The node search: the number of comparisons is the cost. -/
def srch (J : ℕ) (L H s : ℝ) : Cm ℕ := selectNode J L H s

/-- A table read at a computed index: one operation (out of range reads `0`). -/
def tread {J : ℕ} (tab : Fin J → ℝ) (g : ℕ) : Cm ℝ := (if h : g < J then tab ⟨g, h⟩ else 0, 1)

/-! ## Small blocks -/

def nbProg (n : ℕ) : RProg (Fin (mA n)) Unit :=
  RProg.ofProg (Prog.sumProd ((List.finRange (mA n)).map fun j => (Arg.inp j, Arg.inp j)))

theorem nbProg_eval {n : ℕ} (b : Fin (mA n) → ℝ) : (nbProg n).eval b () = normSq b := by
  rw [nbProg, RProg.eval_ofProg, eval_sumProd, List.map_map, normSq, Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro j _
  simp [Arg.eval, pow_two]

theorem nbProg_cost (n : ℕ) : (nbProg n).cost = 2 * mA n - 1 := by
  simp [nbProg, cost_sumProd]

def tauSqProg : RProg (Fin 1) Unit := (RExpr.mul (.inp 0) (.inp 0)).prog

theorem tauSqProg_eval (x : ℝ) : tauSqProg.eval ![x] () = x ^ 2 := by
  simp [tauSqProg, pow_two]

theorem tauSqProg_cost : tauSqProg.cost = 1 := by simp [tauSqProg]

/-- Indices of `|ĉ|²` and `|ĉ|` among the outputs of `rdProg`. -/
def ccIx (n : ℕ) : ((((Unit ⊕ Unit) ⊕ Fin n) ⊕ (Unit ⊕ Unit)) ⊕ Fin n) ⊕ (Fin (mA n) × Fin 2) :=
  Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl ()))))
def rIx (n : ℕ) : ((((Unit ⊕ Unit) ⊕ Fin n) ⊕ (Unit ⊕ Unit)) ⊕ Fin n) ⊕ (Fin (mA n) × Fin 2) :=
  Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr ()))))

/-! ## The program -/

section prog

variable (n : ℕ) (hM : 0 < mA n)

def worldP : RProg (WIn (mW n) (2 * n))
    ((((K1 (mW n) ⊕ K2 (JW n)) ⊕ Fin (mW n)) ⊕ Fin (mW n)) ⊕ Unit) :=
  worldProg (mW n) (2 * n) (JW n) (cQ n) (dQ n) (kapA n) (kapB n) (piQ n) n

def wOut (θ : Net3 n) := (worldP n).eval (wVal (θ.1.1, θ.1.2.1))
def tOut (θ : Net3 n) : ℝ := wOut n θ (Sum.inr ())
def chOut (θ : Net3 n) : Fin n → ℝ :=
  (chatProg n (mW n)).eval (Sum.elim (fun i => wOut n θ (Sum.inl (Sum.inr i))) (fun e => θ.1.2.2 e.1 e.2))
def bOut (θ : Net3 n) : Fin (mA n) → ℝ :=
  (agent2 n hM).eval (agVal (chOut n θ) (tOut n θ) θ.2.1.1 θ.2.1.2.1)
def cAOut (θ : Net3 n) : Fin n → ℝ :=
  (chatProg n (mA n)).eval (Sum.elim (bOut n hM θ) (fun e => θ.2.1.2.2 e.1 e.2))
def rdOut (θ : Net3 n) := (rdProg n).eval (Sum.elim (chOut n θ) (fun p => θ.2.1.1 p.1 p.2))
def gOut (θ : Net3 n) := (gridProg n).eval ![rdOut n θ (ccIx n), tOut n θ]
def nbOut (θ : Net3 n) : ℝ := (nbProg n).eval (bOut n hM θ) ()
def ebOut (θ : Net3 n) : ℝ := (ebProg n).eval (bOut n hM θ) ()
def t2Out (θ : Net3 n) : ℝ := tauSqProg.eval ![tOut n θ] ()
def tabOut (θ : Net3 n) (g : Fin (Js n)) : Fin 2 → ℝ :=
  (nodeAny n).eval (nfVal (gOut n θ (Sum.inr (g, Sum.inl ()))) (gOut n θ (Sum.inr (g, Sum.inr ())))
    (fun i => rdOut n θ (Sum.inr (i, 0))) (fun i => rdOut n θ (Sum.inr (i, 1))) θ.2.1.2.1
    (bOut n hM θ) (nbOut n hM θ))

/-- One draw: latitude block, node search, two table reads, hit block. -/
def drawRun (θ : Net3 n) (t : ℝ) (d : DrawSp n) : Cm ℝ :=
  Cm.bind (blk1 (latProg (n - 1)) (latVal (rdOut n θ (rIx n)) (tOut n θ) (t2Out n θ) d.1.1 d.1.2))
    fun s => Cm.bind (srch (Js n) (gOut n θ (Sum.inl 0)) (gOut n θ (Sum.inl 1)) s)
    fun g => Cm.bind (tread (fun g => tabOut n hM θ g 0) g)
    fun f => Cm.bind (tread (fun g => tabOut n hM θ g 1) g)
    fun ω => blk1 (hitProg n (mF n)) (hitVal f ω (ebOut n hM θ) t (cAOut n hM θ) d.2 θ.2.2)

/-- The cost of the setup blocks. -/
def setupCost : ℕ :=
  (worldP n).cost + (chatProg n (mW n)).cost + (agent2 n hM).cost + (chatProg n (mA n)).cost +
    (rdProg n).cost + (gridProg n).cost + (nbProg n).cost + (ebProg n).cost + tauSqProg.cost +
    Js n * (nodeAny n).cost

/-- **The composed program.** -/
def run (t a : ℝ) (k : ℕ) (θ : Net3 n) (σ : Fin k → DrawSp n) : Cm ℝ :=
  ((outProg k).eval (oVal a (fun i => (drawRun n hM θ t (σ i)).1)) (),
    setupCost n hM + ∑ i, (drawRun n hM θ t (σ i)).2 + (outProg k).cost)

end prog

/-! ## The value -/

section value

variable {n : ℕ} (hM : 0 < mA n) (θ : Net3 n)


theorem wOut_b (i : Fin (mW n)) : wOut n θ (Sum.inl (Sum.inr i)) = bWp (θ.1.1, θ.1.2.1) i :=
  (bWp_eq_worldProg _ i).symm

theorem tOut_eq : tOut n θ = tau0p (ret (statedDesign n).toCentres θ).1.1 := by
  have h := tau0p_eq_worldProg (n := n) (θ.1.1, θ.1.2.1)
  unfold tOut wOut worldP
  rw [← h]
  rfl

theorem chOut_eq : chOut n θ = ((ret (statedDesign n).toCentres θ)).1.2 := by
  funext i
  have h : (fun i => wOut n θ (Sum.inl (Sum.inr i))) = bWp (θ.1.1, θ.1.2.1) :=
    funext (wOut_b θ)
  rw [chOut, h, chatProg_eval]
  rfl

theorem bOut_eq : bOut n hM θ = bR (ret (statedDesign n).toCentres θ) := by
  funext j
  rw [bOut, chOut_eq, tOut_eq]
  exact (bAp_eq_agent2 hM ((ret (statedDesign n).toCentres θ)).1 ((ret (statedDesign n).toCentres θ)).2.1.1 j).symm

theorem cAOut_eq : cAOut n hM θ = ((ret (statedDesign n).toCentres θ)).2.1.2 := by
  funext i
  rw [cAOut, bOut_eq, chatProg_eval]
  rfl

theorem rdOut_eq : rdOut n θ = (rdProg n).eval (rdVal (ret (statedDesign n).toCentres θ)) := by
  rw [rdOut, chOut_eq]; rfl

theorem rdOut_cc : rdOut n θ (ccIx n) = normSq ((ret (statedDesign n).toCentres θ)).1.2 := by
  rw [rdOut_eq]
  simp only [ccIx, rdProg, s4, s3, s2, RProg.eval_ext_inl, s1_eval, Sum.elim_inl]

theorem rdOut_r : rdOut n θ (rIx n) = √(normSq ((ret (statedDesign n).toCentres θ)).1.2) := by
  rw [rdOut_eq]
  simp only [rIx, rdProg, s4, s3, s2, RProg.eval_ext_inl, s1_eval, Sum.elim_inr]

theorem gOut_eq : gOut n θ = (gridProg n).eval (gVal (ret (statedDesign n).toCentres θ)) := by
  rw [gOut, rdOut_cc, tOut_eq]; rfl

theorem tabOut_eq (g : Fin (Js n)) :
    tabOut n hM θ g 0 = passFSt (ret (statedDesign n).toCentres θ) g ∧ tabOut n hM θ g 1 = passWSt (ret (statedDesign n).toCentres θ) g := by
  have hs : gOut n θ (Sum.inr (g, Sum.inl ())) = nodeS (ret (statedDesign n).toCentres θ) g := by rw [gOut_eq, gridProg_s]
  have hw : gOut n θ (Sum.inr (g, Sum.inr ())) = √(1 - nodeS (ret (statedDesign n).toCentres θ) g ^ 2) := by
    rw [gOut_eq, gridProg_w]
  have ha : (fun i => rdOut n θ (Sum.inr (i, 0))) = alphaE (ret (statedDesign n).toCentres θ) := by
    funext i; rw [rdOut_eq, rdProg_alpha]
  have hk : (fun i => rdOut n θ (Sum.inr (i, 1))) = kappaE (ret (statedDesign n).toCentres θ) := by
    funext i; rw [rdOut_eq, rdProg_kappa]
  have hnb : nbOut n hM θ = normSq (bR (ret (statedDesign n).toCentres θ)) := by rw [nbOut, nbProg_eval, bOut_eq]
  unfold tabOut
  rw [hs, hw, ha, hk, hnb, bOut_eq]
  exact ⟨(passFSt_eq_nodeAny (ret (statedDesign n).toCentres θ) g).symm, (passWSt_eq_nodeAny (ret (statedDesign n).toCentres θ) g).symm⟩

theorem drawRun_eq (hJ : 1 ≤ Js n) (hn1 : 1 ≤ n) (t : ℝ) (d : DrawSp n) :
    (drawRun n hM θ t d).1 = hitFn (statedDesign n) t ((ret (statedDesign n).toCentres θ), d) := by
  have hlat : (latProg (n - 1)).eval (latVal (rdOut n θ (rIx n)) (tOut n θ) (t2Out n θ) d.1.1 d.1.2) () =
      latitude (√(normSq ((ret (statedDesign n).toCentres θ)).1.2)) (tau0p ((ret (statedDesign n).toCentres θ)).1.1) d.1 := by
    rw [rdOut_r, t2Out, tauSqProg_eval, tOut_eq, latProg_eval]
    rfl
  have hL : gOut n θ (Sum.inl 0) = nodeL (ret (statedDesign n).toCentres θ) := by rw [gOut_eq, gridProg_LHD]; rfl
  have hH : gOut n θ (Sum.inl 1) = nodeH (ret (statedDesign n).toCentres θ) := by rw [gOut_eq, gridProg_LHD]; rfl
  set g := nodeIdx (Js n) (nodeL (ret (statedDesign n).toCentres θ)) (nodeH (ret (statedDesign n).toCentres θ)) (latitude (√(normSq ((ret (statedDesign n).toCentres θ)).1.2)) (tau0p ((ret (statedDesign n).toCentres θ)).1.1) d.1)
    with hg
  have hsel : (selectNode (Js n) (gOut n θ (Sum.inl 0)) (gOut n θ (Sum.inl 1))
      ((latProg (n - 1)).eval (latVal (rdOut n θ (rIx n)) (tOut n θ) (t2Out n θ) d.1.1 d.1.2) ())).1 = g := by
    rw [hL, hH, hlat, selectNode_eq hJ]
  have hlt : g < Js n := by
    have : g ≤ Js n - 1 := by rw [hg]; unfold nodeIdx; exact min_le_left _ _
    omega
  have hread : ∀ j : Fin 2, (tread (fun g => tabOut n hM θ g j) g).1 =
      tabOut n hM θ ⟨g, hlt⟩ j := by
    intro j; simp [tread, hlt]
  simp only [drawRun, Cm.bind, blk1, srch]
  rw [hsel, hread, hread, (tabOut_eq hM θ ⟨g, hlt⟩).1, (tabOut_eq hM θ ⟨g, hlt⟩).2,
    ebOut, ebProg_eval, bOut_eq, cAOut_eq]
  rw [statedDesign, hitFn_eq_hitProg]
  rfl

/-- **The joining theorem, value.** For every `n ≥ 8000` and every input, the composed program
returns `progOut (statedDesign n)`. -/
theorem progOut_eq_run (hn : 8000 ≤ n) (t a : ℝ) (k : ℕ) (σ : Fin k → DrawSp n) :
    (run n hM t a k θ σ).1 = progOut (statedDesign n) t a k θ σ := by
  rw [progOut_eq_outProg]
  simp only [run]
  exact congrArg (fun x => (outProg k).eval (oVal a x) ())
    (funext fun i => drawRun_eq hM θ (by unfold Js; omega) (by omega) t (σ i))

end value

end

end BstLean.Part282

/-- info: 'BstLean.Part282.progOut_eq_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.progOut_eq_run
