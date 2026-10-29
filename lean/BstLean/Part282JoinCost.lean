import BstLean.Part282Join

/-!
# Part 282 (C2), the joining theorem: the cost

`run_cost_le` (every `n ≥ 8000`, `k = draws`): the cost of the composed program `run` is at most
the Part 189 schedule `orderedWork n`; `run_cost_lt`: it is `< 1.0003·2n⁷`.
`progOut_run` combines this with `progOut_eq_run`.
-/

namespace BstLean.Part282

open BstLean.Cost BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part189 BstLean.Part279
open BstLean.Part272
open BstLean.Part169 (Jz)

noncomputable section

theorem Todd_le {n : ℕ} : Todd n ≤ BstLean.Part189.oddAsinLength n := by
  have h := BstLean.Part189.seriesLength_spec 4 (10 ^ 110 * n ^ 20) (by norm_num)
  exact Nat.sInf_le ⟨h.1, h.2⟩

theorem agent2_cost {n : ℕ} (hn : 1 ≤ n) (hM : 0 < mA n) :
    (agent2 n hM).cost ≤ 2 * n ^ 4 + 18 * n ^ 3 + 20 * n ^ 2 + 2 * n + 10 := by
  have hrow : ∀ i, (rowAProgA n i).cost = 4 * n + 1 := by
    intro i
    simp [rowAProgA, mRowProg, rRowProg, RProg.cost_parV, Fin.sum_univ_succ, rowAE, cost_sumProd]
    omega
  have hstep : ∀ j q, (atomStep (mA n) n j q).cost = 7 := by
    intro j q
    simp [atomStep, RProg.cost_parV, Fin.sum_univ_succ, accE, rAtomE, wrE]
  have hloop2 : ∀ j, (atomLoop (mA n) n j).cost = 7 * (n + 1) := by
    intro j
    rw [atomLoop, RProg.cost_iter_const _ _ _ 7 (hstep j)]
    simp; ring
  have hloop : ∀ i, ((atomLoop (mA n) n i).mapIn (sig1 n i)).cost = 7 * (n + 1) := by
    intro i; rw [RProg.cost_mapIn, hloop2]
  have hpR : (pR n).cost = mA n * (4 * n + 1) := by
    rw [pR, RProg.cost_parL2, list_sum_const _ _ _ hrow]; simp
  have hpL1 : (pL1 n).cost = (pR n).cost + mA n * (7 * (n + 1)) := by
    rw [pL1, RProg.cost_ext, RProg.cost_parL2, list_sum_const _ _ _ hloop]; simp
  have hu : (uProg (mA n) n).cost = (mA n - 1) + (2 * mA n - 1) + 5 := by
    simp [uProg, sumEProg, sumAProg, cost_sumArgs, cost_sumProd, uE]
  have hh : (hProg (mA n)).cost = mA n * (2 * mA n - 1) := by
    simp [hProg, mulVecProg_cost]
  have hpB : (pB (mA n) n).cost = (uProg (mA n) n).cost + (hProg (mA n)).cost +
      mA n * (7 * (n + 1)) := by
    rw [pB, RProg.cost_ext, pUH, RProg.cost_ext, RProg.cost_mapIn, RProg.cost_parL2,
      list_sum_const _ _ _ hloop2]; simp
  have hρ : (rhoAProg n).cost = (2 * n - 1) + 4 := by
    simp [rhoAProg, ccAProg, cost_sumProd]
  have hall : (agent2 n hM).cost = (pL1 n).cost + (pB (mA n) n).cost + (rhoAProg n).cost +
      mA n := by
    rw [agent2, RProg.cost_bind, RProg.cost_ext, pAll, RProg.cost_ext, RProg.cost_mapIn,
      RProg.cost_mapIn, RProg.cost_parV]
    simp
  rw [hall, hpL1, hpR, hpB, hu, hh, hρ]
  simp only [mA]
  have h1 : 2 * n ^ 2 - 1 ≤ 2 * n ^ 2 := Nat.sub_le _ _
  have h2 : n ^ 2 * (2 * n ^ 2 - 1) ≤ n ^ 2 * (2 * n ^ 2) := Nat.mul_le_mul_left _ h1
  have h3 : n ^ 2 - 1 ≤ n ^ 2 := Nat.sub_le _ _
  have h4 : 2 * n - 1 ≤ 2 * n := Nat.sub_le _ _
  nlinarith [h1, h2, h3, h4]

theorem rowAny_le {n : ℕ} (hn : 8000 ≤ n) : (rowAny n).cost + 11 ≤ (sphereRowWork n).cost := by
  rw [rowAny_cost]
  by_cases he : n % 2 = 0
  · rw [if_pos he, sphereRowWork_even he]; omega
  · rw [if_neg he, sphereRowWork_odd he]
    have := Todd_le (n := n)
    omega

theorem nodeAny_le {n : ℕ} (hn : 8000 ≤ n) :
    (nodeAny n).cost + 4 * n ^ 2 ≤ (nodeWork n).cost := by
  have h := rowAny_le hn
  have hm := Nat.mul_le_mul_left (n ^ 2) h
  have h6 : 6 ≤ n ^ 2 := by nlinarith
  have hJ : Jz n = conditionalSigns n := rfl
  rw [nodeAny_cost (by omega), nodeWork_cost, hJ]
  have e : n ^ 2 + (n ^ 2 - 1) = 2 * n ^ 2 - 1 := by
    have : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  rw [e]
  nlinarith [hm, h6]

theorem world_chat_le {n : ℕ} (hn : 2 ≤ n) :
    (worldP n).cost + (chatProg n (mW n)).cost ≤ (worldTail n).cost := by
  have hm := one_le_mW (by omega : 1 ≤ n)
  have hJ : JW n = worldSigns n := rfl
  rw [worldP, worldProg_cost _ _ _ _ _ _ _ _ _ hm (by omega), hJ, chatProg_cost]
  simp only [worldTail, Work.cost, dotWork_cost, matVecWork_cost, binomialSetup_cost,
    sharedMean_cost, ops_cost, List.length_cons, List.length_nil]
  have e1 : 2 * n + (2 * n - 1) = 4 * n - 1 := by omega
  have e2 : mW n + (mW n - 1) = 2 * mW n - 1 := by omega
  have e3 : 2 * (2 * n) + 1 = 4 * n - 1 + 2 := by omega
  rw [e1, e2, e3]
  have h7 := worldSigns_ge (by omega : 1 ≤ n)
  simp only [Nat.zero_add, Nat.reduceAdd, mul_one] at *
  omega

theorem drawRun_cost_le {n : ℕ} (hM : 0 < mA n) (θ : Net3 n) (t : ℝ) (d : DrawSp n) :
    (drawRun n hM θ t d).2 ≤ (latProg (n - 1)).cost + (Nat.log 2 (Js n) + 2) + 2 +
      (hitProg n (mF n)).cost := by
  simp only [drawRun, Cm.bind, blk1, srch, tread]
  have := selectNode_count (Js n) (gOut n θ (Sum.inl 0)) (gOut n θ (Sum.inl 1))
    ((latProg (n - 1)).eval (latVal (rdOut n θ (rIx n)) (tOut n θ) (t2Out n θ) d.1.1 d.1.2) ())
  omega

/-! ## The cost, block by block -/

/-- The draws: each draw costs at most its allowance minus 5. -/
theorem draws_cost_le {n : ℕ} (hn : 8000 ≤ n) (hM : 0 < mA n) (t : ℝ) (θ : Net3 n)
    (σ : Fin draws → DrawSp n) :
    ∑ i, (drawRun n hM θ t (σ i)).2 + draws * 5 ≤ draws * drawAllowance n := by
  have hn1 : 1 ≤ n := by omega
  have hdc : ∀ i, (drawRun n hM θ t (σ i)).2 + 5 ≤ drawAllowance n := by
    intro i
    have h := drawRun_cost_le hM θ t (σ i)
    have hl := log_gridNodes_lt n
    have hc := classifierReference_cost (n := n) hn1
    rw [latProg_cost, hitProg_cost] at h
    rw [mlpProg_cost_eq] at hc
    unfold drawAllowance
    simp only [Js, gridNodes] at h hl
    omega
  have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hdc i)
  rw [Finset.sum_add_distrib] at this
  simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] using this

/-- The Agent pass, `c_A`, the row data, the grid, `|b|²`, `√e_b`, `τ₀²`: within the Agent entry
and the setup entry. -/
theorem setup_cost_le {n : ℕ} (hn : 8000 ≤ n) (hM : 0 < mA n) :
    (agent2 n hM).cost + (chatProg n (mA n)).cost + (rdProg n).cost + (gridProg n).cost +
      (nbProg n).cost + (ebProg n).cost + tauSqProg.cost ≤
        (agentWork n).cost + setupAllowance n := by
  have hn1 : 1 ≤ n := by omega
  have hA := agent2_cost hn1 hM
  have hA1 := agentWork_cost hn1
  have hA2 := agentReference_cost hn1
  have hP := passProg_cost (n := n) (m := n ^ 2) hn1 (Nat.one_le_pow _ _ hn1) n
  have hAW : (agentWork n).cost = (passProg n (n ^ 2) n).cost + 2 * n := by omega
  rw [chatProg_cost, nbProg_cost, ebProg_cost n hn1, rdProg_cost hn1, gridProg_cost,
    tauSqProg_cost, hAW, hP]
  generalize (agent2 n hM).cost = A at hA ⊢
  simp only [setupAllowance, gridNodes, Js, mA]
  have h3 : n ^ 2 ≤ n ^ 3 := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : n ^ 3 ≤ n ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
  have h5 : n ≤ n ^ 2 := by nlinarith
  have h6 : n * (2 * n ^ 2 - 1) ≤ 2 * n ^ 3 := by
    have : n * (2 * n ^ 2 - 1) ≤ n * (2 * n ^ 2) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    nlinarith
  have h7 : 12 * n - 2 ≤ 12 * n := Nat.sub_le _ _
  have h8 : 2 * n ^ 2 - 1 ≤ 2 * n ^ 2 := Nat.sub_le _ _
  nlinarith [hA, h3, h4, h5, h6, h7, h8]

/-- The `J_s` node passes: within the grid entry. -/
theorem nodes_cost_le {n : ℕ} (hn : 8000 ≤ n) :
    Js n * (nodeAny n).cost ≤ (gridWork n).cost := by
  have hN := nodeAny_le hn
  have h : (nodeAny n).cost ≤ (nodeWork n).cost := by omega
  simp only [gridWork, Work.cost, Js, gridNodes]
  exact Nat.mul_le_mul_left _ h

/-- The schedule, entry by entry. -/
theorem orderedWork_entries (n : ℕ) :
    (orderedWork n).cost = 2 * n + (worldTail n).cost + (agentWork n).cost + setupAllowance n +
      (gridWork n).cost + draws * drawAllowance n + draws + 4 := by
  have hcost := orderedWork_cost n
  rw [worldWork_eq] at hcost
  simp only [Work.cost] at hcost
  omega

/-- The cost of `run`, block by block (definitional). -/
theorem run_cost_eq {n : ℕ} (hM : 0 < mA n) (t a : ℝ) (k : ℕ) (θ : Net3 n)
    (σ : Fin k → DrawSp n) :
    (run n hM t a k θ σ).2 = (worldP n).cost + (chatProg n (mW n)).cost + (agent2 n hM).cost +
      (chatProg n (mA n)).cost + (rdProg n).cost + (gridProg n).cost + (nbProg n).cost +
      (ebProg n).cost + tauSqProg.cost + Js n * (nodeAny n).cost +
      ∑ i, (drawRun n hM θ t (σ i)).2 + (outProg k).cost := rfl

/-- **The joining theorem, cost.** -/
theorem run_cost_le {n : ℕ} (hn : 8000 ≤ n) (hM : 0 < mA n) (t a : ℝ) (θ : Net3 n)
    (σ : Fin draws → DrawSp n) : (run n hM t a draws θ σ).2 ≤ (orderedWork n).cost := by
  have h1 := draws_cost_le hn hM t θ σ
  have h2 := setup_cost_le hn hM
  have h3 := nodes_cost_le hn
  have h4 := world_chat_le (by omega : 2 ≤ n)
  have h5 := orderedWork_entries n
  have h6 := outProg_cost draws
  have hd : 8 ≤ draws := by unfold draws; norm_num
  rw [run_cost_eq]
  generalize ∑ i, (drawRun n hM θ t (σ i)).2 = D at h1 ⊢
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

theorem run_cost_lt {n : ℕ} (hn : 8000 ≤ n) (hM : 0 < mA n) (t a : ℝ) (θ : Net3 n)
    (σ : Fin draws → DrawSp n) :
    ((run n hM t a draws θ σ).2 : ℝ) < 1.0003 * (2 * (n : ℝ) ^ 7) := by
  have h : ((run n hM t a draws θ σ).2 : ℝ) ≤ ((orderedWork n).cost : ℝ) := by
    exact_mod_cast run_cost_le hn hM t a θ σ
  have h2 := orderedWork_lt_8000 hn
  have h3 : (1.0003 : ℝ) = 10003 / 10000 := by norm_num
  rw [h3]
  exact lt_of_le_of_lt h h2

/-- **C2, joined.** For every `n ≥ 8000` and every input (the three networks `θ`, the threshold
`t`, the factor `a`, the `draws` draws `σ`), the composed program `run` returns
`progOut (statedDesign n) t a draws θ σ`, and its cost (blocks, comparisons, table reads) is
below `1.0003·2n⁷`. -/
theorem progOut_run {n : ℕ} (hn : 8000 ≤ n) (t a : ℝ) (θ : Net3 n) (σ : Fin draws → DrawSp n) :
    ∃ hM : 0 < mA n, (run n hM t a draws θ σ).1 = progOut (statedDesign n) t a draws θ σ ∧
      ((run n hM t a draws θ σ).2 : ℝ) < 1.0003 * (2 * (n : ℝ) ^ 7) := by
  have hM : 0 < mA n := by unfold mA; positivity
  exact ⟨hM, progOut_eq_run hM θ hn t a draws σ, run_cost_lt hn hM t a θ σ⟩

end

end BstLean.Part282

/-- info: 'BstLean.Part282.run_cost_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.run_cost_lt
/-- info: 'BstLean.Part282.progOut_run' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.progOut_run
