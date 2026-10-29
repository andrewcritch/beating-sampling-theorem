import BstLean.Part289Run

namespace BstLean.Part289
open Real BstLean.Cost BstLean.Part130 BstLean.Part157 BstLean.Part189
open BstLean.Part282 BstLean.Part288 BstLean.Part279

/-- Above the branch point the returned value is Part 288's value, with one added comparison. -/
theorem run2_eq_run'_high {n : ℕ} (hn : 11883 ≤ n) (hM : 0 < mA n)
    (t a : ℝ) (k : ℕ) (θ : Net3 n) (σ : Fin k → DrawSp n) :
    (run2 n hM t a k θ σ).1 = (run' n hM t a k θ σ).1 ∧
      (run2 n hM t a k θ σ).2 = (run' n hM t a k θ σ).2 + 1 := by
  refine ⟨?_, run2_cost hM t a k θ σ⟩
  rw [progOut_eq_run2 (by omega), progOut_eq_run' (by omega), statedDesign2_eq hn]

/-- The existing output allowance also pays for the one dimension comparison. -/
theorem run'_cost_add_one_le {n : ℕ} (hn : 8000 ≤ n) (hM : 0 < mA n)
    (t a : ℝ) (θ : Net3 n) (σ : Fin draws → DrawSp n) :
    (run' n hM t a draws θ σ).2 + 1 ≤ (orderedWork n).cost := by
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

theorem run2_cost_lt {n : ℕ} (hn : 8000 ≤ n) (hM : 0 < mA n)
    (t a : ℝ) (θ : Net3 n) (σ : Fin draws → DrawSp n) :
    ((run2 n hM t a draws θ σ).2 : ℝ) < 1.0003 * (2 * (n : ℝ) ^ 7) := by
  have h : ((run2 n hM t a draws θ σ).2 : ℝ) ≤ ((orderedWork n).cost : ℝ) := by
    have hN : (run2 n hM t a draws θ σ).2 ≤ (orderedWork n).cost := by
      rw [run2_cost]
      exact run'_cost_add_one_le hn hM t a θ σ
    exact_mod_cast hN
  exact lt_of_le_of_lt h (by convert orderedWork_lt_8000 hn using 1 <;> norm_num)

/-- The revised program has the same cost bound on both branches, including the comparison. -/
theorem progOut_run2 {n : ℕ} (hn : 8000 ≤ n) (t a : ℝ) (θ : Net3 n)
    (σ : Fin draws → DrawSp n) :
    ∃ hM : 0 < mA n, (run2 n hM t a draws θ σ).1 =
      progOut (statedDesign2 n) t a draws θ σ ∧
      ((run2 n hM t a draws θ σ).2 : ℝ) < 1.0003 * (2 * (n : ℝ) ^ 7) := by
  have hM : 0 < mA n := by unfold mA; positivity
  exact ⟨hM, progOut_eq_run2 hn hM t a draws θ σ, run2_cost_lt hn hM t a θ σ⟩

end BstLean.Part289

/-- info: 'BstLean.Part289.progOut_run2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.progOut_run2
