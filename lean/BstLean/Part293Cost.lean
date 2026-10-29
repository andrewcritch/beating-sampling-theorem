import BstLean.Part289Cost

/-! The counted revised program, including the floor comparison, on the full target range. -/
namespace BstLean.Part293
open BstLean.Part130 BstLean.Part157 BstLean.Part289 BstLean.Part279
open BstLean.Part189 (draws)

theorem statedDesign2_cost {n : ℕ} (hn : 8000 ≤ n) (t : ℝ) (θ : Net3 n)
    (σ : Fin draws → DrawSp n) :
    ∃ hM : 0 < mA n,
      (run2 n hM t BstLean.Part156.aL draws θ σ).1 =
        progOut (statedDesign2 n) t BstLean.Part156.aL draws θ σ ∧
      ((run2 n hM t BstLean.Part156.aL draws θ σ).2 : ℝ) ≤
        1.0003 * (2 * (n : ℝ) ^ 7) := by
  obtain ⟨hM, heq, hcost⟩ := progOut_run2 hn t BstLean.Part156.aL θ σ
  exact ⟨hM, heq, hcost.le⟩

end BstLean.Part293

/-- info: 'BstLean.Part293.statedDesign2_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.statedDesign2_cost
