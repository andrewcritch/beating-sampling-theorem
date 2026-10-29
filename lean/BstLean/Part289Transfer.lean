import BstLean.Part289Design

/-! Every existing stated-classifier conclusion transfers on the unchanged branch. -/
namespace BstLean.Part289
open MeasureTheory BstLean.Part130 BstLean.Part157 BstLean.Part272

theorem progOut_statedDesign2_eq {n : ℕ} (hn : 11883 ≤ n) (t a : ℝ) (k : ℕ)
    (θ : Net3 n) (σ : Fin k → DrawSp n) :
    progOut (statedDesign2 n) t a k θ σ = progOut (statedDesign n) t a k θ σ := by
  rw [statedDesign2_eq hn]

/-- This accepts the conclusion of any Part 278, 281, or 287 stated classifier,
without importing or rebuilding its row certificates. -/
theorem classifier_statedDesign2_of_stated {n : ℕ} (hn : 11883 ≤ n) (t a : ℝ) (k : ℕ)
    (h : 99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas k n)).real
      {x | successNet x.1 t (progOut (statedDesign n) t a k x.1 x.2)}) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas k n)).real
      {x | successNet x.1 t (progOut (statedDesign2 n) t a k x.1 x.2)} := by
  rw [statedDesign2_eq hn]
  exact h

end BstLean.Part289

/-- info: 'BstLean.Part289.classifier_statedDesign2_of_stated' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.classifier_statedDesign2_of_stated
