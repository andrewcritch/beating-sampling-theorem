import BstLean.Part289Hit
import BstLean.Part288Join

/-! The dimension branch is evaluated once and charged one comparison. -/
namespace BstLean.Part289
open Real MeasureTheory BstLean.Cost BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part272 BstLean.Part282 BstLean.Part288
noncomputable section

def floorBranch (n : ℕ) : Cm ℚ := (if n < 11883 then 17 / 100 else 1 / 5, 1)

theorem floorBranch_value (n : ℕ) : ((floorBranch n).1 : ℝ) = scaleFloor n := by
  unfold floorBranch scaleFloor
  split_ifs <;> norm_num

theorem floorBranch_cost (n : ℕ) : (floorBranch n).2 = 1 := rfl

def drawFloorRun (s₀ : ℚ) (n : ℕ) (hM : 0 < mA n) (θ : Net3 n) (t : ℝ)
    (d : DrawSp n) : Cm ℝ :=
  Cm.bind (blk1 (latProg (n - 1)) (latVal (rdOut n θ (rIx n)) (tOut n θ) (t2Out n θ) d.1.1 d.1.2))
    fun s => Cm.bind (selectNode' (Js n) (gOut n θ (Sum.inl 0)) (gOut n θ (Sum.inl 1)) s)
    fun g => Cm.bind (tread (fun g => tabOut n hM θ g 0) g)
    fun f => Cm.bind (tread (fun g => tabOut n hM θ g 1) g)
    fun ω => blk1 (hitFloorProg s₀ n (mF n))
      (hitVal f ω (ebOut n hM θ) t (cAOut n hM θ) d.2 θ.2.2)

def run2 (n : ℕ) (hM : 0 < mA n) (t a : ℝ) (k : ℕ) (θ : Net3 n)
    (σ : Fin k → DrawSp n) : Cm ℝ :=
  Cm.bind (floorBranch n) fun s₀ =>
    ((outProg k).eval (oVal a (fun i => (drawFloorRun s₀ n hM θ t (σ i)).1)) (),
      setupCost n hM + ∑ i, (drawFloorRun s₀ n hM θ t (σ i)).2 + (outProg k).cost)

theorem drawFloorRun_cost {n : ℕ} (s₀ : ℚ) (hM : 0 < mA n) (θ : Net3 n)
    (t : ℝ) (d : DrawSp n) :
    (drawFloorRun s₀ n hM θ t d).2 = (drawRun' n hM θ t d).2 := by
  simp only [drawFloorRun, drawRun', Cm.bind, blk1, hitFloorProg_cost]

theorem run2_cost {n : ℕ} (hM : 0 < mA n) (t a : ℝ) (k : ℕ) (θ : Net3 n)
    (σ : Fin k → DrawSp n) : (run2 n hM t a k θ σ).2 = (run' n hM t a k θ σ).2 + 1 := by
  simp only [run2, Cm.bind, floorBranch_cost, drawFloorRun_cost, run']
  omega

theorem drawFloorRun_eq {n : ℕ} (s₀ : ℚ) (hM : 0 < mA n) (θ : Net3 n)
    (hJ : 1 ≤ Js n) (t : ℝ) (d : DrawSp n) :
    (drawFloorRun s₀ n hM θ t d).1 =
      hitFn (paperDesignFloor n (s₀ : ℝ) passFSt passWSt measurable_passFSt measurable_passWSt)
        t (ret (statedDesign n).toCentres θ, d) := by
  have hlat : (latProg (n - 1)).eval
      (latVal (rdOut n θ (rIx n)) (tOut n θ) (t2Out n θ) d.1.1 d.1.2) () =
      latitude (√(normSq ((ret (statedDesign n).toCentres θ)).1.2))
        (tau0p ((ret (statedDesign n).toCentres θ)).1.1) d.1 := by
    rw [rdOut_r, t2Out, tauSqProg_eval, tOut_eq, latProg_eval]
    rfl
  have hL : gOut n θ (Sum.inl 0) = nodeL (ret (statedDesign n).toCentres θ) := by
    rw [gOut_eq, gridProg_LHD]; rfl
  have hH : gOut n θ (Sum.inl 1) = nodeH (ret (statedDesign n).toCentres θ) := by
    rw [gOut_eq, gridProg_LHD]; rfl
  set g := nodeIdx (Js n) (nodeL (ret (statedDesign n).toCentres θ))
    (nodeH (ret (statedDesign n).toCentres θ))
    (latitude (√(normSq ((ret (statedDesign n).toCentres θ)).1.2))
      (tau0p ((ret (statedDesign n).toCentres θ)).1.1) d.1) with hg
  have hsel : (selectNode' (Js n) (gOut n θ (Sum.inl 0)) (gOut n θ (Sum.inl 1))
      ((latProg (n - 1)).eval
        (latVal (rdOut n θ (rIx n)) (tOut n θ) (t2Out n θ) d.1.1 d.1.2) ())).1 = g := by
    rw [selectNode'_eq_selectNode, hL, hH, hlat, selectNode_eq hJ]
  have hlt : g < Js n := by
    have : g ≤ Js n - 1 := by rw [hg]; unfold nodeIdx; exact min_le_left _ _
    omega
  have hread : ∀ j : Fin 2, (tread (fun g => tabOut n hM θ g j) g).1 =
      tabOut n hM θ ⟨g, hlt⟩ j := by intro j; simp [tread, hlt]
  simp only [drawFloorRun, Cm.bind, blk1]
  rw [hsel, hread, hread, (tabOut_eq hM θ ⟨g, hlt⟩).1, (tabOut_eq hM θ ⟨g, hlt⟩).2,
    ebOut, ebProg_eval, bOut_eq, cAOut_eq, hitFn_floor_eq]
  rfl

theorem progOut_eq_run2 {n : ℕ} (hn : 8000 ≤ n) (hM : 0 < mA n)
    (t a : ℝ) (k : ℕ) (θ : Net3 n) (σ : Fin k → DrawSp n) :
    (run2 n hM t a k θ σ).1 = progOut (statedDesign2 n) t a k θ σ := by
  rw [progOut_eq_outProg]
  simp only [run2, Cm.bind]
  apply congrArg (fun x => (outProg k).eval (oVal a x) ())
  funext i
  rw [drawFloorRun_eq _ hM θ (by unfold Js; omega), floorBranch_value]
  rfl

end
end BstLean.Part289

/-- info: 'BstLean.Part289.progOut_eq_run2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.progOut_eq_run2
/-- info: 'BstLean.Part289.run2_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.run2_cost
