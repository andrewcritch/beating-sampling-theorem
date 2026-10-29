import BstLean.Part289Design
import BstLean.Part282Draw

/-! The existing hit block with a rational floor parameter. -/
namespace BstLean.Part289
open Real MeasureTheory BstLean.Cost BstLean.Part130 BstLean.Part157 BstLean.Part282
noncomputable section

def rsFloorE (s₀ : ℚ) (n m : ℕ) : RExpr (HitIn n m) :=
  RExpr.sqrt (RExpr.mul (.cst (2 / n)) (RExpr.add (.cst s₀) (RExpr.relu
    (RExpr.sub (RExpr.sub (.inp (Sum.inl 1)) (RExpr.mul (.inp (Sum.inl 0)) (.inp (Sum.inl 0))))
      (.cst s₀)))))

def yFloorProg (s₀ : ℚ) (n m : ℕ) : RProg (HitIn n m) (Fin n) :=
  (Part282.RProg.ext (lamE n m).prog ((rsFloorE s₀ n m).prog.mapIn Sum.inl)).bind
    (RProg.parF fun i => (yE n m i).prog)

def fyFloorProg (s₀ : ℚ) (n m : ℕ) : RProg (HitIn n m) (Fin 1) :=
  (yFloorProg s₀ n m).mlpStep (fun e => Sum.inr (Sum.inr (Sum.inr e)))

def hitFloorProg (s₀ : ℚ) (n m : ℕ) : RProg (HitIn n m) Unit :=
  ((fyFloorProg s₀ n m).bind (rE n m).prog).bind
    (RExpr.div (.inp (Sum.inr ())) (.inp (Sum.inr ()))).prog

theorem yFloorProg_eval {n m : ℕ} (s₀ : ℚ) (f ω rb t : ℝ)
    (cA η : Fin n → ℝ) (F : MlpParam n m 1) :
    (yFloorProg s₀ n m).eval (hitVal f ω rb t cA η F) =
      (f / rb) • cA + √(2 / (n : ℝ) * max (s₀ : ℝ) (ω - f ^ 2)) • η := by
  funext i
  rw [yFloorProg, RProg.eval_bind, RProg.eval_parF, RExpr.eval_prog]
  simp only [yE, RExpr.eval_add, RExpr.eval_mul, RExpr.eval_inp, Sum.elim_inr, Sum.elim_inl,
    Part282.RProg.eval_ext_inl, Part282.RProg.eval_ext_inr, RProg.eval_mapIn, RExpr.eval_prog]
  simp only [lamE, rsFloorE, RExpr.eval_div, RExpr.eval_sqrt, RExpr.eval_mul, RExpr.eval_add,
    RExpr.eval_relu, RExpr.eval_sub, RExpr.eval_inp, RExpr.eval_cst, hitVal, Sum.elim_inl,
    Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Function.comp_apply]
  have hmax : (s₀ : ℝ) + relu (ω - f * f - (s₀ : ℝ)) = max (s₀ : ℝ) (ω - f ^ 2) := by
    unfold relu
    rw [pow_two]
    rcases le_total (ω - f * f) (s₀ : ℝ) with h | h
    · rw [max_eq_left (by linarith), max_eq_left h]; ring
    · rw [max_eq_right (by linarith), max_eq_right h]; ring
  rw [hmax]
  have h2 : Matrix.vecHead (Matrix.vecTail ![ω, rb, t]) = rb := rfl
  try simp only [h2]
  push_cast
  ring

theorem hitFloorProg_eval {n m : ℕ} (s₀ : ℚ) (f ω rb t : ℝ)
    (cA η : Fin n → ℝ) (F : MlpParam n m 1) :
    (hitFloorProg s₀ n m).eval (hitVal f ω rb t cA η F) () =
      if t < mlpEval F ((f / rb) • cA + √(2 / (n : ℝ) * max (s₀ : ℝ) (ω - f ^ 2)) • η) 0
      then 1 else 0 := by
  rw [hitFloorProg, RProg.eval_bind, RExpr.eval_prog]
  simp only [RExpr.eval_div, RExpr.eval_inp, Sum.elim_inr]
  rw [RProg.eval_bind, RExpr.eval_prog]
  simp only [rE, RExpr.eval_relu, RExpr.eval_sub, RExpr.eval_inp, Sum.elim_inr, Sum.elim_inl]
  rw [ind_pos, fyFloorProg,
    RProg.eval_mlpStep (yFloorProg s₀ n m) (fun e => Sum.inr (Sum.inr (Sum.inr e)))
      (hitVal f ω rb t cA η F) F (fun _ => rfl), yFloorProg_eval]
  simp only [hitVal, Sum.elim_inl, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, sub_pos]

theorem hitFloorProg_cost (s₀ : ℚ) (n m : ℕ) :
    (hitFloorProg s₀ n m).cost = (hitProg n m).cost := by
  rw [hitProg_cost]
  simp only [hitFloorProg, fyFloorProg, yFloorProg, RProg.cost_bind, RProg.cost_mlpStep,
    Part282.RProg.cost_ext, RProg.cost_mapIn, RExpr.cost_prog]
  rw [RProg.cost_parF_eq _ 3 (fun i => by simp [yE])]
  simp [lamE, rsFloorE, rE]
  ring

theorem hitFn_floor_eq {n : ℕ} (s₀ : ℚ) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    (t : ℝ) (c : Ret n) (d : DrawSp n) :
    hitFn (paperDesignFloor n (s₀ : ℝ) fT wT hf hw) t (c, d) =
      (hitFloorProg s₀ n (mF n)).eval
        (hitVal (fT c (gridNode (fun c => tau0p c.1.1) c
          (latitude (√(normSq c.1.2)) (tau0p c.1.1) d.1)))
          (wT c (gridNode (fun c => tau0p c.1.1) c
          (latitude (√(normSq c.1.2)) (tau0p c.1.1) d.1)))
          (√(normSq (bAp c.1 c.2.1.1) / (n : ℝ))) t c.2.1.2 d.2 c.2.2) () := by
  rw [hitFloorProg_eval]
  unfold hitFn hitEv
  simp only [Set.indicator, Set.mem_setOf_eq, classifier, drawY, Pi.one_apply]
  rfl

end
end BstLean.Part289

/-- info: 'BstLean.Part289.hitFn_floor_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.hitFn_floor_eq
/-- info: 'BstLean.Part289.hitFloorProg_cost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.hitFloorProg_cost
