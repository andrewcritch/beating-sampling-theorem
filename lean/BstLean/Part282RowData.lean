import BstLean.Part282Node
import BstLean.Part161Lat

/-!
# Part 282 (C2), the row data `α_i`, `κ_i`

Lean: `Part272Reduce.alphaE`, `kappaE`, `uEff` (Decision A: the axis `uEff c = H(û)e₀`, which is
`ĉ/|ĉ|` for `ĉ ≠ 0` and `−e₀` for `ĉ = 0`).

`rdProg n`: from `ĉ` and `A₁`: `|ĉ|²`, `r = |ĉ|`, `w = e₀ − ĉ/r`, `|w|²`, `⟨w, e₀⟩`,
`u = e₀ − ((2/|w|²)⟨w, e₀⟩)w` (this is `uEff c`, by `Part161.hh_mulVec`), and for each row
`α_i = A₁ᵢ·u`, `κ_i = √relu(|A₁ᵢ|² − α_i²)`. There is no branching: at `ĉ = 0` total division
gives `w = e₀` and `u = −e₀`, as in `uEff`.
`rdProg_alpha`, `rdProg_kappa`: the outputs are `alphaE c i`, `kappaE c i` for every retained
value (no hypothesis on `ĉ`). `rdProg_cost`: `12n − 2 + n²(4n + 2)` for `n ≥ 1`. This is more
than the five operations per row of Part 279's `rowDataWork` (which uses `μ_i/|ĉ|`); it is
far below the Part 189 setup reserve `100n³`.
-/

namespace BstLean.Part282

open BstLean.Cost BstLean.Part130 BstLean.Part157 BstLean.Part272
open BstLean.Part169 (A1)
open BstLean.Part161 (hhMat uHat hh_mulVec)

noncomputable section

variable (n : ℕ)

abbrev RDIn : Type := Fin n ⊕ (Fin (mA n) × Fin n)

def rdVal {n : ℕ} (c : Ret n) : RDIn n → ℝ := Sum.elim c.1.2 (fun p => A1 c p.1 p.2)

/-- `e₀` as rational constants. -/
def e0q {n : ℕ} (j : Fin n) : ℚ := if (j : ℕ) = 0 then 1 else 0

theorem e0q_cast {n : ℕ} (j : Fin n) : ((e0q j : ℚ) : ℝ) = e0 n j := by
  unfold e0q e0; split_ifs <;> simp

def ccProg : RProg (RDIn n) Unit :=
  RProg.ofProg (Prog.sumProd ((List.finRange n).map fun j => (Arg.inp (Sum.inl j), Arg.inp (Sum.inl j))))

def s1 : RProg (RDIn n) (Unit ⊕ Unit) := RProg.ext (ccProg n) (RExpr.sqrt (.inp (Sum.inr ()))).prog

def wE (j : Fin n) : RExpr (RDIn n ⊕ (Unit ⊕ Unit)) :=
  RExpr.sub (.cst (e0q j)) (RExpr.div (.inp (Sum.inl (Sum.inl j))) (.inp (Sum.inr (Sum.inr ()))))

def s2 : RProg (RDIn n) ((Unit ⊕ Unit) ⊕ Fin n) := RProg.ext (s1 n) (RProg.parV (wE n))

abbrev RE2 : Type := RDIn n ⊕ ((Unit ⊕ Unit) ⊕ Fin n)

def nwProg : RProg (RE2 n) Unit :=
  RProg.ofProg (Prog.sumProd ((List.finRange n).map fun j =>
    (Arg.inp (Sum.inr (Sum.inr j)), Arg.inp (Sum.inr (Sum.inr j)))))

def veProg : RProg (RE2 n) Unit :=
  RProg.ofProg (Prog.sumProd ((List.finRange n).map fun j =>
    (Arg.inp (Sum.inr (Sum.inr j)), Arg.cst (e0q j))))

def s3 : RProg (RDIn n) (((Unit ⊕ Unit) ⊕ Fin n) ⊕ (Unit ⊕ Unit)) :=
  RProg.ext (s2 n) (RProg.ext (nwProg n) ((veProg n).mapIn Sum.inl))

abbrev RE3 : Type := RDIn n ⊕ (((Unit ⊕ Unit) ⊕ Fin n) ⊕ (Unit ⊕ Unit))

def uaxE (j : Fin n) : RExpr (RE3 n) :=
  RExpr.sub (.cst (e0q j)) (RExpr.mul (RExpr.mul (RExpr.div (.cst 2) (.inp (Sum.inr (Sum.inr (Sum.inl ())))))
    (.inp (Sum.inr (Sum.inr (Sum.inr ()))))) (.inp (Sum.inr (Sum.inl (Sum.inr j)))))

def s4 : RProg (RDIn n) ((((Unit ⊕ Unit) ⊕ Fin n) ⊕ (Unit ⊕ Unit)) ⊕ Fin n) :=
  RProg.ext (s3 n) (RProg.parV (uaxE n))

abbrev RE4 : Type := RDIn n ⊕ ((((Unit ⊕ Unit) ⊕ Fin n) ⊕ (Unit ⊕ Unit)) ⊕ Fin n)

def alphaProg (i : Fin (mA n)) : RProg (RE4 n) Unit :=
  RProg.ofProg (Prog.sumProd ((List.finRange n).map fun j =>
    (Arg.inp (Sum.inl (Sum.inr (i, j))), Arg.inp (Sum.inr (Sum.inr j)))))

def qProg (i : Fin (mA n)) : RProg (RE4 n) Unit :=
  RProg.ofProg (Prog.sumProd ((List.finRange n).map fun j =>
    (Arg.inp (Sum.inl (Sum.inr (i, j))), Arg.inp (Sum.inl (Sum.inr (i, j))))))

def kapOutE : Fin 2 → RExpr (RE4 n ⊕ (Unit ⊕ Unit)) :=
  ![.inp (Sum.inr (Sum.inl ())),
    RExpr.sqrt (RExpr.relu (RExpr.sub (.inp (Sum.inr (Sum.inr ())))
      (RExpr.mul (.inp (Sum.inr (Sum.inl ()))) (.inp (Sum.inr (Sum.inl ()))))))]

def rowD (i : Fin (mA n)) : RProg (RE4 n) (Fin 2) :=
  (RProg.ext (alphaProg n i) ((qProg n i).mapIn Sum.inl)).bind (RProg.parV (kapOutE n))

/-- **The row data program.** Output `Sum.inr (i, 0)`: `α_i`; `Sum.inr (i, 1)`: `κ_i`. -/
def rdProg : RProg (RDIn n) (((((Unit ⊕ Unit) ⊕ Fin n) ⊕ (Unit ⊕ Unit)) ⊕ Fin n) ⊕
    (Fin (mA n) × Fin 2)) :=
  RProg.ext (s4 n) (RProg.parL2 (rowD n) (List.finRange (mA n)))

variable {n}

theorem sumProd_inp_eval {ι : Type} (l : List (Fin n)) (f g : Fin n → Arg ι) (v : ι → ℝ) :
    (Prog.sumProd (l.map fun j => (f j, g j))).eval v () =
      (l.map fun j => (f j).eval v [] * (g j).eval v []).sum := by
  rw [eval_sumProd, List.map_map]
  rfl

theorem s1_eval (c : Ret n) : (s1 n).eval (rdVal c) =
    Sum.elim (fun _ => normSq c.1.2) (fun _ => √(normSq c.1.2)) := by
  have hcc : (ccProg n).eval (rdVal c) () = normSq c.1.2 := by
    rw [ccProg, RProg.eval_ofProg, sumProd_inp_eval, normSq, Fin.sum_univ_def]
    congr 1
    apply List.map_congr_left
    intro j _
    simp [Arg.eval, rdVal, pow_two]
  funext x
  rcases x with u | u <;> cases u
  · rw [s1, RProg.eval_ext_inl, hcc] <;> rfl
  · rw [s1, RProg.eval_ext_inr, RExpr.eval_prog]
    simp [hcc]

/-- `w = e₀ − û`. -/
theorem s2_eval (c : Ret n) : (s2 n).eval (rdVal c) =
    Sum.elim ((s1 n).eval (rdVal c)) (e0 n - uHat c) := by
  funext x
  rcases x with u | j
  · rw [s2, RProg.eval_ext_inl] <;> rfl
  · rw [s2, RProg.eval_ext_inr, RProg.eval_parV, s1_eval]
    simp only [wE, RExpr.eval_sub, RExpr.eval_div, RExpr.eval_inp, RExpr.eval_cst, Sum.elim_inl,
      Sum.elim_inr, e0q_cast, uHat, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_eq_inv_mul] <;> rfl

theorem s3_eval (c : Ret n) : (s3 n).eval (rdVal c) =
    Sum.elim ((s2 n).eval (rdVal c))
      (Sum.elim (fun _ => normSq (e0 n - uHat c)) (fun _ => ∑ j, (e0 n - uHat c) j * e0 n j)) := by
  funext x
  rcases x with y | y
  · rw [s3, RProg.eval_ext_inl] <;> rfl
  · rcases y with u | u <;> cases u
    · rw [s3, RProg.eval_ext_inr, RProg.eval_ext_inl, nwProg, RProg.eval_ofProg, sumProd_inp_eval,
        normSq, Fin.sum_univ_def]
      simp only [Sum.elim_inr, Sum.elim_inl]
      congr 1
      apply List.map_congr_left
      intro j _
      simp [Arg.eval, s2_eval, pow_two]
    · rw [s3, RProg.eval_ext_inr, RProg.eval_ext_inr, RProg.eval_mapIn, veProg, RProg.eval_ofProg,
        sumProd_inp_eval, Fin.sum_univ_def]
      simp only [Sum.elim_inr, Sum.elim_inl]
      congr 1
      apply List.map_congr_left
      intro j _
      simp [Arg.eval, s2_eval, e0q_cast]

theorem s4_eval (c : Ret n) : (s4 n).eval (rdVal c) = Sum.elim ((s3 n).eval (rdVal c)) (uEff c) := by
  funext x
  rcases x with y | j
  · rw [s4, RProg.eval_ext_inl] <;> rfl
  · rw [s4, RProg.eval_ext_inr, RProg.eval_parV, uEff, hh_mulVec]
    simp only [uaxE, RExpr.eval_sub, RExpr.eval_mul, RExpr.eval_div, RExpr.eval_inp, RExpr.eval_cst,
      Sum.elim_inr, Sum.elim_inl, e0q_cast, s3_eval, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    simp only [s2_eval, Sum.elim_inr, Pi.sub_apply]
    push_cast
    ring

theorem rdProg_alpha (c : Ret n) (i : Fin (mA n)) :
    (rdProg n).eval (rdVal c) (Sum.inr (i, 0)) = alphaE c i := by
  rw [rdProg, RProg.eval_ext_inr, RProg.eval_parL2 _ _ _ _ _ (List.mem_finRange i), rowD,
    RProg.eval_bind, RProg.eval_parV]
  simp only [kapOutE, Matrix.cons_val_zero, RExpr.eval_inp, Sum.elim_inr, RProg.eval_ext_inl]
  rw [alphaProg, RProg.eval_ofProg, sumProd_inp_eval, alphaE, Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro j _
  simp only [Function.comp_apply, Arg.eval, Sum.elim_inl, Sum.elim_inr, s4_eval]
  rfl

theorem rdProg_kappa (c : Ret n) (i : Fin (mA n)) :
    (rdProg n).eval (rdVal c) (Sum.inr (i, 1)) = kappaE c i := by
  have ha := rdProg_alpha c i
  rw [rdProg, RProg.eval_ext_inr, RProg.eval_parL2 _ _ _ _ _ (List.mem_finRange i), rowD,
    RProg.eval_bind, RProg.eval_parV] at ha ⊢
  simp only [kapOutE, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    RExpr.eval_inp, RExpr.eval_sqrt, RExpr.eval_relu, RExpr.eval_sub, RExpr.eval_mul,
    Sum.elim_inr, RProg.eval_ext_inl, RProg.eval_ext_inr, RProg.eval_mapIn] at ha ⊢
  have hq : (qProg n i).eval (Sum.elim (rdVal c) ((s4 n).eval (rdVal c))) () = ∑ j, A1 c i j ^ 2 := by
    rw [qProg, RProg.eval_ofProg, sumProd_inp_eval, Fin.sum_univ_def]
    congr 1
    apply List.map_congr_left
    intro j _
    simp [Arg.eval, rdVal, pow_two]
  have hc : (Sum.elim (Sum.elim (rdVal c) ((s4 n).eval (rdVal c)))
      ((alphaProg n i).eval (Sum.elim (rdVal c) ((s4 n).eval (rdVal c)))) ∘ Sum.inl) =
      Sum.elim (rdVal c) ((s4 n).eval (rdVal c)) := rfl
  rw [hc, hq, ha, kappaE, relu, sq (alphaE c i)]

theorem rdProg_cost (hn : 1 ≤ n) : (rdProg n).cost = 12 * n - 2 + n ^ 2 * (4 * n + 2) := by
  have hrow : ∀ i, (rowD n i).cost = 4 * n + 2 := by
    intro i
    simp [rowD, alphaProg, qProg, RProg.cost_parV, Fin.sum_univ_succ, kapOutE, cost_sumProd]
    omega
  rw [rdProg, RProg.cost_ext, RProg.cost_parL2, list_sum_const _ _ _ hrow]
  simp [s4, s3, s2, s1, ccProg, nwProg, veProg, RProg.cost_parV, cost_sumProd, wE, uaxE, mA]
  omega

end

end BstLean.Part282

/-- info: 'BstLean.Part282.rdProg_kappa' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.rdProg_kappa
