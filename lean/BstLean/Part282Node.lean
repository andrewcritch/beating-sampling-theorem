import BstLean.Part282Row

/-!
# Part 282 (C2), one node pass after the rows

Paper: `theorem7-01-statement-program.tex`, step 5 (the conditional pass at one node).
Lean: `Part272Stated.vsig2G`, `betaG`, `beta2G`, `fPassG`, `wPassG`.

`nodeTail M J n`: the inputs are the row values `a_i`, `e_i` (`i < M`), the matrix `A₂`
(`M × M`), the vector `b` and the number `|b|²`. The program computes
`u = √(relu((2/M)(Σe − Σa²))/J)`, `h = A₂a`, for each `j` the two binomial sums
`β_j = Σ_q w_q relu(h_j + (2q − J)u)`, `β₂_j = Σ_q w_q relu(h_j + (2q − J)u)²`
(`w_q = C(J,q)/2^J` is a rational constant; seven operations per atom), and the two outputs
`Σβ_j b_j/(√n·√|b|²)` and `Σβ₂_j/n`. `nodeTail_eval`: the outputs are `fPassG`, `wPassG` in the
generic form (`nodeF`, `nodeW`). `nodeTail_cost`: `M(2M − 1) + 7M(J + 1) + 6M + 6`
operations.

Compared with `Part279.nodeWork'` (`matVecWork M M` plus `7(J+1)` per row), the tail has
`6M + 6` more operations: the sums `Σe`, `Σa²`, `Σβ_j b_j`, `Σβ₂_j` and the scalars. These are
not in `nodeWork'`.
-/

namespace BstLean.Part282

open BstLean.Cost BstLean.Part130 BstLean.Part150

noncomputable section

variable {ι κ ν : Type}

/-! ## One program with several outputs per element of a list -/

/-- One program `p k` (outputs `ν`) for each `k ∈ l`; output `(k, x)` is `p k` at `x`. -/
def RProg.parL2 [DecidableEq κ] (p : κ → RProg ι ν) : List κ → RProg ι (κ × ν)
  | [] => RProg.ofArgs fun _ => .cst 0
  | k :: l =>
      (p k).bind
        ⟨((RProg.parL2 p l).mapIn Sum.inl).body,
          fun jx => if jx.1 = k then .inp (Sum.inr jx.2) else ((RProg.parL2 p l).mapIn Sum.inl).out jx⟩

theorem RProg.eval_parL2 [DecidableEq κ] (p : κ → RProg ι ν) (l : List κ) (v : ι → ℝ) (k : κ)
    (x : ν) (hk : k ∈ l) : (RProg.parL2 p l).eval v (k, x) = (p k).eval v x := by
  induction l with
  | nil => simp at hk
  | cons j l ih =>
    simp only [RProg.parL2, RProg.eval_bind]
    by_cases h : k = j
    · subst h; simp [RProg.eval, Arg.eval]
    · have hk' : k ∈ l := by simpa [h] using hk
      have := RProg.eval_mapIn Sum.inl (RProg.parL2 p l) (Sum.elim v ((p j).eval v)) (k, x)
      simp only [RProg.eval, h, ite_false] at this ⊢
      rw [this]
      exact ih hk'

theorem RProg.cost_parL2 [DecidableEq κ] (p : κ → RProg ι ν) (l : List κ) :
    (RProg.parL2 p l).cost = (l.map fun k => (p k).cost).sum := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [RProg.parL2, RProg.cost_bind, List.map_cons, List.sum_cons]
    rw [← ih]
    simp [RProg.cost, RProg.mapIn]

theorem list_sum_const {α : Type} (l : List α) (f : α → ℕ) (c : ℕ) (h : ∀ a, f a = c) :
    (l.map f).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih, h a]; ring

/-! ## The values -/

/-- `v_σ = max(0, (2/M)(Σe − Σa²))`. -/
def nodeV {M : ℕ} (a e : Fin M → ℝ) : ℝ := max 0 (2 / (M : ℝ) * (∑ i, e i - normSq a))

/-- The node value `f̃` for the row values `a`, `e`. -/
def nodeF (n J : ℕ) {M : ℕ} (a e : Fin M → ℝ) (A : Matrix (Fin M) (Fin M) ℝ) (b : Fin M → ℝ) : ℝ :=
  (∑ j, binMean J (fun z => relu (A.mulVec a j + √(nodeV a e) * z)) * b j) /
    (√(n : ℝ) * √(normSq b))

/-- The node value `ω̃` for the row values `a`, `e`. -/
def nodeW (n J : ℕ) {M : ℕ} (a e : Fin M → ℝ) (A : Matrix (Fin M) (Fin M) ℝ) : ℝ :=
  (∑ j, binMean J (fun z => relu (A.mulVec a j + √(nodeV a e) * z) ^ 2)) / (n : ℝ)

/-! ## The program -/

/-- The inputs: `a`, `e`; the entries of `A₂`; `b`; `|b|²`. -/
abbrev NIn (M : ℕ) : Type := (Fin M ⊕ Fin M) ⊕ ((Fin M × Fin M) ⊕ (Fin M ⊕ Unit))

def nVal {M : ℕ} (a e : Fin M → ℝ) (A : Matrix (Fin M) (Fin M) ℝ) (b : Fin M → ℝ) (nb : ℝ) :
    NIn M → ℝ :=
  Sum.elim (Sum.elim a e) (Sum.elim (fun p => A p.1 p.2) (Sum.elim b fun _ => nb))

def aIx {M : ℕ} (i : Fin M) : NIn M := Sum.inl (Sum.inl i)
def eIx {M : ℕ} (i : Fin M) : NIn M := Sum.inl (Sum.inr i)

/-- `Σ e_i`. -/
def sumEProg (M : ℕ) : RProg (NIn M) Unit :=
  RProg.ofProg (Prog.sumArgs ((List.finRange M).map fun i => Arg.inp (eIx i)))

/-- `Σ a_i²`. -/
def sumAProg (M : ℕ) : RProg (NIn M) Unit :=
  RProg.ofProg (Prog.sumProd ((List.finRange M).map fun i => (Arg.inp (aIx i), Arg.inp (aIx i))))

/-- `u = √(relu((2/M)(Σe − Σa²))/J)`. -/
def uE (M J : ℕ) : RExpr (NIn M ⊕ (Unit ⊕ Unit)) :=
  RExpr.sqrt (RExpr.div (RExpr.relu (RExpr.mul (.cst (2 / M))
    (RExpr.sub (.inp (Sum.inr (Sum.inl ()))) (.inp (Sum.inr (Sum.inr ()))))))
    (.cst (J : ℚ)))

def uProg (M J : ℕ) : RProg (NIn M) Unit :=
  (RProg.ext (sumEProg M) ((sumAProg M).mapIn Sum.inl)).bind (uE M J).prog

/-- `h = A₂ a`. -/
def hProg (M : ℕ) : RProg (NIn M) (Fin M) :=
  RProg.ofProg ((mulVecProg M M).mapIn (Sum.elim (fun j => aIx j) (fun p => Sum.inr (Sum.inl p))))

/-- The environment of the atom loops. -/
abbrev AEnv (M : ℕ) : Type := NIn M ⊕ (Unit ⊕ Fin M)

def pUH (M J : ℕ) : RProg (NIn M) (Unit ⊕ Fin M) := RProg.ext (uProg M J) ((hProg M).mapIn Sum.inl)

/-- `r = relu(h_j + (2q − J)u)`. -/
def rAtomE (M J : ℕ) (j : Fin M) (q : ℕ) : RExpr (AEnv M ⊕ Fin 2) :=
  RExpr.relu (RExpr.add (.inp (Sum.inl (Sum.inr (Sum.inr j))))
    (RExpr.mul (.cst (2 * (q : ℚ) - J)) (.inp (Sum.inl (Sum.inr (Sum.inl ()))))))

/-- `w_q r`. -/
def wrE (M J : ℕ) (q : ℕ) : RExpr ((AEnv M ⊕ Fin 2) ⊕ Unit) :=
  RExpr.mul (.cst ((J.choose q : ℚ) / 2 ^ J)) (.inp (Sum.inr ()))

/-- `β ← β + w_q r`, `β₂ ← β₂ + (w_q r) r`. -/
def accE (M : ℕ) : Fin 2 → RExpr ((AEnv M ⊕ Fin 2) ⊕ (Unit ⊕ Unit)) :=
  ![RExpr.add (.inp (Sum.inl (Sum.inr 0))) (.inp (Sum.inr (Sum.inr ()))),
    RExpr.add (.inp (Sum.inl (Sum.inr 1)))
      (RExpr.mul (.inp (Sum.inr (Sum.inr ()))) (.inp (Sum.inr (Sum.inl ()))))]

def atomStep (M J : ℕ) (j : Fin M) (q : ℕ) : RProg (AEnv M ⊕ Fin 2) (Fin 2) :=
  (RProg.ext (rAtomE M J j q).prog (wrE M J q).prog).bind (RProg.parV (accE M))

def atomLoop (M J : ℕ) (j : Fin M) : RProg (AEnv M) (Fin 2) :=
  RProg.iter (RProg.ofArgs fun _ => .cst 0) (atomStep M J j) (J + 1)

def pB (M J : ℕ) : RProg (NIn M) ((Unit ⊕ Fin M) ⊕ (Fin M × Fin 2)) :=
  RProg.ext (pUH M J) (RProg.parL2 (atomLoop M J) (List.finRange M))

abbrev FEnv (M : ℕ) : Type := NIn M ⊕ ((Unit ⊕ Fin M) ⊕ (Fin M × Fin 2))

/-- `Σ β_j b_j` and `Σ β₂_j`. -/
def fNumProg (M : ℕ) : RProg (FEnv M) Unit :=
  RProg.ofProg (Prog.sumProd ((List.finRange M).map fun j =>
    (Arg.inp (Sum.inr (Sum.inr (j, 0))), Arg.inp (Sum.inl (Sum.inr (Sum.inr (Sum.inl j)))))))

def wNumProg (M : ℕ) : RProg (FEnv M) Unit :=
  RProg.ofProg (Prog.sumArgs ((List.finRange M).map fun j => Arg.inp (Sum.inr (Sum.inr (j, 1)))))

def outNE (M n : ℕ) : Fin 2 → RExpr (FEnv M ⊕ (Unit ⊕ Unit)) :=
  ![RExpr.div (.inp (Sum.inr (Sum.inl ())))
      (RExpr.mul (RExpr.sqrt (.cst (n : ℚ))) (RExpr.sqrt (.inp (Sum.inl (Sum.inl (Sum.inr (Sum.inr (Sum.inr ())))))))),
    RExpr.div (.inp (Sum.inr (Sum.inr ()))) (.cst (n : ℚ))]

/-- **The node pass after the rows.** Output `0`: `f̃`; output `1`: `ω̃`. -/
def nodeTail (M J n : ℕ) : RProg (NIn M) (Fin 2) :=
  (pB M J).bind ((RProg.ext (fNumProg M) ((wNumProg M).mapIn Sum.inl)).bind (RProg.parV (outNE M n)))

/-! ## The value -/

section value

variable {M : ℕ} (J n : ℕ) (a e : Fin M → ℝ) (A : Matrix (Fin M) (Fin M) ℝ) (b : Fin M → ℝ)
  (nb : ℝ)

theorem sumEProg_eval : (sumEProg M).eval (nVal a e A b nb) () = ∑ i, e i := by
  rw [sumEProg, RProg.eval_ofProg, eval_sumArgs, List.map_map, Fin.sum_univ_def]
  rfl

theorem sumAProg_eval : (sumAProg M).eval (nVal a e A b nb) () = normSq a := by
  rw [sumAProg, RProg.eval_ofProg, eval_sumProd, List.map_map, normSq, Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro i _
  simp [Arg.eval, nVal, aIx, pow_two]

theorem uProg_eval : (uProg M J).eval (nVal a e A b nb) () = √(nodeV a e / J) := by
  rw [uProg, RProg.eval_bind, RExpr.eval_prog]
  simp only [uE, RExpr.eval_sqrt, RExpr.eval_div, RExpr.eval_relu, RExpr.eval_mul,
    RExpr.eval_sub, RExpr.eval_inp, RExpr.eval_cst, Sum.elim_inr, RProg.eval_ext_inl,
    RProg.eval_ext_inr, RProg.eval_mapIn]
  have hc : (Sum.elim (nVal a e A b nb) ((sumEProg M).eval (nVal a e A b nb)) ∘ Sum.inl) =
      nVal a e A b nb := rfl
  try rw [hc]
  rw [sumEProg_eval, sumAProg_eval, nodeV, relu]
  push_cast
  try rfl

theorem hProg_eval : (hProg M).eval (nVal a e A b nb) = A.mulVec a := by
  funext i
  rw [hProg, RProg.eval_ofProg, BstLean.Cost.eval_mapIn]
  have h : (nVal a e A b nb ∘ Sum.elim (fun j => aIx j) (fun p => Sum.inr (Sum.inl p))) =
      Sum.elim a (fun p => A p.1 p.2) := by
    funext x; rcases x with j | p <;> rfl
  rw [h, mulVecProg_eval]

theorem pUH_eval : (pUH M J).eval (nVal a e A b nb) =
    Sum.elim (fun _ => √(nodeV a e / J)) (A.mulVec a) := by
  funext x
  rcases x with u | j
  · cases u
    simp only [pUH, RProg.eval_ext_inl, Sum.elim_inl]
    exact uProg_eval J a e A b nb
  · simp only [pUH, RProg.eval_ext_inr, RProg.eval_mapIn, Sum.elim_inr]
    have hc : (Sum.elim (nVal a e A b nb) ((uProg M J).eval (nVal a e A b nb)) ∘ Sum.inl) =
        nVal a e A b nb := rfl
    try rw [hc]
    rw [hProg_eval]

/-- The state of the atom loop after `t` steps. -/
theorem atomLoop_aux (j : Fin M) (w : AEnv M → ℝ) (h u : ℝ)
    (hh : w (Sum.inr (Sum.inr j)) = h) (hu : w (Sum.inr (Sum.inl ())) = u) (t : ℕ) :
    (RProg.iter (RProg.ofArgs fun _ => .cst 0) (atomStep M J j) t).eval w =
      ![∑ q ∈ Finset.range t, ((J.choose q : ℚ) / 2 ^ J : ℚ) * relu (h + (2 * (q : ℚ) - J : ℚ) * u),
        ∑ q ∈ Finset.range t, ((J.choose q : ℚ) / 2 ^ J : ℚ) * relu (h + (2 * (q : ℚ) - J : ℚ) * u) *
          relu (h + (2 * (q : ℚ) - J : ℚ) * u)] := by
  induction t with
  | zero =>
    funext x; fin_cases x <;> simp [Arg.eval]
  | succ t ih =>
    rw [RProg.eval_iter_succ, ih]
    funext x
    simp only [atomStep, RProg.eval_bind, RProg.eval_parV]
    fin_cases x
    all_goals (simp [accE, wrE, rAtomE, hh, hu, Finset.sum_range_succ]) <;> ring

theorem binMean_relu_eq (h v : ℝ) (hv : 0 ≤ v) :
    binMean J (fun z => relu (h + √v * z)) =
      ∑ q ∈ Finset.range (J + 1), ((J.choose q : ℚ) / 2 ^ J : ℚ) *
        relu (h + (2 * (q : ℚ) - J : ℚ) * √(v / J)) := by
  unfold binMean binW binAtom
  refine Finset.sum_congr rfl fun q _ => ?_
  push_cast
  have e : √v * ((2 * (q : ℝ) - J) / √(J : ℝ)) = (2 * q - J) * √(v / J) := by
    rw [Real.sqrt_div' v (Nat.cast_nonneg J)]; ring
  rw [e]

theorem binMean_relu2_eq (h v : ℝ) (hv : 0 ≤ v) :
    binMean J (fun z => relu (h + √v * z) ^ 2) =
      ∑ q ∈ Finset.range (J + 1), ((J.choose q : ℚ) / 2 ^ J : ℚ) *
        relu (h + (2 * (q : ℚ) - J : ℚ) * √(v / J)) * relu (h + (2 * (q : ℚ) - J : ℚ) * √(v / J)) := by
  unfold binMean binW binAtom
  refine Finset.sum_congr rfl fun q _ => ?_
  push_cast
  have e : √v * ((2 * (q : ℝ) - J) / √(J : ℝ)) = (2 * q - J) * √(v / J) := by
    rw [Real.sqrt_div' v (Nat.cast_nonneg J)]; ring
  rw [e, pow_two]
  ring

theorem pB_eval (j : Fin M) :
    (pB M J).eval (nVal a e A b nb) (Sum.inr (j, 0)) =
        binMean J (fun z => relu (A.mulVec a j + √(nodeV a e) * z)) ∧
      (pB M J).eval (nVal a e A b nb) (Sum.inr (j, 1)) =
        binMean J (fun z => relu (A.mulVec a j + √(nodeV a e) * z) ^ 2) := by
  have hv : 0 ≤ nodeV a e := le_max_left _ _
  have key := atomLoop_aux J j (Sum.elim (nVal a e A b nb) ((pUH M J).eval (nVal a e A b nb)))
    (A.mulVec a j) (√(nodeV a e / J)) (by rw [pUH_eval]; rfl) (by rw [pUH_eval]; rfl) (J + 1)
  simp only [pB, RProg.eval_ext_inr]
  rw [RProg.eval_parL2 _ _ _ _ _ (List.mem_finRange j), RProg.eval_parL2 _ _ _ _ _
    (List.mem_finRange j)]
  rw [binMean_relu_eq J _ _ hv, binMean_relu2_eq J _ _ hv]
  constructor
  · rw [atomLoop, key]; rfl
  · rw [atomLoop, key]; rfl

theorem nodeTail_eval :
    (nodeTail M J n).eval (nVal a e A b nb) 0 = (∑ j, binMean J (fun z =>
        relu (A.mulVec a j + √(nodeV a e) * z)) * b j) / (√(n : ℝ) * √nb) ∧
      (nodeTail M J n).eval (nVal a e A b nb) 1 =
        (∑ j, binMean J (fun z => relu (A.mulVec a j + √(nodeV a e) * z) ^ 2)) / (n : ℝ) := by
  set w := Sum.elim (nVal a e A b nb) ((pB M J).eval (nVal a e A b nb)) with hw
  have hF : (fNumProg M).eval w () =
      ∑ j, binMean J (fun z => relu (A.mulVec a j + √(nodeV a e) * z)) * b j := by
    rw [fNumProg, RProg.eval_ofProg, eval_sumProd, List.map_map, Fin.sum_univ_def]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply, Arg.eval, hw, Sum.elim_inr, Sum.elim_inl, (pB_eval J a e A b nb j).1]
    try rfl
  have hW : (wNumProg M).eval w () =
      ∑ j, binMean J (fun z => relu (A.mulVec a j + √(nodeV a e) * z) ^ 2) := by
    rw [wNumProg, RProg.eval_ofProg, eval_sumArgs, List.map_map, Fin.sum_univ_def]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply, Arg.eval, hw, Sum.elim_inr, (pB_eval J a e A b nb j).2]
  have hc : (Sum.elim w ((fNumProg M).eval w) ∘ Sum.inl) = w := rfl
  constructor
  · simp only [nodeTail, RProg.eval_bind, RProg.eval_parV, ← hw]
    simp only [outNE, Matrix.cons_val_zero, RExpr.eval_div, RExpr.eval_mul, RExpr.eval_sqrt,
      RExpr.eval_inp, RExpr.eval_cst, Sum.elim_inr, Sum.elim_inl, RProg.eval_ext_inl, hF]
    simp [hw, nVal]
  · simp only [nodeTail, RProg.eval_bind, RProg.eval_parV, ← hw]
    simp only [outNE, Matrix.cons_val_one, Matrix.head_cons, RExpr.eval_div, RExpr.eval_inp,
      RExpr.eval_cst, Sum.elim_inr, RProg.eval_ext_inr, RProg.eval_mapIn, hc, hW]
    try simp
    first | rw [hW] | simp [hW]

end value

/-! ## The cost -/

theorem nodeTail_cost (M J n : ℕ) (hM : 1 ≤ M) :
    (nodeTail M J n).cost = M * (2 * M - 1) + 7 * M * (J + 1) + 6 * M + 6 := by
  have h1 : M - 1 + 1 = M := by omega
  have h2 : 2 * M - 1 + 1 = 2 * M := by omega
  have hstep : ∀ j q, (atomStep M J j q).cost = 7 := by
    intro j q
    simp [atomStep, RProg.cost_parV, Fin.sum_univ_succ, accE, rAtomE, wrE]
  have hloop : ∀ j, (atomLoop M J j).cost = 7 * (J + 1) := by
    intro j
    rw [atomLoop, RProg.cost_iter_const _ _ _ 7 (hstep j)]
    simp; ring
  simp only [nodeTail, pB, pUH, uProg, RProg.cost_bind, RProg.cost_ext, RProg.cost_mapIn,
    RProg.cost_parV, RExpr.cost_prog]
  rw [RProg.cost_parL2, list_sum_const _ _ _ hloop]
  simp only [sumEProg, sumAProg, hProg, fNumProg, wNumProg, RProg.cost_ofProg, cost_sumArgs,
    cost_sumProd, BstLean.Cost.cost_mapIn, mulVecProg_cost, List.length_map, List.length_finRange]
  simp [Fin.sum_univ_succ, uE, outNE]
  nlinarith [h1, h2]

end

end BstLean.Part282

/-- info: 'BstLean.Part282.nodeTail_eval' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.nodeTail_eval
