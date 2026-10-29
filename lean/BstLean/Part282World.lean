import BstLean.Part282Node

/-!
# Part 282 (C2), the World pass

Paper: `theorem7-01-statement-program.tex`, steps 1 and 2. Lean: `Part157Paper.bWp`, `tau0p`.

* The constants of step 1 are rational numbers, except `κ̃`, which has one square root:
  `cQ`, `dQ`, `rQ`, `piQ` with `cQ_cast : (cQ n : ℝ) = cNt n`, `dQ_cast`, `kapT_eq`.
  In the model rational constants are free, so the program uses them as constants.
* `worldProg m N J c d kA kB kP nn`: from the entries of `W₁` (`m × N`) and `W₂` (`m × m`):
  the row norms `q_j = |row_j(W₁)|²` and `h_j = c√q_j`, `S_W = Σq_j/m`, `t = √(S_W d)/√J`,
  the offsets `o_q = (2q − J)t`, `a = W₂h`, for each row `b_i = Σ_q w_q relu(a_i + o_q)`
  (`w_q = C(J,q)/2^J`, a rational constant), `ν = |b|²`, and
  `τ₀ = √((2/m)ν·relu(2nn(2/m)ν/(S_W κ²) − 1))`, `κ = (√kA + kB)/kP`.
* `worldProg_bW`, `worldProg_tau`: the values in closed form.
  `bWp_eq_worldProg`, `tau0p_eq_worldProg`: with the constants of step 1 they are
  `bWp θ i` and `tau0p θ`.
* `worldProg_cost`: `m(2N + 1) + (m − 1) + 5 + (J + 1) + m(2m − 1) + m(4J + 3) + (2m − 1) + 15`.
-/

namespace BstLean.Part282

open BstLean.Cost BstLean.Part130 BstLean.Part157 BstLean.Part150
open BstLean.Part141 (aOf rowS)
open BstLean.Part136 (HidParam)

noncomputable section

/-! ## The constants of step 1 -/

def ATsumQ (T : ℕ) (v : ℚ) : ℚ :=
  ∑ j ∈ Finset.range T, (-1 : ℚ) ^ j * v ^ (2 * j + 1) / (2 * (j : ℚ) + 1)

theorem ATsumQ_cast (T : ℕ) (v : ℚ) : ((ATsumQ T v : ℚ) : ℝ) = ATsum T (v : ℝ) := by
  unfold ATsumQ ATsum; push_cast; rfl

def QTsumQ (T : ℕ) (v : ℚ) : ℚ :=
  ∑ j ∈ Finset.range T, ((2 * j).factorial : ℚ) * v ^ (2 * j + 1) /
    (4 ^ j * (j.factorial : ℚ) ^ 2 * (2 * (j : ℚ) + 1))

theorem QTsumQ_cast (T : ℕ) (v : ℚ) : ((QTsumQ T v : ℚ) : ℝ) = QTsum T (v : ℝ) := by
  unfold QTsumQ QTsum; push_cast; rfl

def piQ (n : ℕ) : ℚ := 16 * ATsumQ (Tpi n) (1 / 5) - 4 * ATsumQ (Tpi n) (1 / 239)

theorem piQ_cast (n : ℕ) : ((piQ n : ℚ) : ℝ) = piT n := by
  unfold piQ piT; push_cast [ATsumQ_cast]; norm_num

def cQ (n : ℕ) : ℚ := (piQ n)⁻¹ * ∏ j ∈ Finset.Icc 1 (n - 1), (2 * (j : ℚ)) / (2 * (j : ℚ) + 1)

theorem cQ_cast (n : ℕ) : ((cQ n : ℚ) : ℝ) = cNt n := by
  unfold cQ cNt; push_cast [piQ_cast]; rfl

def dQ (n : ℕ) : ℚ := 1 / (2 * (n : ℚ)) - 2 * cQ n ^ 2

theorem dQ_cast (n : ℕ) : ((dQ n : ℚ) : ℝ) = dNt n := by
  unfold dQ dNt; push_cast [cQ_cast]; rfl

def rQ (n : ℕ) : ℚ := 2 * (2 * (n : ℚ)) * cQ n ^ 2

theorem rQ_cast (n : ℕ) : ((rQ n : ℚ) : ℝ) = rNt n := by
  unfold rQ rNt; push_cast [cQ_cast]; rfl

/-- `κ̃ = (√kA + kB)/kP` with rational `kA`, `kB`, `kP`. -/
def kapA (n : ℕ) : ℚ := 1 - rQ n ^ 2
def kapB (n : ℕ) : ℚ := rQ n * (piQ n / 2 + QTsumQ (Tkap n) (rQ n))

theorem kapT_eq (n : ℕ) :
    kapT n = (√((kapA n : ℚ) : ℝ) + ((kapB n : ℚ) : ℝ)) / ((piQ n : ℚ) : ℝ) := by
  unfold kapT kapA kapB
  push_cast [rQ_cast, piQ_cast, QTsumQ_cast]
  rfl

/-! ## The program -/

section prog

variable (m N J : ℕ)

abbrev WIn : Type := (Fin m × Fin N) ⊕ (Fin m × Fin m)

def wVal {m N : ℕ} (θ : HidParam N m) : WIn m N → ℝ :=
  Sum.elim (fun p => θ.1 p.1 p.2) (fun p => θ.2 p.1 p.2)

/-- `q_j = |row_j(W₁)|²`. -/
def rowSqProg (j : Fin m) : RProg (WIn m N) Unit :=
  RProg.ofProg (Prog.sumProd ((List.finRange N).map fun k =>
    (Arg.inp (Sum.inl (j, k)), Arg.inp (Sum.inl (j, k)))))

/-- `(q_j, c√q_j)`. -/
def rowAProg (c : ℚ) (j : Fin m) : RProg (WIn m N) (Unit ⊕ Unit) :=
  RProg.ext (rowSqProg m N j) (RExpr.mul (.cst c) (RExpr.sqrt (.inp (Sum.inr ())))).prog

def pA (c : ℚ) : RProg (WIn m N) (Fin m × (Unit ⊕ Unit)) :=
  RProg.parL2 (rowAProg m N c) (List.finRange m)

abbrev K1 : Type := Fin m × (Unit ⊕ Unit)
abbrev K2 : Type := (Unit ⊕ Unit) ⊕ Fin (J + 1)
abbrev EA : Type := WIn m N ⊕ K1 m

def sumQProg : RProg (EA m N) Unit :=
  RProg.ofProg (Prog.sumArgs ((List.finRange m).map fun j => Arg.inp (Sum.inr (j, Sum.inl ()))))

/-- `S_W = Σq_j/m`. -/
def pSW : RProg (EA m N) Unit :=
  (sumQProg m N).bind (RExpr.div (.inp (Sum.inr ())) (.cst (m : ℚ))).prog

/-- `t = √(S_W d)/√J`. -/
def tE (d : ℚ) : RExpr (EA m N ⊕ Unit) :=
  RExpr.div (RExpr.sqrt (RExpr.mul (.inp (Sum.inr ())) (.cst d))) (RExpr.sqrt (.cst (J : ℚ)))

/-- `o_q = (2q − J)t`. -/
def offE (q : Fin (J + 1)) : RExpr (EA m N ⊕ (Unit ⊕ Unit)) :=
  RExpr.mul (.cst (2 * (q : ℚ) - J)) (.inp (Sum.inr (Sum.inr ())))

def pBO (d : ℚ) : RProg (EA m N) (K2 J) :=
  RProg.ext (RProg.ext (pSW m N) (tE m N J d).prog) (RProg.parV (offE m N J))

def q2 (c d : ℚ) : RProg (WIn m N) (K1 m ⊕ K2 J) := RProg.ext (pA m N c) (pBO m N J d)

abbrev EB : Type := WIn m N ⊕ (K1 m ⊕ K2 J)

/-- `a = W₂ h`. -/
def pH : RProg (EB m N J) (Fin m) :=
  RProg.ofProg ((mulVecProg m m).mapIn
    (Sum.elim (fun j => Sum.inr (Sum.inl (j, Sum.inr ()))) (fun p => Sum.inl (Sum.inr p))))

def q3 (c d : ℚ) : RProg (WIn m N) ((K1 m ⊕ K2 J) ⊕ Fin m) := RProg.ext (q2 m N J c d) (pH m N J)

abbrev EC : Type := WIn m N ⊕ ((K1 m ⊕ K2 J) ⊕ Fin m)

def aIC (i : Fin m) : EC m N J := Sum.inr (Sum.inr i)
def oIC (q : ℕ) : EC m N J :=
  Sum.inr (Sum.inl (Sum.inr (Sum.inr ⟨q % (J + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩)))

/-- The atom `q = 0`: `w₀ relu(a_i + o₀)`. -/
def bInitE (i : Fin m) : RExpr (EC m N J) :=
  RExpr.mul (.cst ((J.choose 0 : ℚ) / 2 ^ J)) (RExpr.relu (RExpr.add (.inp (aIC m N J i)) (.inp (oIC m N J 0))))

/-- The atom `q = t + 1`, added to the sum. -/
def bStepE (i : Fin m) (t : ℕ) : RExpr (EC m N J ⊕ Unit) :=
  RExpr.add (.inp (Sum.inr ())) (RExpr.mul (.cst ((J.choose (t + 1) : ℚ) / 2 ^ J))
    (RExpr.relu (RExpr.add (.inp (Sum.inl (aIC m N J i))) (.inp (Sum.inl (oIC m N J (t + 1)))))))

def bLoop (i : Fin m) : RProg (EC m N J) Unit :=
  RProg.iter (bInitE m N J i).prog (fun t => (bStepE m N J i t).prog) J

def q4 (c d : ℚ) : RProg (WIn m N) (((K1 m ⊕ K2 J) ⊕ Fin m) ⊕ Fin m) :=
  RProg.ext (q3 m N J c d) (RProg.parF (bLoop m N J))

abbrev ED : Type := WIn m N ⊕ (((K1 m ⊕ K2 J) ⊕ Fin m) ⊕ Fin m)

/-- `ν = |b|²`. -/
def nuProg : RProg (ED m N J) Unit :=
  RProg.ofProg (Prog.sumProd ((List.finRange m).map fun i =>
    (Arg.inp (Sum.inr (Sum.inr i)), Arg.inp (Sum.inr (Sum.inr i)))))

def swIx : ED m N J ⊕ Unit := Sum.inl (Sum.inr (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inl ()))))))

/-- `κ = (√kA + kB)/kP`. -/
def kapE (kA kB kP : ℚ) : RExpr (ED m N J ⊕ Unit) :=
  RExpr.div (RExpr.add (RExpr.sqrt (.cst kA)) (.cst kB)) (.cst kP)

/-- `τ₀ = √((2/m)ν·relu(2nn(2/m)ν/(S_W κ²) − 1))`. -/
def tauE (kA kB kP : ℚ) (nn : ℕ) : RExpr (ED m N J ⊕ Unit) :=
  RExpr.sqrt (RExpr.mul (RExpr.mul (.cst (2 / m)) (.inp (Sum.inr ())))
    (RExpr.relu (RExpr.sub (RExpr.div (RExpr.mul (.cst (2 * nn * (2 / m))) (.inp (Sum.inr ())))
      (RExpr.mul (.inp (swIx m N J)) (RExpr.mul (kapE m N J kA kB kP) (kapE m N J kA kB kP))))
      (.cst 1))))

/-- **The World pass.** Output `Sum.inl (Sum.inr i)`: `b_{W,i}`; output `Sum.inr ()`: `τ₀`. -/
def worldProg (c d kA kB kP : ℚ) (nn : ℕ) :
    RProg (WIn m N) ((((K1 m ⊕ K2 J) ⊕ Fin m) ⊕ Fin m) ⊕ Unit) :=
  RProg.ext (q4 m N J c d) ((nuProg m N J).bind (tauE m N J kA kB kP nn).prog)

end prog

/-! ## The values -/

section values

variable {m N : ℕ} (J : ℕ) (θ : HidParam N m) (c d : ℚ)

theorem rowSqProg_eval (j : Fin m) :
    (rowSqProg m N j).eval (wVal θ) () = normSq (BstLean.Part130.rowOf j θ.1) := by
  rw [rowSqProg, RProg.eval_ofProg, eval_sumProd, List.map_map, normSq, Fin.sum_univ_def]
  congr 1
  apply List.map_congr_left
  intro k _
  simp [Arg.eval, wVal, BstLean.Part130.rowOf, pow_two]

theorem pA_eval (j : Fin m) :
    (pA m N c).eval (wVal θ) (j, Sum.inl ()) = normSq (BstLean.Part130.rowOf j θ.1) ∧
      (pA m N c).eval (wVal θ) (j, Sum.inr ()) =
        (c : ℝ) * √(normSq (BstLean.Part130.rowOf j θ.1)) := by
  rw [pA, RProg.eval_parL2 _ _ _ _ _ (List.mem_finRange j),
    RProg.eval_parL2 _ _ _ _ _ (List.mem_finRange j)]
  constructor
  · rw [rowAProg, RProg.eval_ext_inl, rowSqProg_eval]
  · rw [rowAProg, RProg.eval_ext_inr, RExpr.eval_prog]
    simp [rowSqProg_eval]

/-- `S_W` in closed form. -/
theorem q2_SW : (q2 m N J c d).eval (wVal θ) (Sum.inr (Sum.inl (Sum.inl ()))) =
    rowS θ.1 / (m : ℝ) := by
  simp only [q2, RProg.eval_ext_inr, pBO, RProg.eval_ext_inl, pSW, RProg.eval_bind,
    RExpr.eval_prog, RExpr.eval_div, RExpr.eval_inp, RExpr.eval_cst, Sum.elim_inr]
  rw [sumQProg, RProg.eval_ofProg, eval_sumArgs, List.map_map, rowS, Fin.sum_univ_def]
  congr 1
  · congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply, Arg.eval, Sum.elim_inr, (pA_eval θ c j).1]
  all_goals simp

theorem q2_t : (q2 m N J c d).eval (wVal θ) (Sum.inr (Sum.inl (Sum.inr ()))) =
    √(rowS θ.1 / (m : ℝ) * d) / √(J : ℝ) := by
  have h := q2_SW J θ c d
  simp only [q2, RProg.eval_ext_inr, pBO, RProg.eval_ext_inl] at h ⊢
  simp only [tE, RExpr.eval_prog, RExpr.eval_div, RExpr.eval_sqrt, RExpr.eval_mul,
    RExpr.eval_inp, RExpr.eval_cst, Sum.elim_inr, h]
  try simp

theorem q2_o (q : Fin (J + 1)) : (q2 m N J c d).eval (wVal θ) (Sum.inr (Sum.inr q)) =
    (2 * (q : ℝ) - J) * (√(rowS θ.1 / (m : ℝ) * d) / √(J : ℝ)) := by
  have h := q2_t J θ c d
  simp only [q2, RProg.eval_ext_inr, RProg.eval_ext_inl, pBO] at h
  simp only [q2, RProg.eval_ext_inr, RProg.eval_ext_inl, pBO, RProg.eval_parV, offE,
    RExpr.eval_mul, RExpr.eval_inp, RExpr.eval_cst, Sum.elim_inr]
  rw [h]
  push_cast
  ring

theorem q3_a (i : Fin m) : (q3 m N J c d).eval (wVal θ) (Sum.inr i) = aOf (c : ℝ) θ i := by
  simp only [q3, RProg.eval_ext_inr, pH, RProg.eval_ofProg, BstLean.Cost.eval_mapIn]
  have h : (Sum.elim (wVal θ) ((q2 m N J c d).eval (wVal θ)) ∘
      Sum.elim (fun j => Sum.inr (Sum.inl (j, Sum.inr ()))) (fun p => Sum.inl (Sum.inr p))) =
      Sum.elim (fun j => (c : ℝ) * √(normSq (BstLean.Part130.rowOf j θ.1)))
        (fun p : Fin m × Fin m => θ.2 p.1 p.2) := by
    funext x
    rcases x with j | p
    · simp only [Function.comp_apply, Sum.elim_inl, Sum.elim_inr, q2, RProg.eval_ext_inl]
      exact (pA_eval θ c j).2
    · rfl
  rw [h, mulVecProg_eval]
  rfl

/-- The sum of the atoms after `t` steps. -/
theorem bLoop_aux (i : Fin m) (w : EC m N J → ℝ) (a : ℝ) (o : ℕ → ℝ)
    (ha : w (aIC m N J i) = a) (ho : ∀ q, q ≤ J → w (oIC m N J q) = o q) (t : ℕ) (ht : t ≤ J) :
    (RProg.iter (bInitE m N J i).prog (fun t => (bStepE m N J i t).prog) t).eval w () =
      ∑ q ∈ Finset.range (t + 1), ((J.choose q : ℚ) / 2 ^ J : ℚ) * relu (a + o q) := by
  induction t with
  | zero =>
    simp [bInitE, ha, ho 0 (Nat.zero_le _)]
  | succ t ih =>
    have ih' : (RProg.iter (bInitE m N J i).prog (fun t => (bStepE m N J i t).prog) t).eval w =
        fun _ => ∑ q ∈ Finset.range (t + 1), ((J.choose q : ℚ) / 2 ^ J : ℚ) * relu (a + o q) :=
      funext fun u => by cases u; exact ih (by omega)
    rw [RProg.eval_iter_succ, ih', RExpr.eval_prog]
    simp only [bStepE, RExpr.eval_add, RExpr.eval_mul, RExpr.eval_relu, RExpr.eval_inp,
      RExpr.eval_cst, Sum.elim_inr, Sum.elim_inl, ha, ho (t + 1) ht]
    rw [Finset.sum_range_succ (n := t + 1)]

theorem q4_b (i : Fin m) : (q4 m N J c d).eval (wVal θ) (Sum.inr i) =
    binMean J (fun z => relu (aOf (c : ℝ) θ i + √(rowS θ.1 / (m : ℝ) * d) * z)) := by
  simp only [q4, RProg.eval_ext_inr, RProg.eval_parF, bLoop]
  rw [bLoop_aux J i _ (aOf (c : ℝ) θ i)
    (fun q => (2 * (q : ℝ) - J) * (√(rowS θ.1 / (m : ℝ) * d) / √(J : ℝ)))
    (by simp only [aIC, Sum.elim_inr, q3_a]) ?_ J le_rfl]
  · unfold binMean binW binAtom
    refine Finset.sum_congr rfl fun q _ => ?_
    push_cast
    have e : (2 * (q : ℝ) - J) * (√(rowS θ.1 / (m : ℝ) * d) / √(J : ℝ)) =
        √(rowS θ.1 / (m : ℝ) * d) * ((2 * q - J) / √(J : ℝ)) := by ring
    rw [e]
  · intro q hq
    simp only [oIC, Sum.elim_inr, q3, RProg.eval_ext_inl]
    rw [q2_o]
    simp [Nat.mod_eq_of_lt (Nat.lt_succ_of_le hq)]

theorem worldProg_bW (kA kB kP : ℚ) (nn : ℕ) (i : Fin m) :
    (worldProg m N J c d kA kB kP nn).eval (wVal θ) (Sum.inl (Sum.inr i)) =
      binMean J (fun z => relu (aOf (c : ℝ) θ i + √(rowS θ.1 / (m : ℝ) * d) * z)) := by
  simp only [worldProg, RProg.eval_ext_inl]
  exact q4_b J θ c d i

theorem worldProg_tau (kA kB kP : ℚ) (nn : ℕ) :
    (worldProg m N J c d kA kB kP nn).eval (wVal θ) (Sum.inr ()) =
      √(((2 / m : ℚ) : ℝ) *
          normSq (fun i => binMean J (fun z => relu (aOf (c : ℝ) θ i + √(rowS θ.1 / (m : ℝ) * d) * z))) *
        relu (((2 * nn * (2 / m) : ℚ) : ℝ) *
          normSq (fun i => binMean J (fun z => relu (aOf (c : ℝ) θ i + √(rowS θ.1 / (m : ℝ) * d) * z))) /
          (rowS θ.1 / (m : ℝ) * ((√((kA : ℚ) : ℝ) + ((kB : ℚ) : ℝ)) / ((kP : ℚ) : ℝ) *
            ((√((kA : ℚ) : ℝ) + ((kB : ℚ) : ℝ)) / ((kP : ℚ) : ℝ)))) - ((1 : ℚ) : ℝ))) := by
  have hnu : (nuProg m N J).eval (Sum.elim (wVal θ) ((q4 m N J c d).eval (wVal θ))) () =
      normSq (fun i => binMean J (fun z => relu (aOf (c : ℝ) θ i + √(rowS θ.1 / (m : ℝ) * d) * z))) := by
    rw [nuProg, RProg.eval_ofProg, eval_sumProd, List.map_map, normSq, Fin.sum_univ_def]
    congr 1
    apply List.map_congr_left
    intro i _
    simp only [Function.comp_apply, Arg.eval, Sum.elim_inr, q4_b, pow_two]
  have hsw : Sum.elim (wVal θ) ((q4 m N J c d).eval (wVal θ))
      (Sum.inr (Sum.inl (Sum.inl (Sum.inr (Sum.inl (Sum.inl ())))))) = rowS θ.1 / (m : ℝ) := by
    simp only [Sum.elim_inr, q4, q3, RProg.eval_ext_inl]
    exact q2_SW J θ c d
  simp only [worldProg, RProg.eval_ext_inr, RProg.eval_bind, RExpr.eval_prog]
  simp only [tauE, kapE, swIx, RExpr.eval_sqrt, RExpr.eval_mul, RExpr.eval_relu, RExpr.eval_sub,
    RExpr.eval_div, RExpr.eval_add, RExpr.eval_inp, RExpr.eval_cst, Sum.elim_inr, Sum.elim_inl,
    hnu, hsw]

end values

/-! ## The World pass of the stated program -/

theorem bWp_eq_worldProg {n : ℕ} (θ : WHid n) (i : Fin (mW n)) :
    bWp θ i = (worldProg (mW n) (2 * n) (JW n) (cQ n) (dQ n) (kapA n) (kapB n) (piQ n) n).eval
      (wVal θ) (Sum.inl (Sum.inr i)) := by
  rw [worldProg_bW, cQ_cast, dQ_cast]
  rfl

theorem tau0p_eq_worldProg {n : ℕ} (θ : WHid n) :
    tau0p θ = (worldProg (mW n) (2 * n) (JW n) (cQ n) (dQ n) (kapA n) (kapB n) (piQ n) n).eval
      (wVal θ) (Sum.inr ()) := by
  have hb : (fun i => binMean (JW n) (fun z =>
      relu (aOf ((cQ n : ℚ) : ℝ) θ i + √(rowS θ.1 / (mW n : ℝ) * ((dQ n : ℚ) : ℝ)) * z))) = bWp θ := by
    funext i; rw [bWp_eq_worldProg, worldProg_bW]
  rw [worldProg_tau, hb, ← kapT_eq, tau0p, SWp]
  push_cast
  simp only [relu]
  ring_nf

/-! ## The cost -/

theorem worldProg_cost (m N J : ℕ) (c d kA kB kP : ℚ) (nn : ℕ) (hm : 1 ≤ m) (hN : 1 ≤ N) :
    (worldProg m N J c d kA kB kP nn).cost =
      m * (2 * N + 1) + (m - 1) + 5 + (J + 1) + m * (2 * m - 1) + m * (4 * J + 3) +
        (2 * m - 1) + 15 := by
  have hrow : ∀ j, (rowAProg m N c j).cost = 2 * N + 1 := by
    intro j
    simp [rowAProg, rowSqProg, cost_sumProd]
    omega
  have hloop : ∀ i, (bLoop m N J i).cost = 4 * J + 3 := by
    intro i
    rw [bLoop, RProg.cost_iter_const _ _ _ 4 (fun t => by simp [bStepE])]
    simp [bInitE]; ring
  simp only [worldProg, q4, q3, q2, pA, pBO, pSW, RProg.cost_ext, RProg.cost_bind,
    RExpr.cost_prog, RProg.cost_parV]
  rw [RProg.cost_parL2, list_sum_const _ _ _ hrow, RProg.cost_parF_eq _ _ hloop]
  simp [sumQProg, nuProg, pH, cost_sumArgs, cost_sumProd, mulVecProg_cost, tE, offE, tauE, kapE]
  first | omega | ring_nf | (ring_nf; omega)

end

end BstLean.Part282
