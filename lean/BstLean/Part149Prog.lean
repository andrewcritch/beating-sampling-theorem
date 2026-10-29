import BstLean.Part149SDefs
import BstLean.Part140Cost

/-!
# Part 149, item 5: the stage of the network `A` as straight-line programs (no forward pass of `A`)

Do not use `sorry`, `native_decide` or `axiom`.

The model is `RProg` of `Part130Cost` (operations `+ − × ÷ √ relu`, each costs one). The pattern
is that of `Part140Cost`: two programs with an ORACLE between them. `m` is the hidden width of
`A`, `A₂` (`m × m`) and `A₃` (`n × m`) are the second and the third matrix of `A`.

* The oracle inputs: the vector `b₁ : ℝ^m` and the number `N₂` (in the application
  `b₁ = b1 c τ A₁`, `N₂ = N2 c τ A₁`). They are INPUTS of the program; no program computes them.
* `preProgB m`: from the entries of `A₂`, the vector `b₁` and the number `N₂`: the vector
  `a = A₂ b₁` (outputs `inl i`) and the scale `s = √((2/m)(N₂ − |b₁|²))` (output `inr ()`)
  (`preProgB_eval_a`, `preProgB_eval_s`, `preProgB_cost`).
* the oracle: `b_i = psiS s a_i`, one oracle operation per coordinate: `m` oracle operations
  (`preProgB_bMF`). They are not instructions of `RProg`.
* `postProgB k n m mF`: from the centre `b`, the entries of `A₃`, the weights of `F` and `k`
  vectors `γ_i`: the mean of `F(A₃ b + τ·γ_i)`, `τ = tauOutOf n b` (`postProgB_eval`,
  `postProgB_cost`, `postProgB_gSampB`). There is no `sphProj` and no evaluation of `A`.
* `costB`, `costB149`: the total count is at most
  `2m² + m(2n + 4) + 8 + k(2n + 1 + cost of F)`. The cost of a forward pass of `A` does not
  occur, and the term `2m²` occurs once.
-/

namespace BstLean.Part149

open BstLean.Cost
open BstLean.Part130 BstLean.Part140 BstLean.Part141
open BstLean.Part137 (psiS)

noncomputable section

section tails

variable {ι : Type}

/-- From `q` (the input `inr ()`) and the input `c`: `√((2/m)(c − q))`, by 3 operations. -/
def sTailB (m : ℕ) (c : ι) : RProg (ι ⊕ Unit) Unit :=
  ⟨[⟨.sub, .inp (Sum.inl c), .inp (Sum.inr ())⟩,
    ⟨.mul, .cst (2 / (m : ℚ)), .reg 0⟩,
    ⟨.sqrt, .reg 1, .reg 1⟩], fun _ => .reg 2⟩

theorem sTailB_eval (m : ℕ) (c : ι) (v : ι ⊕ Unit → ℝ) (u : Unit) :
    (sTailB m c).eval v u = √(2 / (m : ℝ) * (v (Sum.inl c) - v (Sum.inr ()))) := by
  simp [sTailB, RProg.eval, rrun, RInstr.eval, ROp.eval, Arg.eval]

theorem sTailB_cost (m : ℕ) (c : ι) : (sTailB m c).cost = 3 := rfl

/-- From `q` (the input `inr ()`): `√(relu(2/n − (2/m)q))`, by 4 operations. -/
def tauTailB (n m : ℕ) (ι : Type) : RProg (ι ⊕ Unit) Unit :=
  ⟨[⟨.mul, .cst (2 / (m : ℚ)), .inp (Sum.inr ())⟩,
    ⟨.sub, .cst (2 / (n : ℚ)), .reg 0⟩,
    ⟨.relu, .reg 1, .reg 1⟩,
    ⟨.sqrt, .reg 2, .reg 2⟩], fun _ => .reg 3⟩

theorem tauTailB_eval (n m : ℕ) (v : ι ⊕ Unit → ℝ) (u : Unit) :
    (tauTailB n m ι).eval v u = √(relu (2 / (n : ℝ) - 2 / (m : ℝ) * v (Sum.inr ()))) := by
  simp [tauTailB, RProg.eval, rrun, RInstr.eval, ROp.eval, Arg.eval]

theorem tauTailB_cost (n m : ℕ) : (tauTailB n m ι).cost = 4 := rfl

end tails

/-! ## The program before the oracle -/

section pre

variable (m : ℕ)

/-- The inputs of `preProgB`: the entries of `A₂`, the vector `b₁`, the number `N₂`. -/
abbrev PreInB : Type := (Fin m × Fin m) ⊕ Fin m ⊕ Unit

variable {m}

/-- The inputs as one valuation. -/
def preValB (A₂ : Matrix (Fin m) (Fin m) ℝ) (b₁ : Fin m → ℝ) (N₂ : ℝ) : PreInB m → ℝ :=
  Sum.elim (fun e => A₂ e.1 e.2) (Sum.elim b₁ (fun _ => N₂))

variable (m)

/-- `a = A₂ b₁`: `m(2m − 1)` operations. -/
def aProgB : RProg (PreInB m) (Fin m) :=
  (RProg.args (fun j : Fin m => Arg.inp (Sum.inr (Sum.inl j)))).linStep (fun e => Sum.inl e)

/-- `s = √((2/m)(N₂ − |b₁|²))`: `(2m − 1) + 3` operations. -/
def sProgB : RProg (PreInB m) Unit :=
  (RProg.ofProg (sqProg m (fun j => (Sum.inr (Sum.inl j) : PreInB m)))).bind
    (sTailB m (Sum.inr (Sum.inr ())))

/-- **The program before the oracle**: from the entries of `A₂`, the vector `b₁` and the number
`N₂`: the vector `a = A₂ b₁` (outputs `inl i`) and the scale `s` (output `inr ()`). The centre is
then `b_i = psiS s a_i`: one ORACLE operation per coordinate (not in this program). -/
def preProgB : RProg (PreInB m) (Fin m ⊕ Unit) :=
  (aProgB m).ext ((sProgB m).mapIn Sum.inl)

variable {m}

theorem preProgB_eval_a (A₂ : Matrix (Fin m) (Fin m) ℝ) (b₁ : Fin m → ℝ) (N₂ : ℝ) (i : Fin m) :
    (preProgB m).eval (preValB A₂ b₁ N₂) (Sum.inl i) = (A₂.mulVec b₁) i := by
  rw [preProgB, RProg.eval_ext_inl, aProgB,
    RProg.eval_linStep _ _ (preValB A₂ b₁ N₂) A₂ (fun _ => rfl)]
  rfl

theorem preProgB_eval_s (A₂ : Matrix (Fin m) (Fin m) ℝ) (b₁ : Fin m → ℝ) (N₂ : ℝ) :
    (preProgB m).eval (preValB A₂ b₁ N₂) (Sum.inr ()) =
      √(2 / (m : ℝ) * (N₂ - normSq b₁)) := by
  rw [preProgB, RProg.eval_ext_inr, RProg.eval_mapIn, sProgB, RProg.eval_bind, sTailB_eval]
  simp only [Sum.elim_inr, Sum.elim_inl, Function.comp, RProg.eval_ofProg, sqProg_eval]
  rfl

/-- **The operation count of `preProgB`** (exact). -/
theorem preProgB_cost : (preProgB m).cost = m * (2 * m - 1) + (2 * m - 1) + 3 := by
  simp only [preProgB, RProg.cost_ext, RProg.cost_mapIn, aProgB, RProg.cost_linStep,
    RProg.cost_args, sProgB, RProg.cost_bind, RProg.cost_ofProg, sqProg_cost, sTailB_cost]
  omega

theorem preProgB_cost_le : (preProgB m).cost ≤ m * (2 * m - 1) + 2 * m + 3 := by
  rw [preProgB_cost]
  omega

end pre

/-! ## The program after the oracle -/

section post

variable (k n m mF : ℕ)

/-- The inputs of `postProgB`: the centre `b`, the entries of `A₃`, the `k` vectors `γ_i`, the
weights of `F`. -/
abbrev PostInB : Type := Fin m ⊕ (Fin n × Fin m) ⊕ (Fin k × Fin n) ⊕ MlpW n mF 1

variable {k n m mF}

/-- The inputs as one valuation. -/
def postValB (b : Fin m → ℝ) (A₃ : Matrix (Fin n) (Fin m) ℝ) (F : MlpParam n mF 1)
    (γ : Fin k → Fin n → ℝ) : PostInB k n m mF → ℝ :=
  Sum.elim b (Sum.elim (fun e => A₃ e.1 e.2) (Sum.elim (fun e => γ e.1 e.2) (mlpW F)))

variable (k n m mF)

/-- `A₃ b`: `n(2m − 1)` operations. -/
def cProgB : RProg (PostInB k n m mF) (Fin n) :=
  (RProg.args (fun j : Fin m => Arg.inp (Sum.inl j))).linStep (fun e => Sum.inr (Sum.inl e))

/-- `τ = tauOutOf n b`: `(2m − 1) + 4` operations. -/
def tauProgB : RProg (PostInB k n m mF) Unit :=
  (RProg.ofProg (sqProg m (fun j => (Sum.inl j : PostInB k n m mF)))).bind (tauTailB n m _)

/-- `A₃ b` and `τ`. -/
def postPreB : RProg (PostInB k n m mF) (Fin n ⊕ Unit) :=
  (cProgB k n m mF).ext ((tauProgB k n m mF).mapIn Sum.inl)

/-- `y_i = A₃ b + τ·γ_i`: `2n` operations. -/
def yProgB (i : Fin k) : RProg (PostInB k n m mF ⊕ (Fin n ⊕ Unit)) (Fin n) :=
  RProg.ofProg (Prog.par (fun j : Fin n =>
      axpyIn (Sum.inr (Sum.inl j)) (Sum.inr (Sum.inr ()))
        (Sum.inl (Sum.inr (Sum.inr (Sum.inl (i, j))))))
    (List.finRange n))

/-- One sample: `F(y_i)` (a forward pass of `F` only). -/
def postSampleB (i : Fin k) : RProg (PostInB k n m mF ⊕ (Fin n ⊕ Unit)) Unit :=
  ((yProgB k n m mF i).mlpStep
    (fun e => Sum.inl (Sum.inr (Sum.inr (Sum.inr e))))).mapOut (fun _ => (0 : Fin 1))

/-- **The program after the oracle**: from the centre `b`, `A₃`, `k` vectors `γ_i` and the
weights of `F`: the mean of `F(A₃ b + τ·γ_i)`, `τ = tauOutOf n b`. No evaluation of `A`. -/
def postProgB : RProg (PostInB k n m mF) Unit :=
  (postPreB k n m mF).bind
    ((RProg.par (postSampleB k n m mF) (List.finRange k)).bind (meanTail k _))

variable {k n m mF}

theorem cProgB_eval (b : Fin m → ℝ) (A₃ : Matrix (Fin n) (Fin m) ℝ) (F : MlpParam n mF 1)
    (γ : Fin k → Fin n → ℝ) :
    (cProgB k n m mF).eval (postValB b A₃ F γ) = A₃.mulVec b := by
  rw [cProgB, RProg.eval_linStep _ _ (postValB b A₃ F γ) A₃ (fun _ => rfl)]
  rfl

theorem tauProgB_eval (b : Fin m → ℝ) (A₃ : Matrix (Fin n) (Fin m) ℝ) (F : MlpParam n mF 1)
    (γ : Fin k → Fin n → ℝ) (u : Unit) :
    (tauProgB k n m mF).eval (postValB b A₃ F γ) u = tauOutOf n b := by
  rw [tauProgB, RProg.eval_bind, tauTailB_eval]
  simp only [Sum.elim_inr, RProg.eval_ofProg, sqProg_eval]
  rfl

theorem postSampleB_eval (i : Fin k) (v : PostInB k n m mF ⊕ (Fin n ⊕ Unit) → ℝ)
    (γ : Fin k → Fin n → ℝ) (F : MlpParam n mF 1)
    (hγ : ∀ j, v (Sum.inl (Sum.inr (Sum.inr (Sum.inl (i, j))))) = γ i j)
    (hF : ∀ e, v (Sum.inl (Sum.inr (Sum.inr (Sum.inr e)))) = mlpW F e) (u : Unit) :
    (postSampleB k n m mF i).eval v u =
      evF F ((fun j => v (Sum.inr (Sum.inl j))) + v (Sum.inr (Sum.inr ())) • γ i) := by
  have hy : (yProgB k n m mF i).eval v =
      (fun j => v (Sum.inr (Sum.inl j))) + v (Sum.inr (Sum.inr ())) • γ i := by
    funext j
    rw [yProgB, RProg.eval_ofProg, eval_par_mem _ _ _ _ (List.mem_finRange j), axpyIn_eval, hγ]
    simp
  rw [postSampleB, RProg.eval_mapOut, RProg.eval_mlpStep _ _ v F hF, hy]
  rfl

/-- **The value of `postProgB`**: the mean of `F(A₃ b + τ·γ_i)` over the `k` vectors,
`τ = tauOutOf n b`. -/
theorem postProgB_eval (b : Fin m → ℝ) (A₃ : Matrix (Fin n) (Fin m) ℝ) (F : MlpParam n mF 1)
    (γ : Fin k → Fin n → ℝ) :
    (postProgB k n m mF).eval (postValB b A₃ F γ) () =
      (k : ℝ)⁻¹ * ∑ i, evF F (A₃.mulVec b + tauOutOf n b • γ i) := by
  rw [postProgB, RProg.eval_bind, RProg.eval_bind, meanTail_eval]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Sum.elim_inr]
  rw [RProg.eval_par_mem _ _ _ _ (List.mem_finRange i),
    postSampleB_eval i _ γ F (fun _ => rfl) (fun _ => rfl)]
  congr 1
  have h1 : (fun j : Fin n => Sum.elim (postValB b A₃ F γ)
      ((postPreB k n m mF).eval (postValB b A₃ F γ)) (Sum.inr (Sum.inl j))) =
      A₃.mulVec b := by
    funext j
    simp only [Sum.elim_inr, postPreB, RProg.eval_ext_inl]
    rw [cProgB_eval]
  have h2 : Sum.elim (postValB b A₃ F γ)
      ((postPreB k n m mF).eval (postValB b A₃ F γ)) (Sum.inr (Sum.inr ())) =
      tauOutOf n b := by
    simp only [Sum.elim_inr, postPreB, RProg.eval_ext_inr, RProg.eval_mapIn]
    exact tauProgB_eval b A₃ F γ ()
  rw [h1, h2]

theorem postSampleB_cost (i : Fin k) :
    (postSampleB k n m mF i).cost = 2 * n + mlpCost n mF 1 := by
  have hy : (yProgB k n m mF i).cost = 2 * n := by
    simp [yProgB, cost_par, axpyIn_cost]
    ring
  simp only [postSampleB, RProg.cost_mapOut, RProg.cost_mlpStep, hy]

/-- **The operation count of `postProgB`.** -/
theorem postProgB_cost :
    (postProgB k n m mF).cost ≤ n * (2 * m - 1) + (2 * m + 4) +
      k * (2 * n + mlpCost n mF 1) + k + 1 := by
  have h1 : (postPreB k n m mF).cost ≤ n * (2 * m - 1) + (2 * m + 4) := by
    simp only [postPreB, RProg.cost_ext, RProg.cost_mapIn, cProgB, RProg.cost_linStep,
      RProg.cost_args, tauProgB, RProg.cost_bind, RProg.cost_ofProg, sqProg_cost, tauTailB_cost]
    omega
  have h2 : (RProg.par (postSampleB k n m mF) (List.finRange k)).cost ≤
      k * (2 * n + mlpCost n mF 1) := by
    rw [RProg.cost_par]
    have := List.sum_le_length_nsmul
      ((List.finRange k).map fun i => (postSampleB k n m mF i).cost)
      (2 * n + mlpCost n mF 1) (by
        intro x hx
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
        exact le_of_eq (postSampleB_cost i))
    simpa using this
  have h3 : (meanTail k (PostInB k n m mF ⊕ (Fin n ⊕ Unit))).cost ≤ k + 1 := by
    simp only [meanTail, RProg.cost_ofProg, cost_bind, sumProg_cost, cost_op1]
    omega
  simp only [postProgB, RProg.cost_bind]
  omega

end post

/-! ## The connection to the definitions of this part -/

section link

variable {n k : ℕ}

/-- The oracle `psiS` applied to the outputs of `preProgB` (at the oracle inputs `b1`, `N2`)
gives the mean-field centre: `m` oracle operations. -/
theorem preProgB_bMF (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (i : Fin (mA n)) :
    psiS ((preProgB (mA n)).eval
        (preValB A.2.1 (b1 (cenA W) (tauWA W) A.1) (N2 (cenA W) (tauWA W) A.1)) (Sum.inr ()))
      ((preProgB (mA n)).eval
        (preValB A.2.1 (b1 (cenA W) (tauWA W) A.1) (N2 (cenA W) (tauWA W) A.1)) (Sum.inl i)) =
      bMFW W A i := by
  rw [preProgB_eval_s, preProgB_eval_a]
  rfl

/-- The output of `postProgB` at the mean-field centre is the sample output `gSampB`. -/
theorem postProgB_gSampB {mF : ℕ} (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (F : MlpParam n mF 1) (γ : Fin k → Fin n → ℝ) :
    (postProgB k n (mA n) mF).eval (postValB (bMFW W A) A.2.2 F γ) () = gSampB k W A F γ := by
  rw [postProgB_eval]
  rfl

end link

/-! ## The total count -/

/-- The total count of the stage of `A` for hidden width `m`: the program before the oracle,
`m` oracle operations (`psiS`), the program after the oracle. No term is the cost of a forward
pass of `A`. -/
theorem costB (k n m mF : ℕ) :
    (preProgB m).cost + m + (postProgB k n m mF).cost ≤
      2 * m ^ 2 + m * (2 * n + 4) + 8 + k * (2 * n + 1 + mlpCost n mF 1) := by
  have h1 := preProgB_cost_le (m := m)
  have h2 := postProgB_cost (k := k) (n := n) (m := m) (mF := mF)
  have a1 : m * (2 * m - 1) + m ≤ 2 * m ^ 2 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have : m * (2 * m - 1) + m = m * (2 * m - 1 + 1) := by ring
      rw [this, Nat.sub_add_cancel (by omega)]
      exact le_of_eq (by ring)
  have a2 : n * (2 * m - 1) ≤ 2 * (m * n) := by
    calc n * (2 * m - 1) ≤ n * (2 * m) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = 2 * (m * n) := by ring
  have e2 : m * (2 * n + 4) = 2 * (m * n) + 4 * m := by ring
  have e3 : k * (2 * n + mlpCost n mF 1) + k = k * (2 * n + 1 + mlpCost n mF 1) := by ring
  rw [e2]
  generalize k * (2 * n + mlpCost n mF 1) = Y at e3 h2 ⊢
  generalize k * (2 * n + 1 + mlpCost n mF 1) = Z at e3 ⊢
  generalize m * (2 * m - 1) = P at a1 h1 ⊢
  generalize n * (2 * m - 1) = Q at a2 h2 ⊢
  omega

/-- **`costB149`**: at the widths of the Focus the total count of the stage of `A` is at most
`2·m_A² + m_A(2n + 4) + 8 + k·(2n + 1 + cost of F)`: one pass over `A₂` (`2·m_A²`, once, not
`k` times), lower-order terms, and `k` evaluations of `F`. `mlpCost n (mA n) n` does not
occur. -/
theorem costB149 (k n : ℕ) :
    (preProgB (mA n)).cost + mA n + (postProgB k n (mA n) (mF n)).cost ≤
      2 * (mA n) ^ 2 + (mA n) * (2 * n + 4) + 8 + k * (2 * n + 1 + mlpCost n (mF n) 1) :=
  costB k n (mA n) (mF n)

end

end BstLean.Part149

open BstLean.Part149 in
#print axioms preProgB_eval_a
open BstLean.Part149 in
#print axioms preProgB_eval_s
open BstLean.Part149 in
#print axioms preProgB_cost
open BstLean.Part149 in
#print axioms postProgB_eval
open BstLean.Part149 in
#print axioms postProgB_cost
open BstLean.Part149 in
#print axioms preProgB_bMF
open BstLean.Part149 in
#print axioms postProgB_gSampB
open BstLean.Part149 in
#print axioms costB
open BstLean.Part149 in
#print axioms costB149
