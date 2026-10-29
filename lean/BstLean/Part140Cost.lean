import BstLean.Part140Tau
import BstLean.Part130Cost

/-!
# Part 140, item 4 (`cost140`): the estimate with `k` sample points as straight-line programs

Role: `delegations/statements/p140-spec.md` (item 4). Paper sources: `onW8c-cx.md` §7,
`onW17c-cx.md` §7 (the cost `C₁`).

The model is `RProg` of `Part130Cost`: operations `+ − × ÷ √ relu`, each costs one; reading an
input, a register or a rational constant is free; the cost is the number of instructions.

**`ψ_s` is NOT an arithmetic function.** The computed centre is `b̂_i = ψ_s(a_i)`,
`a = M₂ h̄₁`. This file has two programs with an ORACLE between them:

* `preProg N m`: from the entries of `M₁`, `M₂` and the constant `c_N`: the vector `a = M₂ h̄₁`
  and the scale `s` (`preProg_eval_a`, `preProg_eval_s`, `preProg_cost`).
* the oracle: `b̂_i = psiS s a_i`, one oracle operation per coordinate: `m` oracle operations.
  They are counted as `m` in `costHat`; they are not instructions of `RProg`.
* `hatProg k n m mA mF`: from the centre `b`, the entries of `M₃`, the constant
  `c₁ = 1/(γκ₁²)`, `k` Gaussian vectors and the weights of `A`, `F`: the mean of
  `F(A(y_i/|y_i|))`, `y_i = M₃ b + τ·γ_i`, `τ = tauOf m b c₁` (`hatProg_eval`,
  `hatProg_eval_sphPt`, `hatProg_cost`). `tauOf_bhat`: at `b = b̂` and `c₁ = 1/(γκ₁²)` the scalar
  is `tauHat` of `Part140Tau`.
* `costHat`, `cost140`: the total count is at most
  `2m² + m(2N + 2n + 4) + k(5n + 2 + cost of A + cost of F) + 12`.

The constants `c_N = cN N` and `c₁` are real numbers that depend on the dimension only; they are
INPUTS of the programs (the model has rational constants only). The Gaussian vectors are inputs
(free). The program has no branching: it computes `sphProj` (which is `0` at `0`), not `sphPt`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part130

open BstLean.Cost

noncomputable section

/-! ## Small combinators for `RProg` (new names in the namespace of `RProg`) -/

variable {ι ι₂ κ κ₂ ν : Type}

/-- A program with no instructions. -/
def RProg.args (o : κ → Arg ι) : RProg ι κ := ⟨[], o⟩

@[simp] theorem RProg.eval_args (o : κ → Arg ι) (v : ι → ℝ) (k : κ) :
    (RProg.args o).eval v k = (o k).eval v [] := rfl

@[simp] theorem RProg.cost_args (o : κ → Arg ι) : (RProg.args o).cost = 0 := rfl

/-- Run `p`, then `q` on the inputs and `p`'s outputs; keep the outputs of both. -/
def RProg.ext (p : RProg ι κ) (q : RProg (ι ⊕ κ) ν) : RProg ι (κ ⊕ ν) :=
  p.bind ⟨q.body, Sum.elim (fun k => .inp (Sum.inr k)) q.out⟩

theorem RProg.eval_ext_inl (p : RProg ι κ) (q : RProg (ι ⊕ κ) ν) (v : ι → ℝ) (k : κ) :
    (p.ext q).eval v (Sum.inl k) = p.eval v k := by
  simp only [RProg.ext, RProg.eval_bind]
  rfl

theorem RProg.eval_ext_inr (p : RProg ι κ) (q : RProg (ι ⊕ κ) ν) (v : ι → ℝ) (l : ν) :
    (p.ext q).eval v (Sum.inr l) = q.eval (Sum.elim v (p.eval v)) l := by
  simp only [RProg.ext, RProg.eval_bind]
  rfl

@[simp] theorem RProg.cost_ext (p : RProg ι κ) (q : RProg (ι ⊕ κ) ν) :
    (p.ext q).cost = p.cost + q.cost := by
  simp [RProg.ext, RProg.bind, RProg.cost]

/-- Run one program per index in the list `l`; output `k` is program `p k` if `k ∈ l`. -/
def RProg.par [DecidableEq κ] (p : κ → RProg ι Unit) : List κ → RProg ι κ
  | [] => RProg.args fun _ => .cst 0
  | k :: l =>
      (p k).bind
        ⟨((RProg.par p l).mapIn Sum.inl).body,
          fun j => if j = k then .inp (Sum.inr ()) else ((RProg.par p l).mapIn Sum.inl).out j⟩

theorem RProg.eval_par_mem [DecidableEq κ] (p : κ → RProg ι Unit) (l : List κ) (v : ι → ℝ)
    (k : κ) (hk : k ∈ l) : (RProg.par p l).eval v k = (p k).eval v () := by
  induction l with
  | nil => simp at hk
  | cons j l ih =>
    simp only [RProg.par, RProg.eval_bind]
    by_cases h : k = j
    · subst h; simp [RProg.eval, Arg.eval]
    · have hk' : k ∈ l := by simpa [h] using hk
      have := RProg.eval_mapIn Sum.inl (RProg.par p l) (Sum.elim v ((p j).eval v)) k
      simp only [RProg.eval, h, ite_false] at this ⊢
      rw [this]
      exact ih hk'

theorem RProg.cost_par [DecidableEq κ] (p : κ → RProg ι Unit) (l : List κ) :
    (RProg.par p l).cost = (l.map fun k => (p k).cost).sum := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [RProg.par, RProg.cost_bind, List.map_cons, List.sum_cons]
    rw [← ih]
    simp [RProg.cost, RProg.mapIn]

end

end BstLean.Part130

namespace BstLean.Part140

open BstLean.Cost
open BstLean.Part105 (sphProj rescaleProg)
open BstLean.Part132 (nrm nrm_sq)
open BstLean.Part130 BstLean.Part136 BstLean.Part137

noncomputable section

section comb

variable {ι ι₂ κ κ₂ ν : Type}

/-- `Σ_j x_j²` for the inputs `x_j = f j`: `2m − 1` operations. -/
def sqProg (m : ℕ) (f : Fin m → ι) : Prog ι Unit :=
  Prog.sumProd ((List.finRange m).map fun j => (Arg.inp (f j), Arg.inp (f j)))

theorem sqProg_eval (m : ℕ) (f : Fin m → ι) (v : ι → ℝ) (u : Unit) :
    (sqProg m f).eval v u = ∑ j, v (f j) ^ 2 := by
  rw [sqProg, eval_sumProd, List.map_map, Fin.sum_univ_def]
  apply congrArg
  apply List.map_congr_left
  intro j _
  simp [Arg.eval, pow_two]

theorem sqProg_cost (m : ℕ) (f : Fin m → ι) : (sqProg m f).cost = 2 * m - 1 := by
  simp [sqProg, cost_sumProd]

/-- The sum of the inputs `f i`, `i : Fin k`: `k − 1` additions. -/
def sumProg (k : ℕ) (f : Fin k → ι) : Prog ι Unit :=
  Prog.sumArgs ((List.finRange k).map fun i => Arg.inp (f i))

theorem sumProg_eval (k : ℕ) (f : Fin k → ι) (v : ι → ℝ) (u : Unit) :
    (sumProg k f).eval v u = ∑ i, v (f i) := by
  rw [sumProg, eval_sumArgs, List.map_map, Fin.sum_univ_def]
  rfl

theorem sumProg_cost (k : ℕ) (f : Fin k → ι) : (sumProg k f).cost = k - 1 := by
  simp [sumProg, cost_sumArgs]

/-- From `q` (the input `inr ()`) and the input `c`:
`√((2/m)q · relu((2/m)q·c − 1))`, by 6 operations. -/
def tauTail (m : ℕ) (c : ι) : RProg (ι ⊕ Unit) Unit :=
  ⟨[⟨.mul, .cst (2 / (m : ℚ)), .inp (Sum.inr ())⟩,
    ⟨.mul, .reg 0, .inp (Sum.inl c)⟩,
    ⟨.sub, .reg 1, .cst 1⟩,
    ⟨.relu, .reg 2, .reg 2⟩,
    ⟨.mul, .reg 0, .reg 3⟩,
    ⟨.sqrt, .reg 4, .reg 4⟩], fun _ => .reg 5⟩

theorem tauTail_eval (m : ℕ) (c : ι) (v : ι ⊕ Unit → ℝ) (u : Unit) :
    (tauTail m c).eval v u =
      √(2 / (m : ℝ) * v (Sum.inr ()) *
        relu (2 / (m : ℝ) * v (Sum.inr ()) * v (Sum.inl c) - 1)) := by
  simp [tauTail, RProg.eval, rrun, RInstr.eval, ROp.eval, Arg.eval]

theorem tauTail_cost (m : ℕ) (c : ι) : (tauTail m c).cost = 6 := rfl

/-- From `S` (the input `inr ()`) and the input `c`:
`√(S·(1/(mN) − (2/m)c²))`, by 5 operations. -/
def sTail (N m : ℕ) (c : ι) : RProg (ι ⊕ Unit) Unit :=
  ⟨[⟨.mul, .inp (Sum.inl c), .inp (Sum.inl c)⟩,
    ⟨.mul, .cst (2 / (m : ℚ)), .reg 0⟩,
    ⟨.sub, .cst (1 / ((m : ℚ) * N)), .reg 1⟩,
    ⟨.mul, .inp (Sum.inr ()), .reg 2⟩,
    ⟨.sqrt, .reg 3, .reg 3⟩], fun _ => .reg 4⟩

theorem sTail_eval (N m : ℕ) (c : ι) (v : ι ⊕ Unit → ℝ) (u : Unit) :
    (sTail N m c).eval v u =
      √(v (Sum.inr ()) * (1 / ((m : ℝ) * N) - 2 / (m : ℝ) * (v (Sum.inl c) * v (Sum.inl c)))) := by
  simp [sTail, RProg.eval, rrun, RInstr.eval, ROp.eval, Arg.eval]

theorem sTail_cost (N m : ℕ) (c : ι) : (sTail N m c).cost = 5 := rfl

/-- `√x · c` for the inputs `x`, `c`: 2 operations. -/
def sqrtMul (x c : ι) : RProg ι Unit :=
  ⟨[⟨.sqrt, .inp x, .inp x⟩, ⟨.mul, .inp c, .reg 0⟩], fun _ => .reg 1⟩

theorem sqrtMul_eval (x c : ι) (v : ι → ℝ) (u : Unit) :
    (sqrtMul x c).eval v u = v c * √(v x) := by
  simp [sqrtMul, RProg.eval, rrun, RInstr.eval, ROp.eval, Arg.eval]

theorem sqrtMul_cost (x c : ι) : (sqrtMul x c).cost = 2 := rfl

/-- `a + t·g` for the inputs `a`, `t`, `g`: 2 operations. -/
def axpyIn (a t g : ι) : Prog ι Unit :=
  (Prog.op1 .mul (.inp t) (.inp g)).bind (Prog.op1 .add (.inp (Sum.inl a)) (.inp (Sum.inr ())))

theorem axpyIn_eval (a t g : ι) (v : ι → ℝ) (u : Unit) :
    (axpyIn a t g).eval v u = v a + v t * v g := by
  simp [axpyIn, eval_bind, Op.eval, Arg.eval]

theorem axpyIn_cost (a t g : ι) : (axpyIn a t g).cost = 2 := rfl

end comb

/-! ## The scalar -/

/-- `τ` from `|b|²` and the constant `c₁ = 1/(γκ₁²)`:
`τ² = t|b|²·max(0, t|b|²·c₁ − 1)`, `t = 2/m`. -/
def tauOf (m : ℕ) (b : Fin m → ℝ) (c₁ : ℝ) : ℝ :=
  √(2 / (m : ℝ) * normSq b * relu (2 / (m : ℝ) * normSq b * c₁ - 1))

/-- At the computed centre and `c₁ = 1/(γκ₁²)` the scalar is `tauHat`. -/
lemma tauOf_bhat {N m : ℕ} (θ : HidParam N m) :
    tauOf m (bhat θ) (1 / (2 / (N : ℝ) * kap1 N ^ 2)) = tauHat N m θ := by
  unfold tauOf tauHat Bh relu
  rw [mul_one_div]

/-! ## The program after the oracle -/

section hat

variable (k n m mA mF : ℕ)

/-- The inputs of `hatProg`: the centre `b`, the entries of `M₃`, the constant `c₁`, the `k`
Gaussian vectors, the weights of `A` and of `F`. -/
abbrev HatIn : Type :=
  Fin m ⊕ (Fin n × Fin m) ⊕ Unit ⊕ (Fin k × Fin n) ⊕ MlpW n mA n ⊕ MlpW n mF 1

variable {k n m mA mF}

/-- The inputs as one valuation. -/
def hatVal (b : Fin m → ℝ) (M₃ : Matrix (Fin n) (Fin m) ℝ) (c₁ : ℝ) (γ : Fin k → Fin n → ℝ)
    (A : MlpParam n mA n) (F : MlpParam n mF 1) : HatIn k n m mA mF → ℝ :=
  Sum.elim b (Sum.elim (fun e => M₃ e.1 e.2) (Sum.elim (fun _ => c₁)
    (Sum.elim (fun e => γ e.1 e.2) (Sum.elim (mlpW A) (mlpW F)))))

variable (k n m mA mF)

/-- `ĉ = M₃ b`: `n(2m − 1)` operations. -/
def cProg : RProg (HatIn k n m mA mF) (Fin n) :=
  (RProg.args (fun j : Fin m => Arg.inp (Sum.inl j))).linStep (fun e => Sum.inr (Sum.inl e))

/-- `τ = tauOf m b c₁`: `(2m − 1) + 6` operations. -/
def tauProg : RProg (HatIn k n m mA mF) Unit :=
  (RProg.ofProg (sqProg m (fun j => (Sum.inl j : HatIn k n m mA mF)))).bind
    (tauTail m (Sum.inr (Sum.inr (Sum.inl ()))))

/-- `ĉ` and `τ`. -/
def hatPre : RProg (HatIn k n m mA mF) (Fin n ⊕ Unit) :=
  (cProg k n m mA mF).ext ((tauProg k n m mA mF).mapIn Sum.inl)

/-- `y_i = ĉ + τ·γ_i`: `2n` operations. -/
def yProg (i : Fin k) : RProg (HatIn k n m mA mF ⊕ (Fin n ⊕ Unit)) (Fin n) :=
  RProg.ofProg (Prog.par (fun j : Fin n =>
      axpyIn (Sum.inr (Sum.inl j)) (Sum.inr (Sum.inr ()))
        (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j)))))))
    (List.finRange n))

/-- One sample: `F(A(y_i/|y_i|))`. -/
def hatSample (i : Fin k) : RProg (HatIn k n m mA mF ⊕ (Fin n ⊕ Unit)) Unit :=
  ((((yProg k n m mA mF i).rescaleStep).mlpStep
      (fun e => Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl e))))))).mlpStep
    (fun e => Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr e))))))).mapOut
    (fun _ => (0 : Fin 1))

/-- The mean of the `k` values: `k − 1` additions and one multiplication by `1/k`. -/
def meanTail (ι : Type) : RProg (ι ⊕ Fin k) Unit :=
  RProg.ofProg ((sumProg k (fun i => (Sum.inr i : ι ⊕ Fin k))).bind
    (Prog.op1 .mul (.cst (1 / (k : ℚ))) (.inp (Sum.inr ()))))

/-- **The estimate with `k` sample points, after the oracle**: from the centre `b`, `M₃`, the
constant `c₁`, `k` Gaussian vectors `γ_i` and the weights of `A`, `F`: the mean of
`F(A(y_i/|y_i|))`, `y_i = M₃ b + τ·γ_i`, `τ = tauOf m b c₁`. -/
def hatProg : RProg (HatIn k n m mA mF) Unit :=
  (hatPre k n m mA mF).bind
    ((RProg.par (hatSample k n m mA mF) (List.finRange k)).bind (meanTail k _))

variable {k n m mA mF}

theorem cProg_eval (b : Fin m → ℝ) (M₃ : Matrix (Fin n) (Fin m) ℝ) (c₁ : ℝ)
    (γ : Fin k → Fin n → ℝ) (A : MlpParam n mA n) (F : MlpParam n mF 1) :
    (cProg k n m mA mF).eval (hatVal b M₃ c₁ γ A F) = M₃.mulVec b := by
  rw [cProg, RProg.eval_linStep _ _ (hatVal b M₃ c₁ γ A F) M₃ (fun _ => rfl)]
  rfl

theorem tauProg_eval (b : Fin m → ℝ) (M₃ : Matrix (Fin n) (Fin m) ℝ) (c₁ : ℝ)
    (γ : Fin k → Fin n → ℝ) (A : MlpParam n mA n) (F : MlpParam n mF 1) (u : Unit) :
    (tauProg k n m mA mF).eval (hatVal b M₃ c₁ γ A F) u = tauOf m b c₁ := by
  rw [tauProg, RProg.eval_bind, tauTail_eval]
  simp only [Sum.elim_inr, Sum.elim_inl, RProg.eval_ofProg, sqProg_eval]
  rfl

theorem hatSample_eval (i : Fin k) (v : HatIn k n m mA mF ⊕ (Fin n ⊕ Unit) → ℝ)
    (γ : Fin k → Fin n → ℝ) (A : MlpParam n mA n) (F : MlpParam n mF 1)
    (hγ : ∀ j, v (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inl (i, j)))))) = γ i j)
    (hA : ∀ e, v (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl e)))))) = mlpW A e)
    (hF : ∀ e, v (Sum.inl (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr e)))))) = mlpW F e)
    (u : Unit) :
    (hatSample k n m mA mF i).eval v u =
      phiN A F (sphProj ((fun j => v (Sum.inr (Sum.inl j))) +
        v (Sum.inr (Sum.inr ())) • γ i)) := by
  have hy : (yProg k n m mA mF i).eval v =
      (fun j => v (Sum.inr (Sum.inl j))) + v (Sum.inr (Sum.inr ())) • γ i := by
    funext j
    rw [yProg, RProg.eval_ofProg, eval_par_mem _ _ _ _ (List.mem_finRange j), axpyIn_eval, hγ]
    simp
  rw [hatSample, RProg.eval_mapOut, RProg.eval_mlpStep _ _ v F hF,
    RProg.eval_mlpStep _ _ v A hA, RProg.eval_rescaleStep, hy]
  rfl

theorem meanTail_eval (ι : Type) (v : ι ⊕ Fin k → ℝ) (u : Unit) :
    (meanTail k ι).eval v u = (k : ℝ)⁻¹ * ∑ i, v (Sum.inr i) := by
  rw [meanTail, RProg.eval_ofProg, eval_bind, eval_op1]
  simp [Op.eval, Arg.eval, sumProg_eval]

/-- **The value of `hatProg`**: the mean of `F(A(sphProj(M₃ b + τ·γ_i)))` over the `k` Gaussian
vectors, `τ = tauOf m b c₁`. -/
theorem hatProg_eval (b : Fin m → ℝ) (M₃ : Matrix (Fin n) (Fin m) ℝ) (c₁ : ℝ)
    (γ : Fin k → Fin n → ℝ) (A : MlpParam n mA n) (F : MlpParam n mF 1) :
    (hatProg k n m mA mF).eval (hatVal b M₃ c₁ γ A F) () =
      (k : ℝ)⁻¹ * ∑ i, phiN A F (sphProj (M₃.mulVec b + tauOf m b c₁ • γ i)) := by
  rw [hatProg, RProg.eval_bind, RProg.eval_bind, meanTail_eval]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Sum.elim_inr]
  rw [RProg.eval_par_mem _ _ _ _ (List.mem_finRange i),
    hatSample_eval i _ γ A F (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)]
  congr 2
  have h1 : (fun j : Fin n => Sum.elim (hatVal b M₃ c₁ γ A F)
      ((hatPre k n m mA mF).eval (hatVal b M₃ c₁ γ A F)) (Sum.inr (Sum.inl j))) =
      M₃.mulVec b := by
    funext j
    simp only [Sum.elim_inr, hatPre, RProg.eval_ext_inl]
    rw [cProg_eval]
  have h2 : Sum.elim (hatVal b M₃ c₁ γ A F)
      ((hatPre k n m mA mF).eval (hatVal b M₃ c₁ γ A F)) (Sum.inr (Sum.inr ())) =
      tauOf m b c₁ := by
    simp only [Sum.elim_inr, hatPre, RProg.eval_ext_inr, RProg.eval_mapIn]
    exact tauProg_eval b M₃ c₁ γ A F ()
  rw [h1, h2]

/-- The value with the fixed-point normalization `sphPt`, when no `y_i` is zero. -/
theorem hatProg_eval_sphPt (b : Fin m → ℝ) (M₃ : Matrix (Fin n) (Fin m) ℝ) (c₁ : ℝ)
    (γ : Fin k → Fin n → ℝ) (A : MlpParam n mA n) (F : MlpParam n mF 1)
    (h : ∀ i, normSq (M₃.mulVec b + tauOf m b c₁ • γ i) ≠ 0) :
    (hatProg k n m mA mF).eval (hatVal b M₃ c₁ γ A F) () =
      (k : ℝ)⁻¹ * ∑ i, phiN A F (sphPt (M₃.mulVec b + tauOf m b c₁ • γ i)) := by
  have e : ∀ i, sphPt (M₃.mulVec b + tauOf m b c₁ • γ i) =
      sphProj (M₃.mulVec b + tauOf m b c₁ • γ i) := fun i => by
    unfold sphPt
    simp only [h i, ↓reduceIte]
  rw [hatProg_eval]
  simp_rw [e]

theorem hatSample_cost (i : Fin k) :
    (hatSample k n m mA mF i).cost ≤
      2 * n + (3 * n + 1) + mlpCost n mA n + mlpCost n mF 1 := by
  have hy : (yProg k n m mA mF i).cost = 2 * n := by
    simp [yProg, cost_par, axpyIn_cost]
    ring
  have := RProg.cost_rescaleStep (yProg k n m mA mF i)
  simp only [hatSample, RProg.cost_mapOut, RProg.cost_mlpStep]
  omega

/-- **The operation count of `hatProg`.** -/
theorem hatProg_cost :
    (hatProg k n m mA mF).cost ≤ n * (2 * m - 1) + (2 * m + 6) +
      k * (2 * n + (3 * n + 1) + mlpCost n mA n + mlpCost n mF 1) + k + 1 := by
  have h1 : (hatPre k n m mA mF).cost ≤ n * (2 * m - 1) + (2 * m + 6) := by
    simp only [hatPre, RProg.cost_ext, RProg.cost_mapIn, cProg, RProg.cost_linStep,
      RProg.cost_args, tauProg, RProg.cost_bind, RProg.cost_ofProg, sqProg_cost, tauTail_cost]
    omega
  have h2 : (RProg.par (hatSample k n m mA mF) (List.finRange k)).cost ≤
      k * (2 * n + (3 * n + 1) + mlpCost n mA n + mlpCost n mF 1) := by
    rw [RProg.cost_par]
    have := List.sum_le_length_nsmul ((List.finRange k).map fun i => (hatSample k n m mA mF i).cost)
      (2 * n + (3 * n + 1) + mlpCost n mA n + mlpCost n mF 1) (by
        intro x hx
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
        exact hatSample_cost i)
    simpa using this
  have h3 : (meanTail k (HatIn k n m mA mF ⊕ (Fin n ⊕ Unit))).cost ≤ k + 1 := by
    simp only [meanTail, RProg.cost_ofProg, cost_bind, sumProg_cost, cost_op1]
    omega
  simp only [hatProg, RProg.cost_bind]
  omega

end hat

/-! ## The program before the oracle -/

section pre

variable (N m : ℕ)

/-- The inputs of `preProg`: the entries of `M₁`, of `M₂`, and the constant `c_N`. -/
abbrev PreIn : Type := (Fin m × Fin N) ⊕ (Fin m × Fin m) ⊕ Unit

variable {N m}

/-- The inputs as one valuation. -/
def preVal (θ : HidParam N m) (c : ℝ) : PreIn N m → ℝ :=
  Sum.elim (fun e => θ.1 e.1 e.2) (Sum.elim (fun e => θ.2 e.1 e.2) (fun _ => c))

variable (N m)

/-- The squared row lengths of `M₁`: `m(2N − 1)` operations. -/
def rowProg : RProg (PreIn N m) (Fin m) :=
  RProg.ofProg (Prog.par (fun j : Fin m =>
    sqProg N (fun i => (Sum.inl (j, i) : PreIn N m))) (List.finRange m))

/-- `h̄₁_j = c_N·√(|row_j|²)`: `2m` operations. -/
def h1Prog : RProg (PreIn N m ⊕ Fin m) (Fin m) :=
  RProg.par (fun j : Fin m => sqrtMul (Sum.inr j) (Sum.inl (Sum.inr (Sum.inr ()))))
    (List.finRange m)

/-- `s` from the squared row lengths: `(m − 1) + 5` operations. -/
def sProg : RProg (PreIn N m ⊕ Fin m) Unit :=
  (RProg.ofProg (sumProg m (fun j => (Sum.inr j : PreIn N m ⊕ Fin m)))).bind
    (sTail N m (Sum.inl (Sum.inr (Sum.inr ()))))

/-- **The program before the oracle**: from the entries of `M₁`, `M₂` and the constant `c_N`:
the vector `a = M₂ h̄₁` (outputs `inl i`) and the scale `s` (output `inr ()`). The computed
centre is then `b̂_i = psiS s a_i`: one ORACLE operation per coordinate (not in this program). -/
def preProg : RProg (PreIn N m) (Fin m ⊕ Unit) :=
  (rowProg N m).bind
    (((h1Prog N m).linStep (fun e => Sum.inl (Sum.inr (Sum.inl e)))).ext
      ((sProg N m).mapIn Sum.inl))

variable {N m}

theorem rowProg_eval (θ : HidParam N m) (c : ℝ) (j : Fin m) :
    (rowProg N m).eval (preVal θ c) j = normSq (rowOf j θ.1) := by
  rw [rowProg, RProg.eval_ofProg, eval_par_mem _ _ _ _ (List.mem_finRange j), sqProg_eval]
  rfl

theorem h1Prog_eval (hN : 1 ≤ N) (θ : HidParam N m) (j : Fin m) :
    (h1Prog N m).eval (Sum.elim (preVal θ (cN N)) ((rowProg N m).eval (preVal θ (cN N)))) j =
      h1bar θ.1 j := by
  rw [h1Prog, RProg.eval_par_mem _ _ _ _ (List.mem_finRange j), sqrtMul_eval, h1bar_eq hN]
  simp only [Sum.elim_inr, Sum.elim_inl, rowProg_eval]
  rfl

theorem preProg_eval_a (hN : 1 ≤ N) (θ : HidParam N m) (i : Fin m) :
    (preProg N m).eval (preVal θ (cN N)) (Sum.inl i) = (θ.2.mulVec (h1bar θ.1)) i := by
  rw [preProg, RProg.eval_bind, RProg.eval_ext_inl,
    RProg.eval_linStep _ _ _ θ.2 (fun _ => rfl)]
  congr 1
  funext j
  exact h1Prog_eval hN θ j

theorem preProg_eval_s (hN : 1 ≤ N) (hm : 1 ≤ m) (θ : HidParam N m) :
    (preProg N m).eval (preVal θ (cN N)) (Sum.inr ()) = sS θ.1 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  rw [preProg, RProg.eval_bind, RProg.eval_ext_inr, RProg.eval_mapIn, sProg, RProg.eval_bind,
    sTail_eval]
  simp only [Sum.elim_inr, Sum.elim_inl, Function.comp, RProg.eval_ofProg, sumProg_eval,
    rowProg_eval]
  unfold sS
  congr 1
  rw [GamS_rows hN hm]
  have e1 : normSq (h1bar θ.1) = cN N ^ 2 * ∑ j, normSq (rowOf j θ.1) := by
    unfold normSq
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h1bar_eq hN, mul_pow, nrm_sq]
    rfl
  rw [e1, ← Finset.sum_div]
  have e2 : preVal θ (cN N) (Sum.inr (Sum.inr ())) = cN N := rfl
  rw [e2]
  field_simp

theorem preProg_cost :
    (preProg N m).cost = m * (2 * N - 1) + 2 * m + m * (2 * m - 1) + (m - 1) + 5 := by
  simp only [preProg, RProg.cost_bind, RProg.cost_ext, RProg.cost_mapIn, RProg.cost_linStep,
    rowProg, RProg.cost_ofProg, cost_par, sqProg_cost, h1Prog, RProg.cost_par, sqrtMul_cost,
    sProg, sumProg_cost, sTail_cost, List.map_const', List.sum_replicate, List.length_finRange,
    smul_eq_mul]
  ring

theorem preProg_cost_le (hN : 1 ≤ N) :
    (preProg N m).cost ≤ m * (2 * N + 1) + m * (2 * m - 1) + (m - 1) + 5 := by
  rw [preProg_cost]
  have : m * (2 * N - 1) + 2 * m = m * (2 * N + 1) := by
    have h2 : 2 * N - 1 + 2 = 2 * N + 1 := by omega
    rw [← h2, Nat.mul_add]
    omega
  omega

end pre

/-! ## The total count -/

/-- **The total count of the estimate with `k` sample points**: the program before the oracle,
`m` oracle operations (`b̂_i = ψ_s(a_i)`), and the program after the oracle. -/
def costHat (k N n m mA mF : ℕ) : ℕ :=
  (m * (2 * N + 1) + m * (2 * m - 1) + (m - 1) + 5) + m +
    (n * (2 * m - 1) + (2 * m + 6) +
      k * (2 * n + (3 * n + 1) + mlpCost n mA n + mlpCost n mF 1) + k + 1)

/-- The two programs and the `m` oracle operations cost at most `costHat`. -/
theorem costHat_ge (k : ℕ) {N : ℕ} (n m mA mF : ℕ) (hN : 1 ≤ N) :
    (preProg N m).cost + m + (hatProg k n m mA mF).cost ≤ costHat k N n m mA mF := by
  have h1 := preProg_cost_le (m := m) hN
  have h2 := hatProg_cost (k := k) (n := n) (m := m) (mA := mA) (mF := mF)
  unfold costHat
  omega

/-- **`cost140`**: the total count is at most
`2m² + m(2N + 2n + 4) + 12 + k·(5n + 2 + cost of A + cost of F)`: one pass over `M₂`
(`2m²`), lower-order terms `O(m(N + n))`, and `k` evaluations of `F∘A`. -/
theorem cost140 (k N n m mA mF : ℕ) :
    costHat k N n m mA mF ≤ 2 * m ^ 2 + m * (2 * N + 2 * n + 4) + 12 +
      k * (5 * n + 2 + mlpCost n mA n + mlpCost n mF 1) := by
  unfold costHat
  have a1 : m * (2 * m - 1) ≤ 2 * m ^ 2 - m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have : m * (2 * m - 1) = 2 * m ^ 2 - m := by
        rw [Nat.mul_sub, Nat.mul_one]; congr 1; ring
      omega
  have a0 : m ≤ 2 * m ^ 2 := by nlinarith [Nat.zero_le m]
  have a2 : n * (2 * m - 1) ≤ 2 * (m * n) := by
    calc n * (2 * m - 1) ≤ n * (2 * m) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = 2 * (m * n) := by ring
  have e1 : m * (2 * N + 1) = 2 * (m * N) + m := by ring
  have e2 : m * (2 * N + 2 * n + 4) = 2 * (m * N) + 2 * (m * n) + 4 * m := by ring
  have e3 : k * (2 * n + (3 * n + 1) + mlpCost n mA n + mlpCost n mF 1) + k =
      k * (5 * n + 2 + mlpCost n mA n + mlpCost n mF 1) := by ring
  rw [e1, e2]
  generalize k * (2 * n + (3 * n + 1) + mlpCost n mA n + mlpCost n mF 1) = Y at e3 ⊢
  generalize k * (5 * n + 2 + mlpCost n mA n + mlpCost n mF 1) = Z at e3 ⊢
  generalize m * (2 * m - 1) = P at a1 ⊢
  generalize n * (2 * m - 1) = Q at a2 ⊢
  omega

end

end BstLean.Part140

open BstLean.Part140 in
#print axioms tauOf_bhat
open BstLean.Part140 in
#print axioms hatProg_eval
open BstLean.Part140 in
#print axioms hatProg_eval_sphPt
open BstLean.Part140 in
#print axioms hatProg_cost
open BstLean.Part140 in
#print axioms preProg_eval_a
open BstLean.Part140 in
#print axioms preProg_eval_s
open BstLean.Part140 in
#print axioms preProg_cost
open BstLean.Part140 in
#print axioms costHat_ge
open BstLean.Part140 in
#print axioms cost140
