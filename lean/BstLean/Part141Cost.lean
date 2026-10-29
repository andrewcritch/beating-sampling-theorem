import BstLean.Part141Defs

/-!
# Part 141, item 4: ONE straight-line program with rational constants and no oracle

Role: `delegations/statements/p141-spec.md` (item 4). Paper sources: `onW8c-cx.md` §§2, 7,
`onW17c-cx.md` §7.

The model is `RProg` of `Part130Cost`: operations `+ − × ÷ √ relu`, each costs one; reading an
input, a register or a RATIONAL constant is free; the cost is the number of instructions.

* `preProg_eval_a'`, `preProg_eval_s'`: the program `preProg` of Part 140 with an arbitrary
  real number `c` at its constant input computes `aOf c θ` and `sOf c θ`.
* `atomStage p z a s`: from the inputs `a_i` and `s`, with rational constants `p_ℓ`, `z_ℓ`:
  `b_i = Σ_ℓ p_ℓ·relu(a_i + s·z_ℓ)`; `L + m(3L + (L − 1))` operations.
* **`arithProg k N n m mA mF L c c₁ p z`**: the composed program. Its inputs are the entries of
  `W`, `k` Gaussian vectors and the weights of `A`, `F`. Its constants are rational. It has no
  oracle and no real-constant input.
* **`arithProg_eval`**, `arithProg_eval_sphPt`: its value.
* **`arithProg_cost`**, **`arithCost141`**: its operation count.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part141

open BstLean.Cost
open BstLean.Part105 (sphProj)
open BstLean.Part130 BstLean.Part136 BstLean.Part137 BstLean.Part140

noncomputable section

/-! ## `preProg` with an arbitrary constant -/

section pre

variable {N m : ℕ}

theorem h1Prog_eval' (θ : HidParam N m) (c : ℝ) (j : Fin m) :
    (h1Prog N m).eval (Sum.elim (preVal θ c) ((rowProg N m).eval (preVal θ c))) j =
      c * √(normSq (rowOf j θ.1)) := by
  rw [h1Prog, RProg.eval_par_mem _ _ _ _ (List.mem_finRange j), sqrtMul_eval]
  simp only [Sum.elim_inr, Sum.elim_inl, rowProg_eval]
  rfl

/-- `preProg` with the constant `c`: the outputs `inl i` are `aOf c θ i`. -/
theorem preProg_eval_a' (θ : HidParam N m) (c : ℝ) (i : Fin m) :
    (preProg N m).eval (preVal θ c) (Sum.inl i) = aOf c θ i := by
  rw [preProg, RProg.eval_bind, RProg.eval_ext_inl,
    RProg.eval_linStep _ _ _ θ.2 (fun _ => rfl)]
  unfold aOf
  congr 1
  funext j
  exact h1Prog_eval' θ c j

/-- `preProg` with the constant `c`: the output `inr ()` is `sOf c θ`. -/
theorem preProg_eval_s' (θ : HidParam N m) (c : ℝ) :
    (preProg N m).eval (preVal θ c) (Sum.inr ()) = sOf c θ := by
  rw [preProg, RProg.eval_bind, RProg.eval_ext_inr, RProg.eval_mapIn, sProg, RProg.eval_bind,
    sTail_eval]
  simp only [Sum.elim_inr, Sum.elim_inl, Function.comp, RProg.eval_ofProg, sumProg_eval,
    rowProg_eval]
  rfl

end pre

/-! ## The atom stage -/

section atom

variable {J : Type} {L : ℕ}

/-- `s·z_ℓ` for every atom: `L` multiplications. -/
def szProg (z : Fin L → ℚ) (s : J) : RProg J (Fin L) :=
  RProg.par (fun ℓ : Fin L => ⟨[⟨.mul, .inp s, .cst (z ℓ)⟩], fun _ => .reg 0⟩) (List.finRange L)

theorem szProg_eval (z : Fin L → ℚ) (s : J) (v : J → ℝ) (ℓ : Fin L) :
    (szProg z s).eval v ℓ = v s * (z ℓ : ℝ) := by
  rw [szProg, RProg.eval_par_mem _ _ _ _ (List.mem_finRange ℓ)]
  simp [RProg.eval, rrun, RInstr.eval, ROp.eval, Arg.eval]

theorem szProg_cost (z : Fin L → ℚ) (s : J) : (szProg (J := J) z s).cost = L := by
  rw [szProg, RProg.cost_par]
  simp [RProg.cost]

/-- One term `p_ℓ·relu(a + (s·z_ℓ))`: 3 operations. The input `inr ℓ` is `s·z_ℓ`. -/
def termProg (p : Fin L → ℚ) (a : J) (ℓ : Fin L) : RProg (J ⊕ Fin L) Unit :=
  ⟨[⟨.add, .inp (Sum.inl a), .inp (Sum.inr ℓ)⟩,
    ⟨.relu, .reg 0, .reg 0⟩,
    ⟨.mul, .cst (p ℓ), .reg 1⟩], fun _ => .reg 2⟩

theorem termProg_eval (p : Fin L → ℚ) (a : J) (ℓ : Fin L) (v : J ⊕ Fin L → ℝ) (u : Unit) :
    (termProg p a ℓ).eval v u = (p ℓ : ℝ) * relu (v (Sum.inl a) + v (Sum.inr ℓ)) := by
  simp [termProg, RProg.eval, rrun, RInstr.eval, ROp.eval, Arg.eval]

theorem termProg_cost (p : Fin L → ℚ) (a : J) (ℓ : Fin L) : (termProg p a ℓ).cost = 3 := rfl

/-- One coordinate `Σ_ℓ p_ℓ·relu(a + (s·z_ℓ))`: `3L + (L − 1)` operations. -/
def atomI (p : Fin L → ℚ) (a : J) : RProg (J ⊕ Fin L) Unit :=
  (RProg.par (termProg p a) (List.finRange L)).bind
    (RProg.ofProg (sumProg L (fun ℓ => (Sum.inr ℓ : (J ⊕ Fin L) ⊕ Fin L))))

theorem atomI_eval (p : Fin L → ℚ) (a : J) (v : J ⊕ Fin L → ℝ) (u : Unit) :
    (atomI p a).eval v u = ∑ ℓ, (p ℓ : ℝ) * relu (v (Sum.inl a) + v (Sum.inr ℓ)) := by
  rw [atomI, RProg.eval_bind, RProg.eval_ofProg, sumProg_eval]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [Sum.elim_inr]
  rw [RProg.eval_par_mem _ _ _ _ (List.mem_finRange ℓ), termProg_eval]

theorem atomI_cost (p : Fin L → ℚ) (a : J) : (atomI p a).cost = 3 * L + (L - 1) := by
  simp [atomI, RProg.cost_par, termProg_cost, sumProg_cost]
  ring

variable {m : ℕ}

/-- **The atom stage**: `b_i = Σ_ℓ p_ℓ·relu(a_i + s·z_ℓ)` for the inputs `a i`, `s`. -/
def atomStage (p z : Fin L → ℚ) (a : Fin m → J) (s : J) : RProg J (Fin m) :=
  (szProg z s).bind (RProg.par (fun i : Fin m => atomI p (a i)) (List.finRange m))

theorem atomStage_eval (p z : Fin L → ℚ) (a : Fin m → J) (s : J) (v : J → ℝ) (i : Fin m) :
    (atomStage p z a s).eval v i =
      atomSum (fun ℓ => (p ℓ : ℝ)) (fun ℓ => (z ℓ : ℝ)) (v s) (v (a i)) := by
  rw [atomStage, RProg.eval_bind, RProg.eval_par_mem _ _ _ _ (List.mem_finRange i), atomI_eval]
  unfold atomSum
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  simp only [Sum.elim_inl, Sum.elim_inr, szProg_eval]

theorem atomStage_cost (p z : Fin L → ℚ) (a : Fin m → J) (s : J) :
    (atomStage p z a s).cost = L + m * (3 * L + (L - 1)) := by
  simp [atomStage, RProg.cost_par, szProg_cost, atomI_cost]

theorem atomStage_cost_le (p z : Fin L → ℚ) (a : Fin m → J) (s : J) :
    (atomStage p z a s).cost ≤ L + m * (4 * L) := by
  rw [atomStage_cost]
  have : 3 * L + (L - 1) ≤ 4 * L := by omega
  have := Nat.mul_le_mul_left m this
  omega

end atom

/-! ## The composed program -/

section prog

variable (k N n m mA mF L : ℕ)

/-- The inputs of `arithProg`: the entries of `W` (`M₁`, `M₂`, `M₃`), the `k` Gaussian vectors,
the weights of `A` and of `F`. -/
abbrev ArIn : Type := MlpW N m n ⊕ (Fin k × Fin n) ⊕ MlpW n mA n ⊕ MlpW n mF 1

variable {k N n m mA mF L}

/-- The inputs as one valuation. -/
def arVal (W : MlpParam N m n) (γ : Fin k → Fin n → ℝ) (A : MlpParam n mA n)
    (F : MlpParam n mF 1) : ArIn k N n m mA mF → ℝ :=
  Sum.elim (mlpW W) (Sum.elim (fun e => γ e.1 e.2) (Sum.elim (mlpW A) (mlpW F)))

variable (k N n m mA mF)

/-- The two rational constants as outputs of a program with no instruction:
`inl ()` is `c`, `inr ()` is `c₁`. -/
def constProg (c c₁ : ℚ) : RProg (ArIn k N n m mA mF) (Unit ⊕ Unit) :=
  RProg.args (Sum.elim (fun _ => .cst c) (fun _ => .cst c₁))

/-- The inputs of `preProg` inside the composed program. -/
def preSig : PreIn N m → ArIn k N n m mA mF ⊕ (Unit ⊕ Unit) :=
  Sum.elim (fun e => Sum.inl (Sum.inl (Sum.inl e)))
    (Sum.elim (fun e => Sum.inl (Sum.inl (Sum.inr (Sum.inl e))))
      (fun _ => Sum.inr (Sum.inl ())))

/-- The inputs of `hatProg` inside the composed program. -/
def hatSig : HatIn k n m mA mF →
    ((ArIn k N n m mA mF ⊕ (Unit ⊕ Unit)) ⊕ (Fin m ⊕ Unit)) ⊕ Fin m :=
  Sum.elim (fun j => Sum.inr j)
    (Sum.elim (fun e => Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inr e))))))
      (Sum.elim (fun _ => Sum.inl (Sum.inl (Sum.inr (Sum.inr ()))))
        (Sum.elim (fun e => Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inl e)))))
          (Sum.elim (fun e => Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inr (Sum.inl e))))))
            (fun e => Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inr (Sum.inr e))))))))))

variable (L)

/-- **The arithmetic one-pass program.** Inputs: the entries of `W`, `k` Gaussian vectors, the
weights of `A` and `F`. Rational constants: `c` (in the place of `c_N`), `c₁` (in the place of
`1/(γκ₁²)`), the weights `p_ℓ` and the atoms `z_ℓ`. Steps: `preProg` with the constant `c`
(outputs `a = aOf c θ`, `s = sOf c θ`), the atom stage (`b_i = Σ_ℓ p_ℓ·relu(a_i + s·z_ℓ)`), then
`hatProg` with the centre `b` and the constant `c₁`. -/
def arithProg (c c₁ : ℚ) (p z : Fin L → ℚ) : RProg (ArIn k N n m mA mF) Unit :=
  (constProg k N n m mA mF c c₁).bind
    (((preProg N m).mapIn (preSig k N n m mA mF)).bind
      ((atomStage p z (fun i : Fin m => Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr ()))).bind
        ((hatProg k n m mA mF).mapIn (hatSig k N n m mA mF))))

variable {k N n m mA mF L}

/-- **The value of `arithProg`**: the mean of `F(A(sphProj(M₃ b + τ·γ_i)))` over the `k`
Gaussian vectors, with the centre `b = bOf c p z (M₁, M₂)` and `τ = tauOf m b c₁`. -/
theorem arithProg_eval (c c₁ : ℚ) (p z : Fin L → ℚ) (W : MlpParam N m n)
    (γ : Fin k → Fin n → ℝ) (A : MlpParam n mA n) (F : MlpParam n mF 1) :
    (arithProg k N n m mA mF L c c₁ p z).eval (arVal W γ A F) () =
      (k : ℝ)⁻¹ * ∑ i, phiN A F (sphProj (W.2.2.mulVec
          (bOf (c : ℝ) (fun ℓ => (p ℓ : ℝ)) (fun ℓ => (z ℓ : ℝ)) ((W.1, W.2.1) : HidParam N m)) +
        tauOf m (bOf (c : ℝ) (fun ℓ => (p ℓ : ℝ)) (fun ℓ => (z ℓ : ℝ))
          ((W.1, W.2.1) : HidParam N m)) (c₁ : ℝ) • γ i)) := by
  set θ : HidParam N m := (W.1, W.2.1) with hθ
  set b := bOf (c : ℝ) (fun ℓ => (p ℓ : ℝ)) (fun ℓ => (z ℓ : ℝ)) θ with hb
  rw [arithProg, RProg.eval_bind, RProg.eval_bind, RProg.eval_bind, RProg.eval_mapIn]
  set v0 : ArIn k N n m mA mF ⊕ (Unit ⊕ Unit) → ℝ :=
    Sum.elim (arVal W γ A F) ((constProg k N n m mA mF c c₁).eval (arVal W γ A F)) with hv0
  have hpre : v0 ∘ preSig k N n m mA mF = preVal θ (c : ℝ) := by
    funext e
    rcases e with e | e | e <;> rfl
  set v1 : (ArIn k N n m mA mF ⊕ (Unit ⊕ Unit)) ⊕ (Fin m ⊕ Unit) → ℝ :=
    Sum.elim v0 (((preProg N m).mapIn (preSig k N n m mA mF)).eval v0) with hv1
  have hv1a : ∀ i : Fin m, v1 (Sum.inr (Sum.inl i)) = aOf (c : ℝ) θ i := by
    intro i
    simp only [hv1, Sum.elim_inr, RProg.eval_mapIn]
    rw [hpre, preProg_eval_a']
  have hv1s : v1 (Sum.inr (Sum.inr ())) = sOf (c : ℝ) θ := by
    simp only [hv1, Sum.elim_inr, RProg.eval_mapIn]
    rw [hpre, preProg_eval_s']
  have hhat : (Sum.elim v1 ((atomStage p z (fun i : Fin m => Sum.inr (Sum.inl i))
      (Sum.inr (Sum.inr ()))).eval v1)) ∘ hatSig k N n m mA mF =
      hatVal b W.2.2 (c₁ : ℝ) γ A F := by
    funext e
    rcases e with j | e | e | e | e | e
    · simp only [Function.comp, hatSig, Sum.elim_inl, Sum.elim_inr, hatVal]
      rw [atomStage_eval, hv1a, hv1s]
      rfl
    all_goals rfl
  rw [hhat, hatProg_eval]

/-- The value with the fixed-point normalization `sphPt`, when no point is zero before the
normalization. -/
theorem arithProg_eval_sphPt (c c₁ : ℚ) (p z : Fin L → ℚ) (W : MlpParam N m n)
    (γ : Fin k → Fin n → ℝ) (A : MlpParam n mA n) (F : MlpParam n mF 1)
    (h : ∀ i, normSq (W.2.2.mulVec
          (bOf (c : ℝ) (fun ℓ => (p ℓ : ℝ)) (fun ℓ => (z ℓ : ℝ)) ((W.1, W.2.1) : HidParam N m)) +
        tauOf m (bOf (c : ℝ) (fun ℓ => (p ℓ : ℝ)) (fun ℓ => (z ℓ : ℝ))
          ((W.1, W.2.1) : HidParam N m)) (c₁ : ℝ) • γ i) ≠ 0) :
    (arithProg k N n m mA mF L c c₁ p z).eval (arVal W γ A F) () =
      (k : ℝ)⁻¹ * ∑ i, phiN A F (sphPt (W.2.2.mulVec
          (bOf (c : ℝ) (fun ℓ => (p ℓ : ℝ)) (fun ℓ => (z ℓ : ℝ)) ((W.1, W.2.1) : HidParam N m)) +
        tauOf m (bOf (c : ℝ) (fun ℓ => (p ℓ : ℝ)) (fun ℓ => (z ℓ : ℝ))
          ((W.1, W.2.1) : HidParam N m)) (c₁ : ℝ) • γ i)) := by
  have e : ∀ y : Fin n → ℝ, normSq y ≠ 0 → sphPt y = sphProj y := fun y hy => by
    unfold sphPt
    simp only [hy, ↓reduceIte]
  refine (arithProg_eval c c₁ p z W γ A F).trans
    (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
  rw [e _ (h i)]

/-- **The operation count of `arithProg`** (exact): `preProg`, the atom stage, `hatProg`. -/
theorem arithProg_cost_eq (c c₁ : ℚ) (p z : Fin L → ℚ) :
    (arithProg k N n m mA mF L c c₁ p z).cost =
      (preProg N m).cost + (L + m * (3 * L + (L - 1))) + (hatProg k n m mA mF).cost := by
  simp only [arithProg, RProg.cost_bind, RProg.cost_mapIn, constProg, RProg.cost_args,
    atomStage_cost]
  omega

theorem arithProg_cost (c c₁ : ℚ) (p z : Fin L → ℚ) :
    (arithProg k N n m mA mF L c c₁ p z).cost ≤
      (preProg N m).cost + (L + m * (4 * L)) + (hatProg k n m mA mF).cost := by
  rw [arithProg_cost_eq]
  have : 3 * L + (L - 1) ≤ 4 * L := by omega
  have := Nat.mul_le_mul_left m this
  omega

/-- **`arithCost141`.** For `N = 2n` inputs: the operation count of the arithmetic program is at
most `2m² + m(6n + 4L + 4) + L + 12 + k·(5n + 2 + mlpCost n mA n + mlpCost n mF 1)`
(leading term `2m²`: one pass over `M₂`; `L` is the number of atoms). -/
theorem arithCost141 (k n m mA mF L : ℕ) (hn : 1 ≤ n) (c c₁ : ℚ) (p z : Fin L → ℚ) :
    (arithProg k (2 * n) n m mA mF L c c₁ p z).cost ≤
      2 * m ^ 2 + m * (6 * n + 4 * L + 4) + L + 12 +
        k * (5 * n + 2 + mlpCost n mA n + mlpCost n mF 1) := by
  have h0 := arithProg_cost (k := k) (N := 2 * n) (n := n) (m := m) (mA := mA) (mF := mF)
    c c₁ p z
  have h1 := costHat_ge k (N := 2 * n) n m mA mF (by omega)
  have h2 := cost140 k (2 * n) n m mA mF
  have e : m * (2 * (2 * n) + 2 * n + 4) = m * (6 * n + 4) := by ring_nf
  rw [e] at h2
  have e2 : m * (6 * n + 4 * L + 4) = m * (6 * n + 4) + m * (4 * L) := by ring
  rw [e2]
  omega

end prog

end

end BstLean.Part141

open BstLean.Part141 in
#print axioms preProg_eval_a'
open BstLean.Part141 in
#print axioms preProg_eval_s'
open BstLean.Part141 in
#print axioms atomStage_eval
open BstLean.Part141 in
#print axioms atomStage_cost
open BstLean.Part141 in
#print axioms arithProg_eval
open BstLean.Part141 in
#print axioms arithProg_eval_sphPt
open BstLean.Part141 in
#print axioms arithProg_cost_eq
open BstLean.Part141 in
#print axioms arithProg_cost
open BstLean.Part141 in
#print axioms arithCost141
