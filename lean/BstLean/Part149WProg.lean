import BstLean.Part141Err
import BstLean.Part141Cost

/-!
# Part 149: the W stage alone as ONE straight-line program

The model is `RProg` of `Part130Cost` (operations `+ − × ÷ √ relu`, each costs one; reading an
input or a rational constant is free).

* `wStageProgG N n m L c c₁ p z`: the inputs are the entries of `W = (M₁, M₂, M₃)` ONLY
  (`MlpW N m n`); the outputs `inl i` are the centre `M₃ b`, the output `inr ()` is the scalar
  `tauOf m b c₁`, with `b = bOf c p z (M₁, M₂)`. Steps: the two rational constants, `preProg` of
  Part 140, `atomStage` of Part 141, then the centre and the scalar (as `hatPre` of Part 140,
  with no sample).
* `wStageProg n`: the program at the widths and the rational constants of `arithProg141`.
* `wStageProg_eval_c`, `wStageProg_eval_tau`: its outputs are `cenA W` and `tauWA W`.
* `wStageProg_cost`: at most `2m² + m(6n + 4·LA n + 4) + LA n + 12` operations, `m = mW n`.
-/

namespace BstLean.Part149

open BstLean.Cost
open BstLean.Part130 BstLean.Part136 BstLean.Part137 BstLean.Part140 BstLean.Part141

noncomputable section

section general

variable (N n m L : ℕ)

/-- The inputs and the two constants. -/
abbrev WSt1 : Type := MlpW N m n ⊕ (Unit ⊕ Unit)

/-- With the outputs `a`, `s` of `preProg`. -/
abbrev WSt2 : Type := WSt1 N n m ⊕ (Fin m ⊕ Unit)

/-- With the centre `b` of the atom stage. -/
abbrev WSt3 : Type := WSt2 N n m ⊕ Fin m

/-- The inputs of the W stage as one valuation: the entries of `W`. -/
def wVal {N n m : ℕ} (W : MlpParam N m n) : MlpW N m n → ℝ := mlpW W

/-- The two rational constants: `inl ()` is `c`, `inr ()` is `c₁`. No instruction. -/
def wsConst (c c₁ : ℚ) : RProg (MlpW N m n) (Unit ⊕ Unit) :=
  RProg.args (Sum.elim (fun _ => .cst c) (fun _ => .cst c₁))

/-- The inputs of `preProg` inside the W stage. -/
def wsPreSig : PreIn N m → WSt1 N n m :=
  Sum.elim (fun e => Sum.inl (Sum.inl e))
    (Sum.elim (fun e => Sum.inl (Sum.inr (Sum.inl e))) (fun _ => Sum.inr (Sum.inl ())))

/-- The centre `M₃ b`: `n(2m − 1)` operations. -/
def wsCen : RProg (WSt3 N n m) (Fin n) :=
  (RProg.args (fun j : Fin m => Arg.inp (Sum.inr j : WSt3 N n m))).linStep
    (fun e => Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inr e)))))

/-- The scalar `tauOf m b c₁`: `(2m − 1) + 6` operations. -/
def wsTau : RProg (WSt3 N n m) Unit :=
  (RProg.ofProg (sqProg m (fun j => (Sum.inr j : WSt3 N n m)))).bind
    (tauTail m (Sum.inl (Sum.inl (Sum.inr (Sum.inr ())))))

/-- The centre and the scalar. -/
def wsTail : RProg (WSt3 N n m) (Fin n ⊕ Unit) :=
  (wsCen N n m).ext ((wsTau N n m).mapIn Sum.inl)

/-- **The W stage, general parameters.** Inputs: the entries of `W`. Outputs: `inl i` is
`(M₃ b)_i`, `inr ()` is `tauOf m b c₁`, with `b = bOf c p z (M₁, M₂)`. -/
def wStageProgG (c c₁ : ℚ) (p z : Fin L → ℚ) : RProg (MlpW N m n) (Fin n ⊕ Unit) :=
  (wsConst N n m c c₁).bind
    (((preProg N m).mapIn (wsPreSig N n m)).bind
      ((atomStage p z (fun i : Fin m => (Sum.inr (Sum.inl i) : WSt2 N n m))
          (Sum.inr (Sum.inr ()))).bind (wsTail N n m)))

variable {N n m L}

/-- The valuation before the tail. -/
def wsV3 (c c₁ : ℚ) (p z : Fin L → ℚ) (W : MlpParam N m n) : WSt3 N n m → ℝ :=
  let v0 : WSt1 N n m → ℝ := Sum.elim (wVal W) ((wsConst N n m c c₁).eval (wVal W))
  let v1 : WSt2 N n m → ℝ := Sum.elim v0 (((preProg N m).mapIn (wsPreSig N n m)).eval v0)
  Sum.elim v1 ((atomStage p z (fun i : Fin m => (Sum.inr (Sum.inl i) : WSt2 N n m))
    (Sum.inr (Sum.inr ()))).eval v1)

theorem wStageProgG_eval (c c₁ : ℚ) (p z : Fin L → ℚ) (W : MlpParam N m n) :
    (wStageProgG N n m L c c₁ p z).eval (wVal W) = (wsTail N n m).eval (wsV3 c c₁ p z W) := by
  funext o
  rw [wStageProgG, RProg.eval_bind, RProg.eval_bind, RProg.eval_bind]
  rfl

theorem wsV3_b (c c₁ : ℚ) (p z : Fin L → ℚ) (W : MlpParam N m n) (j : Fin m) :
    wsV3 c c₁ p z W (Sum.inr j) =
      bOf (c : ℝ) (fun ℓ => (p ℓ : ℝ)) (fun ℓ => (z ℓ : ℝ)) ((W.1, W.2.1) : HidParam N m) j := by
  set θ : HidParam N m := (W.1, W.2.1) with hθ
  set v0 : WSt1 N n m → ℝ := Sum.elim (wVal W) ((wsConst N n m c c₁).eval (wVal W)) with hv0
  have hpre : v0 ∘ wsPreSig N n m = preVal θ (c : ℝ) := by
    funext e
    rcases e with e | e | e <;> rfl
  set v1 : WSt2 N n m → ℝ :=
    Sum.elim v0 (((preProg N m).mapIn (wsPreSig N n m)).eval v0) with hv1
  have hv1a : ∀ i : Fin m, v1 (Sum.inr (Sum.inl i)) = aOf (c : ℝ) θ i := by
    intro i
    simp only [hv1, Sum.elim_inr, RProg.eval_mapIn]
    rw [hpre, preProg_eval_a']
  have hv1s : v1 (Sum.inr (Sum.inr ())) = sOf (c : ℝ) θ := by
    simp only [hv1, Sum.elim_inr, RProg.eval_mapIn]
    rw [hpre, preProg_eval_s']
  change (atomStage p z (fun i : Fin m => (Sum.inr (Sum.inl i) : WSt2 N n m))
    (Sum.inr (Sum.inr ()))).eval v1 j = _
  rw [atomStage_eval, hv1a, hv1s]
  rfl

theorem wsV3_M3 (c c₁ : ℚ) (p z : Fin L → ℚ) (W : MlpParam N m n) (e : Fin n × Fin m) :
    wsV3 c c₁ p z W (Sum.inl (Sum.inl (Sum.inl (Sum.inr (Sum.inr e))))) = W.2.2 e.1 e.2 := rfl

theorem wsV3_c1 (c c₁ : ℚ) (p z : Fin L → ℚ) (W : MlpParam N m n) :
    wsV3 c c₁ p z W (Sum.inl (Sum.inl (Sum.inr (Sum.inr ())))) = (c₁ : ℝ) := rfl

/-- The outputs `inl i`: the centre `M₃ b`. -/
theorem wStageProgG_eval_c (c c₁ : ℚ) (p z : Fin L → ℚ) (W : MlpParam N m n) (i : Fin n) :
    (wStageProgG N n m L c c₁ p z).eval (wVal W) (Sum.inl i) =
      W.2.2.mulVec (bOf (c : ℝ) (fun ℓ => (p ℓ : ℝ)) (fun ℓ => (z ℓ : ℝ))
        ((W.1, W.2.1) : HidParam N m)) i := by
  rw [wStageProgG_eval, wsTail, RProg.eval_ext_inl, wsCen,
    RProg.eval_linStep _ _ (wsV3 c c₁ p z W) W.2.2 (fun e => wsV3_M3 c c₁ p z W e)]
  congr 1
  funext j
  exact wsV3_b c c₁ p z W j

/-- The output `inr ()`: the scalar `tauOf m b c₁`. -/
theorem wStageProgG_eval_tau (c c₁ : ℚ) (p z : Fin L → ℚ) (W : MlpParam N m n) :
    (wStageProgG N n m L c c₁ p z).eval (wVal W) (Sum.inr ()) =
      tauOf m (bOf (c : ℝ) (fun ℓ => (p ℓ : ℝ)) (fun ℓ => (z ℓ : ℝ))
        ((W.1, W.2.1) : HidParam N m)) (c₁ : ℝ) := by
  rw [wStageProgG_eval, wsTail, RProg.eval_ext_inr, RProg.eval_mapIn, wsTau, RProg.eval_bind,
    tauTail_eval]
  simp only [Sum.elim_inr, Sum.elim_inl, Function.comp, RProg.eval_ofProg, sqProg_eval]
  unfold tauOf normSq
  simp only [wsV3_b, wsV3_c1]

/-- **The operation count of the W stage** (exact): `preProg`, the atom stage, the centre and
the scalar. -/
theorem wStageProgG_cost_eq (c c₁ : ℚ) (p z : Fin L → ℚ) :
    (wStageProgG N n m L c c₁ p z).cost =
      (preProg N m).cost + (L + m * (3 * L + (L - 1))) + (n * (2 * m - 1) + ((2 * m - 1) + 6)) := by
  simp only [wStageProgG, RProg.cost_bind, RProg.cost_mapIn, wsConst, RProg.cost_args,
    atomStage_cost, wsTail, RProg.cost_ext, wsCen, RProg.cost_linStep, wsTau, RProg.cost_ofProg,
    sqProg_cost, tauTail_cost]
  omega

/-- For `N = 2n` inputs: at most `2m² + m(6n + 4L + 4) + L + 12` operations. -/
theorem wStageProgG_cost (n m L : ℕ) (hn : 1 ≤ n) (c c₁ : ℚ) (p z : Fin L → ℚ) :
    (wStageProgG (2 * n) n m L c c₁ p z).cost ≤
      2 * m ^ 2 + m * (6 * n + 4 * L + 4) + L + 12 := by
  rw [wStageProgG_cost_eq]
  have h1 := preProg_cost_le (N := 2 * n) (m := m) (by omega)
  have a1 : m * (2 * m - 1) ≤ 2 * m ^ 2 := by
    calc m * (2 * m - 1) ≤ m * (2 * m) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = 2 * m ^ 2 := by ring
  have a2 : n * (2 * m - 1) ≤ 2 * (m * n) := by
    calc n * (2 * m - 1) ≤ n * (2 * m) := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = 2 * (m * n) := by ring
  have a3 : m * (3 * L + (L - 1)) ≤ 4 * (m * L) := by
    calc m * (3 * L + (L - 1)) ≤ m * (4 * L) := Nat.mul_le_mul_left _ (by omega)
      _ = 4 * (m * L) := by ring
  have e1 : m * (2 * (2 * n) + 1) = 4 * (m * n) + m := by ring
  have e2 : m * (6 * n + 4 * L + 4) = 6 * (m * n) + 4 * (m * L) + 4 * m := by ring
  rw [e1] at h1
  rw [e2]
  generalize m * (2 * m - 1) = P at a1 h1 ⊢
  generalize n * (2 * m - 1) = Q at a2 ⊢
  generalize m * (3 * L + (L - 1)) = R at a3 ⊢
  omega

end general

/-! ## The W stage at the widths and the constants of `arithProg141` -/

/-- **The W stage**: inputs the entries of `W = (M₁, M₂, M₃)` only; outputs the centre `cenA W`
(`inl i`) and the scalar `tauWA W` (`inr ()`). The rational constants are those of
`arithProg141`: `cA n`, `c1A n`, the atoms `zA n` and the weights `pA n`. -/
def wStageProg (n : ℕ) : RProg (MlpW (2 * n) (mW n) n) (Fin n ⊕ Unit) :=
  wStageProgG (2 * n) n (mW n) (LA n) (cA n) (c1A n) (pA n) (zA n)

theorem wStageProg_eval_c {n : ℕ} (W : MlpParam (2 * n) (mW n) n) (i : Fin n) :
    (wStageProg n).eval (wVal W) (Sum.inl i) = cenA W i :=
  wStageProgG_eval_c (cA n) (c1A n) (pA n) (zA n) W i

theorem wStageProg_eval_tau {n : ℕ} (W : MlpParam (2 * n) (mW n) n) :
    (wStageProg n).eval (wVal W) (Sum.inr ()) = tauWA W :=
  wStageProgG_eval_tau (cA n) (c1A n) (pA n) (zA n) W

theorem wStageProg_cost {n : ℕ} (hn : 1 ≤ n) :
    (wStageProg n).cost ≤ 2 * mW n ^ 2 + mW n * (6 * n + 4 * LA n + 4) + LA n + 12 :=
  wStageProgG_cost n (mW n) (LA n) hn (cA n) (c1A n) (pA n) (zA n)

end

end BstLean.Part149

open BstLean.Part149 in
#print axioms wStageProgG_eval_c
open BstLean.Part149 in
#print axioms wStageProgG_eval_tau
open BstLean.Part149 in
#print axioms wStageProgG_cost_eq
open BstLean.Part149 in
#print axioms wStageProg_eval_c
open BstLean.Part149 in
#print axioms wStageProg_eval_tau
open BstLean.Part149 in
#print axioms wStageProg_cost
