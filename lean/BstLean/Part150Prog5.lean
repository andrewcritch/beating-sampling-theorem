import BstLean.Part150Prog4
import BstLean.Part149WProg

/-!
# Part 150, items 4 and 5: the arithmetic program without the zero factor, and ONE straight-line
program for the whole chain (the `W` stage, the pass over `A`, the `F` stage)

* `gA150n k n m mF J`: `gA150` of `Part150Prog4` without the zero factor `ζ`: `passProg`, then
  `k` forward passes of `F` at `c̃_A + σ̃_p γ_i`, then the mean. `gA150n_eval` (`τ > 0`),
  `gA150n_cost` (exact).
* `fullProg150 k n J`: the `W` stage `wStageProg n` of Part 149 in front. Inputs (`FullIn k n`):
  the entries of `W`, of `A₁, A₂, A₃` (`m = mA n`), the `k` Gaussian vectors, the weights of `F`
  (`mF n`). **`fullProg150_eval`** (`tauWA W > 0`), `fullProg150_cost_eq`, `fullProg150_cost`,
  `fullProg150_cost_paper`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open BstLean.Cost Finset
open BstLean.Part130 BstLean.Part140 BstLean.Part141 BstLean.Part149

noncomputable section

section noZeta

variable (k n m mF J : ℕ)

/-- The inputs of one sample of Part 149 (`postSampleB`) as inputs and values here (no zero
factor). The centre input and the `A₃` input of `postSampleB` are not read by it. -/
def gSigN : PostInB k n m mF ⊕ (Fin n ⊕ Unit) → GIn k n m mF ⊕ (Fin n ⊕ Unit)
  | .inl (.inl _) => .inr (.inr ())
  | .inl (.inr (.inl e)) => .inl (.inl (.inr (.inr (.inr (.inr e)))))
  | .inl (.inr (.inr (.inl e))) => .inl (.inr (.inl e))
  | .inl (.inr (.inr (.inr e))) => .inl (.inr (.inr e))
  | .inr (.inl j) => .inr (.inl j)
  | .inr (.inr _) => .inr (.inr ())

/-- **The arithmetic program after the pass over `W`, without the zero factor**: the pass over
`A` (`passProg`), then `k` forward passes of `F` at `c̃_A + σ̃_p γ_i`, then the mean. No oracle;
no forward pass of `A`. -/
def gA150n : RProg (GIn k n m mF) Unit :=
  ((passProg n m J).mapIn Sum.inl).bind
    ((RProg.par (fun i => (postSampleB k n m mF i).mapIn (gSigN k n m mF)) (List.finRange k)).bind
      (meanTail k (GIn k n m mF ⊕ (Fin n ⊕ Unit))))

variable {k n m mF J}

variable (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (A₃ : Matrix (Fin n) (Fin m) ℝ) (γ : Fin k → Fin n → ℝ)
    (F : MlpParam n mF 1)

/-- The value of `gA150n` for every valuation `v` of its inputs, in terms of the two outputs
of `passProg`. -/
theorem gA150n_eval_v (v : GIn k n m mF → ℝ)
    (hγ : ∀ i j, v (Sum.inr (Sum.inl (i, j))) = γ i j)
    (hF : ∀ e, v (Sum.inr (Sum.inr e)) = mlpW F e) :
    (gA150n k n m mF J).eval v () =
      (k : ℝ)⁻¹ * ∑ i, evF F
        ((fun j => (passProg n m J).eval (v ∘ Sum.inl) (Sum.inl j)) +
          (passProg n m J).eval (v ∘ Sum.inl) (Sum.inr ()) • γ i) := by
  rw [gA150n, RProg.eval_bind, RProg.eval_bind, meanTail_eval]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  simp only [Sum.elim_inr]
  rw [RProg.eval_par_mem _ _ _ _ (List.mem_finRange i), RProg.eval_mapIn,
    postSampleB_eval i _ γ F (fun j => hγ i j) (fun e => hF e)]
  simp only [Function.comp, gSigN, Sum.elim_inr, RProg.eval_mapIn]

/-- **The value of `gA150n`** for `τ > 0`: `(1/k)·Σ_i F(c̃_A + σ̃_p γ_i)` with the finite centre
of `Part150CDefs` (`J₁ = J₂ = J`). -/
theorem gA150n_eval (hτ : 0 < τ) :
    (gA150n k n m mF J).eval (gVal c τ A₁ A₂ A₃ γ F) () =
      (k : ℝ)⁻¹ * ∑ i, evF F (cT J J A₁ A₂ A₃ c τ + sigT J J A₁ A₂ c τ • γ i) := by
  rw [gA150n_eval_v γ F _ (fun _ _ => rfl) (fun _ => rfl)]
  have e0 : gVal c τ A₁ A₂ A₃ γ F ∘ Sum.inl = passVal c τ A₁ A₂ A₃ := rfl
  rw [e0, passProg_eval_sig c τ A₁ A₂ A₃ hτ]
  have e : (fun j => (passProg n m J).eval (passVal c τ A₁ A₂ A₃) (Sum.inl j)) =
      cT J J A₁ A₂ A₃ c τ := funext fun j => passProg_eval_c c τ A₁ A₂ A₃ hτ j
  rw [e]

/-- **The operation count of `gA150n`** (exact). -/
theorem gA150n_cost (k n m mF J : ℕ) :
    (gA150n k n m mF J).cost =
      (passProg n m J).cost + k * (2 * n + mlpCost n mF 1) + ((k - 1) + 1) := by
  have h2 : (RProg.par (fun i => (postSampleB k n m mF i).mapIn (gSigN k n m mF))
      (List.finRange k)).cost = k * (2 * n + mlpCost n mF 1) := by
    rw [RProg.cost_par]
    simp [postSampleB_cost]
  have h3 : (meanTail k (GIn k n m mF ⊕ (Fin n ⊕ Unit))).cost = (k - 1) + 1 := by
    simp only [meanTail, RProg.cost_ofProg, cost_bind, sumProg_cost, cost_op1]
  simp only [gA150n, RProg.cost_bind, RProg.cost_mapIn, h2, h3]
  ring

end noZeta

/-! ## One program for the whole chain -/

section whole

variable (k n J : ℕ)

/-- The inputs of the whole program: the entries of `W`, of `A₁, A₂, A₃` (`m = mA n`), the `k`
Gaussian vectors, the weights of `F`. -/
abbrev FullIn : Type :=
  MlpW (2 * n) (mW n) n ⊕
    ((Fin (mA n) × Fin n) ⊕ (Fin (mA n) × Fin (mA n)) ⊕ (Fin n × Fin (mA n))) ⊕
    (Fin k × Fin n) ⊕ MlpW n (mF n) 1

variable {k n}

/-- The inputs as one valuation. -/
def fullVal (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n) (F : MlpParam n (mF n) 1)
    (γ : Fin k → Fin n → ℝ) : FullIn k n → ℝ :=
  Sum.elim (wVal W) (Sum.elim
    (Sum.elim (fun e => A.1 e.1 e.2) (Sum.elim (fun e => A.2.1 e.1 e.2) (fun e => A.2.2 e.1 e.2)))
    (Sum.elim (fun e => γ e.1 e.2) (mlpW F)))

variable (k n)

/-- The inputs of `gA150n` as inputs of the whole program and outputs of the `W` stage. -/
def fullSig : GIn k n (mA n) (mF n) → FullIn k n ⊕ (Fin n ⊕ Unit)
  | .inl (.inl j) => .inr (.inl j)
  | .inl (.inr (.inl _)) => .inr (.inr ())
  | .inl (.inr (.inr e)) => .inl (.inr (.inl e))
  | .inr (.inl e) => .inl (.inr (.inr (.inl e)))
  | .inr (.inr e) => .inl (.inr (.inr (.inr e)))

/-- **The whole arithmetic program as ONE straight-line program**: the `W` stage (`wStageProg`
of Part 149: `ĉ`, `τ̃₀`), then the pass over `A` with binomial sums and `k` forward passes of `F`
(`gA150n`). Inputs: the entries of `W`, `A`, `F` and `k` Gaussian vectors. Operations
`+ − × ÷ √ relu` and rational constants only; no oracle; no forward pass of `A`. -/
def fullProg150 : RProg (FullIn k n) Unit :=
  ((wStageProg n).mapIn Sum.inl).bind ((gA150n k n (mA n) (mF n) J).mapIn (fullSig k n))

variable {k n J}

/-- **The value of the whole program** when `τ̃₀ > 0`: the mean of `F(c̃_A + σ̃_p γ_i)` at the
centre `ĉ = cenA W` and the scalar `τ̃₀ = tauWA W` of the `W` stage. -/
theorem fullProg150_eval (W : MlpParam (2 * n) (mW n) n) (A : MlpParam n (mA n) n)
    (F : MlpParam n (mF n) 1) (γ : Fin k → Fin n → ℝ) (hτ : 0 < tauWA W) :
    (fullProg150 k n J).eval (fullVal W A F γ) () =
      (k : ℝ)⁻¹ * ∑ i, evF F (cT J J A.1 A.2.1 A.2.2 (cenA W) (tauWA W) +
        sigT J J A.1 A.2.1 (cenA W) (tauWA W) • γ i) := by
  rw [fullProg150, RProg.eval_bind, RProg.eval_mapIn]
  have e : Sum.elim (fullVal W A F γ) (((wStageProg n).mapIn Sum.inl).eval (fullVal W A F γ)) ∘
      fullSig k n = gVal (cenA W) (tauWA W) A.1 A.2.1 A.2.2 γ F := by
    have e0 : fullVal W A F γ ∘ Sum.inl = wVal W := rfl
    funext x
    rcases x with (j | u | x) | x | x
    · simp only [Function.comp, fullSig, Sum.elim_inr, RProg.eval_mapIn]
      rw [e0, wStageProg_eval_c]
      rfl
    · simp only [Function.comp, fullSig, Sum.elim_inr, RProg.eval_mapIn]
      rw [e0, wStageProg_eval_tau]
      rfl
    · rcases x with x | x | x <;> rfl
    · rfl
    · rfl
  rw [e, gA150n_eval _ _ _ _ _ _ _ hτ]

/-- The count of the whole program (exact): the `W` stage plus `gA150n`. -/
theorem fullProg150_cost_eq (k n J : ℕ) :
    (fullProg150 k n J).cost = (wStageProg n).cost + (gA150n k n (mA n) (mF n) J).cost := by
  simp only [fullProg150, RProg.cost_bind, RProg.cost_mapIn]

/-- The count of the whole program: the bound of the `W` stage plus the exact count of the
rest. -/
theorem fullProg150_cost (k J : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (fullProg150 k n J).cost ≤
      2 * mW n ^ 2 + mW n * (6 * n + 4 * LA n + 4) + LA n + 12 +
        ((passProg n (mA n) J).cost + k * (2 * n + mlpCost n (mF n) 1) + ((k - 1) + 1)) := by
  rw [fullProg150_cost_eq, gA150n_cost]
  have := wStageProg_cost hn
  omega

/-- The count of the whole program against the paper's `C_A(n, J)` (`m = mA n = n²`): the part
after the `W` stage is `CA45 n J − (2J + 9)` operations for the pass over `A`, `k` samples of
`F` at `2n + mlpCost n (mF n) 1` each, and `(k − 1) + 1` for the mean. -/
theorem fullProg150_cost_paper (k J : ℕ) {n : ℕ} (hn : 1 ≤ n) :
    (fullProg150 k n J).cost + (2 * J + 9) ≤
      2 * mW n ^ 2 + mW n * (6 * n + 4 * LA n + 4) + LA n + 12 +
        (CA45 n J + k * (2 * n + mlpCost n (mF n) 1) + ((k - 1) + 1)) := by
  have h1 := fullProg150_cost k J hn
  have h2 : (passProg n (mA n) J).cost + (2 * J + 9) = CA45 n J := passProg_cost_paper hn J
  omega

end whole

end

end BstLean.Part150

open BstLean.Part150 in
#print axioms gA150n_eval_v
open BstLean.Part150 in
#print axioms gA150n_eval
open BstLean.Part150 in
#print axioms gA150n_cost
open BstLean.Part150 in
#print axioms fullProg150_eval
open BstLean.Part150 in
#print axioms fullProg150_cost_eq
open BstLean.Part150 in
#print axioms fullProg150_cost
open BstLean.Part150 in
#print axioms fullProg150_cost_paper
