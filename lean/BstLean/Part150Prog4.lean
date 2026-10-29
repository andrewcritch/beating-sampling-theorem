import BstLean.Part150Prog3

/-!
# Part 150, item 4: the operation count of the pass over `A`, and the program with the `F` stage

Role: `delegations/statements/p150-spec.md`, item 4. Paper source: `onW45-opus-prover.md` §6
(the count `C_A(n, J)`), `onW45c-cx.md` §7 (the count, stage by stage).

* `passAll_cost_eq`: the exact count, stage by stage, for every `n`, `m`, `J`.
* **`passProg_cost`**: for `n, m ≥ 1`:
  `cost = 2m² + 6mn + 10mJ + 15m + 2J + 2n + 12`.
* `CA45 n J = 2n⁴ + 6n³ + n²(10J + 15) + 4J + 2n + 21`: the count of the paper.
* **`passProg_cost_paper`**: at `m = n²`: `cost + (2J + 9) = CA45 n J`. The difference `2J + 9`:
  `2J` operations for the binomial weights (rational constants are free in the Lean model);
  `6` for the zero factor (not in `passProg`); `3` because the sums `G`, `H`, `ν` start from
  their first term.
* `passProgZ_cost`: with the zero factor: `cost + (2J + 4) = CA45 n J` (the last
  multiplication by `ζ` is in the `F` stage).
* **`gA150 k n m mF J`**: the composed program: the pass over `A`, then `k` forward passes of
  `F` at `c̃_A + σ̃_p γ_i`, the mean, and the multiplication by `ζ`. Inputs: `c`, `τ`, the
  entries of `A₁`, `A₂`, `A₃`, `k` Gaussian vectors, the weights of `F`.
* **`gA150_eval`** (`τ > 0`), `gA150_eval_zero` (`τ = 0`: the output is `0`), **`gA150_cost`**.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open BstLean.Cost Finset
open BstLean.Part130 BstLean.Part140 BstLean.Part149

noncomputable section

/-! ## The count of the pass over `A` -/

theorem passAll_cost_eq (n m J : ℕ) :
    (passAll n m J).cost = (J + 3) + ((2 * n - 1) + 4) + (2 * (m * (2 * n - 1)) + 3 * m) +
      (4 * (m * (J + 1)) + 2 * (m * J)) + 3 * m + ((m - 1) + (2 * m - 1) + 3 + (J + 1)) +
      (m * (2 * m - 1) + 3 * (m * (J + 1)) + m * J) +
      ((2 * m - 1) + n * (2 * m - 1) + n + 5) := by
  simp only [passAll, pA3, pA2, pA1, pA1b, pA1a, pA0, pS, p0, RProg.cost_stage, op1Stage_cost,
    dotStage_cost, sumStage_cost, RProg.cost_args, Fintype.card_fin, Fintype.card_unit,
    Fintype.card_prod, Nat.add_sub_cancel]
  ring

/-- **The operation count of the pass over `A`** (exact), `n, m ≥ 1`. -/
theorem passProg_cost {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (J : ℕ) :
    (passProg n m J).cost =
      2 * m ^ 2 + 6 * (m * n) + 10 * (m * J) + 15 * m + 2 * J + 2 * n + 12 := by
  rw [passProg, RProg.cost_mapOut, passAll_cost_eq]
  obtain ⟨n, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have e1 : 2 * (n + 1) - 1 = 2 * n + 1 := by omega
  have e2 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  rw [e1, e2, Nat.add_sub_cancel]
  ring

/-- The count of the paper (`onW45` §6): `C_A(n, J)`. -/
def CA45 (n J : ℕ) : ℕ := 2 * n ^ 4 + 6 * n ^ 3 + n ^ 2 * (10 * J + 15) + 4 * J + 2 * n + 21

/-- **Comparison with the count of the paper** at `m = n²`. -/
theorem passProg_cost_paper {n : ℕ} (hn : 1 ≤ n) (J : ℕ) :
    (passProg n (n ^ 2) J).cost + (2 * J + 9) = CA45 n J := by
  rw [passProg_cost hn (Nat.one_le_pow _ _ hn), CA45]
  ring

theorem passProg_cost_le_paper {n : ℕ} (hn : 1 ≤ n) (J : ℕ) :
    (passProg n (n ^ 2) J).cost ≤ CA45 n J := by
  have := passProg_cost_paper hn J
  omega

theorem passProgZ_cost_eq (n m J : ℕ) : (passProgZ n m J).cost = (passProg n m J).cost + 5 := by
  simp only [passProgZ, passProg, RProg.cost_mapOut, passAllZ, RProg.cost_stage, op1Stage_cost,
    Fintype.card_unit]

theorem passProgZ_cost_paper {n : ℕ} (hn : 1 ≤ n) (J : ℕ) :
    (passProgZ n (n ^ 2) J).cost + (2 * J + 4) = CA45 n J := by
  have := passProg_cost_paper hn J
  rw [passProgZ_cost_eq]
  omega

/-! ## The composed program: the pass over `A`, then the `F` stage -/

section full

variable (k n m mF J : ℕ)

/-- The inputs of `gA150`: the inputs of the pass over `A`, the `k` Gaussian vectors, the
weights of `F`. -/
abbrev GIn : Type := PIn n m ⊕ (Fin k × Fin n) ⊕ MlpW n mF 1

variable {k n m mF}

/-- The inputs as one valuation. -/
def gVal (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (A₃ : Matrix (Fin n) (Fin m) ℝ) (γ : Fin k → Fin n → ℝ)
    (F : MlpParam n mF 1) : GIn k n m mF → ℝ :=
  Sum.elim (passVal c τ A₁ A₂ A₃) (Sum.elim (fun e => γ e.1 e.2) (mlpW F))

variable (k n m mF)

/-- The inputs of one sample of Part 149 (`postSampleB`) as inputs and values here. The centre
input and the `A₃` input of `postSampleB` are not read by it. -/
def gSig : PostInB k n m mF ⊕ (Fin n ⊕ Unit) → GIn k n m mF ⊕ (Fin n ⊕ Unit ⊕ Unit)
  | .inl (.inl _) => .inr (.inr (.inl ()))
  | .inl (.inr (.inl e)) => .inl (.inl (.inr (.inr (.inr (.inr e)))))
  | .inl (.inr (.inr (.inl e))) => .inl (.inr (.inl e))
  | .inl (.inr (.inr (.inr e))) => .inl (.inr (.inr e))
  | .inr (.inl j) => .inr (.inl j)
  | .inr (.inr _) => .inr (.inr (.inl ()))

/-- The product of the inputs `z` and `inr ()`: one operation. -/
def mulZ {ι : Type} (z : ι) : RProg (ι ⊕ Unit) Unit :=
  ⟨[⟨.mul, .inp (Sum.inl z), .inp (Sum.inr ())⟩], fun _ => .reg 0⟩

theorem mulZ_eval {ι : Type} (z : ι) (v : ι ⊕ Unit → ℝ) (u : Unit) :
    (mulZ z).eval v u = v (Sum.inl z) * v (Sum.inr ()) := by
  simp [mulZ, RProg.eval, rrun, RInstr.eval, ROp.eval, Arg.eval]

theorem mulZ_cost {ι : Type} (z : ι) : (mulZ z).cost = 1 := rfl

/-- The mean of the `k` values, times `ζ`: `(k − 1) + 2` operations. -/
def meanZ : RProg ((GIn k n m mF ⊕ (Fin n ⊕ Unit ⊕ Unit)) ⊕ Fin k) Unit :=
  (meanTail k (GIn k n m mF ⊕ (Fin n ⊕ Unit ⊕ Unit))).bind
    (mulZ (Sum.inl (Sum.inr (Sum.inr (Sum.inr ())))))

/-- **The arithmetic program after the pass over `W`**: the pass over `A` (`passProgZ`), then
`k` forward passes of `F` at `c̃_A + σ̃_p γ_i`, the mean, and the zero factor. No oracle; no
forward pass of `A`. -/
def gA150 : RProg (GIn k n m mF) Unit :=
  ((passProgZ n m J).mapIn Sum.inl).bind
    ((RProg.par (fun i => (postSampleB k n m mF i).mapIn (gSig k n m mF)) (List.finRange k)).bind
      (meanZ k n m mF))

variable {k n m mF J}

theorem meanZ_eval (v : (GIn k n m mF ⊕ (Fin n ⊕ Unit ⊕ Unit)) ⊕ Fin k → ℝ) (u : Unit) :
    (meanZ k n m mF).eval v u =
      v (Sum.inl (Sum.inr (Sum.inr (Sum.inr ())))) * ((k : ℝ)⁻¹ * ∑ i, v (Sum.inr i)) := by
  rw [meanZ, RProg.eval_bind, mulZ_eval]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [meanTail_eval]

variable (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (A₃ : Matrix (Fin n) (Fin m) ℝ) (γ : Fin k → Fin n → ℝ)
    (F : MlpParam n mF 1)

/-- The value of `gA150` in terms of the three outputs of `passProgZ`. -/
theorem gA150_eval_gen :
    (gA150 k n m mF J).eval (gVal c τ A₁ A₂ A₃ γ F) () =
      (passProgZ n m J).eval (passVal c τ A₁ A₂ A₃) (Sum.inr (Sum.inr ())) *
        ((k : ℝ)⁻¹ * ∑ i, evF F
          ((fun j => (passProgZ n m J).eval (passVal c τ A₁ A₂ A₃) (Sum.inl j)) +
            (passProgZ n m J).eval (passVal c τ A₁ A₂ A₃) (Sum.inr (Sum.inl ())) • γ i)) := by
  rw [gA150, RProg.eval_bind, RProg.eval_bind, meanZ_eval]
  refine congrArg₂ (· * ·) ?_ (congrArg _ (Finset.sum_congr rfl fun i _ => ?_))
  · simp only [Sum.elim_inl, Sum.elim_inr, RProg.eval_mapIn]
    rfl
  simp only [Sum.elim_inr]
  rw [RProg.eval_par_mem _ _ _ _ (List.mem_finRange i), RProg.eval_mapIn,
    postSampleB_eval i _ γ F (fun _ => rfl) (fun _ => rfl)]
  simp only [Function.comp, gSig, Sum.elim_inr, RProg.eval_mapIn]
  rfl

/-- **The value of `gA150`** for `τ > 0`: `ζ·(1/k)·Σ_i F(c̃_A + σ̃_p γ_i)` with the finite centre
of `Part150CDefs` (`J₁ = J₂ = J`) and `ζ = (s̃²/s̃²)·(|b̃′|²/|b̃′|²)`. -/
theorem gA150_eval (hτ : 0 < τ) :
    (gA150 k n m mF J).eval (gVal c τ A₁ A₂ A₃ γ F) () =
      sT2 J A₁ c τ / sT2 J A₁ c τ *
          (normSq (bT J J A₁ A₂ c τ) / normSq (bT J J A₁ A₂ c τ)) *
        ((k : ℝ)⁻¹ * ∑ i, evF F (cT J J A₁ A₂ A₃ c τ + sigT J J A₁ A₂ c τ • γ i)) := by
  rw [gA150_eval_gen, passProgZ_eval_zeta c τ A₁ A₂ A₃ hτ, passProgZ_eval_sig c τ A₁ A₂ A₃ hτ]
  have e : (fun j => (passProgZ n m J).eval (passVal c τ A₁ A₂ A₃) (Sum.inl j)) =
      cT J J A₁ A₂ A₃ c τ := funext fun j => passProgZ_eval_c c τ A₁ A₂ A₃ hτ j
  rw [e]

/-- The value of `gA150` when `τ > 0`, `s̃² ≠ 0`, `b̃′ ≠ 0`: the mean of `F(c̃_A + σ̃_p γ_i)`. -/
theorem gA150_eval_one (hτ : 0 < τ) (hs : sT2 J A₁ c τ ≠ 0)
    (hb : normSq (bT J J A₁ A₂ c τ) ≠ 0) :
    (gA150 k n m mF J).eval (gVal c τ A₁ A₂ A₃ γ F) () =
      (k : ℝ)⁻¹ * ∑ i, evF F (cT J J A₁ A₂ A₃ c τ + sigT J J A₁ A₂ c τ • γ i) := by
  rw [gA150_eval c τ A₁ A₂ A₃ γ F hτ, div_self hs, div_self hb, one_mul, one_mul]

/-- At `τ = 0` the output of `gA150` is `0`, for every other input. -/
theorem gA150_eval_zero (hτ : τ = 0) :
    (gA150 k n m mF J).eval (gVal c τ A₁ A₂ A₃ γ F) () = 0 := by
  rw [gA150_eval_gen, passProgZ_eval_zeta_zero c τ A₁ A₂ A₃ hτ, zero_mul]

/-- **The operation count of `gA150`** (exact). -/
theorem gA150_cost (k n m mF J : ℕ) :
    (gA150 k n m mF J).cost =
      (passProgZ n m J).cost + k * (2 * n + mlpCost n mF 1) + ((k - 1) + 2) := by
  have h2 : (RProg.par (fun i => (postSampleB k n m mF i).mapIn (gSig k n m mF))
      (List.finRange k)).cost = k * (2 * n + mlpCost n mF 1) := by
    rw [RProg.cost_par]
    simp [postSampleB_cost]
  have h3 : (meanZ k n m mF).cost = (k - 1) + 2 := by
    simp only [meanZ, RProg.cost_bind, meanTail, RProg.cost_ofProg, cost_bind, sumProg_cost,
      cost_op1, mulZ_cost]
  simp only [gA150, RProg.cost_bind, RProg.cost_mapIn, h2, h3]
  ring

/-- The count of `gA150` at `m = n²` against the paper: the `A` part is `CA45 n J − (2J + 4)`
plus one multiplication by `ζ`; one sample of `F` costs `2n + mlpCost n mF 1`. -/
theorem gA150_cost_paper {n : ℕ} (hn : 1 ≤ n) (k mF J : ℕ) :
    (gA150 k n (n ^ 2) mF J).cost + (2 * J + 3) =
      CA45 n J + k * (2 * n + mlpCost n mF 1) + (k - 1) + 1 := by
  have := passProgZ_cost_paper hn J
  rw [gA150_cost]
  omega

end full

end

end BstLean.Part150
