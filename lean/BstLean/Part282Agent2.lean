import BstLean.Part282Node
import BstLean.Part157Paper

/-!
# Part 282 (C2), the global Agent pass for every `τ₀` (including `τ₀ = 0`), and `ĉ`, `c_A`

Lean: `Part150CDefs.bT`, `hT`, `sT`; `Part157Paper.bAp`; `Part157Net.netRet`.

`agent2 n`: from `ĉ`, `τ`, `A₁`, `A₂`: for each first-layer row `m_i = A₁ᵢ·ĉ`,
`u_i = τ√(|A₁ᵢ|²/J)` and the two binomial sums `h_i = Σ_q w_q relu(m_i + (2q − J)u_i)`,
`e_i = Σ_q w_q relu(·)²` (the atom loop of `Part282Node`, seven operations per atom); then the
second layer is `Part282Node.pB` on `(h, e, A₂)`; then `ρ = √(|ĉ|² + nτ²)` and `b_j = β_j/ρ`.
`agent2_eval`: output `j` is `bT n n A₁ A₂ ĉ τ j / rhoC ĉ τ` for EVERY `τ` (no hypothesis).
`bAp_eq_agent2`: so it is `bAp wc θ j` for every retained value.

`chatProg`: `ĉ = W₃ b_W` (`mulVecProg n m_W`), `chatProg_eval`; the same program gives `c_A = A₃ b`.
-/

namespace BstLean.Part282

open BstLean.Cost BstLean.Part130 BstLean.Part150 BstLean.Part157

noncomputable section

section agent

variable (n : ℕ)

/-- The inputs: `ĉ`, `τ`, `A₁` (`n² × n`), `A₂` (`n² × n²`). -/
abbrev AgIn : Type := Fin n ⊕ (Unit ⊕ ((Fin (mA n) × Fin n) ⊕ (Fin (mA n) × Fin (mA n))))

def agVal {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) : AgIn n → ℝ :=
  Sum.elim c (Sum.elim (fun _ => τ) (Sum.elim (fun p => A₁ p.1 p.2) (fun p => A₂ p.1 p.2)))

def a1Ix (i : Fin (mA n)) (j : Fin n) : AgIn n := Sum.inr (Sum.inr (Sum.inl (i, j)))

/-- `m_i = A₁ᵢ·ĉ`. -/
def mRowProg (i : Fin (mA n)) : RProg (AgIn n) Unit :=
  RProg.ofProg (Prog.sumProd ((List.finRange n).map fun j => (Arg.inp (a1Ix n i j), Arg.inp (Sum.inl j))))

/-- `|A₁ᵢ|²`. -/
def rRowProg (i : Fin (mA n)) : RProg (AgIn n) Unit :=
  RProg.ofProg (Prog.sumProd ((List.finRange n).map fun j => (Arg.inp (a1Ix n i j), Arg.inp (a1Ix n i j))))

/-- `(m_i, u_i = τ√(|A₁ᵢ|²/n))`. -/
def rowAE : Fin 2 → RExpr (AgIn n ⊕ (Unit ⊕ Unit)) :=
  ![.inp (Sum.inr (Sum.inl ())),
    RExpr.mul (.inp (Sum.inl (Sum.inr (Sum.inl ()))))
      (RExpr.sqrt (RExpr.div (.inp (Sum.inr (Sum.inr ()))) (.cst (n : ℚ))))]

def rowAProgA (i : Fin (mA n)) : RProg (AgIn n) (Fin 2) :=
  (RProg.ext (mRowProg n i) ((rRowProg n i).mapIn Sum.inl)).bind (RProg.parV (rowAE n))

def pR : RProg (AgIn n) (Fin (mA n) × Fin 2) := RProg.parL2 (rowAProgA n) (List.finRange (mA n))

abbrev AE1 : Type := AgIn n ⊕ (Fin (mA n) × Fin 2)

/-- The atom loop of `Part282Node` with `h ↦ m_i`, `u ↦ u_i`. -/
def sig1 (i : Fin (mA n)) : AEnv (mA n) → AE1 n :=
  Sum.elim (fun _ => Sum.inr (i, 0)) (Sum.elim (fun _ => Sum.inr (i, 1)) (fun _ => Sum.inr (i, 0)))

def pL1 : RProg (AgIn n) ((Fin (mA n) × Fin 2) ⊕ (Fin (mA n) × Fin 2)) :=
  RProg.ext (pR n) (RProg.parL2 (fun i => (atomLoop (mA n) n i).mapIn (sig1 n i)) (List.finRange (mA n)))

abbrev AE2 : Type := AgIn n ⊕ ((Fin (mA n) × Fin 2) ⊕ (Fin (mA n) × Fin 2))

/-- The inputs of `pB`: `a = h`, `e = e`, `A = A₂`, `b`, `|b|²` unused (set to `h`, `h₀`). -/
def tau2 (hn : 0 < mA n) : NIn (mA n) → AE2 n :=
  Sum.elim (Sum.elim (fun i => Sum.inr (Sum.inr (i, 0))) (fun i => Sum.inr (Sum.inr (i, 1))))
    (Sum.elim (fun p => Sum.inl (Sum.inr (Sum.inr (Sum.inr p))))
      (Sum.elim (fun i => Sum.inr (Sum.inr (i, 0))) (fun _ => Sum.inr (Sum.inr (⟨0, hn⟩, 0)))))

def pAll (hn : 0 < mA n) : RProg (AgIn n)
    (((Fin (mA n) × Fin 2) ⊕ (Fin (mA n) × Fin 2)) ⊕ ((Unit ⊕ Fin (mA n)) ⊕ (Fin (mA n) × Fin 2))) :=
  RProg.ext (pL1 n) ((pB (mA n) n).mapIn (tau2 n hn))

/-- `ρ = √(|ĉ|² + nτ²)`. -/
def ccAProg : RProg (AgIn n) Unit :=
  RProg.ofProg (Prog.sumProd ((List.finRange n).map fun j => (Arg.inp (Sum.inl j), Arg.inp (Sum.inl j))))

def rhoAProg : RProg (AgIn n) Unit :=
  (ccAProg n).bind (RExpr.sqrt (RExpr.add (.inp (Sum.inr ()))
    (RExpr.mul (.cst (n : ℚ)) (RExpr.mul (.inp (Sum.inl (Sum.inr (Sum.inl ()))))
      (.inp (Sum.inl (Sum.inr (Sum.inl ())))))))).prog

/-- **The global Agent pass** (every `τ`). Output `j`: `b_j`. -/
def agent2 (hn : 0 < mA n) : RProg (AgIn n) (Fin (mA n)) :=
  (RProg.ext (pAll n hn) ((rhoAProg n).mapIn Sum.inl)).bind
    (RProg.parV fun j => RExpr.div (.inp (Sum.inr (Sum.inl (Sum.inr (Sum.inr (j, 0))))))
      (.inp (Sum.inr (Sum.inr ()))))

end agent

section values

variable {n : ℕ} (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
  (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)

theorem sqrt_max_zero (x : ℝ) : √(max 0 x) = √x := by
  rcases le_total 0 x with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, Real.sqrt_zero, Real.sqrt_eq_zero'.mpr h]

theorem binMean_relu_gen (J : ℕ) (h s : ℝ) :
    binMean J (fun z => relu (h + s * z)) =
      ∑ q ∈ Finset.range (J + 1), ((J.choose q : ℚ) / 2 ^ J : ℚ) *
        relu (h + (2 * (q : ℚ) - J : ℚ) * (s / √(J : ℝ))) := by
  unfold binMean binW binAtom
  refine Finset.sum_congr rfl fun q _ => ?_
  push_cast
  have e : s * ((2 * (q : ℝ) - J) / √(J : ℝ)) = (2 * q - J) * (s / √(J : ℝ)) := by ring
  rw [e]

theorem binMean_relu2_gen (J : ℕ) (h s : ℝ) :
    binMean J (fun z => relu (h + s * z) ^ 2) =
      ∑ q ∈ Finset.range (J + 1), ((J.choose q : ℚ) / 2 ^ J : ℚ) *
        relu (h + (2 * (q : ℚ) - J : ℚ) * (s / √(J : ℝ))) *
          relu (h + (2 * (q : ℚ) - J : ℚ) * (s / √(J : ℝ))) := by
  unfold binMean binW binAtom
  refine Finset.sum_congr rfl fun q _ => ?_
  push_cast
  have e : s * ((2 * (q : ℝ) - J) / √(J : ℝ)) = (2 * q - J) * (s / √(J : ℝ)) := by ring
  rw [e, pow_two]
  ring

theorem rowAProgA_eval (i : Fin (mA n)) :
    (rowAProgA n i).eval (agVal c τ A₁ A₂) =
      ![mRow A₁ c i, sRow A₁ τ i / √(n : ℝ)] := by
  have hm : (mRowProg n i).eval (agVal c τ A₁ A₂) () = mRow A₁ c i := by
    rw [mRowProg, RProg.eval_ofProg, eval_sumProd, List.map_map, mRow, Matrix.mulVec, dotProduct,
      Fin.sum_univ_def]
    rfl
  have hr : (rRowProg n i).eval (agVal c τ A₁ A₂) () = ∑ j, A₁ i j ^ 2 := by
    rw [rRowProg, RProg.eval_ofProg, eval_sumProd, List.map_map, Fin.sum_univ_def]
    congr 1
    apply List.map_congr_left
    intro j _
    simp [Arg.eval, agVal, a1Ix, pow_two]
  funext x
  rw [rowAProgA, RProg.eval_bind, RProg.eval_parV]
  fin_cases x
  · simp [rowAE, hm]
  · have hr' : (rRowProg n i).eval (Sum.elim c (Sum.elim (fun _ => τ)
        (Sum.elim (fun p => A₁ p.1 p.2) fun p => A₂ p.1 p.2))) () = ∑ j, A₁ i j ^ 2 := hr
    simp [rowAE, hr, hr', sRow, agVal, Real.sqrt_div' _ (Nat.cast_nonneg n)] <;> ring

theorem pL1_eval (i : Fin (mA n)) :
    (pL1 n).eval (agVal c τ A₁ A₂) (Sum.inr (i, 0)) = hT n A₁ c τ i ∧
      (pL1 n).eval (agVal c τ A₁ A₂) (Sum.inr (i, 1)) =
        binMean n (fun z => relu (mRow A₁ c i + sRow A₁ τ i * z) ^ 2) := by
  have hR : ∀ k, (pR n).eval (agVal c τ A₁ A₂) (i, k) = ![mRow A₁ c i, sRow A₁ τ i / √(n : ℝ)] k := by
    intro k
    rw [pR, RProg.eval_parL2 _ _ _ _ _ (List.mem_finRange i), rowAProgA_eval]
  have key := atomLoop_aux n i (Sum.elim (agVal c τ A₁ A₂) ((pR n).eval (agVal c τ A₁ A₂)) ∘ sig1 n i)
    (mRow A₁ c i) (sRow A₁ τ i / √(n : ℝ)) (by simp [sig1, hR]) (by simp [sig1, hR]) (n + 1)
  simp only [pL1, RProg.eval_ext_inr]
  rw [RProg.eval_parL2 _ _ _ _ _ (List.mem_finRange i), RProg.eval_parL2 _ _ _ _ _
    (List.mem_finRange i), RProg.eval_mapIn, RProg.eval_mapIn]
  constructor
  · rw [atomLoop, key]; simp only [hT]; rw [binMean_relu_gen]; rfl
  · rw [atomLoop, key, binMean_relu2_gen]; rfl

theorem agent2_eval (hn : 0 < mA n) (j : Fin (mA n)) :
    (agent2 n hn).eval (agVal c τ A₁ A₂) j = bT n n A₁ A₂ c τ j / rhoC c τ := by
  set v := agVal c τ A₁ A₂ with hv
  set hv1 : Fin (mA n) → ℝ := fun i => hT n A₁ c τ i with hh
  set ev1 : Fin (mA n) → ℝ := fun i => binMean n (fun z => relu (mRow A₁ c i + sRow A₁ τ i * z) ^ 2)
    with he
  have henv : (Sum.elim v ((pL1 n).eval v) ∘ tau2 n hn) =
      nVal hv1 ev1 A₂ hv1 (hv1 ⟨0, hn⟩) := by
    funext x
    rcases x with (i | i) | (p | (i | u))
    · exact (pL1_eval c τ A₁ A₂ i).1
    · exact (pL1_eval c τ A₁ A₂ i).2
    · rfl
    · exact (pL1_eval c τ A₁ A₂ i).1
    · exact (pL1_eval c τ A₁ A₂ ⟨0, hn⟩).1
  have hs : √(nodeV hv1 ev1) = sT n A₁ c τ := by
    unfold nodeV
    rw [sqrt_max_zero, sT, sT2, gT]
    congr 1
    simp only [hh, he, normSq]
    ring
  have hB : (pAll n hn).eval v (Sum.inr (Sum.inr (j, 0))) = bT n n A₁ A₂ c τ j := by
    rw [pAll, RProg.eval_ext_inr, RProg.eval_mapIn, henv, (pB_eval n hv1 ev1 A₂ hv1 _ j).1, hs]
    rfl
  have hρ : (rhoAProg n).eval v () = rhoC c τ := by
    rw [rhoAProg, RProg.eval_bind, RExpr.eval_prog]
    simp only [RExpr.eval_sqrt, RExpr.eval_add, RExpr.eval_mul, RExpr.eval_inp, RExpr.eval_cst,
      Sum.elim_inr, Sum.elim_inl]
    rw [ccAProg, RProg.eval_ofProg, eval_sumProd, List.map_map, rhoC, normSq, Fin.sum_univ_def]
    congr 2
    · congr 1
      apply List.map_congr_left
      intro i _
      simp [Arg.eval, hv, agVal, pow_two]
    · simp [hv, agVal, pow_two]
  rw [agent2, RProg.eval_bind, RProg.eval_parV]
  simp only [RExpr.eval_div, RExpr.eval_inp, Sum.elim_inr, RProg.eval_ext_inl, RProg.eval_ext_inr,
    RProg.eval_mapIn]
  have hc : (Sum.elim v ((pAll n hn).eval v) ∘ Sum.inl) = v := rfl
  rw [hc, hρ, hB]

end values

/-- **The global Agent centre is the Agent program, for every retained value.** -/
theorem bAp_eq_agent2 {n : ℕ} (hn : 0 < mA n) (wc : WRet n) (θ : AHid n) (j : Fin (mA n)) :
    bAp wc θ j = (agent2 n hn).eval (agVal wc.2 (tau0p wc.1) θ.1 θ.2) j :=
  (agent2_eval wc.2 (tau0p wc.1) θ.1 θ.2 hn j).symm

/-! ## `ĉ = W₃ b_W` and `c_A = A₃ b` -/

/-- `M z` for an `r × c` matrix: `mulVecProg` with inputs `z` and the matrix. -/
def chatProg (r c : ℕ) : RProg (Fin c ⊕ (Fin r × Fin c)) (Fin r) := RProg.ofProg (mulVecProg r c)

theorem chatProg_eval {r c : ℕ} (M : Matrix (Fin r) (Fin c) ℝ) (z : Fin c → ℝ) (i : Fin r) :
    (chatProg r c).eval (Sum.elim z (fun e => M e.1 e.2)) i = M.mulVec z i := by
  rw [chatProg, RProg.eval_ofProg, mulVecProg_eval]

theorem chatProg_cost (r c : ℕ) : (chatProg r c).cost = r * (2 * c - 1) := by
  rw [chatProg, RProg.cost_ofProg, mulVecProg_cost]

/-- `ĉ` of the retained data is `chatProg` at `b_W` and `W₃`. -/
theorem chat_eq {n : ℕ} (D : Centres n) (θ : Net3 n) (i : Fin n) :
    (ret D θ).1.2 i = (chatProg n (mW n)).eval
      (Sum.elim (D.bW (θ.1.1, θ.1.2.1)) (fun e => θ.1.2.2 e.1 e.2)) i := by
  rw [chatProg_eval]; rfl

/-- `c_A` of the retained data is `chatProg` at `b` and `A₃`. -/
theorem cA_eq {n : ℕ} (D : Centres n) (θ : Net3 n) (i : Fin n) :
    (ret D θ).2.1.2 i = (chatProg n (mA n)).eval
      (Sum.elim (D.bA (ret D θ).1 (θ.2.1.1, θ.2.1.2.1)) (fun e => θ.2.1.2.2 e.1 e.2)) i := by
  rw [chatProg_eval]; rfl

end

end BstLean.Part282

/-- info: 'BstLean.Part282.bAp_eq_agent2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.bAp_eq_agent2
/-- info: 'BstLean.Part282.chat_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part282.chat_eq
