import BstLean.Part150Prog2
import BstLean.Part150Centre

/-!
# Part 150, item 4: the value of the arithmetic pass over `A`

Role: `delegations/statements/p150-spec.md`, item 4. Paper source: `onW45-opus-prover.md` §1,
`onW45c-cx.md` §1 (the zero-case repair: the identification needs `τ > 0`).

* `firstLayer_h`, `firstLayer_g`: the normalization `x = m/s` of the paper is right when
  `s = 0 → m = 0` (homogeneity of `relu`; total division).
* **`passProg_eval_c`**, **`passProg_eval_sig`**: for `τ > 0` the outputs of `passProg n m J` are
  EXACTLY `cT J J A₁ A₂ A₃ c τ` and `sigT J J A₁ A₂ c τ` of `Part150CDefs`.
* `passProgZ_eval_c`, `passProgZ_eval_sig`, `passProgZ_eval_zeta`, `passProgZ_eval_zeta_one`,
  `passProgZ_eval_zeta_zero`: the same with the zero factor `ζ`; `ζ = 0` at `τ = 0`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open BstLean.Cost Finset
open BstLean.Part130 BstLean.Part140

noncomputable section

lemma pQ_cast (J l : ℕ) : ((pQ J l : ℚ) : ℝ) = binW J l := by
  simp [pQ, binW]

/-- The first-layer mean with the normalized shift `x = m/s`. -/
lemma firstLayer_h (J : ℕ) {mm s : ℝ} (hs : 0 ≤ s) (h0 : s = 0 → mm = 0) :
    s * ∑ l : Fin (J + 1), ((pQ J l : ℚ) : ℝ) * relu (mm / s + binAtom J l) =
      binMean J (fun z => relu (mm + s * z)) := by
  unfold binMean
  rw [← Fin.sum_univ_eq_sum_range (fun l => binW J l * relu (mm + s * binAtom J l)) (J + 1),
    mul_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [pQ_cast]
  rcases eq_or_lt_of_le hs with h | h
  · subst h
    rw [h0 rfl]
    simp [relu]
  · rw [mul_left_comm, ← relu_mul_of_nonneg hs]
    congr 2
    field_simp

/-- The first-layer second moment with the normalized shift `x = m/s`. -/
lemma firstLayer_g (J : ℕ) {mm s t2q : ℝ} (hs : 0 ≤ s) (h0 : s = 0 → mm = 0)
    (hq : t2q = s ^ 2) :
    t2q * ∑ l : Fin (J + 1), ((pQ J l : ℚ) : ℝ) * relu (mm / s + binAtom J l) *
        relu (mm / s + binAtom J l) =
      binMean J (fun z => relu (mm + s * z) ^ 2) := by
  unfold binMean
  rw [← Fin.sum_univ_eq_sum_range (fun l => binW J l * relu (mm + s * binAtom J l) ^ 2) (J + 1),
    mul_sum, hq]
  refine sum_congr rfl fun l _ => ?_
  rw [pQ_cast]
  rcases eq_or_lt_of_le hs with h | h
  · subst h
    rw [h0 rfl]
    simp [relu]
  · have e : mm + s * binAtom J l = s * (mm / s + binAtom J l) := by field_simp
    rw [e, relu_mul_of_nonneg hs]
    ring

variable {n m J : ℕ}

lemma mRow_eq_zero_of_sRow (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (i : Fin m) (h : sRow A₁ τ i = 0) : mRow A₁ c i = 0 := by
  have h1 : √(∑ j, A₁ i j ^ 2) = 0 := (mul_eq_zero.mp h).resolve_left hτ.ne'
  have h2 : ∑ j, A₁ i j ^ 2 = 0 :=
    (Real.sqrt_eq_zero (sum_nonneg fun _ _ => sq_nonneg _)).mp h1
  have h3 : ∀ j, A₁ i j = 0 := fun j => by
    have := (sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp h2 j (mem_univ j)
    exact pow_eq_zero_iff (by norm_num) |>.mp this
  simp [mRow, Matrix.mulVec, dotProduct, h3]

lemma sRow_sq' (A₁ : Matrix (Fin m) (Fin n) ℝ) (τ : ℝ) (i : Fin m) :
    τ * τ * ∑ j, A₁ i j ^ 2 = sRow A₁ τ i ^ 2 := by
  rw [sRow_sq]; ring

variable (c : Fin n → ℝ) (τ : ℝ) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (A₃ : Matrix (Fin n) (Fin m) ℝ)

local notation "V₀" => passVal c τ A₁ A₂ A₃

local macro "ssimp" : tactic =>
  `(tactic| simp only [RProg.eval_stage, Option.elim, op1Stage_eval, dotStage_eval,
    sumStage_eval, ROp.eval, Arg.eval])

local macro "keep" : tactic => `(tactic| simp only [RProg.eval_stage, Option.elim])

local macro "insimp" : tactic =>
  `(tactic| (simp only [passAll, pA3, pA2, pA1, pA1b, pA1a, pA0, pS, RProg.eval_stage,
    Option.elim]; rfl))

/-! ## (S) -/

theorem pS_c (j : Fin n) : (pS n m J).eval V₀ (.c j) = c j := by insimp
theorem pS_tau : (pS n m J).eval V₀ .tau = τ := by insimp

theorem pS_z (l : Fin (J + 1)) : (pS n m J).eval V₀ (.z l) = binAtom J l := by
  unfold pS
  ssimp
  unfold binAtom
  push_cast
  ring

/-! ## (A0) -/

theorem pA0_c (j : Fin n) : (pA0 n m J).eval V₀ (.c j) = c j := by insimp
theorem pA0_tau : (pA0 n m J).eval V₀ .tau = τ := by insimp
theorem pA0_A1 (i : Fin m) (j : Fin n) : (pA0 n m J).eval V₀ (.A1 i j) = A₁ i j := by insimp

theorem pA0_z (l : Fin (J + 1)) : (pA0 n m J).eval V₀ (.z l) = binAtom J l := by
  unfold pA0; keep; exact pS_z c τ A₁ A₂ A₃ l

theorem pA0_tau2 : (pA0 n m J).eval V₀ .tau2 = τ * τ := by
  unfold pA0; ssimp; rw [pS_tau]

theorem pA0_rho2 : (pA0 n m J).eval V₀ .rho2 = normSq c + (n : ℝ) * τ ^ 2 := by
  unfold pA0; ssimp
  simp [pS_c, pS_tau, normSq, pow_two]

theorem pA0_rho : (pA0 n m J).eval V₀ .rho = rhoC c τ := by
  unfold pA0; ssimp
  simp [pS_c, pS_tau, normSq, pow_two, rhoC]

/-! ## (A1), first part -/

theorem pA1a_z (l : Fin (J + 1)) : (pA1a n m J).eval V₀ (.z l) = binAtom J l := by
  unfold pA1a; keep; exact pA0_z c τ A₁ A₂ A₃ l
theorem pA1a_tau2 : (pA1a n m J).eval V₀ .tau2 = τ * τ := by
  unfold pA1a; keep; exact pA0_tau2 c τ A₁ A₂ A₃
theorem pA1a_rho2 : (pA1a n m J).eval V₀ .rho2 = normSq c + (n : ℝ) * τ ^ 2 := by
  unfold pA1a; keep; exact pA0_rho2 c τ A₁ A₂ A₃
theorem pA1a_rho : (pA1a n m J).eval V₀ .rho = rhoC c τ := by
  unfold pA1a; keep; exact pA0_rho c τ A₁ A₂ A₃

theorem pA1a_q (i : Fin m) : (pA1a n m J).eval V₀ (.q i) = ∑ j, A₁ i j ^ 2 := by
  unfold pA1a; ssimp
  simp only [pA0_A1, pow_two]

theorem pA1a_s (i : Fin m) : (pA1a n m J).eval V₀ (.s i) = sRow A₁ τ i := by
  unfold pA1a; ssimp
  simp only [pA0_A1, pA0_tau, sRow, pow_two]

theorem pA1a_x (i : Fin m) :
    (pA1a n m J).eval V₀ (.x i) = mRow A₁ c i / sRow A₁ τ i := by
  unfold pA1a; ssimp
  simp only [pA0_A1, pA0_tau, pA0_c, sRow, pow_two]
  rfl

/-! ## (A1), the atoms -/

theorem pA1b_z (l : Fin (J + 1)) : (pA1b n m J).eval V₀ (.z l) = binAtom J l := by
  unfold pA1b; keep; exact pA1a_z c τ A₁ A₂ A₃ l
theorem pA1b_tau2 : (pA1b n m J).eval V₀ .tau2 = τ * τ := by
  unfold pA1b; keep; exact pA1a_tau2 c τ A₁ A₂ A₃
theorem pA1b_rho2 : (pA1b n m J).eval V₀ .rho2 = normSq c + (n : ℝ) * τ ^ 2 := by
  unfold pA1b; keep; exact pA1a_rho2 c τ A₁ A₂ A₃
theorem pA1b_rho : (pA1b n m J).eval V₀ .rho = rhoC c τ := by
  unfold pA1b; keep; exact pA1a_rho c τ A₁ A₂ A₃
theorem pA1b_q (i : Fin m) : (pA1b n m J).eval V₀ (.q i) = ∑ j, A₁ i j ^ 2 := by
  unfold pA1b; keep; exact pA1a_q c τ A₁ A₂ A₃ i
theorem pA1b_s (i : Fin m) : (pA1b n m J).eval V₀ (.s i) = sRow A₁ τ i := by
  unfold pA1b; keep; exact pA1a_s c τ A₁ A₂ A₃ i

theorem pA1b_al (i : Fin m) : (pA1b n m J).eval V₀ (.al i) =
    ∑ l : Fin (J + 1), ((pQ J l : ℚ) : ℝ) * relu (mRow A₁ c i / sRow A₁ τ i + binAtom J l) := by
  unfold pA1b; ssimp
  simp only [pA1a_x, pA1a_z]

theorem pA1b_be (i : Fin m) : (pA1b n m J).eval V₀ (.be i) =
    ∑ l : Fin (J + 1), ((pQ J l : ℚ) : ℝ) * relu (mRow A₁ c i / sRow A₁ τ i + binAtom J l) *
      relu (mRow A₁ c i / sRow A₁ τ i + binAtom J l) := by
  unfold pA1b; ssimp
  simp only [pA1a_x, pA1a_z]

/-! ## (A1), the end -/

theorem pA1_z (l : Fin (J + 1)) : (pA1 n m J).eval V₀ (.z l) = binAtom J l := by
  unfold pA1; keep; exact pA1b_z c τ A₁ A₂ A₃ l
theorem pA1_rho2 : (pA1 n m J).eval V₀ .rho2 = normSq c + (n : ℝ) * τ ^ 2 := by
  unfold pA1; keep; exact pA1b_rho2 c τ A₁ A₂ A₃
theorem pA1_rho : (pA1 n m J).eval V₀ .rho = rhoC c τ := by
  unfold pA1; keep; exact pA1b_rho c τ A₁ A₂ A₃

theorem pA1_h (hτ : 0 < τ) (i : Fin m) : (pA1 n m J).eval V₀ (.h i) = hT J A₁ c τ i := by
  unfold pA1; ssimp
  rw [pA1b_s, pA1b_al]
  exact firstLayer_h J (sRow_nonneg A₁ hτ.le i) (mRow_eq_zero_of_sRow A₁ c hτ i)

theorem pA1_g (hτ : 0 < τ) (i : Fin m) : (pA1 n m J).eval V₀ (.g i) =
    binMean J (fun z => relu (mRow A₁ c i + sRow A₁ τ i * z) ^ 2) := by
  unfold pA1; ssimp
  rw [pA1b_tau2, pA1b_q, pA1b_be]
  exact firstLayer_g J (sRow_nonneg A₁ hτ.le i) (mRow_eq_zero_of_sRow A₁ c hτ i)
    (sRow_sq' A₁ τ i)

/-! ## (A2) -/

theorem pA2_A2 (i j : Fin m) : (pA2 n m J).eval V₀ (.A2 i j) = A₂ i j := by insimp
theorem pA2_rho2 : (pA2 n m J).eval V₀ .rho2 = normSq c + (n : ℝ) * τ ^ 2 := by
  unfold pA2; keep; exact pA1_rho2 c τ A₁ A₂ A₃
theorem pA2_rho : (pA2 n m J).eval V₀ .rho = rhoC c τ := by
  unfold pA2; keep; exact pA1_rho c τ A₁ A₂ A₃
theorem pA2_h (hτ : 0 < τ) (i : Fin m) : (pA2 n m J).eval V₀ (.h i) = hT J A₁ c τ i := by
  unfold pA2; keep; exact pA1_h c τ A₁ A₂ A₃ hτ i

theorem pA2_st (hτ : 0 < τ) : (pA2 n m J).eval V₀ .st = sT J A₁ c τ := by
  unfold pA2; ssimp
  simp only [pA1_g c τ A₁ A₂ A₃ hτ, pA1_h c τ A₁ A₂ A₃ hτ]
  unfold sT sT2 gT
  congr 1
  push_cast
  simp only [pow_two]
  ring

theorem pA2_d (hτ : 0 < τ) (l : Fin (J + 1)) :
    (pA2 n m J).eval V₀ (.d l) = sT J A₁ c τ * binAtom J l := by
  have h := pA2_st c τ A₁ A₂ A₃ hτ (J := J)
  unfold pA2 at h ⊢
  rw [RProg.eval_stage] at h ⊢
  simp only [Option.elim, op1Stage_eval, ROp.eval, Arg.eval] at h ⊢
  rw [h]
  congr 1
  keep
  exact pA1_z c τ A₁ A₂ A₃ l

/-! ## (A3) -/

theorem pA3_A3 (i : Fin n) (j : Fin m) : (pA3 n m J).eval V₀ (.A3 i j) = A₃ i j := by insimp
theorem pA3_rho2 : (pA3 n m J).eval V₀ .rho2 = normSq c + (n : ℝ) * τ ^ 2 := by
  unfold pA3; keep; exact pA2_rho2 c τ A₁ A₂ A₃
theorem pA3_rho : (pA3 n m J).eval V₀ .rho = rhoC c τ := by
  unfold pA3; keep; exact pA2_rho c τ A₁ A₂ A₃

theorem pA3_b (hτ : 0 < τ) (i : Fin m) :
    (pA3 n m J).eval V₀ (.b i) = bT J J A₁ A₂ c τ i := by
  unfold pA3; ssimp
  simp only [pA2_A2, pA2_h c τ A₁ A₂ A₃ hτ, pA2_d c τ A₁ A₂ A₃ hτ]
  unfold bT binMean
  rw [← Fin.sum_univ_eq_sum_range (fun l => binW J l *
    relu ((A₂.mulVec (hT J A₁ c τ)) i + sT J A₁ c τ * binAtom J l)) (J + 1)]
  refine sum_congr rfl fun l _ => ?_
  rw [pQ_cast]
  rfl

/-! ## (A4) and the outputs -/

theorem passAll_cT (hτ : 0 < τ) (i : Fin n) :
    (passAll n m J).eval V₀ (.cT i) = cT J J A₁ A₂ A₃ c τ i := by
  unfold passAll; ssimp
  simp only [pA3_A3, pA3_b c τ A₁ A₂ A₃ hτ, pA3_rho]
  rfl

theorem passAll_nu (hτ : 0 < τ) :
    (passAll n m J).eval V₀ .nu = normSq (bT J J A₁ A₂ c τ) := by
  unfold passAll; ssimp
  simp only [pA3_b c τ A₁ A₂ A₃ hτ, normSq, pow_two]

theorem passAll_sig (hτ : 0 < τ) :
    (passAll n m J).eval V₀ .sig = sigT J J A₁ A₂ c τ := by
  unfold passAll; ssimp
  simp only [pA3_b c τ A₁ A₂ A₃ hτ, pA3_rho2]
  unfold sigT rhoC relu normSq
  rw [Real.sq_sqrt (add_nonneg (sum_nonneg fun _ _ => sq_nonneg _) (by positivity))]
  push_cast
  simp only [pow_two]

/-- **The value of the pass over `A`, first output**: `c̃_A = (A₃ b̃′)/ρ`, for `τ > 0`. -/
theorem passProg_eval_c (hτ : 0 < τ) (i : Fin n) :
    (passProg n m J).eval V₀ (Sum.inl i) = cT J J A₁ A₂ A₃ c τ i := by
  rw [passProg, RProg.eval_mapOut]
  exact passAll_cT c τ A₁ A₂ A₃ hτ i

/-- **The value of the pass over `A`, second output**:
`σ̃_p = √(max(0, 2/n − (2/m)|b̃′|²/ρ²))`, for `τ > 0`. -/
theorem passProg_eval_sig (hτ : 0 < τ) :
    (passProg n m J).eval V₀ (Sum.inr ()) = sigT J J A₁ A₂ c τ := by
  rw [passProg, RProg.eval_mapOut]
  exact passAll_sig c τ A₁ A₂ A₃ hτ

/-! ## The zero factor -/

theorem passAll_tau2 : (passAll n m J).eval V₀ .tau2 = τ * τ := by
  simp only [passAll, pA3, pA2, pA1, pA1b, RProg.eval_stage, Option.elim]
  exact pA1a_tau2 c τ A₁ A₂ A₃

theorem pA2_st2 (hτ : 0 < τ) : (pA2 n m J).eval V₀ .st2 = sT2 J A₁ c τ := by
  unfold pA2; ssimp
  simp only [pA1_g c τ A₁ A₂ A₃ hτ, pA1_h c τ A₁ A₂ A₃ hτ]
  unfold sT2 gT
  push_cast
  simp only [pow_two]
  ring

theorem passAll_st2 (hτ : 0 < τ) : (passAll n m J).eval V₀ .st2 = sT2 J A₁ c τ := by
  simp only [passAll, pA3, RProg.eval_stage, Option.elim]
  exact pA2_st2 c τ A₁ A₂ A₃ hτ

theorem passProgZ_eval_c (hτ : 0 < τ) (i : Fin n) :
    (passProgZ n m J).eval V₀ (Sum.inl i) = cT J J A₁ A₂ A₃ c τ i := by
  rw [passProgZ, RProg.eval_mapOut]
  simp only [Sum.elim_inl]
  unfold passAllZ; keep
  exact passAll_cT c τ A₁ A₂ A₃ hτ i

theorem passProgZ_eval_sig (hτ : 0 < τ) :
    (passProgZ n m J).eval V₀ (Sum.inr (Sum.inl ())) = sigT J J A₁ A₂ c τ := by
  rw [passProgZ, RProg.eval_mapOut]
  simp only [Sum.elim_inr, Sum.elim_inl]
  unfold passAllZ; keep
  exact passAll_sig c τ A₁ A₂ A₃ hτ

/-- The zero factor for `τ > 0`: `ζ = (s̃²/s̃²)·(|b̃′|²/|b̃′|²)`. -/
theorem passProgZ_eval_zeta (hτ : 0 < τ) :
    (passProgZ n m J).eval V₀ (Sum.inr (Sum.inr ())) =
      sT2 J A₁ c τ / sT2 J A₁ c τ *
        (normSq (bT J J A₁ A₂ c τ) / normSq (bT J J A₁ A₂ c τ)) := by
  rw [passProgZ, RProg.eval_mapOut]
  simp only [Sum.elim_inr]
  unfold passAllZ; ssimp
  rw [passAll_tau2, passAll_st2 c τ A₁ A₂ A₃ hτ, passAll_nu c τ A₁ A₂ A₃ hτ,
    div_self (mul_pos hτ hτ).ne', one_mul]

/-- The zero factor is `1` when `τ > 0`, `s̃² ≠ 0` and `b̃′ ≠ 0`. -/
theorem passProgZ_eval_zeta_one (hτ : 0 < τ) (hs : sT2 J A₁ c τ ≠ 0)
    (hb : normSq (bT J J A₁ A₂ c τ) ≠ 0) :
    (passProgZ n m J).eval V₀ (Sum.inr (Sum.inr ())) = 1 := by
  rw [passProgZ_eval_zeta c τ A₁ A₂ A₃ hτ, div_self hs, div_self hb, one_mul]

/-- The zero factor is `0` when `τ = 0` (for every `c`, `A₁`, `A₂`, `A₃`). -/
theorem passProgZ_eval_zeta_zero (hτ : τ = 0) :
    (passProgZ n m J).eval V₀ (Sum.inr (Sum.inr ())) = 0 := by
  rw [passProgZ, RProg.eval_mapOut]
  simp only [Sum.elim_inr]
  unfold passAllZ; ssimp
  rw [passAll_tau2, hτ]
  simp

end

end BstLean.Part150
