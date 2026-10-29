import BstLean.Part182OBlk2
import BstLean.Part182Mask
import BstLean.Part182SBlk

/-!
# Part 182 (file `OBlk3`): the O block of Lemma TI as one statement under `nuA n`

No proof is left open; no `native_decide` or `axiom` is used.

Paper: Lemma `t7:p04:ti` (proof, the O block). **`o3_Oblock`**: for unit `x, x'` with `(x·x')² < 1`,
`τ, η₁, η₂ ≥ 0`, `K₁ = m(1/2 + η₁)`, `K₂ = m(1/2 + η₂)`:
`Pr(|P_E J(x)ᵀ J(x') e'| > o3_kO n τ K₁ K₂) ≤ 8e^{−τ} + 2e^{−2η₁²m} + e^{−2η₂²m}` (`e' = eTan x' x`,
`P_E = PEm x x'`), with `o3_kO` the paper's `n k_o` (`B·Y·j_z`). The projection on
`span(a, a', p')` is a measurable Gram–Schmidt projection `o3_P` (rank `≤ 3`).
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (mask measurable_mask jac)
open BstLean.Part153 (projT nrm nrm_nonneg nrm_sq nrm_smul)

variable {m : ℕ}

/-- Normalization `w ↦ w/|w|` (`0` at `0`). -/
noncomputable def o3_nz (w : Fin m → ℝ) : Fin m → ℝ := (nrm w)⁻¹ • w

lemma o3_nz_cases (w : Fin m → ℝ) : (w = 0 ∧ o3_nz w = 0) ∨ (w ≠ 0 ∧ normSq (o3_nz w) = 1) := by
  by_cases h : w = 0
  · left; refine ⟨h, ?_⟩; simp [o3_nz, h]
  · right
    refine ⟨h, ?_⟩
    have hp : 0 < normSq w := by
      rcases lt_or_eq_of_le (normSq_nonneg w) with h1 | h1
      · exact h1
      · exact absurd (BstLean.Part134.eq_zero_of_normSq h1.symm) h
    have hn : 0 < nrm w := Real.sqrt_pos.2 hp
    unfold o3_nz
    rw [← nrm_sq, nrm_smul, abs_of_pos (inv_pos.2 hn), mul_pow, inv_pow, nrm_sq, ← nrm_sq,
      inv_mul_cancel₀ (by positivity)]

lemma o3_nz_eq (w : Fin m → ℝ) : nrm w • o3_nz w = w := by
  rcases o3_nz_cases w with ⟨h, -⟩ | ⟨h, -⟩
  · simp [h, o3_nz]
  · have hp : 0 < normSq w := by
      rcases lt_or_eq_of_le (normSq_nonneg w) with h1 | h1
      · exact h1
      · exact absurd (BstLean.Part134.eq_zero_of_normSq h1.symm) h
    have hn : 0 < nrm w := Real.sqrt_pos.2 hp
    unfold o3_nz
    rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]

lemma o3_dot_self (w : Fin m → ℝ) : o3_nz w ⬝ᵥ o3_nz w = 0 ∨ o3_nz w ⬝ᵥ o3_nz w = 1 := by
  rw [ms_dot_self]
  rcases o3_nz_cases w with ⟨-, h⟩ | ⟨-, h⟩
  · left; rw [h]; simp [normSq]
  · right; exact h

/-- If `g ⬝ g ∈ {0, 1}` then `(g ⬝ v)(1 − g ⬝ g) = 0`. -/
lemma o3_kill {g v : Fin m → ℝ} (hg : g ⬝ᵥ g = 0 ∨ g ⬝ᵥ g = 1) : (g ⬝ᵥ v) * (1 - g ⬝ᵥ g) = 0 := by
  rcases hg with h | h
  · have : g = 0 := BstLean.Part134.eq_zero_of_normSq (by rw [← ms_dot_self]; exact h)
    simp [this]
  · rw [h]; ring

/-- The Gram–Schmidt vectors of `(a, b, c)`. -/
noncomputable def o3_g1 (a : Fin m → ℝ) : Fin m → ℝ := o3_nz a
noncomputable def o3_w2 (a b : Fin m → ℝ) : Fin m → ℝ := b - (o3_g1 a ⬝ᵥ b) • o3_g1 a
noncomputable def o3_g2 (a b : Fin m → ℝ) : Fin m → ℝ := o3_nz (o3_w2 a b)
noncomputable def o3_w3 (a b c : Fin m → ℝ) : Fin m → ℝ :=
  c - (o3_g1 a ⬝ᵥ c) • o3_g1 a - (o3_g2 a b ⬝ᵥ c) • o3_g2 a b
noncomputable def o3_g3 (a b c : Fin m → ℝ) : Fin m → ℝ := o3_nz (o3_w3 a b c)

/-- The projection onto `span(a, b, c)` (Gram–Schmidt). -/
noncomputable def o3_P (a b c : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  vecMulVec (o3_g1 a) (o3_g1 a) + vecMulVec (o3_g2 a b) (o3_g2 a b) +
    vecMulVec (o3_g3 a b c) (o3_g3 a b c)

lemma o3_orth12 (a b : Fin m → ℝ) : o3_g1 a ⬝ᵥ o3_g2 a b = 0 := by
  have h : o3_g1 a ⬝ᵥ o3_w2 a b = 0 := by
    unfold o3_w2
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have := o3_kill (v := b) (o3_dot_self a)
    unfold o3_g1; linarith
  unfold o3_g2 o3_nz
  rw [dotProduct_smul, h, smul_zero]

lemma o3_orth13 (a b c : Fin m → ℝ) : o3_g1 a ⬝ᵥ o3_g3 a b c = 0 := by
  have h : o3_g1 a ⬝ᵥ o3_w3 a b c = 0 := by
    unfold o3_w3
    rw [dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, o3_orth12, mul_zero, sub_zero]
    have := o3_kill (v := c) (o3_dot_self a)
    unfold o3_g1; linarith
  unfold o3_g3 o3_nz
  rw [dotProduct_smul, h, smul_zero]

lemma o3_orth23 (a b c : Fin m → ℝ) : o3_g2 a b ⬝ᵥ o3_g3 a b c = 0 := by
  have h : o3_g2 a b ⬝ᵥ o3_w3 a b c = 0 := by
    unfold o3_w3
    rw [dotProduct_sub, dotProduct_sub, dotProduct_smul, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, dotProduct_comm (o3_g2 a b) (o3_g1 a), o3_orth12, mul_zero, sub_zero]
    have := o3_kill (v := c) (o3_dot_self (o3_w2 a b))
    unfold o3_g2; linarith
  unfold o3_g3 o3_nz
  rw [dotProduct_smul, h, smul_zero]

lemma o3_P_mulVec (a b c v : Fin m → ℝ) :
    o3_P a b c *ᵥ v = (o3_g1 a ⬝ᵥ v) • o3_g1 a + (o3_g2 a b ⬝ᵥ v) • o3_g2 a b +
      (o3_g3 a b c ⬝ᵥ v) • o3_g3 a b c := by
  unfold o3_P
  simp only [Matrix.add_mulVec]
  have key : ∀ g : Fin m → ℝ, vecMulVec g g *ᵥ v = (g ⬝ᵥ v) • g := by
    intro g; ext i
    simp [Matrix.mulVec, vecMulVec, dotProduct, Finset.mul_sum, mul_comm, mul_left_comm]
  rw [key, key, key]

/-- `P` fixes a vector `nrm w • nz w`-type combination. -/
lemma o3_fix_g {g : Fin m → ℝ} (hg : g ⬝ᵥ g = 0 ∨ g ⬝ᵥ g = 1) : (g ⬝ᵥ g) • g = g := by
  rcases hg with h | h
  · have : g = 0 := BstLean.Part134.eq_zero_of_normSq (by rw [← ms_dot_self]; exact h)
    simp [this]
  · rw [h, one_smul]

lemma o3_P_g1 (a b c : Fin m → ℝ) : o3_P a b c *ᵥ o3_g1 a = o3_g1 a := by
  rw [o3_P_mulVec, dotProduct_comm (o3_g2 a b), o3_orth12, dotProduct_comm (o3_g3 a b c),
    o3_orth13, zero_smul, zero_smul, add_zero, add_zero]
  exact o3_fix_g (o3_dot_self a)

lemma o3_P_g2 (a b c : Fin m → ℝ) : o3_P a b c *ᵥ o3_g2 a b = o3_g2 a b := by
  rw [o3_P_mulVec, o3_orth12, dotProduct_comm (o3_g3 a b c), o3_orth23, zero_smul, zero_smul,
    zero_add, add_zero]
  exact o3_fix_g (o3_dot_self _)

lemma o3_P_g3 (a b c : Fin m → ℝ) : o3_P a b c *ᵥ o3_g3 a b c = o3_g3 a b c := by
  rw [o3_P_mulVec, o3_orth13, o3_orth23, zero_smul, zero_smul, zero_add, zero_add]
  exact o3_fix_g (o3_dot_self _)

lemma o3_P_a (a b c : Fin m → ℝ) : o3_P a b c *ᵥ a = a := by
  have h : o3_P a b c *ᵥ (nrm a • o3_g1 a) = nrm a • o3_g1 a := by
    rw [Matrix.mulVec_smul, o3_P_g1]
  have e : nrm a • o3_g1 a = a := o3_nz_eq a
  rwa [e] at h

lemma o3_P_b (a b c : Fin m → ℝ) : o3_P a b c *ᵥ b = b := by
  have h : o3_P a b c *ᵥ (nrm (o3_w2 a b) • o3_g2 a b + (o3_g1 a ⬝ᵥ b) • o3_g1 a) =
      nrm (o3_w2 a b) • o3_g2 a b + (o3_g1 a ⬝ᵥ b) • o3_g1 a := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, o3_P_g1, o3_P_g2]
  have e : nrm (o3_w2 a b) • o3_g2 a b + (o3_g1 a ⬝ᵥ b) • o3_g1 a = b := by
    unfold o3_g2; rw [o3_nz_eq]; unfold o3_w2; abel
  rwa [e] at h

lemma o3_P_c (a b c : Fin m → ℝ) : o3_P a b c *ᵥ c = c := by
  have h : o3_P a b c *ᵥ (nrm (o3_w3 a b c) • o3_g3 a b c + (o3_g1 a ⬝ᵥ c) • o3_g1 a +
      (o3_g2 a b ⬝ᵥ c) • o3_g2 a b) = nrm (o3_w3 a b c) • o3_g3 a b c + (o3_g1 a ⬝ᵥ c) • o3_g1 a +
      (o3_g2 a b ⬝ᵥ c) • o3_g2 a b := by
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, o3_P_g1, o3_P_g2, o3_P_g3]
  have e : nrm (o3_w3 a b c) • o3_g3 a b c + (o3_g1 a ⬝ᵥ c) • o3_g1 a +
      (o3_g2 a b ⬝ᵥ c) • o3_g2 a b = c := by
    unfold o3_g3; rw [o3_nz_eq]; unfold o3_w3; abel
  rwa [e] at h

lemma o3_P_symm (a b c : Fin m → ℝ) : (o3_P a b c)ᵀ = o3_P a b c := by
  unfold o3_P
  simp only [Matrix.transpose_add, Matrix.transpose_vecMulVec]

lemma o3_P_idem (a b c : Fin m → ℝ) : o3_P a b c * o3_P a b c = o3_P a b c := by
  refine Matrix.toLin'.injective ?_
  refine LinearMap.ext fun v => ?_
  simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
  conv_lhs => rw [o3_P_mulVec a b c v]
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    Matrix.mulVec_smul, o3_P_g1, o3_P_g2, o3_P_g3, ← o3_P_mulVec]

/-- A unit vector orthogonal to two given vectors (`m ≥ 3`). -/
lemma o3_perp2 (hm : 3 ≤ m) (u w : Fin m → ℝ) :
    ∃ v : Fin m → ℝ, v ⬝ᵥ v = 1 ∧ u ⬝ᵥ v = 0 ∧ w ⬝ᵥ v = 0 := by
  set M : Matrix (Fin 2) (Fin m) ℝ := Matrix.of ![u, w] with hM
  have hk : LinearMap.ker (Matrix.mulVecLin M) ≠ ⊥ := by
    refine LinearMap.ker_ne_bot_of_finrank_lt ?_
    simp only [Module.finrank_fin_fun]
    omega
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  have hMv : M *ᵥ v = 0 := hv
  have h0 : u ⬝ᵥ v = 0 := by
    have := congrFun hMv 0
    simpa [hM, Matrix.mulVec] using this
  have h1 : w ⬝ᵥ v = 0 := by
    have := congrFun hMv 1
    simpa [hM, Matrix.mulVec] using this
  rcases o3_nz_cases v with ⟨h, -⟩ | ⟨-, h⟩
  · exact absurd h hv0
  · refine ⟨o3_nz v, by rw [ms_dot_self]; exact h, ?_, ?_⟩
    · unfold o3_nz; rw [dotProduct_smul, h0, smul_zero]
    · unfold o3_nz; rw [dotProduct_smul, h1, smul_zero]

/-- Extension of an orthogonal family of unit-or-zero vectors to an orthonormal triple. -/
lemma o3_frame (hm : 3 ≤ m) {g1 g2 g3 : Fin m → ℝ}
    (h1 : g1 ⬝ᵥ g1 = 0 ∨ g1 ⬝ᵥ g1 = 1) (h2 : g2 ⬝ᵥ g2 = 0 ∨ g2 ⬝ᵥ g2 = 1)
    (h3 : g3 ⬝ᵥ g3 = 0 ∨ g3 ⬝ᵥ g3 = 1)
    (h12 : g1 ⬝ᵥ g2 = 0) (h13 : g1 ⬝ᵥ g3 = 0) (h23 : g2 ⬝ᵥ g3 = 0) :
    ∃ f1 f2 f3 : Fin m → ℝ, f1 ⬝ᵥ f1 = 1 ∧ f2 ⬝ᵥ f2 = 1 ∧ f3 ⬝ᵥ f3 = 1 ∧
      f1 ⬝ᵥ f2 = 0 ∧ f1 ⬝ᵥ f3 = 0 ∧ f2 ⬝ᵥ f3 = 0 ∧
      (g1 = 0 ∨ g1 = f1) ∧ (g2 = 0 ∨ g2 = f2) ∧ (g3 = 0 ∨ g3 = f3) := by
  have z : ∀ g : Fin m → ℝ, g ⬝ᵥ g = 0 → g = 0 := fun g h =>
    BstLean.Part134.eq_zero_of_normSq (by rw [← ms_dot_self]; exact h)
  -- step 1
  obtain ⟨f1, hf1, hf12, hf13, hg1⟩ : ∃ f1 : Fin m → ℝ, f1 ⬝ᵥ f1 = 1 ∧ f1 ⬝ᵥ g2 = 0 ∧ f1 ⬝ᵥ g3 = 0 ∧
      (g1 = 0 ∨ g1 = f1) := by
    rcases h1 with h | h
    · obtain ⟨v, hv, hv2, hv3⟩ := o3_perp2 hm g2 g3
      exact ⟨v, hv, by rw [dotProduct_comm]; exact hv2, by rw [dotProduct_comm]; exact hv3,
        Or.inl (z g1 h)⟩
    · exact ⟨g1, h, h12, h13, Or.inr rfl⟩
  obtain ⟨f2, hf2, hf21, hf23, hg2⟩ : ∃ f2 : Fin m → ℝ, f2 ⬝ᵥ f2 = 1 ∧ f1 ⬝ᵥ f2 = 0 ∧
      f2 ⬝ᵥ g3 = 0 ∧ (g2 = 0 ∨ g2 = f2) := by
    rcases h2 with h | h
    · obtain ⟨v, hv, hv1, hv3⟩ := o3_perp2 hm f1 g3
      exact ⟨v, hv, hv1, by rw [dotProduct_comm]; exact hv3, Or.inl (z g2 h)⟩
    · exact ⟨g2, h, hf12, h23, Or.inr rfl⟩
  obtain ⟨f3, hf3, hf31, hf32, hg3⟩ : ∃ f3 : Fin m → ℝ, f3 ⬝ᵥ f3 = 1 ∧ f1 ⬝ᵥ f3 = 0 ∧
      f2 ⬝ᵥ f3 = 0 ∧ (g3 = 0 ∨ g3 = f3) := by
    rcases h3 with h | h
    · obtain ⟨v, hv, hv1, hv2⟩ := o3_perp2 hm f1 f2
      exact ⟨v, hv, hv1, hv2, Or.inl (z g3 h)⟩
    · exact ⟨g3, h, hf13, hf23, Or.inr rfl⟩
  exact ⟨f1, f2, f3, hf1, hf2, hf3, hf21, hf31, hf32, hg1, hg2, hg3⟩

/-- **Rank ≤ 3** of `o3_P`: an orthonormal `m × 3` frame `U` with `P = U Uᵀ P` (`m ≥ 3`). -/
lemma o3_P_rank3 (hm : 3 ≤ m) (a b c : Fin m → ℝ) :
    ∃ U : Matrix (Fin m) (Fin 3) ℝ, Uᵀ * U = 1 ∧ o3_P a b c = U * Uᵀ * o3_P a b c := by
  obtain ⟨f1, f2, f3, hf1, hf2, hf3, h12, h13, h23, hg1, hg2, hg3⟩ :=
    o3_frame hm (o3_dot_self a) (o3_dot_self (o3_w2 a b)) (o3_dot_self (o3_w3 a b c))
      (o3_orth12 a b) (o3_orth13 a b c) (o3_orth23 a b c)
  set U : Matrix (Fin m) (Fin 3) ℝ := Matrix.of fun i j => ![f1, f2, f3] j i with hU
  have hUU : ∀ w : Fin m → ℝ, (U * Uᵀ) *ᵥ w = (f1 ⬝ᵥ w) • f1 + (f2 ⬝ᵥ w) • f2 + (f3 ⬝ᵥ w) • f3 := by
    intro w; ext i
    simp only [hU, Matrix.mulVec, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      dotProduct, Fin.sum_univ_three, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, Finset.sum_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => by ring
  have fix1 : (U * Uᵀ) *ᵥ f1 = f1 := by
    rw [hUU, hf1, dotProduct_comm f2, h12, dotProduct_comm f3, h13]; simp
  have fix2 : (U * Uᵀ) *ᵥ f2 = f2 := by
    rw [hUU, hf2, h12, dotProduct_comm f3, h23]; simp
  have fix3 : (U * Uᵀ) *ᵥ f3 = f3 := by
    rw [hUU, hf3, h13, h23]; simp
  have fixg : ∀ g f : Fin m → ℝ, (g = 0 ∨ g = f) → (U * Uᵀ) *ᵥ f = f → (U * Uᵀ) *ᵥ g = g := by
    intro g f hg hf
    rcases hg with h | h
    · rw [h, Matrix.mulVec_zero]
    · rw [h, hf]
  refine ⟨U, ?_, ?_⟩
  · have key : ∀ j k, (Uᵀ * U) j k = ![f1, f2, f3] j ⬝ᵥ ![f1, f2, f3] k := by
      intro j k; simp [hU, Matrix.mul_apply, dotProduct]
    ext j k
    rw [key]
    fin_cases j <;> fin_cases k <;>
      simp [hf1, hf2, hf3, h12, h13, h23, dotProduct_comm f2 f1, dotProduct_comm f3 f1,
        dotProduct_comm f3 f2]
  · refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec]
    rw [Matrix.mulVec_mulVec, o3_P_mulVec, Matrix.mulVec_add, Matrix.mulVec_add,
      Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul,
      fixg (o3_g1 a) f1 hg1 fix1, fixg (o3_g2 a b) f2 hg2 fix2, fixg (o3_g3 a b c) f3 hg3 fix3]

lemma measurable_o3_P : Measurable (fun t : (Fin m → ℝ) × (Fin m → ℝ) × (Fin m → ℝ) =>
    o3_P t.1 t.2.1 t.2.2) := by
  unfold o3_P o3_g3 o3_w3 o3_g2 o3_w2 o3_g1 o3_nz nrm normSq
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  simp only [Matrix.add_apply, vecMulVec_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
    dotProduct]
  fun_prop

/-- If `ReLU(g) = 0` then `diag(mask g) w = 0`. -/
lemma o3_obD_zero {k : ℕ} {g : Fin k → ℝ} (h : reluV g = 0) (w : Fin k → ℝ) : obD g *ᵥ w = 0 := by
  rw [ob_obD_mulVec]
  funext i
  have hi : relu (g i) = 0 := congrFun h i
  have hg : g i ≤ 0 := by
    unfold relu at hi
    have := le_max_right 0 (g i); linarith
  simp [BstLean.Part151.mask_of_nonpos hg]

section main

variable {n : ℕ}

/-- A fixed unit vector of `ℝ^m` (`m ≥ 1`). -/
noncomputable def o3_e0 (m : ℕ) : Fin m → ℝ := fun i => if i.val = 0 then 1 else 0

lemma o3_e0_unit (hm : 1 ≤ m) : normSq (o3_e0 m) = 1 := by
  unfold normSq o3_e0
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin m)]
  · simp
  · intro b _ hb
    have : b.val ≠ 0 := fun h => hb (Fin.ext h)
    simp [this]
  · simp

/-- The unit direction of `a' = ReLU(A x')` (a fixed unit vector if `a' = 0`). -/
noncomputable def o3_U (x' : Fin n → ℝ) (A : Matrix (Fin (mA n)) (Fin n) ℝ) : Fin (mA n) → ℝ :=
  if reluV (A *ᵥ x') = 0 then o3_e0 (mA n) else o3_nz (reluV (A *ᵥ x'))

lemma o3_U_unit (hm : 1 ≤ mA n) (x' : Fin n → ℝ) (A : Matrix (Fin (mA n)) (Fin n) ℝ) :
    normSq (o3_U x' A) = 1 := by
  unfold o3_U
  split_ifs with h
  · exact o3_e0_unit hm
  · rcases o3_nz_cases (reluV (A *ᵥ x')) with ⟨h', -⟩ | ⟨-, h'⟩
    · exact absurd h' h
    · exact h'

lemma measurable_reluV_mul (x' : Fin n → ℝ) :
    Measurable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => reluV (A *ᵥ x')) := by
  unfold reluV relu
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

lemma measurable_o3_U (x' : Fin n → ℝ) : Measurable (o3_U x') := by
  have h1 := measurable_reluV_mul (n := n) x'
  have hs : MeasurableSet {A : Matrix (Fin (mA n)) (Fin n) ℝ | reluV (A *ᵥ x') = 0} :=
    measurableSet_eq_fun h1 measurable_const
  have h2 : Measurable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => o3_nz (reluV (A *ᵥ x'))) := by
    unfold o3_nz nrm normSq
    have h1' := h1
    refine measurable_pi_iff.mpr fun i => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    refine Measurable.mul ?_ ((measurable_pi_apply i).comp h1)
    refine Measurable.inv ?_
    refine Measurable.sqrt ?_
    exact Finset.measurable_sum _ fun k _ => ((measurable_pi_apply k).comp h1).pow_const 2
  exact Measurable.ite hs measurable_const h2

/-- `p' = D₁' A₁ e'`. -/
noncomputable def o3_pp (x' e' : Fin n → ℝ) (A : Matrix (Fin (mA n)) (Fin n) ℝ) : Fin (mA n) → ℝ :=
  obD (A *ᵥ x') *ᵥ (A *ᵥ e')

/-- `r = p' − (u·p')u`. -/
noncomputable def o3_R (x' e' : Fin n → ℝ) (A : Matrix (Fin (mA n)) (Fin n) ℝ) : Fin (mA n) → ℝ :=
  o3_pp x' e' A - (o3_U x' A ⬝ᵥ o3_pp x' e' A) • o3_U x' A

lemma measurable_o3_pp (x' e' : Fin n → ℝ) : Measurable (o3_pp x' e') := by
  have hmask := measurable_mask
  unfold o3_pp
  simp only [ob_obD_mulVec]
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  fun_prop

lemma measurable_o3_R (x' e' : Fin n → ℝ) : Measurable (o3_R x' e') := by
  have hU := measurable_o3_U (n := n) x'
  have hp := measurable_o3_pp (n := n) x' e'
  unfold o3_R
  have hd : Measurable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => o3_U x' A ⬝ᵥ o3_pp x' e' A) := by
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp hU).mul ((measurable_pi_apply i).comp hp)
  exact hp.sub (hd.smul hU)

lemma o3_U_dot_R (hm : 1 ≤ mA n) (x' e' : Fin n → ℝ) (A : Matrix (Fin (mA n)) (Fin n) ℝ) :
    o3_U x' A ⬝ᵥ o3_R x' e' A = 0 := by
  unfold o3_R
  rw [dotProduct_sub, dotProduct_smul, smul_eq_mul, ms_dot_self, o3_U_unit hm, mul_one, sub_self]

lemma o3_nrm_R_le (hm : 1 ≤ mA n) (x' e' : Fin n → ℝ) (A : Matrix (Fin (mA n)) (Fin n) ℝ) :
    nrm (o3_R x' e' A) ≤ nrm (o3_pp x' e' A) := by
  have h0 := o3_U_dot_R hm x' e' A
  have e : o3_pp x' e' A = o3_R x' e' A + (o3_U x' A ⬝ᵥ o3_pp x' e' A) • o3_U x' A := by
    unfold o3_R; abel
  have hsq : normSq (o3_pp x' e' A) = normSq (o3_R x' e' A) +
      (o3_U x' A ⬝ᵥ o3_pp x' e' A) ^ 2 * normSq (o3_U x' A) := by
    conv_lhs => rw [e]
    rw [← ms_dot_self, ← ms_dot_self, ← ms_dot_self]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    rw [dotProduct_comm (o3_R x' e' A) (o3_U x' A), h0]
    ring
  unfold nrm
  refine Real.sqrt_le_sqrt ?_
  rw [hsq]
  have := normSq_nonneg (o3_U x' A)
  nlinarith [sq_nonneg (o3_U x' A ⬝ᵥ o3_pp x' e' A)]

/-- `|u·p'| = |(a'/|a'|)·p'|`. -/
lemma o3_eps_eq (x' e' : Fin n → ℝ) (A : Matrix (Fin (mA n)) (Fin n) ℝ) :
    o3_U x' A ⬝ᵥ o3_pp x' e' A =
      ((nrm (reluV (A *ᵥ x')))⁻¹ • reluV (A *ᵥ x')) ⬝ᵥ (obD (A *ᵥ x') *ᵥ (A *ᵥ e')) := by
  unfold o3_U o3_pp
  split_ifs with h
  · rw [o3_obD_zero h, h]; simp
  · rfl

/-- `|D₂(a') w| ≤ |D₂(u) w|`. -/
lemma o3_mask_le (x' : Fin n → ℝ) (A : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (w : Fin (mA n) → ℝ) :
    nrm (obD (A₂ *ᵥ reluV (A *ᵥ x')) *ᵥ w) ≤ nrm (obD (A₂ *ᵥ o3_U x' A) *ᵥ w) := by
  by_cases h : reluV (A *ᵥ x') = 0
  · rw [h, Matrix.mulVec_zero]
    have : obD (0 : Fin (mA n) → ℝ) *ᵥ w = 0 := by
      rw [ob_obD_mulVec]; funext i; simp [BstLean.Part151.mask_of_nonpos (le_refl (0:ℝ))]
    rw [this]
    simp only [nrm, normSq, Pi.zero_apply]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
      Real.sqrt_zero]
    exact nrm_nonneg _
  · have hU : o3_U x' A = o3_nz (reluV (A *ᵥ x')) := by unfold o3_U; rw [if_neg h]
    have hp : 0 < nrm (reluV (A *ᵥ x')) := by
      rcases o3_nz_cases (reluV (A *ᵥ x')) with ⟨h', -⟩ | ⟨-, -⟩
      · exact absurd h' h
      · exact Real.sqrt_pos.2 (mk_normSq_pos h)
    have e : reluV (A *ᵥ x') = nrm (reluV (A *ᵥ x')) • o3_U x' A := by rw [hU, o3_nz_eq]
    rw [e, Matrix.mulVec_smul, ob_obD_smul_pos hp]

lemma o3_jac_e (x' e' : Fin n → ℝ) (A : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :
    jac A A₂ x' *ᵥ e' = obD (A₂ *ᵥ reluV (A *ᵥ x')) *ᵥ (A₂ *ᵥ o3_pp x' e' A) := by
  rw [ob_jac_eq]; unfold o3_pp; simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- The vector `z` as a function of `(A₁, B)` with `B = A₂ P`. -/
noncomputable def o3_Zf (x x' e' : Fin n → ℝ)
    (q : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) : Fin (mA n) → ℝ :=
  obD (q.2 *ᵥ reluV (q.1 *ᵥ x)) *ᵥ (obD (q.2 *ᵥ reluV (q.1 *ᵥ x')) *ᵥ (q.2 *ᵥ o3_pp x' e' q.1))

/-- The projection on `span(a, a', p')` as a function of `A₁`. -/
noncomputable def o3_Pf (x x' e' : Fin n → ℝ) (A : Matrix (Fin (mA n)) (Fin n) ℝ) :
    Matrix (Fin (mA n)) (Fin (mA n)) ℝ :=
  o3_P (reluV (A *ᵥ x)) (reluV (A *ᵥ x')) (o3_pp x' e' A)

/-- The vector `y₁` as a function of `(A₂, (A₁x, A₁e))` (with `x' = c x + σ e`, `e' = σ x − c e`). -/
noncomputable def o3_Yf (c σ : ℝ) (B : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (gh : (Fin (mA n) → ℝ) × (Fin (mA n) → ℝ)) : Fin (mA n) → ℝ :=
  obD gh.1 *ᵥ (Bᵀ *ᵥ (obD (B *ᵥ reluV gh.1) *ᵥ (obD (B *ᵥ reluV (c • gh.1 + σ • gh.2)) *ᵥ
    (B *ᵥ (obD (c • gh.1 + σ • gh.2) *ᵥ (σ • gh.1 - c • gh.2))))))

lemma measurable_o3_Zf (x x' e' : Fin n → ℝ) : Measurable (o3_Zf x x' e') := by
  have hmask := measurable_mask
  unfold o3_Zf o3_pp
  simp only [ob_obD_mulVec]
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct, reluV, relu]
  fun_prop

lemma measurable_o3_Yf (c σ : ℝ) : Measurable (Function.uncurry (o3_Yf (n := n) c σ)) := by
  have hmask := measurable_mask
  unfold o3_Yf Function.uncurry
  simp only [ob_obD_mulVec]
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct, reluV, relu, Matrix.transpose_apply, Pi.add_apply,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  fun_prop

lemma measurable_o3_Pf (x x' e' : Fin n → ℝ) : Measurable (o3_Pf x x' e') := by
  have h := (measurable_o3_P (m := mA n)).comp ((measurable_reluV_mul (n := n) x).prodMk
    ((measurable_reluV_mul (n := n) x').prodMk (measurable_o3_pp (n := n) x' e')))
  unfold o3_Pf
  simpa only [Function.comp_def] using h

lemma o3_PEm_symm (x x' : Fin n → ℝ) : (PEm x x')ᵀ = PEm x x' := by
  unfold PEm
  simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_vecMulVec]

lemma o3_Zf_eq (x x' e' : Fin n → ℝ) (A : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) :
    o3_Zf x x' e' (A, A₂ * o3_Pf x x' e' A) =
      obD (A₂ *ᵥ reluV (A *ᵥ x)) *ᵥ (jac A A₂ x' *ᵥ e') := by
  unfold o3_Zf o3_Pf
  simp only [← Matrix.mulVec_mulVec, o3_P_a, o3_P_b, o3_P_c]
  rw [o3_jac_e]

/-- **The O-block assembly with the concrete events** (deterministic). -/
lemma o3_det {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    (hc : (x ⬝ᵥ x') ^ 2 < 1) (hm : 1 ≤ mA n) (A : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) {Yc Bc av ε₀ C pp : ℝ}
    (hYc : 0 ≤ Yc) (hBc : 0 ≤ Bc) (hC : 0 ≤ C)
    (h4 : nrm (fun k => mask ((A *ᵥ x) k) *
        (A₂ᵀ *ᵥ o3_Zf x x' (eTan x' x) (A, A₂ * o3_Pf x x' (eTan x' x) A)) k) ≤
      Yc * nrm (o3_Zf x x' (eTan x' x) (A, A₂ * o3_Pf x x' (eTan x' x) A)))
    (h5 : nrm ((A * PEm x x')ᵀ *ᵥ o3_Yf (x ⬝ᵥ x') (√(1 - (x ⬝ᵥ x') ^ 2)) A₂
        (A *ᵥ x, A *ᵥ eTan x x')) ≤
      Bc * nrm (o3_Yf (x ⬝ᵥ x') (√(1 - (x ⬝ᵥ x') ^ 2)) A₂ (A *ᵥ x, A *ᵥ eTan x x')))
    (h6 : nrm (A₂ *ᵥ o3_U x' A) ≤ av)
    (h7 : |((nrm (reluV (A *ᵥ x')))⁻¹ • reluV (A *ᵥ x')) ⬝ᵥ
        (obD (A *ᵥ x') *ᵥ (A *ᵥ eTan x' x))| ≤ ε₀)
    (h8 : nrm (obD (A₂ *ᵥ o3_U x' A) *ᵥ (A₂ *ᵥ o3_R x' (eTan x' x) A)) ≤
      C * nrm (o3_R x' (eTan x' x) A))
    (h9 : nrm (o3_pp x' (eTan x' x) A) ≤ pp) :
    nrm (PEm x x' *ᵥ (((jac A A₂ x)ᵀ * jac A A₂ x') *ᵥ eTan x' x)) ≤
      Bc * Yc * (ε₀ * av + C * pp) := by
  obtain ⟨-, -, -, hx'e, he'e⟩ := sb_frame hx hx' hc
  set c := x ⬝ᵥ x' with hcd
  set σ := √(1 - c ^ 2) with hσ
  set e := eTan x x' with hed
  set e' := eTan x' x with he'd
  have hAx' : A *ᵥ x' = c • (A *ᵥ x) + σ • (A *ᵥ e) := by
    conv_lhs => rw [hx'e]
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  have hAe' : A *ᵥ e' = σ • (A *ᵥ x) - c • (A *ᵥ e) := by
    rw [he'e, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
  -- the vector y₁
  have hY : o3_Yf c σ A₂ (A *ᵥ x, A *ᵥ e) = obD (A *ᵥ x) *ᵥ (A₂ᵀ *ᵥ
      (obD (A₂ *ᵥ reluV (A *ᵥ x)) *ᵥ (jac A A₂ x' *ᵥ e'))) := by
    rw [o3_jac_e]
    unfold o3_Yf o3_pp
    simp only
    rw [← hAx', ← hAe']
  -- z
  have hz := o3_Zf_eq x x' e' A A₂
  -- j_z
  have hjz : nrm (jac A A₂ x' *ᵥ e') ≤ ε₀ * av + C * pp := by
    refine ob_jz A A₂ x' e' (o3_U x' A) (o3_R x' e' A) (o3_U x' A ⬝ᵥ o3_pp x' e' A) ?_ hC h6 ?_ ?_
      ((o3_nrm_R_le hm x' e' A).trans h9)
    · change o3_pp x' e' A = _
      unfold o3_R; abel
    · rw [o3_eps_eq]; exact h7
    · exact (o3_mask_le x' A A₂ _).trans h8
  refine ob_assembly A A₂ x x' (PEm x x') (o3_PEm_symm x x') e' hYc hBc hjz ?_ ?_
  · have h4' := h4
    rw [hz] at h4'
    rw [ob_obD_mulVec]
    exact h4'
  · rw [← hY]
    exact h5

lemma o3_real_le {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {S : Set α}
    {b : ℝ} (hb : 0 ≤ b) (h : μ S ≤ ENNReal.ofReal b) : μ.real S ≤ b := by
  rw [Measure.real]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans (le_of_eq (ENNReal.toReal_ofReal hb))

lemma o3_fst (T : Set (Matrix (Fin (mA n)) (Fin n) ℝ)) :
    (BstLean.Part153.nuA n).real {θ | θ.1 ∈ T} = (gaussMat (mA n) n (2 / (n : ℝ))).real T := by
  have hP2 : IsProbabilityMeasure (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) := by
    unfold gaussMat; infer_instance
  have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ | θ.1 ∈ T} =
      T ×ˢ Set.univ := by ext θ; simp
  rw [e, Measure.real, Measure.real, Measure.prod_prod, measure_univ, mul_one]

/-- The second-layer marginal mask count along `u = U(A₁)`, under `nuA` (Fubini). -/
lemma o3_count2 (hm : 1 ≤ mA n) (x' : Fin n → ℝ) {η : ℝ} (hη : 0 ≤ η) :
    (BstLean.Part153.nuA n).real {θ | ((mA n : ℕ) : ℝ) * (1 / 2 + η) <
      ∑ i, mask ((θ.2 *ᵥ o3_U x' θ.1) i)} ≤ exp (-2 * η ^ 2 * (mA n : ℕ)) := by
  have hP1 : IsProbabilityMeasure (gaussMat (mA n) n (2 / (n : ℝ))) := by
    unfold gaussMat; infer_instance
  have hP2 : IsProbabilityMeasure (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) := by
    unfold gaussMat; infer_instance
  have hU := measurable_o3_U (n := n) x'
  have hc : Continuous (fun z : Matrix (Fin (mA n)) (Fin (mA n)) ℝ × (Fin (mA n) → ℝ) => z.1 *ᵥ z.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hAu : Measurable (fun q : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ =>
      q.2 *ᵥ o3_U x' q.1) := hc.measurable.comp (measurable_snd.prodMk (hU.comp measurable_fst))
  have hSm : MeasurableSet {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      ((mA n : ℕ) : ℝ) * (1 / 2 + η) < ∑ i, mask ((θ.2 *ᵥ o3_U x' θ.1) i)} :=
    measurableSet_lt measurable_const (Finset.measurable_sum _ fun i _ =>
      measurable_mask.comp ((measurable_pi_apply i).comp hAu))
  have hB : 0 ≤ exp (-2 * η ^ 2 * (mA n : ℕ)) := (exp_pos _).le
  refine o3_real_le hB ?_
  unfold BstLean.Part153.nuA
  rw [Measure.prod_apply hSm]
  calc ∫⁻ A, (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) (Prod.mk A ⁻¹'
        {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
          ((mA n : ℕ) : ℝ) * (1 / 2 + η) < ∑ i, mask ((θ.2 *ᵥ o3_U x' θ.1) i)})
        ∂gaussMat (mA n) n (2 / (n : ℝ))
      ≤ ∫⁻ _A, ENNReal.ofReal (exp (-2 * η ^ 2 * (mA n : ℕ))) ∂gaussMat (mA n) n (2 / (n : ℝ)) := by
        refine lintegral_mono fun A => ?_
        have hu0 : o3_U x' A ≠ 0 := by
          intro h0
          have := o3_U_unit hm x' A
          rw [h0] at this; simp [normSq] at this
        have hv : (0 : ℝ) < 2 / ((mA n : ℕ) : ℝ) := by
          have : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by exact_mod_cast hm
          positivity
        have h := single_tail (M := mA n) hv hu0 hη
        rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
        exact ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal (exp (-2 * η ^ 2 * (mA n : ℕ))) := by
        rw [lintegral_const, measure_univ, mul_one]

/-- The paper's `n k_o` with `B = √γ(√n + υ)`, `Y = √t((√m + √3 + υ) + (√K₁ + υ))`,
`j_z = √γυ·√t(√m + υ) + √t(√K₂ + υ)·√γ(√K₁ + υ)`, `υ = √(2τ)`, `γ = 2/n`, `t = 2/m`. -/
noncomputable def o3_kO (n : ℕ) (τ K₁ K₂ : ℝ) : ℝ :=
  (√(2 / (n : ℝ)) * (√(n : ℝ) + √(2 * τ))) *
    (√(2 / ((mA n : ℕ) : ℝ)) * ((√((mA n : ℕ) : ℝ) + √3 + √(2 * τ)) + (√K₁ + √(2 * τ)))) *
    (√(2 / (n : ℝ)) * √(2 * τ) * (√(2 / ((mA n : ℕ) : ℝ)) * (√((mA n : ℕ) : ℝ) + √(2 * τ))) +
      √(2 / ((mA n : ℕ) : ℝ)) * (√K₂ + √(2 * τ)) * (√(2 / (n : ℝ)) * (√K₁ + √(2 * τ))))

/-- **The O block of Lemma TI under `nuA n`**: for unit `x, x'` with `(x·x')² < 1`, `τ, η₁, η₂ ≥ 0`,
`K₁ = m(1/2 + η₁)`, `K₂ = m(1/2 + η₂)`:
`Pr(|P_E J(x)ᵀJ(x') e'| > n k_o) ≤ 8e^{−τ} + 2e^{−2η₁²m} + e^{−2η₂²m}`, `e' = eTan x' x`. -/
theorem o3_Oblock (hn : 2 ≤ n) {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1)
    (hc : (x ⬝ᵥ x') ^ 2 < 1) {τ η₁ η₂ : ℝ} (hτ : 0 ≤ τ) (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂) :
    (BstLean.Part153.nuA n).real {θ | o3_kO n τ (((mA n : ℕ) : ℝ) * (1 / 2 + η₁))
        (((mA n : ℕ) : ℝ) * (1 / 2 + η₂)) <
      nrm (PEm x x' *ᵥ (((jac θ.1 θ.2 x)ᵀ * jac θ.1 θ.2 x') *ᵥ eTan x' x))} ≤
      8 * exp (-τ) + 2 * exp (-2 * η₁ ^ 2 * (mA n : ℕ)) + exp (-2 * η₂ ^ 2 * (mA n : ℕ)) := by
  classical
  have hP1 : IsProbabilityMeasure (gaussMat (mA n) n (2 / (n : ℝ))) := by
    unfold gaussMat; infer_instance
  have hP2 : IsProbabilityMeasure (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) := by
    unfold gaussMat; infer_instance
  have hmA : 4 ≤ mA n := by unfold mA; nlinarith
  have hm1 : 1 ≤ mA n := by omega
  have hm3 : 3 ≤ mA n := by omega
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := by linarith
  have hmR : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by exact_mod_cast hm1
  have hv : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have ht : (0 : ℝ) < 2 / ((mA n : ℕ) : ℝ) := by positivity
  obtain ⟨hxx, hee, hxe, hx'e, he'e⟩ := sb_frame hx hx' hc
  have hc' : (x' ⬝ᵥ x) ^ 2 < 1 := by rw [dotProduct_comm]; exact hc
  have hx'e' : x' ⬝ᵥ eTan x' x = 0 := by rw [dotProduct_comm]; exact eTan_dot_x hx' hx hc'
  have he'u : normSq (eTan x' x) = 1 := by rw [← ms_dot_self]; exact eTan_dot_self hx' hx hc'
  have heu : normSq (eTan x x') = 1 := by rw [← ms_dot_self]; exact hee
  have hx0 : x ≠ 0 := by intro h; rw [h] at hx; simp [normSq] at hx
  have hx'0 : x' ≠ 0 := by intro h; rw [h] at hx'; simp [normSq] at hx'
  set K₁ := ((mA n : ℕ) : ℝ) * (1 / 2 + η₁) with hK₁
  set K₂ := ((mA n : ℕ) : ℝ) * (1 / 2 + η₂) with hK₂
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hK₂0 : 0 ≤ K₂ := by positivity
  set e := eTan x x' with hed
  set e' := eTan x' x with he'd
  set c := x ⬝ᵥ x' with hcd
  set σ := √(1 - c ^ 2) with hσd
  set M := mA n with hM
  -- the nine bad sets
  set S1 := {θ : Matrix (Fin M) (Fin n) ℝ × Matrix (Fin M) (Fin M) ℝ |
    θ.1 ∈ {A : Matrix (Fin M) (Fin n) ℝ | (M : ℝ) * (1 / 2 + η₁) < ∑ i, mask ((A *ᵥ x) i)}} with hS1
  set S2 := {θ : Matrix (Fin M) (Fin n) ℝ × Matrix (Fin M) (Fin M) ℝ |
    θ.1 ∈ {A : Matrix (Fin M) (Fin n) ℝ | (M : ℝ) * (1 / 2 + η₁) < ∑ i, mask ((A *ᵥ x') i)}}
    with hS2
  set S3 := {θ : Matrix (Fin M) (Fin n) ℝ × Matrix (Fin M) (Fin M) ℝ |
    (M : ℝ) * (1 / 2 + η₂) < ∑ i, mask ((θ.2 *ᵥ o3_U x' θ.1) i)} with hS3
  set S4 := {q : Matrix (Fin M) (Fin n) ℝ × Matrix (Fin M) (Fin M) ℝ |
    ∑ i, (fun A : Matrix (Fin M) (Fin n) ℝ => fun i => mask ((A *ᵥ x) i)) q.1 i ≤ K₁ ∧
      √(2 / (M : ℝ)) * ((√(M : ℝ) + √3 + √(2 * τ)) + (√K₁ + √(2 * τ))) *
        nrm (o3_Zf x x' e' (q.1, q.2 * o3_Pf x x' e' q.1)) <
      nrm (fun k => (fun A : Matrix (Fin M) (Fin n) ℝ => fun i => mask ((A *ᵥ x) i)) q.1 k *
        (q.2ᵀ *ᵥ o3_Zf x x' e' (q.1, q.2 * o3_Pf x x' e' q.1)) k)} with hS4
  set S5 := {q : Matrix (Fin M) (Fin n) ℝ × Matrix (Fin M) (Fin M) ℝ |
    √(2 / (n : ℝ)) * (√(n : ℝ) + √(2 * τ)) * nrm (o3_Yf c σ q.2 (q.1 *ᵥ x, q.1 *ᵥ e)) <
      nrm ((q.1 * PEm x x')ᵀ *ᵥ o3_Yf c σ q.2 (q.1 *ᵥ x, q.1 *ᵥ e))} with hS5
  set S6 := {q : Matrix (Fin M) (Fin n) ℝ × Matrix (Fin M) (Fin M) ℝ |
    √(2 / (M : ℝ)) * (√(M : ℝ) + √(2 * τ)) < nrm (q.2 *ᵥ o3_U x' q.1)} with hS6
  set S7 := {θ : Matrix (Fin M) (Fin n) ℝ × Matrix (Fin M) (Fin M) ℝ |
    θ.1 ∈ {A : Matrix (Fin M) (Fin n) ℝ | √(2 / (n : ℝ)) * √(2 * τ) <
      |((nrm (reluV (A *ᵥ x')))⁻¹ • reluV (A *ᵥ x')) ⬝ᵥ (obD (A *ᵥ x') *ᵥ (A *ᵥ e'))|}} with hS7
  set S8 := {q : Matrix (Fin M) (Fin n) ℝ × Matrix (Fin M) (Fin M) ℝ |
    ∑ i, mask ((q.2 *ᵥ o3_U x' q.1) i) ≤ K₂ ∧
      √(2 / (M : ℝ)) * (√K₂ + √(2 * τ)) * nrm (o3_R x' e' q.1) <
        nrm (obD (q.2 *ᵥ o3_U x' q.1) *ᵥ (q.2 *ᵥ o3_R x' e' q.1))} with hS8
  set S9 := {θ : Matrix (Fin M) (Fin n) ℝ × Matrix (Fin M) (Fin M) ℝ |
    θ.1 ∈ {A : Matrix (Fin M) (Fin n) ℝ | ∑ i, mask ((A *ᵥ x') i) ≤ K₁ ∧
      √(2 / (n : ℝ)) * (√K₁ + √(2 * τ)) ≤ nrm (obD (A *ᵥ x') *ᵥ (A *ᵥ e'))}} with hS9
  -- inclusion
  have hsub : {θ : Matrix (Fin M) (Fin n) ℝ × Matrix (Fin M) (Fin M) ℝ | o3_kO n τ K₁ K₂ <
      nrm (PEm x x' *ᵥ (((jac θ.1 θ.2 x)ᵀ * jac θ.1 θ.2 x') *ᵥ e'))} ⊆
      S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ S7 ∪ S8 ∪ S9 := by
    intro θ hθ
    by_contra hno
    simp only [Set.mem_union, not_or] at hno
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨n1, n2⟩, n3⟩, n4⟩, n5⟩, n6⟩, n7⟩, n8⟩, n9⟩ := hno
    simp only [hS1, hS2, hS3, hS4, hS5, hS6, hS7, hS8, hS9, Set.mem_setOf_eq, not_lt, not_and,
      not_le] at n1 n2 n3 n4 n5 n6 n7 n8 n9
    have h9 : nrm (o3_pp x' e' θ.1) ≤ √(2 / (n : ℝ)) * (√K₁ + √(2 * τ)) := (n9 n2).le
    have h8 := n8 n3
    have h4 := n4 n1
    have hdet := o3_det hx hx' hc hm1 θ.1 θ.2 (by positivity) (by positivity) (by positivity)
      h4 n5 n6 n7 h8 h9
    simp only [Set.mem_setOf_eq] at hθ
    have : o3_kO n τ K₁ K₂ =
        √(2 / (n : ℝ)) * (√(n : ℝ) + √(2 * τ)) *
          (√(2 / ((mA n : ℕ) : ℝ)) * ((√((mA n : ℕ) : ℝ) + √3 + √(2 * τ)) + (√K₁ + √(2 * τ)))) *
          (√(2 / (n : ℝ)) * √(2 * τ) * (√(2 / ((mA n : ℕ) : ℝ)) * (√((mA n : ℕ) : ℝ) + √(2 * τ))) +
            √(2 / ((mA n : ℕ) : ℝ)) * (√K₂ + √(2 * τ)) * (√(2 / (n : ℝ)) * (√K₁ + √(2 * τ)))) := rfl
    rw [this] at hθ
    exact absurd hdet (not_le.mpr hθ)
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  set μ := BstLean.Part153.nuA n with hμ
  have hτe : 0 ≤ exp (-τ) := (exp_pos _).le
  have b1 : μ.real S1 ≤ exp (-2 * η₁ ^ 2 * (M : ℕ)) := by
    rw [hS1, hμ, o3_fst]; exact single_tail hv hx0 hη₁
  have b2 : μ.real S2 ≤ exp (-2 * η₁ ^ 2 * (M : ℕ)) := by
    rw [hS2, hμ, o3_fst]; exact single_tail hv hx'0 hη₁
  have b3 : μ.real S3 ≤ exp (-2 * η₂ ^ 2 * (M : ℕ)) := o3_count2 hm1 x' hη₂
  have hdm : Measurable (fun A : Matrix (Fin M) (Fin n) ℝ => fun i => mask ((A *ᵥ x) i)) := by
    have hmask := measurable_mask
    refine measurable_pi_iff.mpr fun i => ?_
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hd : ∀ (A : Matrix (Fin M) (Fin n) ℝ) i,
      (fun A : Matrix (Fin M) (Fin n) ℝ => fun i => mask ((A *ᵥ x) i)) A i = 0 ∨
      (fun A : Matrix (Fin M) (Fin n) ℝ => fun i => mask ((A *ᵥ x) i)) A i = 1 := by
    intro A i
    simp only [mask]
    split_ifs <;> simp
  have b4 : μ.real S4 ≤ 2 * exp (-τ) := o3_real_le (by positivity)
    (o2_y1_tail (gaussMat (mA n) n (2 / (n : ℝ))) ht hτ (o3_Pf x x' e') (measurable_o3_Pf x x' e')
      (fun A => o3_P_symm _ _ _) (fun A => o3_P_idem _ _ _) (fun A => o3_P_rank3 hm3 _ _ _)
      (fun A : Matrix (Fin M) (Fin n) ℝ => fun i => mask ((A *ᵥ x) i)) hdm hd
      (o3_Zf x x' e') (measurable_o3_Zf x x' e'))
  have b5 : μ.real S5 ≤ exp (-τ) := o3_real_le hτe
    (ob_len_joint (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) hv hx heu hxe (PEm x x')
      (bk_projT_x_PEm hx hx' hc) (bk_projT_e_PEm hx hx' hc) (bk_opN_PEm hx hx' hc)
      (o3_Yf c σ) (measurable_o3_Yf c σ) hτ)
  have b6 : μ.real S6 ≤ exp (-τ) := o3_real_le hτe
    (ob_Av_joint (gaussMat (mA n) n (2 / (n : ℝ))) ht (o3_U x') (measurable_o3_U x')
      (fun A => by rw [nrm, o3_U_unit hm1, Real.sqrt_one]) hτ)
  have b7 : μ.real S7 ≤ 2 * exp (-τ) := by
    rw [hS7, hμ, o3_fst]
    exact o3_real_le (by positivity) (ob_eps_tail hv hx' he'u hx'e' hτ)
  have b8 : μ.real S8 ≤ exp (-τ) := o3_real_le hτe
    (o2_mtan_joint (gaussMat (mA n) n (2 / (n : ℝ))) ht (o3_U x') (o3_R x' e')
      (measurable_o3_U x') (measurable_o3_R x' e') (o3_U_unit hm1 x') (o3_U_dot_R hm1 x' e') hτ)
  have b9 : μ.real S9 ≤ exp (-τ) := by
    rw [hS9, hμ, o3_fst]
    exact o3_real_le hτe (ob_p_tail hv hx' he'u hx'e' hτ)
  have U1 := measureReal_union_le (μ := μ) (S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ S7 ∪ S8) S9
  have U2 := measureReal_union_le (μ := μ) (S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6 ∪ S7) S8
  have U3 := measureReal_union_le (μ := μ) (S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5 ∪ S6) S7
  have U4 := measureReal_union_le (μ := μ) (S1 ∪ S2 ∪ S3 ∪ S4 ∪ S5) S6
  have U5 := measureReal_union_le (μ := μ) (S1 ∪ S2 ∪ S3 ∪ S4) S5
  have U6 := measureReal_union_le (μ := μ) (S1 ∪ S2 ∪ S3) S4
  have U7 := measureReal_union_le (μ := μ) (S1 ∪ S2) S3
  have U8 := measureReal_union_le (μ := μ) S1 S2
  linarith

end main





end BstLean.Part182

open BstLean.Part182 in
#print axioms o3_Oblock
