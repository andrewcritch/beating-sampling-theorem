import BstLean.Part74Defs
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Part 74: correctness of the computable evaluators `EG`, `EGs`, `dvEs`

* `EG_correct`: `gE (monP v M) = EG (pw v) f M` (Lemma G3 of omSU2).
* `EGs_correct`: `gE (γ^e · monP v M) = EGs (pw v) f g e M`, `γ = Sp v 1 1`.
* `dvEs_correct`: `gE (∂_v^c (γ^e · monP v M)) = dvEs (pw v) f g c e M`.
* `polyP`, `dvEsLR`: the same for a list of terms (a linear combination).
No hypothesis on the norm of `v` is used.
-/

namespace BstLean.Part74

open MeasureTheory MvPolynomial
open BstLean.Part29 (stdGauss)

variable {n : ℕ}

/-! ## Basic facts -/

theorem Sp_zero (v : Fin n → ℝ) (a : ℕ) : Sp v a 0 = C (pw v a) := by
  simp [Sp, pw, map_sum]

theorem gE_C (c : ℝ) : gE (C c : MvPolynomial (Fin n) ℝ) = c := by
  rw [gE_apply]; simp

theorem gE_one : gE (1 : MvPolynomial (Fin n) ℝ) = 1 := by
  rw [← C_1, gE_C]

theorem gE_C_mul (c : ℝ) (P : MvPolynomial (Fin n) ℝ) : gE (C c * P) = c * gE P := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

theorem monP_nil (v : Fin n → ℝ) : monP v [] = 1 := by simp [monP]

theorem monP_cons (v : Fin n → ℝ) (ab : ℕ × ℕ) (M : Mon) :
    monP v (ab :: M) = Sp v ab.1 ab.2 * monP v M := by simp [monP]

theorem lin_list_sum {α : Type} (T : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) (L : List α) (k : α → ℝ)
    (P : α → MvPolynomial (Fin n) ℝ) :
    T ((L.map fun y => C (k y) * P y).sum) = (L.map fun y => k y * T (P y)).sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, map_add, ih]
    rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

/-- `gE ∘ ∂_v^c` as a linear map. -/
noncomputable def gD (v : Fin n → ℝ) (c : ℕ) : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ :=
  gE ∘ₗ ((dvD v).toLinearMap ^ c)

theorem gD_apply (v : Fin n → ℝ) (c : ℕ) (P : MvPolynomial (Fin n) ℝ) :
    gD v c P = gE ((dvD v)^[c] P) := by
  show gE (((dvD v).toLinearMap ^ c) P) = _
  rw [Module.End.pow_apply]
  rfl

theorem pderiv_Sp (v : Fin n → ℝ) (i : Fin n) (a b : ℕ) :
    pderiv i (Sp v a b) = C ((b : ℝ) * v i ^ a) * X i ^ (b - 1) := by
  classical
  unfold Sp
  rw [map_sum, Finset.sum_eq_single i]
  · rw [pderiv_C_mul, pderiv_pow, pderiv_X_self]
    simp only [map_mul, map_natCast]
    ring
  · intro j _ hj
    rw [pderiv_C_mul, pderiv_pow, pderiv_X_of_ne hj]
    simp
  · intro h; exact absurd (Finset.mem_univ i) h

theorem dvD_applyE (v : Fin n → ℝ) (P : MvPolynomial (Fin n) ℝ) :
    dvD v P = ∑ i, C (v i) * pderiv i P := by
  simp [dvD, smul_eq_C_mul]

/-! ## Lemma G3 -/

theorem Sp_succ_mul (v : Fin n → ℝ) (a b : ℕ) (Q : MvPolynomial (Fin n) ℝ) :
    Sp v a (b + 1) * Q = ∑ i, C (v i ^ a) * (X i * (X i ^ b * Q)) := by
  simp only [Sp, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem gE_Sp_succ (v : Fin n → ℝ) (a b : ℕ) (Q : MvPolynomial (Fin n) ℝ) :
    gE (Sp v a (b + 1) * Q) =
      (b : ℝ) * gE (Sp v a (b - 1) * Q) + gE (∑ i, C (v i ^ a) * (X i ^ b * pderiv i Q)) := by
  rw [Sp_succ_mul, map_sum]
  simp only [gE_C_mul, gE_X_mul]
  have h : ∀ i : Fin n, pderiv i (X i ^ b * Q) =
      C (b : ℝ) * (X i ^ (b - 1) * Q) + X i ^ b * pderiv i Q := by
    intro i
    rw [Derivation.leibniz, pderiv_pow, pderiv_X_self]
    simp only [smul_eq_mul, map_natCast]
    ring
  simp only [h, map_add, gE_C_mul, mul_add, Finset.sum_add_distrib]
  congr 1
  · simp only [Sp, Finset.sum_mul, map_sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, gE_C_mul]
    ring
  · simp only [map_sum, gE_C_mul]

theorem pstep_poly (v : Fin n → ℝ) (a b : ℕ) (M : Mon) :
    ∑ i, C (v i ^ a) * (X i ^ b * pderiv i (monP v M)) =
      ((pstep a b M).map fun y => C (y.1 : ℝ) * monP v y.2).sum := by
  induction M with
  | nil => simp [monP_nil, pstep]
  | cons x xs ih =>
    obtain ⟨a', b'⟩ := x
    cases b' with
    | zero =>
      simp only [pstep, List.map_map, monP_cons, Sp_zero, pderiv_C_mul]
      have h1 : ∑ i, C (v i ^ a) * (X i ^ b * (C (pw v a') * pderiv i (monP v xs))) =
          C (pw v a') * ∑ i, C (v i ^ a) * (X i ^ b * pderiv i (monP v xs)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [h1, ih, ← List.sum_map_mul_left]
      congr 1
      apply List.map_congr_left
      intro y _
      simp only [Function.comp_apply, monP_cons, Sp_zero]
      ring
    | succ b' =>
      simp only [pstep, List.map_cons, List.sum_cons, List.map_map, monP_cons]
      have h1 : ∑ i, C (v i ^ a) * (X i ^ b * pderiv i (Sp v a' (b' + 1) * monP v xs)) =
          C (((b' + 1 : ℕ) : ℝ)) * (Sp v (a + a') (b + b') * monP v xs) +
            Sp v a' (b' + 1) * ∑ i, C (v i ^ a) * (X i ^ b * pderiv i (monP v xs)) := by
        rw [Finset.mul_sum]
        have : C (((b' + 1 : ℕ) : ℝ)) * (Sp v (a + a') (b + b') * monP v xs) =
            ∑ i, C (v i ^ a) * (X i ^ b * (C (((b' + 1 : ℕ) : ℝ) * v i ^ a') * X i ^ b')) *
              monP v xs := by
          rw [← Finset.sum_mul, ← mul_assoc]
          congr 1
          simp only [Sp, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [map_mul, map_pow, pow_add]
          ring
        rw [this, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Derivation.leibniz, pderiv_Sp]
        simp only [smul_eq_mul, Nat.add_sub_cancel]
        ring
      rw [h1, ih, ← List.sum_map_mul_left]
      congr 2
      apply List.map_congr_left
      intro y _
      simp only [Function.comp_apply, monP_cons]
      ring

theorem mdeg_cons (ab : ℕ × ℕ) (M : Mon) : mdeg (ab :: M) = ab.2 + mdeg M := by
  simp [mdeg]

theorem pstep_meas (a b : ℕ) (M : Mon) :
    ∀ y ∈ pstep a b M, y.2.length = M.length ∧ mdeg y.2 + 1 = mdeg M + b := by
  induction M with
  | nil => simp [pstep]
  | cons x xs ih =>
    obtain ⟨a', b'⟩ := x
    cases b' with
    | zero =>
      intro y hy
      simp only [pstep, List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      obtain ⟨h1, h2⟩ := ih z hz
      dsimp only
      simp only [mdeg_cons, List.length_cons]
      omega
    | succ b' =>
      intro y hy
      simp only [pstep, List.mem_cons, List.mem_map] at hy
      rcases hy with rfl | ⟨z, hz, rfl⟩
      · simp only [mdeg_cons, List.length_cons]
        exact ⟨trivial, by omega⟩
      · obtain ⟨h1, h2⟩ := ih z hz
        dsimp only
        simp only [mdeg_cons, List.length_cons]
        omega

/-- **Lemma G3, as a correct program.** -/
theorem EG_correct (v : Fin n → ℝ) (f : ℕ) (M : Mon) (h : M.length + mdeg M ≤ f) :
    gE (monP v M) = EG (pw v) f M := by
  induction f generalizing M with
  | zero =>
    cases M with
    | nil => simp [EG, monP_nil, gE_one]
    | cons x xs => simp at h
  | succ f ih =>
    cases M with
    | nil => simp [EG, monP_nil, gE_one]
    | cons x xs =>
      obtain ⟨a, b⟩ := x
      simp only [mdeg_cons, List.length_cons] at h
      rcases b with _ | _ | b
      · rw [monP_cons, Sp_zero, gE_C_mul, EG, ih xs (by omega)]
      · rw [monP_cons, EG]
        show gE (Sp v a (0 + 1) * monP v xs) = _
        rw [gE_Sp_succ, pstep_poly, lin_list_sum]
        simp only [Nat.cast_zero, zero_mul, zero_add]
        congr 1
        apply List.map_congr_left
        intro y hy
        obtain ⟨h1, h2⟩ := pstep_meas a 0 xs y hy
        rw [ih y.2 (by omega)]
      · rw [monP_cons, EG]
        show gE (Sp v a (b + 1 + 1) * monP v xs) = _
        rw [gE_Sp_succ, pstep_poly, lin_list_sum, Nat.add_sub_cancel, ← monP_cons v (a, b) xs,
          ih ((a, b) :: xs) (by simp only [mdeg_cons, List.length_cons]; omega)]
        congr 2
        apply List.map_congr_left
        intro y hy
        obtain ⟨h1, h2⟩ := pstep_meas a (b + 1) xs y hy
        rw [ih y.2 (by omega)]

/-! ## The directional derivative on monomials -/

theorem lin_C_mul (T : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ) (k : ℝ) (P : MvPolynomial (Fin n) ℝ) :
    T (C k * P) = k * T P := by
  rw [← smul_eq_C_mul, map_smul, smul_eq_mul]

theorem dvD_C_mul (v : Fin n → ℝ) (k : ℝ) (P : MvPolynomial (Fin n) ℝ) :
    dvD v (C k * P) = C k * dvD v P := by
  rw [← smul_eq_C_mul, Derivation.map_smul, smul_eq_C_mul]

theorem dvD_Sp_succ (v : Fin n → ℝ) (a b : ℕ) :
    dvD v (Sp v a (b + 1)) = C (((b + 1 : ℕ) : ℝ)) * Sp v (a + 1) b := by
  rw [dvD_applyE]
  simp only [pderiv_Sp, Nat.add_sub_cancel]
  rw [Sp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [map_mul, map_pow, pow_succ]
  ring

theorem dvD_gammaE (v : Fin n → ℝ) : dvD v (Sp v 1 1) = C (pw v 2) := by
  have h := dvD_Sp_succ v 1 0
  rw [Sp_zero] at h
  simpa using h

theorem dstep_poly (v : Fin n → ℝ) (M : Mon) :
    dvD v (monP v M) = ((dstep M).map fun y => C (y.1 : ℝ) * monP v y.2).sum := by
  induction M with
  | nil => simp [monP_nil, dstep]
  | cons x xs ih =>
    obtain ⟨a, b⟩ := x
    cases b with
    | zero =>
      simp only [dstep, List.map_map, monP_cons, Sp_zero, dvD_C_mul]
      rw [ih, ← List.sum_map_mul_left]
      congr 1
      apply List.map_congr_left
      intro y _
      simp only [Function.comp_apply, monP_cons, Sp_zero]
      ring
    | succ b =>
      simp only [dstep, List.map_cons, List.sum_cons, List.map_map, monP_cons]
      rw [Derivation.leibniz, dvD_Sp_succ, ih, smul_eq_mul, smul_eq_mul,
        ← List.sum_map_mul_left]
      rw [add_comm]
      congr 1
      · ring
      · congr 1
        apply List.map_congr_left
        intro y _
        simp only [Function.comp_apply, monP_cons]
        ring

theorem dstep_meas (M : Mon) :
    ∀ y ∈ dstep M, y.2.length = M.length ∧ mdeg y.2 + 1 = mdeg M := by
  induction M with
  | nil => simp [dstep]
  | cons x xs ih =>
    obtain ⟨a, b⟩ := x
    cases b with
    | zero =>
      intro y hy
      simp only [dstep, List.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      obtain ⟨h1, h2⟩ := ih z hz
      dsimp only
      simp only [mdeg_cons, List.length_cons]
      omega
    | succ b =>
      intro y hy
      simp only [dstep, List.mem_cons, List.mem_map] at hy
      rcases hy with rfl | ⟨z, hz, rfl⟩
      · simp only [mdeg_cons, List.length_cons]
        exact ⟨trivial, by omega⟩
      · obtain ⟨h1, h2⟩ := ih z hz
        dsimp only
        simp only [mdeg_cons, List.length_cons]
        omega

/-- The Stein identity in the direction `v`: `E[γ F] = E[∂_v F]`, `γ = Σ v_i g_i`. -/
theorem gE_gamma_mul (v : Fin n → ℝ) (F : MvPolynomial (Fin n) ℝ) :
    gE (Sp v 1 1 * F) = gE (dvD v F) := by
  simp only [Sp, Finset.sum_mul, map_sum, pow_one, mul_assoc, gE_C_mul, gE_X_mul, dvD_applyE]

theorem list_mul_sum {α : Type} (G : MvPolynomial (Fin n) ℝ) (L : List α) (k : α → ℝ)
    (P : α → MvPolynomial (Fin n) ℝ) :
    G * (L.map fun y => C (k y) * P y).sum = (L.map fun y => C (k y) * (G * P y)).sum := by
  rw [← List.sum_map_mul_left]
  congr 1
  apply List.map_congr_left
  intro y _
  ring

theorem dvD_gm0 (v : Fin n → ℝ) (M : Mon) :
    dvD v (Sp v 1 1 ^ 0 * monP v M) =
      ((dstep M).map fun y => C (y.1 : ℝ) * (Sp v 1 1 ^ 0 * monP v y.2)).sum := by
  simp only [pow_zero, one_mul, dstep_poly]

theorem dvD_gm (v : Fin n → ℝ) (e : ℕ) (M : Mon) :
    dvD v (Sp v 1 1 ^ (e + 1) * monP v M) =
      C (((e + 1 : ℕ) : ℝ) * pw v 2) * (Sp v 1 1 ^ e * monP v M) +
        ((dstep M).map fun y => C (y.1 : ℝ) * (Sp v 1 1 ^ (e + 1) * monP v y.2)).sum := by
  rw [Derivation.leibniz, Derivation.leibniz_pow, dvD_gammaE, dstep_poly, ← list_mul_sum]
  simp only [smul_eq_mul, nsmul_eq_mul, Nat.add_sub_cancel, map_mul, map_natCast]
  ring

/-- `E_g[γ^e Π S_{a,b}]`, as a correct program. -/
theorem EGs_correct (v : Fin n → ℝ) (f g e : ℕ) (M : Mon) (hf : M.length + mdeg M ≤ f)
    (hg : e + mdeg M ≤ g) : gE (Sp v 1 1 ^ e * monP v M) = EGs (pw v) f g e M := by
  induction g generalizing e M with
  | zero =>
    cases e with
    | zero => rw [pow_zero, one_mul, EGs, EG_correct v f M hf]
    | succ e => omega
  | succ g ih =>
    rcases e with _ | _ | e
    · rw [pow_zero, one_mul, EGs, EG_correct v f M hf]
    · rw [zero_add, pow_one, gE_gamma_mul, dstep_poly, lin_list_sum, EGs]
      congr 1
      apply List.map_congr_left
      intro y hy
      obtain ⟨h1, h2⟩ := dstep_meas M y hy
      have := ih 0 y.2 (by omega) (by omega)
      rw [pow_zero, one_mul] at this
      rw [this]
    · rw [show Sp v 1 1 ^ (e + 1 + 1) * monP v M = Sp v 1 1 * (Sp v 1 1 ^ (e + 1) * monP v M) by
        ring, gE_gamma_mul, dvD_gm, map_add, gE_C_mul, lin_list_sum, EGs,
        ih e M hf (by omega)]
      congr 2
      apply List.map_congr_left
      intro y hy
      obtain ⟨h1, h2⟩ := dstep_meas M y hy
      rw [ih (e + 1) y.2 (by omega) (by omega)]

/-- `E_g[∂_v^c (γ^e Π S_{a,b})]`, as a correct program. -/
theorem dvEs_correct (v : Fin n → ℝ) (f g c e : ℕ) (M : Mon) (hf : M.length + mdeg M ≤ f)
    (hg : e + mdeg M ≤ g) :
    gE ((dvD v)^[c] (Sp v 1 1 ^ e * monP v M)) = dvEs (pw v) f g c e M := by
  induction c generalizing e M with
  | zero => rw [Function.iterate_zero, id, dvEs, EGs_correct v f g e M hf hg]
  | succ c ih =>
    rw [Function.iterate_succ_apply, ← gD_apply]
    cases e with
    | zero =>
      rw [dvD_gm0, lin_list_sum, dvEs]
      congr 1
      apply List.map_congr_left
      intro y hy
      obtain ⟨h1, h2⟩ := dstep_meas M y hy
      rw [gD_apply, ih 0 y.2 (by omega) (by omega)]
    | succ e =>
      rw [dvD_gm, map_add, lin_C_mul, lin_list_sum, dvEs, gD_apply, ih e M hf (by omega)]
      congr 2
      apply List.map_congr_left
      intro y hy
      obtain ⟨h1, h2⟩ := dstep_meas M y hy
      rw [gD_apply, ih (e + 1) y.2 (by omega) (by omega)]

/-! ## Homogeneity and evaluation -/

theorem Sp_hom (v : Fin n → ℝ) (a b : ℕ) : (Sp v a b).IsHomogeneous b := by
  refine IsHomogeneous.sum _ _ _ fun i _ => ?_
  simpa using (isHomogeneous_C (Fin n) (v i ^ a)).mul (isHomogeneous_X_pow i b)

theorem monP_hom0 (v : Fin n → ℝ) (M : Mon) : (monP v M).IsHomogeneous (mdeg M) := by
  induction M with
  | nil => simpa [monP_nil, mdeg] using isHomogeneous_one (Fin n) ℝ
  | cons x xs ih =>
    rw [monP_cons, mdeg_cons]
    exact (Sp_hom v x.1 x.2).mul ih

theorem monP_hom (v : Fin n → ℝ) (e : ℕ) (M : Mon) :
    (Sp v 1 1 ^ e * monP v M).IsHomogeneous (e + mdeg M) := by
  simpa using ((Sp_hom v 1 1).pow e).mul (monP_hom0 v M)

theorem Sp_eval (v x : Fin n → ℝ) (a b : ℕ) : eval x (Sp v a b) = ∑ i, v i ^ a * x i ^ b := by
  simp [Sp]

theorem monP_eval (v x : Fin n → ℝ) (M : Mon) :
    eval x (monP v M) = (M.map fun ab => ∑ i, v i ^ ab.1 * x i ^ ab.2).prod := by
  induction M with
  | nil => simp [monP_nil]
  | cons y ys ih => rw [monP_cons, eval_mul, ih, Sp_eval, List.map_cons, List.prod_cons]

/-! ## Linear combinations of terms `c · γ^e · Π S_{a,b}` -/

/-- A term: coefficient, exponent of `γ`, monomial. -/
abbrev Trm := ℝ × ℕ × Mon

/-- The polynomial `Σ_t c_t γ^{e_t} Π_{(a,b) ∈ M_t} S_{a,b}`. -/
noncomputable def polyP (v : Fin n → ℝ) (L : List Trm) : MvPolynomial (Fin n) ℝ :=
  (L.map fun t => C t.1 * (Sp v 1 1 ^ t.2.1 * monP v t.2.2)).sum

/-- `E_g[∂_v^c ·]` of a list of terms. -/
def dvEsLR (p : ℕ → ℝ) (f g c : ℕ) (L : List Trm) : ℝ :=
  (L.map fun t => t.1 * dvEs p f g c t.2.1 t.2.2).sum

theorem polyP_dvEs (v : Fin n → ℝ) (f g c : ℕ) (L : List Trm)
    (h : ∀ t ∈ L, t.2.2.length + mdeg t.2.2 ≤ f ∧ t.2.1 + mdeg t.2.2 ≤ g) :
    gE ((dvD v)^[c] (polyP v L)) = dvEsLR (pw v) f g c L := by
  rw [← gD_apply, polyP, lin_list_sum, dvEsLR]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [gD_apply, dvEs_correct v f g c t.2.1 t.2.2 (h t ht).1 (h t ht).2]

theorem polyP_hom (v : Fin n → ℝ) (L : List Trm) (D : ℕ)
    (h : ∀ t ∈ L, t.2.1 + mdeg t.2.2 = D) : (polyP v L).IsHomogeneous D := by
  unfold polyP
  induction L with
  | nil => simpa using isHomogeneous_zero (Fin n) ℝ D
  | cons t ts ih =>
    rw [List.map_cons, List.sum_cons]
    refine IsHomogeneous.add ?_ (ih fun s hs => h s (List.mem_cons_of_mem _ hs))
    have := (isHomogeneous_C (Fin n) t.1).mul (monP_hom v t.2.1 t.2.2)
    rwa [zero_add, h t List.mem_cons_self] at this

theorem polyP_eval (v x : Fin n → ℝ) (L : List Trm) :
    eval x (polyP v L) = (L.map fun t => t.1 * ((∑ i, v i * x i) ^ t.2.1 *
      (t.2.2.map fun ab => ∑ i, v i ^ ab.1 * x i ^ ab.2).prod)).sum := by
  unfold polyP
  induction L with
  | nil => simp
  | cons t ts ih =>
    rw [List.map_cons, List.sum_cons, eval_add, ih, List.map_cons, List.sum_cons, eval_mul,
      eval_C, eval_mul, eval_pow, Sp_eval, monP_eval]
    simp only [pow_one]

example (v : Fin n → ℝ) :
    gE ((dvD v)^[2] (polyP v [(3, 1, [(2, 2), (3, 3)]), (2, 2, [(0, 4)])])) =
      dvEsLR (pw v) 20 20 2 [(3, 1, [(2, 2), (3, 3)]), (2, 2, [(0, 4)])] :=
  polyP_dvEs v 20 20 2 _ (by simp [mdeg])

example (v : Fin n → ℝ) :
    (polyP v [(3, 1, [(2, 2), (3, 3)]), (2, 2, [(0, 4)])]).IsHomogeneous 6 :=
  polyP_hom v _ 6 (by simp [mdeg])

example (v : Fin n → ℝ) : gE (monP v [(0, 4), (0, 4)]) = EG (pw v) 10 [(0, 4), (0, 4)] :=
  EG_correct v 10 _ (by simp [mdeg])

end BstLean.Part74

#print axioms BstLean.Part74.EG_correct
#print axioms BstLean.Part74.EGs_correct
#print axioms BstLean.Part74.dvEs_correct
#print axioms BstLean.Part74.polyP_dvEs
#print axioms BstLean.Part74.polyP_hom
#print axioms BstLean.Part74.polyP_eval
