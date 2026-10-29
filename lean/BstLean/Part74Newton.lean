import BstLean.Part74LineDefs
import BstLean.Part74W33
import BstLean.Part74Expr
import BstLean.Part61LemmaW_Kernel

/-!
# Part 74: Newton's identity for the lists `AL σ j`, general `j`

* `listEval`, `polyPN_listEval`: the value of a list of terms.
* `newton74`: `(j+1) h_{j+1} = Σ_{m ≤ j} π_{m+1} h_{j−m}`; `AL_eval`: `AL σ j` evaluates to
  `j! h_j(u)` when `S_{σ b} = π_b(u)`.
* `kJ_xv74`, `kJ_xx74`, `kJ_vv74`, `kJ_vv74'`: the kernels `k_j` for `j ≤ d`.
* `AL_struct` and its instances: degree, weight and length of the terms of `AL σ j`.
-/

namespace BstLean.Part74

open MvPolynomial
open BstLean.Part56
open BstLean.Part58.Kappa (hval)

variable {n : ℕ}

/-! ## N1 -/

/-- The value of a list of terms, given the values `S a b` of the factors and `s`. -/
noncomputable def listEval (S : ℕ → ℕ → ℝ) (s : ℝ) (L : List TrmN) : ℝ :=
  (L.map fun t => (t.1 : ℝ) * (s ^ t.2.1 * (t.2.2.map fun ab => S ab.1 ab.2).prod)).sum

theorem polyPN_listEval (v x : Fin n → ℝ) (L : List TrmN) :
    eval x (polyPN v L) = listEval (fun a b => ∑ i, v i ^ a * x i ^ b) (∑ i, v i * x i) L :=
  polyPN_eval v x L

theorem listEval_nil (S : ℕ → ℕ → ℝ) (s : ℝ) : listEval S s [] = 0 := by simp [listEval]

theorem listEval_append (S : ℕ → ℕ → ℝ) (s : ℝ) (L1 L2 : List TrmN) :
    listEval S s (L1 ++ L2) = listEval S s L1 + listEval S s L2 := by
  simp [listEval]

theorem listEval_scale (S : ℕ → ℕ → ℝ) (s : ℝ) (c : ℕ) (ab : ℕ × ℕ) (L : List TrmN) :
    listEval S s (L.map fun t => (c * t.1, t.2.1, ab :: t.2.2)) =
      (c : ℝ) * S ab.1 ab.2 * listEval S s L := by
  induction L with
  | nil => simp [listEval]
  | cons t ts ih =>
    simp only [listEval, List.map_cons, List.sum_cons, List.prod_cons] at ih ⊢
    rw [ih]; push_cast; ring

/-! ## N2 -/

theorem newtStep_eval (σ : ℕ → ℕ × ℕ) (S : ℕ → ℕ → ℝ) (s : ℝ) (j : ℕ) (Ls : List (List TrmN))
    (m : ℕ) :
    listEval S s (newtStep σ j m Ls) =
      ∑ i ∈ Finset.range Ls.length, (j.descFactorial (m + i) : ℝ) *
        S (σ (m + i + 1)).1 (σ (m + i + 1)).2 * listEval S s (Ls.getD i []) := by
  induction Ls generalizing m with
  | nil => simp [newtStep, listEval_nil]
  | cons L0 rest ih =>
    rw [newtStep, listEval_append, listEval_scale, ih (m + 1), List.length_cons,
      Finset.sum_range_succ']
    simp only [add_zero, List.getD_cons_zero, List.getD_cons_succ]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [show m + 1 + i = m + (i + 1) by ring]

theorem ALs_eq (σ : ℕ → ℕ × ℕ) (j : ℕ) :
    ALs σ j = (List.range (j + 1)).map fun m => AL σ (j - m) := by
  induction j with
  | zero => simp [ALs, AL]
  | succ j ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    have h1 : AL σ (j + 1 - 0) = newtStep σ j 0 (ALs σ j) := by simp [AL, ALs]
    rw [h1, ALs]
    congr 1
    rw [ih]
    apply List.map_congr_left
    intro m _
    simp

theorem ALs_length (σ : ℕ → ℕ × ℕ) (j : ℕ) : (ALs σ j).length = j + 1 := by
  rw [ALs_eq]; simp

theorem ALs_getD (σ : ℕ → ℕ × ℕ) (j i : ℕ) (hi : i < j + 1) :
    (ALs σ j).getD i [] = AL σ (j - i) := by
  rw [ALs_eq, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  rfl

theorem AL_succ (σ : ℕ → ℕ × ℕ) (j : ℕ) : AL σ (j + 1) = newtStep σ j 0 (ALs σ j) := by
  simp [AL, ALs]

theorem AL_zero (σ : ℕ → ℕ × ℕ) : AL σ 0 = [(1, 0, [])] := by simp [AL, ALs]

/-- `∂_i h_{j+1}(u) = Σ_{m ≤ j} u_i^m h_{j−m}(u)`. -/
theorem pderiv_hsymm_eval74 (u : Fin n → ℝ) (i : Fin n) (j : ℕ) :
    eval u (pderiv i (hsymm (Fin n) ℝ (j + 1))) =
      ∑ m ∈ Finset.range (j + 1), u i ^ m * hval (j - m) u := by
  induction j with
  | zero =>
    rw [BstLean.Part58.Kappa.pderiv_hsymm_succ]
    simp [hval, hsymm_zero]
  | succ j ih =>
    rw [BstLean.Part58.Kappa.pderiv_hsymm_succ, eval_add, eval_mul, eval_X, ih,
      Finset.sum_range_succ' _ (j + 1)]
    simp only [pow_zero, one_mul, Nat.sub_zero, Nat.add_sub_add_right, Finset.mul_sum]
    rw [add_comm]
    congr 1
    · apply Finset.sum_congr rfl
      intro m _
      ring

/-- Newton: `(j+1) h_{j+1} = Σ_{m ≤ j} π_{m+1} h_{j−m}`. -/
theorem newton74 (u : Fin n → ℝ) (j : ℕ) :
    ((j : ℝ) + 1) * hval (j + 1) u =
      ∑ m ∈ Finset.range (j + 1), (∑ i, u i ^ (m + 1)) * hval (j - m) u := by
  have he := BstLean.Part61.W.hval_euler (j + 1) u
  push_cast at he
  rw [← he]
  simp only [pderiv_hsymm_eval74, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The recursion of `A_j = j! h_j`. -/
theorem newtonA74 (u : Fin n → ℝ) (j : ℕ) :
    ((j + 1).factorial : ℝ) * hval (j + 1) u =
      ∑ m ∈ Finset.range (j + 1), (j.descFactorial m : ℝ) * (∑ i, u i ^ (m + 1)) *
        ((((j - m).factorial : ℕ) : ℝ) * hval (j - m) u) := by
  rw [Nat.factorial_succ]
  push_cast
  rw [show ((j : ℝ) + 1) * (j.factorial : ℝ) * hval (j + 1) u =
    (j.factorial : ℝ) * (((j : ℝ) + 1) * hval (j + 1) u) by ring, newton74, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hmj : m ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
  have h := Nat.factorial_mul_descFactorial hmj
  have h' : ((j - m).factorial : ℝ) * (j.descFactorial m : ℝ) = (j.factorial : ℝ) := by
    exact_mod_cast h
  rw [← h']
  ring

theorem AL_eval (σ : ℕ → ℕ × ℕ) (S : ℕ → ℕ → ℝ) (s : ℝ) (u : Fin n → ℝ)
    (hσ : ∀ b, 1 ≤ b → S (σ b).1 (σ b).2 = ∑ i, u i ^ b) (j : ℕ) :
    listEval S s (AL σ j) = (j.factorial : ℝ) * hval j u := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero => simp [AL_zero, listEval, hval, hsymm_zero]
    | succ j =>
      rw [AL_succ, newtStep_eval, ALs_length, newtonA74]
      apply Finset.sum_congr rfl
      intro m hm
      have hmj : m < j + 1 := Finset.mem_range.mp hm
      rw [ALs_getD σ j m hmj, ih (j - m) (by omega), zero_add, hσ (m + 1) (by omega)]

/-! ## N4 -/


theorem newtStep_mem (σ : ℕ → ℕ × ℕ) (j : ℕ) (Ls : List (List TrmN)) (m : ℕ) (t : TrmN)
    (ht : t ∈ newtStep σ j m Ls) :
    ∃ i, i < Ls.length ∧ ∃ t' ∈ Ls.getD i [],
      t = (j.descFactorial (m + i) * t'.1, t'.2.1, σ (m + i + 1) :: t'.2.2) := by
  induction Ls generalizing m with
  | nil => simp [newtStep] at ht
  | cons L0 rest ih =>
    rw [newtStep, List.mem_append] at ht
    rcases ht with h | h
    · obtain ⟨t', ht', rfl⟩ := List.mem_map.mp h
      exact ⟨0, by simp, t', by simpa using ht', rfl⟩
    · obtain ⟨i, hi, t', ht', rfl⟩ := ih (m + 1) h
      refine ⟨i + 1, by simpa using hi, t', by simpa using ht', ?_⟩
      rw [show m + 1 + i = m + (i + 1) by ring]

theorem AL_mem_succ (σ : ℕ → ℕ × ℕ) (j : ℕ) (t : TrmN) (ht : t ∈ AL σ (j + 1)) :
    ∃ i, i ≤ j ∧ ∃ t' ∈ AL σ (j - i),
      t = (j.descFactorial i * t'.1, t'.2.1, σ (i + 1) :: t'.2.2) := by
  rw [AL_succ] at ht
  obtain ⟨i, hi, t', ht', rfl⟩ := newtStep_mem σ j _ 0 t ht
  rw [ALs_length] at hi
  rw [ALs_getD σ j i hi] at ht'
  exact ⟨i, by omega, t', ht', by simp⟩

theorem AL_struct (σ : ℕ → ℕ × ℕ) (cb : ℕ)
    (hσ : ∀ b, 1 ≤ b → (σ b).2 = cb * b ∧ (σ b).1 + (σ b).2 = 2 * b) (j : ℕ) :
    ∀ t ∈ AL σ j, t.2.1 = 0 ∧ mdeg t.2.2 = cb * j ∧ wtM t.2.2 = 2 * j ∧ t.2.2.length ≤ j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero => intro t ht; simp [AL_zero] at ht; subst ht; simp [mdeg, wtM]
    | succ j =>
      intro t ht
      obtain ⟨i, hi, t', ht', rfl⟩ := AL_mem_succ σ j t ht
      obtain ⟨h1, h2, h3, h4⟩ := ih (j - i) (by omega) t' ht'
      obtain ⟨s1, s2⟩ := hσ (i + 1) (by omega)
      refine ⟨h1, ?_, ?_, ?_⟩
      · simp only [mdeg, List.map_cons, List.sum_cons] at h2 ⊢
        rw [h2, s1, ← Nat.mul_add]; congr 1; omega
      · simp only [wtM, List.map_cons, List.sum_cons] at h3 ⊢
        rw [h3, s2]; omega
      · simp only [List.length_cons]; omega

theorem AL_sigX (j : ℕ) :
    ∀ t ∈ AL sigX j, t.2.1 = 0 ∧ mdeg t.2.2 = 1 * j ∧ wtM t.2.2 = 2 * j ∧ t.2.2.length ≤ j :=
  AL_struct sigX 1 (fun b _ => by simp [sigX]; omega) j

theorem AL_sigXX (j : ℕ) :
    ∀ t ∈ AL sigXX j, t.2.1 = 0 ∧ mdeg t.2.2 = 2 * j ∧ wtM t.2.2 = 2 * j ∧ t.2.2.length ≤ j :=
  AL_struct sigXX 2 (fun b _ => by simp [sigXX]) j

theorem AL_sigV (j : ℕ) :
    ∀ t ∈ AL sigV j, t.2.1 = 0 ∧ mdeg t.2.2 = 0 * j ∧ wtM t.2.2 = 2 * j ∧ t.2.2.length ≤ j :=
  AL_struct sigV 0 (fun b _ => by simp [sigV]) j

/-- Every factor of a term of `AL sigV j` is a constant `(a, 0)` with `a ≤ 2j`. -/
theorem AL_sigV_const (j : ℕ) :
    ∀ t ∈ AL sigV j, ∀ ab ∈ t.2.2, ab.2 = 0 ∧ ab.1 ≤ 2 * j := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    cases j with
    | zero => intro t ht; simp [AL_zero] at ht; subst ht; simp
    | succ j =>
      intro t ht ab hab
      obtain ⟨i, hi, t', ht', rfl⟩ := AL_mem_succ sigV j t ht
      rcases List.mem_cons.mp hab with h | h
      · subst h; simp [sigV]; omega
      · obtain ⟨h1, h2⟩ := ih (j - i) (by omega) t' ht' ab h
        exact ⟨h1, by omega⟩

/-! ## N3 -/

theorem kJ_xv74 {d j : ℕ} (hj : j ≤ d) (x v : Fin n → ℝ) :
    kJ d j x v = eval x (polyPN v (AL sigX j)) / (j.factorial : ℝ) := by
  rw [BstLean.Part61.W.kJ_hval j hj x v, polyPN_listEval,
    AL_eval sigX _ _ (fun i => x i * v i) (fun b _ => by
      simp only [sigX]; exact Finset.sum_congr rfl fun i _ => by ring) j]
  field_simp

theorem kJ_xx74 {d j : ℕ} (hj : j ≤ d) (x v : Fin n → ℝ) :
    kJ d j x x = eval x (polyPN v (AL sigXX j)) / (j.factorial : ℝ) := by
  rw [BstLean.Part61.W.kJ_hval j hj x x, polyPN_listEval,
    AL_eval sigXX _ _ (fun i => x i * x i) (fun b _ => by
      simp only [sigXX]; exact Finset.sum_congr rfl fun i _ => by ring) j]
  field_simp

/-- `EG` on a list of constants. -/
theorem EG_const {R : Type} [CommRing R] (p : ℕ → R) (M : Mon) (f : ℕ) (hf : M.length ≤ f)
    (hM : ∀ ab ∈ M, ab.2 = 0) : EG p f M = (M.map fun ab => p ab.1).prod := by
  induction M generalizing f with
  | nil => cases f <;> simp [EG]
  | cons ab M ih =>
    obtain ⟨a, b⟩ := ab
    have hb : b = 0 := hM (a, b) (by simp)
    subst hb
    cases f with
    | zero => simp at hf
    | succ f =>
      rw [EG, ih f (by simpa using hf) (fun ab h => hM ab (by simp [h]))]
      simp

theorem kJ_vv74 {d j : ℕ} (hj : j ≤ d) (v : Fin n → ℝ) (f g : ℕ) (hf : j ≤ f) :
    kJ d j v v = dvEsL (pw v) f g 0 (AL sigV j) / (j.factorial : ℝ) := by
  have hE : dvEsL (pw v) f g 0 (AL sigV j) = listEval (fun a _ => pw v a) 1 (AL sigV j) := by
    unfold dvEsL listEval
    congr 1
    apply List.map_congr_left
    intro t ht
    obtain ⟨h1, -, -, h4⟩ := AL_sigV j t ht
    rw [h1]
    simp only [dvEs, EGs, pow_zero, one_mul]
    rw [EG_const (pw v) t.2.2 f (by omega) (fun ab h => (AL_sigV_const j t ht ab h).1)]
  rw [hE, BstLean.Part61.W.kJ_hval j hj v v,
    AL_eval sigV _ _ (fun i => v i * v i) (fun b _ => by
      simp only [sigV, pw]; exact Finset.sum_congr rfl fun i _ => by ring) j]
  field_simp

theorem kJ_vv74' {d k j : ℕ} (hj : j ≤ d) (hk : 1 ≤ k) (v : Fin n → ℝ) :
    kJ d j v v = kvvF (pw v) d k j := by
  unfold kvvF
  exact kJ_vv74 hj v _ _ (by
    unfold fuelF
    have : d ≤ d * k := Nat.le_mul_of_pos_right d hk
    nlinarith)

end BstLean.Part74

#print axioms BstLean.Part74.AL_eval
#print axioms BstLean.Part74.kJ_xv74
#print axioms BstLean.Part74.kJ_xx74
#print axioms BstLean.Part74.kJ_vv74
#print axioms BstLean.Part74.kJ_vv74'
#print axioms BstLean.Part74.AL_struct
