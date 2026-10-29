import BstLean.Part80Defs3
import BstLean.Part73Orth
import BstLean.Part78Mean
import BstLean.Part71SH

/-!
# Part 80: symmetric sphere integrals (`SphSymm`)

Route: reduce the unit vector `v` to a coordinate vector `e_a` by a Householder reflection, then
use the invariance of `uniformSphere n` under single sign flips and coordinate transpositions.
-/

namespace BstLean.Part80

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part73 (IsOrth uniformSphere_orth orth_sumsq)

section core
variable {n : ℕ}

lemma orth_integral (O : Matrix (Fin n) (Fin n) ℝ) (hO : IsOrth O) (F : (Fin n → ℝ) → ℝ)
    (hF : Continuous F) :
    ∫ x, F (O.mulVec x) ∂uniformSphere n = ∫ x, F x ∂uniformSphere n := by
  have hm : Measurable (fun x : Fin n → ℝ => O.mulVec x) := by fun_prop
  conv_rhs => rw [← uniformSphere_orth O hO]
  rw [integral_map hm.aemeasurable hF.aestronglyMeasurable]

/-- The sign flip of coordinate `m`. -/
def flipv (m : Fin n) (x : Fin n → ℝ) : Fin n → ℝ := fun p => if p = m then - x p else x p

lemma flip_integral (m : Fin n) (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    ∫ x, F (flipv m x) ∂uniformSphere n = ∫ x, F x ∂uniformSphere n := by
  classical
  have hO : IsOrth (Matrix.diagonal (fun p : Fin n => if p = m then (-1 : ℝ) else 1)) := by
    unfold IsOrth
    rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; funext p; split_ifs <;> simp
  have h := orth_integral _ hO F hF
  have e : ∀ x : Fin n → ℝ,
      (Matrix.diagonal (fun p : Fin n => if p = m then (-1 : ℝ) else 1)).mulVec x = flipv m x := by
    intro x; funext p; rw [Matrix.mulVec_diagonal]; unfold flipv; split_ifs <;> simp
  simpa only [e] using h

lemma odd_zero (m : Fin n) (F : (Fin n → ℝ) → ℝ) (hF : Continuous F)
    (hodd : ∀ x, F (flipv m x) = - F x) : ∫ x, F x ∂uniformSphere n = 0 := by
  have h := flip_integral m F hF
  simp only [hodd, integral_neg] at h
  linarith

lemma swap_integral (i j : Fin n) (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    ∫ x, F (fun p => x (Equiv.swap i j p)) ∂uniformSphere n = ∫ x, F x ∂uniformSphere n := by
  classical
  have hO : IsOrth ((Equiv.swap i j).permMatrix ℝ) := by
    unfold IsOrth
    rw [Matrix.transpose_permMatrix, ← Matrix.permMatrix_mul]
    simp
  have h := orth_integral _ hO F hF
  have e : ∀ x : Fin n → ℝ, ((Equiv.swap i j).permMatrix ℝ).mulVec x
      = fun p => x (Equiv.swap i j p) := by
    intro x; rw [Matrix.permMatrix_mulVec]; rfl
  simpa only [e] using h

end core

section coord
variable {n : ℕ} (a : Fin n) (h : ℝ → ℝ)

lemma exch (hn : 2 ≤ n) (G : ℝ → ℝ) (hG : Continuous G) (i : Fin n) (hi : i ≠ a) :
    ((n : ℝ) - 1) * ∫ x, G (x a) * x i ^ 2 ∂uniformSphere n
      = ∫ x, G (x a) * (1 - x a ^ 2) ∂uniformSphere n := by
  classical
  have hsw : ∀ j, j ≠ a → ∫ x, G (x a) * x j ^ 2 ∂uniformSphere n
      = ∫ x, G (x a) * x i ^ 2 ∂uniformSphere n := by
    intro j hj
    have := swap_integral i j (fun x => G (x a) * x i ^ 2) (by fun_prop)
    simp only [Equiv.swap_apply_of_ne_of_ne hi.symm hj.symm, Equiv.swap_apply_left] at this
    exact this
  have hae : (fun x : Fin n → ℝ => G (x a) * (1 - x a ^ 2)) =ᵐ[uniformSphere n]
      fun x => ∑ j ∈ Finset.univ.erase a, G (x a) * x j ^ 2 := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    rw [← Finset.mul_sum, ← hx, Finset.sum_erase_eq_sub (Finset.mem_univ a)]
  rw [integral_congr_ae hae,
    integral_finsetSum _ (fun j _ => BstLean.Part78.sph_int (by omega) (by fun_prop))]
  rw [Finset.sum_congr rfl (fun j hj => hsw j (Finset.ne_of_mem_erase hj))]
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega)]
  simp

/-- `N(i,j) = E[h x_i² x_j²]`. -/
noncomputable def NN (i j : Fin n) : ℝ :=
  ∫ x, h (x a ^ 2) * (x i ^ 2 * x j ^ 2) ∂uniformSphere n

lemma flip_a (m : Fin n) (x : Fin n → ℝ) : flipv m x a ^ 2 = x a ^ 2 := by
  unfold flipv; split_ifs <;> simp

lemma M4_odd (hh : Continuous h) (m i j k l : Fin n)
    (hodd : ∀ x : Fin n → ℝ, flipv m x i * flipv m x j * flipv m x k * flipv m x l
      = -(x i * x j * x k * x l)) :
    ∫ x, h (x a ^ 2) * (x i * x j * x k * x l) ∂uniformSphere n = 0 := by
  apply odd_zero m _ (by fun_prop)
  intro x
  simp only [flip_a, hodd]; ring

lemma M2_odd (hh : Continuous h) (i j : Fin n) (hij : i ≠ j) :
    ∫ x, h (x a ^ 2) * (x i * x j) ∂uniformSphere n = 0 := by
  apply odd_zero i _ (by fun_prop)
  intro x
  simp only [flip_a]
  simp only [flipv, Ne.symm hij, ite_true, ite_false]; ring

lemma M4_formula (hh : Continuous h) (i j k l : Fin n) :
    ∫ x, h (x a ^ 2) * (x i * x j * x k * x l) ∂uniformSphere n =
      (if i = j then if k = l then NN a h i k else 0 else 0)
      + (if i = k then if j = l then NN a h i j else 0 else 0)
      + (if i = l then if j = k then NN a h i j else 0 else 0)
      - 2 * (if i = j then if j = k then if k = l then NN a h i i else 0 else 0 else 0) := by
  classical
  by_cases hij : i = j
  · subst hij
    by_cases hkl : k = l
    · subst hkl
      have e : ∫ x, h (x a ^ 2) * (x i * x i * x k * x k) ∂uniformSphere n = NN a h i k := by
        unfold NN; congr 1; funext x; ring
      rw [e]
      by_cases hik : i = k
      · subst hik; simp; ring
      · simp [hik]
    · have z : ∫ x, h (x a ^ 2) * (x i * x i * x k * x l) ∂uniformSphere n = 0 := by
        apply M4_odd a h hh k
        intro x
        by_cases hik : i = k
        · subst hik; simp only [flipv, Ne.symm hkl, ite_true, ite_false]; ring
        · simp only [flipv, hik, Ne.symm hkl, ite_true, ite_false]; ring
      rw [z]
      by_cases hik : i = k <;> by_cases hil : i = l <;> simp_all
  · by_cases hik : i = k
    · subst hik
      by_cases hjl : j = l
      · subst hjl
        have e : ∫ x, h (x a ^ 2) * (x i * x j * x i * x j) ∂uniformSphere n = NN a h i j := by
          unfold NN; congr 1; funext x; ring
        rw [e]; simp [hij]
      · have z : ∫ x, h (x a ^ 2) * (x i * x j * x i * x l) ∂uniformSphere n = 0 := by
          apply M4_odd a h hh j
          intro x
          simp only [flipv, hij, Ne.symm hjl, ite_true, ite_false]; ring
        rw [z]; simp [hij, hjl, Ne.symm hij]
    · by_cases hil : i = l
      · subst hil
        by_cases hjk : j = k
        · subst hjk
          have e : ∫ x, h (x a ^ 2) * (x i * x j * x j * x i) ∂uniformSphere n = NN a h i j := by
            unfold NN; congr 1; funext x; ring
          rw [e]; simp [hij]
        · have z : ∫ x, h (x a ^ 2) * (x i * x j * x k * x i) ∂uniformSphere n = 0 := by
            apply M4_odd a h hh j
            intro x
            simp only [flipv, hij, Ne.symm hjk, ite_true, ite_false]; ring
          rw [z]; simp [hij, hik, hjk]
      · have z : ∫ x, h (x a ^ 2) * (x i * x j * x k * x l) ∂uniformSphere n = 0 := by
          apply M4_odd a h hh i
          intro x
          simp only [flipv, Ne.symm hij, Ne.symm hik, Ne.symm hil, ite_true, ite_false]; ring
        rw [z]; simp [hij, hik, hil]

end coord

section coordthm
variable {n : ℕ}

lemma sum_ite_const (p : Prop) [Decidable p] (f : Fin n → ℝ) :
    ∑ k, (if p then f k else 0) = if p then ∑ k, f k else 0 := by
  split_ifs <;> simp

theorem sphSymm_coord (hn : 2 ≤ n) (a : Fin n) (h : ℝ → ℝ) (hh : Continuous h)
    (h0 : ∀ s, 0 ≤ h s) (c : Fin n → ℝ) (hc : c a = 0) (S : Matrix (Fin n) (Fin n) ℝ)
    (hS : S.IsSymm) (hSa : S a a = 0) :
    ∫ x, h (x a ^ 2) * (∑ i, c i * x i + ∑ i, ∑ j, S i j * x i * x j) ^ 2 ∂uniformSphere n ≤
      ((∑ i, c i ^ 2) * ∫ x, h (x a ^ 2) * (1 - x a ^ 2) ∂uniformSphere n +
        (∑ i, ∑ j, S i j ^ 2) *
          max (2 * ∫ x, h (x a ^ 2) * (x a ^ 2 * (1 - x a ^ 2)) ∂uniformSphere n)
            (∫ x, h (x a ^ 2) * (1 - x a ^ 2) ^ 2 ∂uniformSphere n)) / ((n : ℝ) - 1) := by
  classical
  have hn1 : 1 ≤ n := by omega
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hint : ∀ {F : (Fin n → ℝ) → ℝ}, Continuous F → Integrable F (uniformSphere n) :=
    fun hF => BstLean.Part78.sph_int hn1 hF
  set I1 := ∫ x, h (x a ^ 2) * (1 - x a ^ 2) ∂uniformSphere n with hI1
  set I3 := ∫ x, h (x a ^ 2) * (x a ^ 2 * (1 - x a ^ 2)) ∂uniformSphere n with hI3
  set I4 := ∫ x, h (x a ^ 2) * (1 - x a ^ 2) ^ 2 ∂uniformSphere n with hI4
  set A := I1 / ((n : ℝ) - 1) with hA
  set A4 := I4 / ((n : ℝ) - 1) with hA4
  set B := (2 * I3) / ((n : ℝ) - 1) with hB
  set K := max B A4 with hK
  have hAK : A4 ≤ K := le_max_right _ _
  have hBK : B ≤ K := le_max_left _ _
  -- second moments
  have hM2 : ∀ i, i ≠ a → ∫ x, h (x a ^ 2) * x i ^ 2 ∂uniformSphere n = A := by
    intro i hi
    have := exch a hn (fun s => h (s ^ 2)) (by fun_prop) i hi
    rw [hA, hI1, ← this]; field_simp
  have hM2' : ∀ i, i ≠ a →
      ∫ x, h (x a ^ 2) * (1 - x a ^ 2) * x i ^ 2 ∂uniformSphere n = A4 := by
    intro i hi
    have := exch a hn (fun s => h (s ^ 2) * (1 - s ^ 2)) (by fun_prop) i hi
    have e : ∫ x, h (x a ^ 2) * (1 - x a ^ 2) * (1 - x a ^ 2) ∂uniformSphere n = I4 := by
      rw [hI4]; congr 1; funext x; ring
    rw [e] at this
    rw [hA4, ← this]; field_simp
  have hNsymm : ∀ i j, NN a h i j = NN a h j i := by
    intro i j; unfold NN; congr 1; funext x; ring
  have hNnn : ∀ i j, 0 ≤ NN a h i j := by
    intro i j; unfold NN
    exact integral_nonneg (fun x => mul_nonneg (h0 _) (by positivity))
  have hNa : ∀ j, j ≠ a → 2 * NN a h a j ≤ B := by
    intro j hj
    have e := exch a hn (fun s => h (s ^ 2) * s ^ 2) (by fun_prop) j hj
    have e1 : ∫ x, h (x a ^ 2) * x a ^ 2 * x j ^ 2 ∂uniformSphere n = NN a h a j := by
      unfold NN; congr 1; funext x; ring
    have e2 : ∫ x, h (x a ^ 2) * x a ^ 2 * (1 - x a ^ 2) ∂uniformSphere n = I3 := by
      rw [hI3]; congr 1; funext x; ring
    rw [e1, e2] at e
    rw [hB, ← e]
    apply le_of_eq; field_simp
  have hNij : ∀ i j, i ≠ j → i ≠ a → j ≠ a → 2 * NN a h i j ≤ A4 := by
    intro i j hij hi hj
    have le : NN a h i j ≤ ∫ x, (h (x a ^ 2) * (1 - x a ^ 2) * x i ^ 2
        + h (x a ^ 2) * (1 - x a ^ 2) * x j ^ 2) / 4 ∂uniformSphere n := by
      unfold NN
      apply integral_mono_ae (hint (by fun_prop)) (hint (by fun_prop))
      filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
      show h (x a ^ 2) * (x i ^ 2 * x j ^ 2) ≤ (h (x a ^ 2) * (1 - x a ^ 2) * x i ^ 2
        + h (x a ^ 2) * (1 - x a ^ 2) * x j ^ 2) / 4
      have h2 : x i ^ 2 + x j ^ 2 ≤ 1 - x a ^ 2 := by
        rw [← hx, ← Finset.sum_erase_eq_sub (Finset.mem_univ a),
          ← Finset.sum_pair (f := fun k => x k ^ 2) hij]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          simp only [Finset.mem_insert, Finset.mem_singleton] at hk
          rcases hk with rfl | rfl
          · exact Finset.mem_erase.mpr ⟨hi, Finset.mem_univ _⟩
          · exact Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩
        · intro k _ _; exact sq_nonneg _
      have hw := h0 (x a ^ 2)
      have key : x i ^ 2 * x j ^ 2 ≤ (1 - x a ^ 2) * (x i ^ 2 + x j ^ 2) / 4 := by
        nlinarith [sq_nonneg (x i ^ 2 - x j ^ 2), sq_nonneg (x i), sq_nonneg (x j),
          mul_nonneg (add_nonneg (sq_nonneg (x i)) (sq_nonneg (x j)))
            (sub_nonneg.mpr h2)]
      calc h (x a ^ 2) * (x i ^ 2 * x j ^ 2)
          ≤ h (x a ^ 2) * ((1 - x a ^ 2) * (x i ^ 2 + x j ^ 2) / 4) :=
            mul_le_mul_of_nonneg_left key hw
        _ = _ := by ring
    rw [integral_div, integral_add (hint (by fun_prop)) (hint (by fun_prop)), hM2' i hi,
      hM2' j hj] at le
    linarith
  have hNK : ∀ i j, i ≠ j → 2 * NN a h i j ≤ K := by
    intro i j hij
    by_cases hi : i = a
    · subst hi; exact (hNa j (Ne.symm hij)).trans hBK
    · by_cases hj : j = a
      · subst hj; rw [hNsymm]; exact (hNa i hi).trans hBK
      · exact (hNij i j hij hi hj).trans hAK
  have hrow : ∀ i, ∑ j, NN a h i j = ∫ x, h (x a ^ 2) * x i ^ 2 ∂uniformSphere n := by
    intro i
    unfold NN
    rw [← integral_finsetSum _ (fun j _ => hint (by fun_prop))]
    apply integral_congr_ae
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    show ∑ j, h (x a ^ 2) * (x i ^ 2 * x j ^ 2) = h (x a ^ 2) * x i ^ 2
    rw [← Finset.mul_sum, ← Finset.mul_sum, hx, mul_one]
  have hLL : ∫ x, h (x a ^ 2) * (∑ i, c i * x i) ^ 2 ∂uniformSphere n = (∑ i, c i ^ 2) * A := by
    have e : ∀ x : Fin n → ℝ, h (x a ^ 2) * (∑ i, c i * x i) ^ 2
        = ∑ i, ∑ j, c i * c j * (h (x a ^ 2) * (x i * x j)) := by
      intro x
      rw [pow_two (∑ i, c i * x i), Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp_rw [e]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
      (fun j _ => (hint (by fun_prop)).const_mul _))]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => (hint (by fun_prop)).const_mul _)]
    simp_rw [integral_const_mul]
    rw [Finset.sum_eq_single i
      (fun j _ hji => by rw [M2_odd a h hh i j (Ne.symm hji), mul_zero])
      (fun hni => absurd (Finset.mem_univ i) hni)]
    by_cases hi : i = a
    · rw [hi, hc]; ring
    · have := hM2 i hi
      have e2 : ∫ x, h (x a ^ 2) * (x i * x i) ∂uniformSphere n = A := by
        rw [← this]; congr 1; funext x; ring
      rw [e2]; ring
  have hLQ : ∫ x, h (x a ^ 2) * ((∑ i, c i * x i) * ∑ i, ∑ j, S i j * x i * x j)
      ∂uniformSphere n = 0 := by
    have h1 := BstLean.Part71.sh_sphere_neg (n := n)
      (fun x => h (x a ^ 2) * ((∑ i, c i * x i) * ∑ i, ∑ j, S i j * x i * x j))
    have h2 : ∀ x : Fin n → ℝ,
        h ((-x) a ^ 2) * ((∑ i, c i * (-x) i) * ∑ i, ∑ j, S i j * (-x) i * (-x) j)
          = -(h (x a ^ 2) * ((∑ i, c i * x i) * ∑ i, ∑ j, S i j * x i * x j)) := by
      intro x
      simp only [Pi.neg_apply, neg_sq, mul_neg, neg_mul, neg_neg, Finset.sum_neg_distrib]
    simp only [h2, integral_neg] at h1
    linarith
  have hQQ : ∫ x, h (x a ^ 2) * (∑ i, ∑ j, S i j * x i * x j) ^ 2 ∂uniformSphere n
      = (∑ i, ∑ k, S i i * S k k * NN a h i k) + (∑ i, ∑ j, S i j * S i j * NN a h i j)
        + (∑ i, ∑ j, S i j * S j i * NN a h i j) - 2 * ∑ i, S i i * S i i * NN a h i i := by
    have e : ∀ x : Fin n → ℝ, h (x a ^ 2) * (∑ i, ∑ j, S i j * x i * x j) ^ 2
        = ∑ i, ∑ j, ∑ k, ∑ l, S i j * S k l * (h (x a ^ 2) * (x i * x j * x k * x l)) := by
      intro x
      rw [pow_two (∑ i, ∑ j, S i j * x i * x j), Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ =>
        Finset.sum_congr rfl fun l _ => by ring
    have i4 : ∀ i j k l, Integrable
        (fun x : Fin n → ℝ => S i j * S k l * (h (x a ^ 2) * (x i * x j * x k * x l)))
        (uniformSphere n) := fun i j k l => (hint (by fun_prop)).const_mul _
    have step : ∫ x, h (x a ^ 2) * (∑ i, ∑ j, S i j * x i * x j) ^ 2 ∂uniformSphere n
        = ∑ i, ∑ j, ∑ k, ∑ l, S i j * S k l *
            ∫ x, h (x a ^ 2) * (x i * x j * x k * x l) ∂uniformSphere n := by
      simp_rw [e]
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
        integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => i4 i j k l)]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [integral_finsetSum _ (fun j _ =>
        integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => i4 i j k l)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ fun l _ => i4 i j k l)]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_finsetSum _ (fun l _ => i4 i j k l)]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [integral_const_mul]
    rw [step]
    simp_rw [M4_formula a h hh]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_zero,
      sum_ite_const, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hsplit : ∫ x, h (x a ^ 2) * (∑ i, c i * x i + ∑ i, ∑ j, S i j * x i * x j) ^ 2
        ∂uniformSphere n
      = ∫ x, h (x a ^ 2) * (∑ i, c i * x i) ^ 2 ∂uniformSphere n
        + 2 * ∫ x, h (x a ^ 2) * ((∑ i, c i * x i) * ∑ i, ∑ j, S i j * x i * x j)
            ∂uniformSphere n
        + ∫ x, h (x a ^ 2) * (∑ i, ∑ j, S i j * x i * x j) ^ 2 ∂uniformSphere n := by
    have e : ∀ x : Fin n → ℝ,
        h (x a ^ 2) * (∑ i, c i * x i + ∑ i, ∑ j, S i j * x i * x j) ^ 2
        = h (x a ^ 2) * (∑ i, c i * x i) ^ 2
          + 2 * (h (x a ^ 2) * ((∑ i, c i * x i) * ∑ i, ∑ j, S i j * x i * x j))
          + h (x a ^ 2) * (∑ i, ∑ j, S i j * x i * x j) ^ 2 := fun x => by ring
    simp_rw [e]
    have iL : Integrable (fun x : Fin n → ℝ => h (x a ^ 2) * (∑ i, c i * x i) ^ 2)
        (uniformSphere n) := hint (by fun_prop)
    have iLQ : Integrable (fun x : Fin n → ℝ =>
        h (x a ^ 2) * ((∑ i, c i * x i) * ∑ i, ∑ j, S i j * x i * x j))
        (uniformSphere n) := hint (by fun_prop)
    have iQ : Integrable (fun x : Fin n → ℝ => h (x a ^ 2) * (∑ i, ∑ j, S i j * x i * x j) ^ 2)
        (uniformSphere n) := hint (by fun_prop)
    refine (integral_add (iL.add (iLQ.const_mul 2)) iQ).trans ?_
    congr 1
    refine (integral_add iL (iLQ.const_mul 2)).trans ?_
    rw [integral_const_mul]
  have hR : ∀ i, S i i ^ 2 * ∑ k, (if i = a ∨ k = a then 0 else NN a h i k) = S i i ^ 2 * A4 := by
    intro i
    by_cases hi : i = a
    · rw [hi, hSa]; ring
    · congr 1
      have e1 : ∑ k, (if i = a ∨ k = a then 0 else NN a h i k)
          = ∑ k, NN a h i k - ∑ k, (if k = a then NN a h i k else 0) := by
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases hk : k = a <;> simp [hi, hk]
      rw [e1, Finset.sum_ite_eq' Finset.univ a]
      simp only [Finset.mem_univ, ite_true]
      rw [hrow, ← hM2' i hi]
      unfold NN
      rw [← integral_sub (hint (by fun_prop)) (hint (by fun_prop))]
      congr 1; funext x; ring
  have hT1 : ∑ i, ∑ k, S i i * S k k * NN a h i k ≤ ∑ i, S i i ^ 2 * A4 := by
    have s1 : ∑ i, ∑ k, S i i * S k k * NN a h i k
        ≤ ∑ i, ∑ k, (S i i ^ 2 / 2 + S k k ^ 2 / 2)
            * (if i = a ∨ k = a then 0 else NN a h i k) := by
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun k _ => ?_
      by_cases hi : i = a
      · simp [hi, hSa]
      · by_cases hk : k = a
        · simp [hk, hSa]
        · rw [show (if i = a ∨ k = a then 0 else NN a h i k) = NN a h i k from by simp [hi, hk]]
          apply mul_le_mul_of_nonneg_right _ (hNnn i k)
          nlinarith [sq_nonneg (S i i - S k k)]
    have s2 : ∑ i, ∑ k, (S i i ^ 2 / 2 + S k k ^ 2 / 2)
        * (if i = a ∨ k = a then 0 else NN a h i k) = ∑ i, S i i ^ 2 * A4 := by
      have p1 : ∑ i, ∑ k, S i i ^ 2 / 2 * (if i = a ∨ k = a then 0 else NN a h i k)
          = (∑ i, S i i ^ 2 * A4) / 2 := by
        rw [Finset.sum_div]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.mul_sum, ← hR i]; ring
      have p2 : ∑ i, ∑ k, S k k ^ 2 / 2 * (if i = a ∨ k = a then 0 else NN a h i k)
          = (∑ i, S i i ^ 2 * A4) / 2 := by
        rw [Finset.sum_comm, ← p1]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
        rw [hNsymm]; simp only [or_comm]
      simp_rw [add_mul, Finset.sum_add_distrib]
      rw [p1, p2]; ring
    linarith
  have hT : (∑ i, ∑ j, S i j * S i j * NN a h i j) + (∑ i, ∑ j, S i j * S j i * NN a h i j)
      - 2 * ∑ i, S i i * S i i * NN a h i i + ∑ i, S i i ^ 2 * A4 ≤ ∑ i, ∑ j, S i j ^ 2 * K := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i),
      ← Finset.add_sum_erase _ (fun j => S i j ^ 2 * K) (Finset.mem_univ i)]
    have hin : ∑ j ∈ Finset.univ.erase i,
        (S i j * S i j * NN a h i j + S i j * S j i * NN a h i j)
        ≤ ∑ j ∈ Finset.univ.erase i, S i j ^ 2 * K := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hji := Finset.ne_of_mem_erase hj
      have := hNK i j (Ne.symm hji)
      have hs : S j i = S i j := hS.apply i j
      rw [hs]
      nlinarith [sq_nonneg (S i j)]
    have hK0 : S i i ^ 2 * A4 ≤ S i i ^ 2 * K := mul_le_mul_of_nonneg_left hAK (sq_nonneg _)
    linarith
  have hmax : max (2 * I3) I4 / ((n : ℝ) - 1) = K := by
    rw [hK, hA4, hB, max_div_div_right hpos.le]
  have hfin : ∑ i, ∑ j, S i j ^ 2 * K = (∑ i, ∑ j, S i j ^ 2) * K := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i _ => (Finset.sum_mul _ _ _).symm
  rw [add_div, mul_div_assoc, mul_div_assoc, hmax, hsplit, hLL, hLQ, hQQ]
  linarith

end coordthm

section reduce
variable {n : ℕ}
open Matrix

/-- A Householder reflection with column `a` equal to the unit vector `v`. -/
lemma exists_orth_col (a : Fin n) (v : Fin n → ℝ) (hv : ∑ i, v i ^ 2 = 1) :
    ∃ O : Matrix (Fin n) (Fin n) ℝ, IsOrth O ∧ ∀ m, O m a = v m := by
  classical
  set u : Fin n → ℝ := fun l => v l - if l = a then 1 else 0 with hu
  set q : ℝ := ∑ l, u l ^ 2 with hq
  set t : ℝ := 2 / q with ht
  have hqv : q = 2 - 2 * v a := by
    have e : ∀ l, u l ^ 2 = v l ^ 2 - (if l = a then 2 * v l else 0) + (if l = a then 1 else 0) := by
      intro l; simp only [hu]; split_ifs <;> ring
    rw [hq]; simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hv]
    simp; ring
  have F1 : ∀ m, t * q * u m = 2 * u m := by
    intro m
    by_cases h0 : q = 0
    · have hm : u m ^ 2 ≤ q := Finset.single_le_sum (fun l _ => sq_nonneg (u l)) (Finset.mem_univ m)
      have : u m = 0 := by nlinarith [sq_nonneg (u m)]
      rw [this]; ring
    · rw [ht]; field_simp
  have hua : u a = - q / 2 := by rw [hqv]; simp [hu]; ring
  refine ⟨Matrix.of fun m l => (if m = l then 1 else 0) - t * u m * u l, ?_, ?_⟩
  · unfold IsOrth
    ext m k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Matrix.one_apply]
    have e : ∀ l, ((if l = m then (1 : ℝ) else 0) - t * u l * u m)
        * ((if l = k then 1 else 0) - t * u l * u k)
        = (if l = m then (if l = k then 1 else 0) else 0) - (if l = m then t * u l * u k else 0)
          - (if l = k then t * u l * u m else 0) + t * u m * u k * t * u l ^ 2 := by
      intro l; split_ifs <;> ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      ← hq]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have := F1 k
    linear_combination (t * u m) * this
  · intro m
    simp only [Matrix.of_apply]
    have := F1 m
    rw [hua]
    have e : (if m = a then (1 : ℝ) else 0) = v m - u m := by simp [hu]
    rw [e]
    linear_combination (1 / 2 : ℝ) * this

lemma dot_mulVec' (O : Matrix (Fin n) (Fin n) ℝ) (w y : Fin n → ℝ) :
    ∑ i, w i * (O.mulVec y) i = ∑ j, (O.transpose.mulVec w) j * y j := by
  have h : w ⬝ᵥ O.mulVec y = (O.transpose.mulVec w) ⬝ᵥ y := by
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  simpa [dotProduct] using h

lemma quad_dot (M : Matrix (Fin n) (Fin n) ℝ) (y : Fin n → ℝ) :
    ∑ i, ∑ j, M i j * y i * y j = y ⬝ᵥ M.mulVec y := by
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma quad_orth (O S : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    ∑ i, ∑ j, S i j * (O.mulVec x) i * (O.mulVec x) j
      = ∑ i, ∑ j, (O.transpose * S * O) i j * x i * x j := by
  rw [quad_dot, quad_dot, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose]

lemma frob_trace (M : Matrix (Fin n) (Fin n) ℝ) :
    ∑ i, ∑ j, M i j ^ 2 = Matrix.trace (M.transpose * M) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma frob_orth (O S : Matrix (Fin n) (Fin n) ℝ) (hO : IsOrth O) :
    ∑ i, ∑ j, (O.transpose * S * O) i j ^ 2 = ∑ i, ∑ j, S i j ^ 2 := by
  rw [frob_trace, frob_trace]
  have e : (O.transpose * S * O).transpose * (O.transpose * S * O)
      = O.transpose * (S.transpose * S * O) := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc O O.transpose, hO.mul_t, Matrix.one_mul]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, hO.mul_t, Matrix.mul_one]

end reduce

/-- **Symmetric sphere integrals, sharper form.** -/
theorem sphSymm2 (n : ℕ) (hn : 4 ≤ n) : SphSymm2 n := by
  classical
  intro v hv h hh h0 c hc S hS hSv
  let a : Fin n := ⟨0, by omega⟩
  obtain ⟨O, hO, hcol⟩ := exists_orth_col a v hv
  have hOtv : O.transpose.mulVec v = Pi.single a 1 := by
    funext j
    have := congrFun (congrFun (show O.transpose * O = 1 from hO) j) a
    simp only [Matrix.mul_apply, Matrix.transpose_apply, hcol, Matrix.one_apply] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Pi.single_apply]
    exact this
  have h1 : ∀ x : Fin n → ℝ, ∑ i, v i * (O.mulVec x) i = x a := by
    intro x; rw [dot_mulVec', hOtv]; simp [Pi.single_apply]
  have h2 : ∀ x : Fin n → ℝ,
      ∑ i, c i * (O.mulVec x) i = ∑ j, (O.transpose.mulVec c) j * x j :=
    fun x => dot_mulVec' O c x
  have h3 := quad_orth O S
  have hc' : (O.transpose.mulVec c) a = 0 := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, hcol]
    rw [← hc]; exact Finset.sum_congr rfl fun i _ => by ring
  have hS' : (O.transpose * S * O).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hS.eq,
      Matrix.mul_assoc]
  have hSa : (O.transpose * S * O) a a = 0 := by
    have := h3 (Pi.single a 1)
    have e : O.mulVec (Pi.single a 1) = v := by
      funext m; simp [Matrix.mulVec, dotProduct, Pi.single_apply, hcol]
    rw [e] at this
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true] at this
    rw [← this, ← hSv]
  have key := sphSymm_coord (by omega) a h hh h0 (O.transpose.mulVec c) hc'
    (O.transpose * S * O) hS' hSa
  have e1 := orth_integral O hO (fun x => h ((∑ i, v i * x i) ^ 2) *
    (∑ i, c i * x i + ∑ i, ∑ j, S i j * x i * x j) ^ 2) (by fun_prop)
  have e2 := orth_integral O hO (fun x => h ((∑ i, v i * x i) ^ 2) *
    (1 - (∑ i, v i * x i) ^ 2)) (by fun_prop)
  have e3 := orth_integral O hO (fun x => h ((∑ i, v i * x i) ^ 2) *
    ((∑ i, v i * x i) ^ 2 * (1 - (∑ i, v i * x i) ^ 2))) (by fun_prop)
  have e4 := orth_integral O hO (fun x => h ((∑ i, v i * x i) ^ 2) *
    (1 - (∑ i, v i * x i) ^ 2) ^ 2) (by fun_prop)
  simp only [h1, h2, h3] at e1 e2 e3 e4
  rw [← e1, ← e2, ← e3, ← e4, ← orth_sumsq hO.t c, ← frob_orth O S hO]
  exact key

/-- **Symmetric sphere integrals.** -/
theorem sphSymm (n : ℕ) (hn : 4 ≤ n) : SphSymm n := by
  intro v hv h hh h0 c hc S hS hSv
  have hn1 : 1 ≤ n := by omega
  have hpos : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (4 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hint : ∀ {F : (Fin n → ℝ) → ℝ}, Continuous F → Integrable F (uniformSphere n) :=
    fun hF => BstLean.Part78.sph_int hn1 hF
  refine (sphSymm2 n hn v hv h hh h0 c hc S hS hSv).trans ?_
  have hs : ∀ᵐ x ∂uniformSphere n, (∑ i, v i * x i) ^ 2 ≤ 1 := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v x
    rw [hx, show ∑ i, v i ^ 2 = 1 from hv] at this
    linarith
  have b1 : 2 * ∫ x, h ((∑ i, v i * x i) ^ 2) *
      ((∑ i, v i * x i) ^ 2 * (1 - (∑ i, v i * x i) ^ 2)) ∂uniformSphere n
      ≤ 1 / 2 * ∫ x, h ((∑ i, v i * x i) ^ 2) ∂uniformSphere n := by
    have le : ∫ x, h ((∑ i, v i * x i) ^ 2) *
        ((∑ i, v i * x i) ^ 2 * (1 - (∑ i, v i * x i) ^ 2)) ∂uniformSphere n
        ≤ ∫ x, h ((∑ i, v i * x i) ^ 2) * (1 / 4) ∂uniformSphere n := by
      apply integral_mono (hint (by fun_prop)) (hint (by fun_prop))
      intro x
      show h ((∑ i, v i * x i) ^ 2) * ((∑ i, v i * x i) ^ 2 * (1 - (∑ i, v i * x i) ^ 2))
        ≤ h ((∑ i, v i * x i) ^ 2) * (1 / 4)
      apply mul_le_mul_of_nonneg_left _ (h0 _)
      nlinarith [sq_nonneg ((∑ i, v i * x i) ^ 2 - 1 / 2)]
    rw [integral_mul_const] at le
    linarith
  have b2 : ∫ x, h ((∑ i, v i * x i) ^ 2) * (1 - (∑ i, v i * x i) ^ 2) ^ 2 ∂uniformSphere n
      ≤ ∫ x, h ((∑ i, v i * x i) ^ 2) * (1 - (∑ i, v i * x i) ^ 2) ∂uniformSphere n := by
    apply integral_mono_ae (hint (by fun_prop)) (hint (by fun_prop))
    filter_upwards [hs] with x hx
    show h ((∑ i, v i * x i) ^ 2) * (1 - (∑ i, v i * x i) ^ 2) ^ 2
      ≤ h ((∑ i, v i * x i) ^ 2) * (1 - (∑ i, v i * x i) ^ 2)
    apply mul_le_mul_of_nonneg_left _ (h0 _)
    nlinarith [sq_nonneg (∑ i, v i * x i)]
  apply div_le_div_of_nonneg_right _ hpos.le
  have hm := max_le (le_max_of_le_right b1) (le_max_of_le_left b2)
  have hF : (0 : ℝ) ≤ ∑ i, ∑ j, S i j ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg (S i j)
  have := mul_le_mul_of_nonneg_left hm hF
  linarith

end BstLean.Part80

#print axioms BstLean.Part80.sphSymm2
#print axioms BstLean.Part80.sphSymm
