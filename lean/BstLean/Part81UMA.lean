import BstLean.Part81Defs2
import BstLean.Part81K3
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Part 81 (UM), part A and B: moments of power sums on the sphere, and `q^k ≤ P_{k+1}`
-/

namespace BstLean.Part81.UM

open MeasureTheory
open BstLean.Part29 (uniformSphere gaussMom)
open BstLean.Part36 (monoVal gpm rhoD)
open BstLean.Part81

variable {n : ℕ}

lemma gaussMom_two_mul_succ (j : ℕ) :
    gaussMom (2 * (j + 1)) = (2 * (j : ℝ) + 1) * gaussMom (2 * j) := by
  have e1 : Even (2 * (j + 1)) := even_two_mul _
  have e2 : Even (2 * j) := even_two_mul _
  simp only [gaussMom, e1, e2, ite_true]
  rcases j with _ | j
  · simp
  · have h1 : 2 * (j + 1 + 1) - 1 = (2 * j + 1) + 2 := by omega
    have h2 : 2 * (j + 1) - 1 = 2 * j + 1 := by omega
    rw [h1, h2, Nat.doubleFactorial_add_two]
    push_cast; ring

lemma gaussMom_zero : gaussMom 0 = 1 := by simp [gaussMom]

lemma gaussMom_two : gaussMom 2 = 1 := by
  have : Even 2 := by decide
  simp [gaussMom, this]

lemma gaussMom_even_pos (j : ℕ) : 0 < gaussMom (2 * j) := by
  induction j with
  | zero => simp [gaussMom_zero]
  | succ j ih => rw [gaussMom_two_mul_succ]; positivity

lemma rhoD_succ (j : ℕ) : rhoD n (j + 1) = rhoD n j * ((n : ℝ) + 2 * j) := by
  unfold rhoD; rw [Finset.prod_range_succ]

lemma rhoD_pos (hn : 1 ≤ n) (r : ℕ) : 0 < rhoD n r := by
  induction r with
  | zero => simp [rhoD]
  | succ r ih => rw [rhoD_succ]; positivity

lemma muS_eq (hn : 1 ≤ n) (j : ℕ) : muS n j = n * gaussMom (2 * j) / rhoD n j := by
  induction j with
  | zero => simp [muS, gaussMom_zero, rhoD]
  | succ j ih =>
    have h1 := rhoD_pos hn j
    have h2 : (0 : ℝ) < (n : ℝ) + 2 * j := by positivity
    rw [muS, ih, gaussMom_two_mul_succ, rhoD_succ]
    field_simp

lemma int_pow_even (hn : 1 ≤ n) (i : Fin n) (j : ℕ) :
    ∫ x, x i ^ (2 * j) ∂uniformSphere n = gaussMom (2 * j) / rhoD n j := by
  rw [K3.mom_pow hn i (2 * j)]; simp

lemma int_sq_pow_ne (hn : 1 ≤ n) (i k : Fin n) (hik : k ≠ i) (j : ℕ) :
    ∫ x, x i ^ 2 * x k ^ (2 * j) ∂uniformSphere n = gaussMom (2 * j) / rhoD n (j + 1) := by
  classical
  have h := (K3.mom hn (Multiset.replicate 2 i + Multiset.replicate (2 * j) k)).2
  have e : ∀ x : Fin n → ℝ,
      monoVal x (Multiset.replicate 2 i + Multiset.replicate (2 * j) k) = x i ^ 2 * x k ^ (2 * j) := by
    intro x; simp [monoVal]; ring
  simp_rw [e] at h
  rw [h]
  have hg : gpm (Multiset.replicate 2 i + Multiset.replicate (2 * j) k) = gaussMom (2 * j) := by
    unfold gpm
    have : ∀ l : Fin n, gaussMom ((Multiset.replicate 2 i + Multiset.replicate (2 * j) k).count l)
        = (if l = i then gaussMom 2 else 1) * (if l = k then gaussMom (2 * j) else 1) := by
      intro l
      rw [Multiset.count_add, Multiset.count_replicate, Multiset.count_replicate]
      by_cases h1 : l = i
      · have h2 : l ≠ k := fun h => hik (h.symm.trans h1)
        simp [h1, Ne.symm hik, hik]
      · by_cases h2 : l = k
        · simp [h2, hik, Ne.symm hik]
        · simp [h1, h2, Ne.symm h1, Ne.symm h2, gaussMom_zero]
    simp_rw [this]
    rw [Finset.prod_mul_distrib]
    simp [gaussMom_two]
  have hc : (Multiset.card (Multiset.replicate 2 i + Multiset.replicate (2 * j) k)) / 2 = j + 1 := by
    simp; omega
  rw [hg, hc]

end BstLean.Part81.UM

namespace BstLean.Part81

open MeasureTheory
open BstLean.Part29 (uniformSphere gaussMom)
open BstLean.Part36 (rhoD)
open BstLean.Part81.UM

theorem int_powsum (n : ℕ) (hn : 1 ≤ n) (j : ℕ) :
    ∫ x, ∑ k, x k ^ (2 * j) ∂uniformSphere n = muS n j := by
  rw [integral_finsetSum _ (fun i _ => BstLean.Part78.sph_int hn (by fun_prop))]
  simp_rw [int_pow_even hn]
  rw [muS_eq hn]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem int_sq_powsum (n : ℕ) (hn : 1 ≤ n) (i : Fin n) (j : ℕ) :
    ∫ x, x i ^ 2 * ∑ k, x k ^ (2 * j) ∂uniformSphere n = muS n j / n := by
  classical
  have hn0 : (0 : ℝ) < n := by positivity
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => BstLean.Part78.sph_int hn (by fun_prop))]
  have hterm : ∀ k : Fin n, ∫ x, x i ^ 2 * x k ^ (2 * j) ∂uniformSphere n
      = gaussMom (2 * j) / rhoD n (j + 1) +
        (if k = i then (2 * (j : ℝ)) * gaussMom (2 * j) / rhoD n (j + 1) else 0) := by
    intro k
    by_cases hk : k = i
    · subst hk
      have e : ∀ x : Fin n → ℝ, x k ^ 2 * x k ^ (2 * j) = x k ^ (2 * (j + 1)) := by
        intro x; ring
      simp_rw [e]
      rw [int_pow_even hn, gaussMom_two_mul_succ]
      simp only [ite_true]
      ring
    · rw [int_sq_pow_ne hn i k hk]; simp [hk]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [muS_eq hn, rhoD_succ]
  have h1 := rhoD_pos hn j
  have h2 : (0 : ℝ) < (n : ℝ) + 2 * j := by positivity
  field_simp

theorem q_pow_le (n : ℕ) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) (k : ℕ) :
    (∑ i, x i ^ 4) ^ k ≤ ∑ i, x i ^ (2 * (k + 1)) := by
  have h := Real.pow_arith_mean_le_arith_mean_pow (Finset.univ : Finset (Fin n))
    (fun i => x i ^ 2) (fun i => x i ^ 2) (fun i _ => sq_nonneg _) hx (fun i _ => sq_nonneg _) k
  have e1 : ∑ i, x i ^ 2 * x i ^ 2 = ∑ i, x i ^ 4 := Finset.sum_congr rfl (fun i _ => by ring)
  have e2 : ∑ i, x i ^ 2 * (x i ^ 2) ^ k = ∑ i, x i ^ (2 * (k + 1)) :=
    Finset.sum_congr rfl (fun i _ => by ring)
  rw [e1, e2] at h; exact h

end BstLean.Part81
