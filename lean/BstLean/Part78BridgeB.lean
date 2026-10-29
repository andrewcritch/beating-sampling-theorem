import BstLean.Part78Defs
import BstLean.Part59Coef
import BstLean.Part59LemmaQ

/-!
# Part 78, wave 1: coefficient form = `(f₀, ℓ, H)` form (`CoefBridge`)
-/

namespace BstLean.Part78

open MeasureTheory
open BstLean.Part36 (CoefIdxD DD mapMD)
open BstLean.Part41 (Mono phiM colM contr trL frob IsSymmT Tens TSymm fval glue)
open BstLean.Part53 (aH g0 heatA fvA TF)
open BstLean.Part59 (polyEval TopNZ g0Q tensOf coefTens59 lemmaQ59)

variable {n : ℕ}

lemma sum_word0 (F : (Fin 0 → Fin n) → ℝ) : ∑ w, F w = F Fin.elim0 := by
  rw [Fintype.sum_unique]
  congr 1

lemma sum_word1 (F : (Fin 1 → Fin n) → ℝ) : ∑ w, F w = ∑ i, F (fun _ => i) := by
  rw [← (Equiv.funUnique (Fin 1) (Fin n)).symm.sum_comp]
  rfl

lemma sum_word2 (F : (Fin 2 → Fin n) → ℝ) : ∑ w, F w = ∑ i, ∑ j, F ![i, j] := by
  rw [← (finTwoArrowEquiv (Fin n)).symm.sum_comp, Fintype.sum_prod_type]
  rfl

lemma contr1 (A : (Fin 1 → Fin n) → ℝ) (y : Fin n → ℝ) :
    contr A (fun _ => y) = ∑ i, A (fun _ => i) * y i := by
  unfold contr
  rw [sum_word1]
  simp

lemma contr2 (A : (Fin 2 → Fin n) → ℝ) (y : Fin n → ℝ) :
    contr A (fun _ => y) = ∑ i, ∑ j, A ![i, j] * y i * y j := by
  unfold contr
  rw [sum_word2]
  simp [Fin.prod_univ_two, mul_assoc]

lemma filt (c : ℕ) (hc : c ≤ 2) (hc0 : 1 ≤ c) :
    (Finset.range 3).filter (fun i => c + 2 * i ≤ 2) = {0} := by
  ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega

lemma filt0 : (Finset.range 3).filter (fun i => 0 + 2 * i ≤ 2) = {0, 1} := by
  ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton]; omega

lemma heat_pos (v : ℝ) (A : Tens n) (c : ℕ) (hc : c ≤ 2) (hc0 : 1 ≤ c) (w : Fin c → Fin n) :
    heatA 2 v A c w = A c w := by
  unfold heatA
  rw [filt c hc hc0, Finset.sum_singleton]
  have hf : (c.factorial : ℝ) ≠ 0 := by positivity
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_zero, add_zero, one_mul]
  rw [div_self hf, one_mul]
  unfold trL
  rw [sum_word0]
  congr 1

lemma heat_zero (v : ℝ) (A : Tens n) (w : Fin 0 → Fin n) :
    heatA 2 v A 0 w = A 0 w + v * ∑ i, A 2 ![i, i] := by
  unfold heatA
  rw [filt0, Finset.sum_pair (by norm_num)]
  unfold trL
  rw [sum_word0, sum_word1]
  have e0 : (glue (0 + 2 * 0) 0 (Fin.elim0 : Fin 0 → Fin n)
      fun t => w ⟨t.1, by have := t.2; omega⟩) = w := by
    funext t; exact t.elim0
  have e1 : ∀ i : Fin n, (glue (0 + 2 * 1) 1 (fun _ : Fin 1 => i)
      fun t => w ⟨t.1, by have := t.2; omega⟩) = ![i, i] := by
    intro i; funext t; fin_cases t <;> simp [glue]
  rw [e0]
  simp only [e1]
  norm_num [Nat.factorial]

/-- **Coefficient form = `(f₀, ℓ, H)` form**, and the value of `g₀` at `(2,2)`. -/
theorem coefBridge (n : ℕ) : CoefBridge n := by
  classical
  intro c
  obtain ⟨hsym, hval, htop⟩ := coefTens59 n 2 c
  set T := tensOf 2 c with hT
  refine ⟨fun i => T 1 (fun _ => i), Matrix.of (fun i j => T 2 ![i, j]), ?_, ?_, ?_, ?_⟩
  · ext i j
    have h := hsym 2 (by norm_num) le_rfl (Equiv.swap 0 1) ![j, i]
    have e : (![j, i] ∘ (Equiv.swap (0 : Fin 2) 1)) = ![i, j] := by
      funext t; fin_cases t <;> simp
    rw [e] at h
    simpa using h.symm
  · intro y
    rw [← hval y]
    unfold fval qfun
    have hI : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
    rw [hI, Finset.sum_pair (by norm_num), contr1, contr2]
    simp [add_assoc]
  · intro h
    have := htop h
    unfold frob at this
    rw [sum_word2] at this
    simpa [frobH] using this
  · intro M
    rw [lemmaQ59 n 2 2 c M]
    unfold g0 fvA qfun trH
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, contr1, contr2]
    unfold contr
    rw [sum_word0]
    simp only [heat_zero, heat_pos _ _ 1 (by norm_num) le_rfl, heat_pos _ _ 2 le_rfl (by norm_num)]
    simp [TF, hT]
    ring

end BstLean.Part78

#print axioms BstLean.Part78.coefBridge
