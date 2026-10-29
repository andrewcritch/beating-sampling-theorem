import BstLean.Part82Defs
import BstLean.Part78BridgeB
import BstLean.Part59Coef
import BstLean.Part59LemmaQ

/-!
# Part 82, wave 1: coefficient form = `(f₀, ℓ, H, T)` form (`CoefBridge3`)

The heat operator at `k = 3` adds `v · tr A₂` to the constant part and `3v · tr A₃` to the linear
part. The parts of degree 2 and 3 do not change.
-/

namespace BstLean.Part82

open MeasureTheory
open BstLean.Part36 (CoefIdxD DD mapMD)
open BstLean.Part41 (Mono phiM colM contr trL frob IsSymmT Tens TSymm fval glue)
open BstLean.Part53 (aH g0 heatA fvA TF)
open BstLean.Part59 (polyEval TopNZ g0Q tensOf coefTens59 lemmaQ59)
open BstLean.Part78 (trH sum_word0 sum_word1 sum_word2 contr1 contr2)

variable {n : ℕ}

namespace BrAux

lemma sum_word3 (F : (Fin 3 → Fin n) → ℝ) : ∑ w, F w = ∑ i, ∑ j, ∑ k, F ![i, j, k] := by
  rw [← (Fin.consEquiv (fun _ : Fin 3 => Fin n)).sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [sum_word2]
  rfl

lemma contr3 (A : (Fin 3 → Fin n) → ℝ) (y : Fin n → ℝ) :
    contr A (fun _ => y) = ∑ i, ∑ j, ∑ k, A ![i, j, k] * y i * y j * y k := by
  unfold contr
  rw [sum_word3]
  simp [Fin.prod_univ_three, mul_assoc]

lemma filtHi (c : ℕ) (hc : c ≤ 3) (hc0 : 2 ≤ c) :
    (Finset.range 4).filter (fun i => c + 2 * i ≤ 3) = {0} := by
  ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]; omega

lemma filtLo (c : ℕ) (hc : c ≤ 1) :
    (Finset.range 4).filter (fun i => c + 2 * i ≤ 3) = {0, 1} := by
  ext i; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert,
    Finset.mem_singleton]; omega

lemma heat_hi (v : ℝ) (A : Tens n) (c : ℕ) (hc : c ≤ 3) (hc0 : 2 ≤ c) (w : Fin c → Fin n) :
    heatA 3 v A c w = A c w := by
  unfold heatA
  rw [filtHi c hc hc0, Finset.sum_singleton]
  have hf : (c.factorial : ℝ) ≠ 0 := by positivity
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_zero, add_zero, one_mul]
  rw [div_self hf, one_mul]
  unfold trL
  rw [sum_word0]
  congr 1

lemma heat_zero (v : ℝ) (A : Tens n) (w : Fin 0 → Fin n) :
    heatA 3 v A 0 w = A 0 w + v * ∑ i, A 2 ![i, i] := by
  unfold heatA
  rw [filtLo 0 (by norm_num), Finset.sum_pair (by norm_num)]
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

lemma heat_one (v : ℝ) (A : Tens n) (w : Fin 1 → Fin n) :
    heatA 3 v A 1 w = A 1 w + 3 * v * ∑ i, A 3 ![i, i, w 0] := by
  unfold heatA
  rw [filtLo 1 le_rfl, Finset.sum_pair (by norm_num)]
  unfold trL
  rw [sum_word0, sum_word1]
  have e0 : (glue (1 + 2 * 0) 0 (Fin.elim0 : Fin 0 → Fin n)
      fun t => w ⟨t.1, by have := t.2; omega⟩) = w := by
    funext t; fin_cases t; simp [glue]
  have e1 : ∀ i : Fin n, (glue (1 + 2 * 1) 1 (fun _ : Fin 1 => i)
      fun t => w ⟨t.1, by have := t.2; omega⟩) = ![i, i, w 0] := by
    intro i; funext t; fin_cases t <;> simp [glue]
  rw [e0]
  simp only [e1]
  norm_num [Nat.factorial]
  left
  ring

end BrAux

open BrAux in
/-- **Coefficient form = `(f₀, ℓ, H, T)` form**, and the value of `g₀` at `(3,3)`. -/
theorem coefBridge3 (n : ℕ) : CoefBridge3 n := by
  classical
  intro c
  obtain ⟨hsym, hval, htop⟩ := coefTens59 n 3 c
  set T := tensOf 3 c with hT
  have s01 : ∀ i j k : Fin n, T 3 ![i, j, k] = T 3 ![j, i, k] := by
    intro i j k
    have h := hsym 3 (by norm_num) le_rfl (Equiv.swap 0 1) ![j, i, k]
    have e : (![j, i, k] ∘ (Equiv.swap (0 : Fin 3) 1)) = ![i, j, k] := by
      funext t; fin_cases t <;> simp [Equiv.swap_apply_of_ne_of_ne]
    rw [e] at h
    exact h
  have s12 : ∀ i j k : Fin n, T 3 ![i, j, k] = T 3 ![i, k, j] := by
    intro i j k
    have h := hsym 3 (by norm_num) le_rfl (Equiv.swap 1 2) ![i, k, j]
    have e : (![i, k, j] ∘ (Equiv.swap (1 : Fin 3) 2)) = ![i, j, k] := by
      funext t; fin_cases t <;> simp [Equiv.swap_apply_of_ne_of_ne]
    rw [e] at h
    exact h
  refine ⟨fun i => T 1 (fun _ => i), Matrix.of (fun i j => T 2 ![i, j]),
    fun i j k => T 3 ![i, j, k], ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    have h := hsym 2 (by norm_num) (by norm_num) (Equiv.swap 0 1) ![j, i]
    have e : (![j, i] ∘ (Equiv.swap (0 : Fin 2) 1)) = ![i, j] := by
      funext t; fin_cases t <;> simp
    rw [e] at h
    simpa using h.symm
  · intro i j k
    exact ⟨s01 i j k, s12 i j k⟩
  · intro y
    rw [← hval y]
    unfold fval cfun
    have hI : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
    rw [hI, Finset.sum_insert (by decide), Finset.sum_pair (by norm_num), contr1, contr2, contr3]
    simp [add_assoc]
  · intro h
    have := htop h
    unfold frob at this
    rw [sum_word3] at this
    simpa [frobT] using this
  · intro M
    rw [lemmaQ59 n 3 3 c M]
    unfold g0 fvA cfun trH trT
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
      contr1, contr2, contr3]
    unfold contr
    rw [sum_word0]
    simp only [heat_zero, heat_one, heat_hi _ _ 2 (by norm_num) le_rfl,
      heat_hi _ _ 3 le_rfl (by norm_num)]
    have hK : ∀ x : Fin n, ∑ i, 3 * aH n 3 * tensOf 3 c 3 ![i, i, x] * colM M default x =
        aH n 3 * ∑ i, 3 * (tensOf 3 c 3 ![x, i, i] * colM M default x) := by
      intro x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have e : tensOf 3 c 3 ![i, i, x] = tensOf 3 c 3 ![x, i, i] := (s12 i i x).trans (s01 i x i)
      rw [e]
      ring
    simp [TF, hT, add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul]
    simp only [hK, ← Finset.mul_sum]
    ring

end BstLean.Part82

#print axioms BstLean.Part82.coefBridge3
