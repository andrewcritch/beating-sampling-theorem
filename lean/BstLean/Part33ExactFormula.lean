import BstLean.Part29ExactFormula
import BstLean.Part29GaussProd

/-!
# Part 33, layer L2: the exact formula for `B` at `(3,2)`

`proofs/option-m/21-uniform-coefficients-cubic.tex`, Lemma 1.1 (`delegations/answers/omU3-opus-prover.md` §1), used by the
exact branch of parts 30–33. For `m(x)_k = c_k + (Lx)_k + xᵀQ_kx` (each `Q_k` symmetric) and a cubic
`f(y) = f₀ + bᵀy + F[y,y] + T[y,y,y]` (`F`, `T` symmetric), and a law whose products of at most six coordinates have the
uniform-sphere moments (`SphereProd6`, a hypothesis; `Part29Sphere.lean` proves the general formula for the sphere),
`B = ∫ f(m(x))` is an explicit polynomial in the coefficients.
-/

namespace BstLean.Part33

open MeasureTheory BstLean.Part29

variable {n : ℕ}

/-- Products of at most six coordinates integrate to `(∏ᵢ gaussMom (count i)) / ∏_{j < r/2} (n + 2j)`; with integrability. -/
structure SphereProd6 (n : ℕ) (μ : Measure (Fin n → ℝ)) : Prop where
  integ : ∀ r, r ≤ 6 → ∀ τ : Fin r → Fin n, Integrable (fun x : Fin n → ℝ => ∏ s, x (τ s)) μ
  mom : ∀ r, r ≤ 6 → ∀ τ : Fin r → Fin n,
    ∫ x, ∏ s, x (τ s) ∂μ =
      (∏ i, gaussMom (Finset.univ.filter fun s => τ s = i).card) / ∏ j ∈ Finset.range (r / 2), ((n : ℝ) + 2 * j)

/-- The cubic function `f`. -/
def funF3 (f0 : ℝ) (b : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (T : Fin n → Fin n → Fin n → ℝ)
    (y : Fin n → ℝ) : ℝ :=
  f0 + ∑ k, b k * y k + ∑ k, ∑ l, F k l * y k * y l + ∑ k, ∑ l, ∑ p, T k l p * y k * y l * y p

/-- `T` is fully symmetric. -/
def TSymm (T : Fin n → Fin n → Fin n → ℝ) : Prop :=
  ∀ a b c, T a b c = T b a c ∧ T a b c = T a c b

private lemma odd_product_moment (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (r : ℕ) (hr : r ≤ 6) (ho : Odd r) (τ : Fin r → Fin n) :
    (∫ x, ∏ s, x (τ s) ∂μ) = 0 := by
  classical
  have hcount : (∑ i : Fin n, (Finset.univ.filter fun s => τ s = i).card) = r := by
    simpa using (Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ) (t := Finset.univ) (f := τ) (by simp)).symm
  have hex : ∃ i : Fin n, ¬ Even (Finset.univ.filter fun s => τ s = i).card := by
    by_contra h
    push Not at h
    have he : Even (∑ i : Fin n, (Finset.univ.filter fun s => τ s = i).card) :=
      Finset.even_sum _ (fun i _ => h i)
    rw [hcount] at he
    exact (Nat.not_even_iff_odd.mpr ho) he
  obtain ⟨i, hi⟩ := hex
  rw [hμ.mom r hr τ]
  have hz : (∏ i, gaussMom (Finset.univ.filter fun s => τ s = i).card) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [gaussMom, hi]
  rw [hz, zero_div]

private lemma coord_integrable (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (i : Fin n) : Integrable (fun x => x i) μ := by
  simpa using hμ.integ 1 (by omega) (fun _ => i)

private lemma coord_moment (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (i : Fin n) : (∫ x, x i ∂μ) = 0 := by
  simpa using odd_product_moment μ hμ 1 (by omega) (by decide) (fun _ => i)

private lemma pair_integrable (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (i j : Fin n) : Integrable (fun x => x i * x j) μ := by
  simpa [Fin.prod_univ_succ] using hμ.integ 2 (by omega) ![i, j]

private lemma pair_moment (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (i j : Fin n) : (∫ x, x i * x j ∂μ) = if i = j then 1 / (n : ℝ) else 0 := by
  classical
  have hm := hμ.mom 2 (by omega) ![i, j]
  simp only [Fin.prod_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.prod_univ_zero, mul_one] at hm
  rw [hm]
  by_cases hij : i = j
  · subst j
    have hp : (∏ k : Fin n, gaussMom (Finset.univ.filter
        fun s : Fin 2 => (![i, i] : Fin 2 → Fin n) s = k).card) = 1 := by
      have hc (k : Fin n) : (Finset.univ.filter
          fun s : Fin 2 => (![i, i] : Fin 2 → Fin n) s = k).card =
          if i = k then 2 else 0 := by
        by_cases hik : i = k <;> simp [Fin.card_filter_univ_succ', hik]
      simp_rw [hc]
      have hg0 : gaussMom 0 = 1 := by norm_num [gaussMom]
      have hg2 : gaussMom 2 = 1 := by norm_num [gaussMom, Nat.doubleFactorial]
      simp [apply_ite, hg0, hg2]
    simp [hp]
  · have hc : (Finset.univ.filter
        fun s : Fin 2 => (![i, j] : Fin 2 → Fin n) s = i).card = 1 := by
      simp [Fin.card_filter_univ_succ',
        Ne.symm hij]
    have hp : (∏ k : Fin n, gaussMom (Finset.univ.filter
        fun s : Fin 2 => (![i, j] : Fin 2 → Fin n) s = k).card) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [hc]
      norm_num [gaussMom]
    simp [hp, hij]

private lemma moment_numerator_support (r : ℕ) (τ : Fin r → Fin n) :
    (∏ i, gaussMom (Finset.univ.filter fun s => τ s = i).card) =
      ∏ i ∈ Finset.univ.image τ, gaussMom (Finset.univ.filter fun s => τ s = i).card := by
  classical
  symm
  apply Finset.prod_subset (Finset.subset_univ _)
  intro i _ hi
  have hc : (Finset.univ.filter fun s => τ s = i) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro s hs
    exact hi (Finset.mem_image.mpr ⟨s, Finset.mem_univ s, (Finset.mem_filter.mp hs).2⟩)
  norm_num [hc, gaussMom]

set_option maxHeartbeats 2000000 in
private lemma four_moment (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (i j k l : Fin n) : (∫ x, x i * x j * x k * x l ∂μ) =
      ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0)) / ((n : ℝ) * (n + 2)) := by
  classical
  have hm := hμ.mom 4 (by omega) ![i, j, k, l]
  have hs : Finset.univ.image (![i, j, k, l] : Fin 4 → Fin n) = {i, j, k, l} := by
    ext a
    simp [Fin.exists_fin_succ, eq_comm]
  rw [moment_numerator_support, hs] at hm
  have hc (a : Fin n) : (Finset.univ.filter
      fun s : Fin 4 => (![i, j, k, l] : Fin 4 → Fin n) s = a).card =
      (if i = a then 1 else 0) + (if j = a then 1 else 0) +
        (if k = a then 1 else 0) + (if l = a then 1 else 0) := by
    by_cases hia : i = a <;> by_cases hja : j = a <;>
      by_cases hka : k = a <;> by_cases hla : l = a <;>
      simp [Fin.card_filter_univ_succ', hia, hja, hka, hla]
  simp_rw [hc] at hm
  have hp : (∏ a ∈ ({i, j, k, l} : Finset (Fin n)), gaussMom
      ((if i = a then 1 else 0) + (if j = a then 1 else 0) +
        (if k = a then 1 else 0) + (if l = a then 1 else 0))) =
      (if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
        (if i = l ∧ j = k then 1 else 0) := by
    clear hm hc hs hμ
    by_cases hij : i = j <;> by_cases hik : i = k <;> by_cases hil : i = l <;>
      by_cases hjk : j = k <;> by_cases hjl : j = l <;> by_cases hkl : k = l <;>
      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
  rw [hp] at hm
  simpa [Fin.prod_univ_succ, Finset.prod_range_succ, mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using hm


set_option linter.unusedSimpArgs false in
set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
set_option linter.unnecessarySeqFocus false in
set_option maxHeartbeats 8000000 in
private lemma six_numerator (i j k l p q : Fin n) :
    (∏ a ∈ ({i, j, k, l, p, q} : Finset (Fin n)), gaussMom
      ((if i = a then 1 else 0) + (if j = a then 1 else 0) + (if k = a then 1 else 0) + (if l = a then 1 else 0) + (if p = a then 1 else 0) + (if q = a then 1 else 0))) =
      (if i = j ∧ k = l ∧ p = q then 1 else 0) +
      (if i = j ∧ k = p ∧ l = q then 1 else 0) +
      (if i = j ∧ k = q ∧ l = p then 1 else 0) +
      (if i = k ∧ j = l ∧ p = q then 1 else 0) +
      (if i = k ∧ j = p ∧ l = q then 1 else 0) +
      (if i = k ∧ j = q ∧ l = p then 1 else 0) +
      (if i = l ∧ j = k ∧ p = q then 1 else 0) +
      (if i = l ∧ j = p ∧ k = q then 1 else 0) +
      (if i = l ∧ j = q ∧ k = p then 1 else 0) +
      (if i = p ∧ j = k ∧ l = q then 1 else 0) +
      (if i = p ∧ j = l ∧ k = q then 1 else 0) +
      (if i = p ∧ j = q ∧ k = l then 1 else 0) +
      (if i = q ∧ j = k ∧ l = p then 1 else 0) +
      (if i = q ∧ j = l ∧ k = p then 1 else 0) +
      (if i = q ∧ j = p ∧ k = l then 1 else 0) := by
  classical
  by_cases hji : j = i
  · subst j
    by_cases hki : k = i
    · subst k
      by_cases hli : l = i
      · subst l
        by_cases hpi : p = i
        · subst p
          by_cases hqi : q = i
          · subst q
            simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
          ·
            simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
        ·
          by_cases hqi : q = i
          · subst q
            simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
          ·
            by_cases hqp : q = p
            · subst q
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
      ·
        by_cases hpi : p = i
        · subst p
          by_cases hqi : q = i
          · subst q
            simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
          ·
            by_cases hql : q = l
            · subst q
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
        ·
          by_cases hpl : p = l
          · subst p
            by_cases hqi : q = i
            · subst q
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hql : q = l
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
          ·
            by_cases hqi : q = i
            · subst q
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hql : q = l
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqp : q = p
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
    ·
      by_cases hli : l = i
      · subst l
        by_cases hpi : p = i
        · subst p
          by_cases hqi : q = i
          · subst q
            simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
          ·
            by_cases hqk : q = k
            · subst q
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
        ·
          by_cases hpk : p = k
          · subst p
            by_cases hqi : q = i
            · subst q
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hqk : q = k
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
          ·
            by_cases hqi : q = i
            · subst q
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hqk : q = k
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqp : q = p
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
      ·
        by_cases hlk : l = k
        · subst l
          by_cases hpi : p = i
          · subst p
            by_cases hqi : q = i
            · subst q
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hqk : q = k
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
          ·
            by_cases hpk : p = k
            · subst p
              by_cases hqi : q = i
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqk : q = k
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hqi : q = i
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqk : q = k
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqp : q = p
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
        ·
          by_cases hpi : p = i
          · subst p
            by_cases hqi : q = i
            · subst q
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hqk : q = k
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hql : q = l
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
          ·
            by_cases hpk : p = k
            · subst p
              by_cases hqi : q = i
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqk : q = k
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hql : q = l
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hpl : p = l
              · subst p
                by_cases hqi : q = i
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqk : q = k
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hql : q = l
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqi : q = i
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqk : q = k
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hql : q = l
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      by_cases hqp : q = p
                      · subst q
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                      ·
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
  ·
    by_cases hki : k = i
    · subst k
      by_cases hli : l = i
      · subst l
        by_cases hpi : p = i
        · subst p
          by_cases hqi : q = i
          · subst q
            simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
          ·
            by_cases hqj : q = j
            · subst q
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
        ·
          by_cases hpj : p = j
          · subst p
            by_cases hqi : q = i
            · subst q
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hqj : q = j
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
          ·
            by_cases hqi : q = i
            · subst q
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hqj : q = j
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqp : q = p
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
      ·
        by_cases hlj : l = j
        · subst l
          by_cases hpi : p = i
          · subst p
            by_cases hqi : q = i
            · subst q
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hqj : q = j
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
          ·
            by_cases hpj : p = j
            · subst p
              by_cases hqi : q = i
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqj : q = j
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hqi : q = i
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqj : q = j
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqp : q = p
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
        ·
          by_cases hpi : p = i
          · subst p
            by_cases hqi : q = i
            · subst q
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hqj : q = j
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hql : q = l
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
          ·
            by_cases hpj : p = j
            · subst p
              by_cases hqi : q = i
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqj : q = j
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hql : q = l
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hpl : p = l
              · subst p
                by_cases hqi : q = i
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqj : q = j
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hql : q = l
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqi : q = i
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqj : q = j
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hql : q = l
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      by_cases hqp : q = p
                      · subst q
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                      ·
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
    ·
      by_cases hkj : k = j
      · subst k
        by_cases hli : l = i
        · subst l
          by_cases hpi : p = i
          · subst p
            by_cases hqi : q = i
            · subst q
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hqj : q = j
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
          ·
            by_cases hpj : p = j
            · subst p
              by_cases hqi : q = i
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqj : q = j
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hqi : q = i
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqj : q = j
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqp : q = p
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
        ·
          by_cases hlj : l = j
          · subst l
            by_cases hpi : p = i
            · subst p
              by_cases hqi : q = i
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqj : q = j
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hpj : p = j
              · subst p
                by_cases hqi : q = i
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqj : q = j
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqi : q = i
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqj : q = j
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hqp : q = p
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
          ·
            by_cases hpi : p = i
            · subst p
              by_cases hqi : q = i
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqj : q = j
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hql : q = l
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hpj : p = j
              · subst p
                by_cases hqi : q = i
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqj : q = j
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hql : q = l
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hpl : p = l
                · subst p
                  by_cases hqi : q = i
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hqj : q = j
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      by_cases hql : q = l
                      · subst q
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                      ·
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqi : q = i
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hqj : q = j
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      by_cases hql : q = l
                      · subst q
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                      ·
                        by_cases hqp : q = p
                        · subst q
                          simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                        ·
                          simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
      ·
        by_cases hli : l = i
        · subst l
          by_cases hpi : p = i
          · subst p
            by_cases hqi : q = i
            · subst q
              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hqj : q = j
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqk : q = k
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
          ·
            by_cases hpj : p = j
            · subst p
              by_cases hqi : q = i
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqj : q = j
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqk : q = k
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hpk : p = k
              · subst p
                by_cases hqi : q = i
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqj : q = j
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hqk : q = k
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqi : q = i
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqj : q = j
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hqk : q = k
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      by_cases hqp : q = p
                      · subst q
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                      ·
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
        ·
          by_cases hlj : l = j
          · subst l
            by_cases hpi : p = i
            · subst p
              by_cases hqi : q = i
              · subst q
                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hqj : q = j
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqk : q = k
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hpj : p = j
              · subst p
                by_cases hqi : q = i
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqj : q = j
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hqk : q = k
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hpk : p = k
                · subst p
                  by_cases hqi : q = i
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hqj : q = j
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      by_cases hqk : q = k
                      · subst q
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                      ·
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqi : q = i
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hqj : q = j
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      by_cases hqk : q = k
                      · subst q
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                      ·
                        by_cases hqp : q = p
                        · subst q
                          simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                        ·
                          simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
          ·
            by_cases hlk : l = k
            · subst l
              by_cases hpi : p = i
              · subst p
                by_cases hqi : q = i
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqj : q = j
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hqk : q = k
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hpj : p = j
                · subst p
                  by_cases hqi : q = i
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hqj : q = j
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      by_cases hqk : q = k
                      · subst q
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                      ·
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hpk : p = k
                  · subst p
                    by_cases hqi : q = i
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      by_cases hqj : q = j
                      · subst q
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                      ·
                        by_cases hqk : q = k
                        · subst q
                          simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                        ·
                          simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hqi : q = i
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      by_cases hqj : q = j
                      · subst q
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                      ·
                        by_cases hqk : q = k
                        · subst q
                          simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                        ·
                          by_cases hqp : q = p
                          · subst q
                            simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                          ·
                            simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
            ·
              by_cases hpi : p = i
              · subst p
                by_cases hqi : q = i
                · subst q
                  simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hqj : q = j
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hqk : q = k
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      by_cases hql : q = l
                      · subst q
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                      ·
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
              ·
                by_cases hpj : p = j
                · subst p
                  by_cases hqi : q = i
                  · subst q
                    simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hqj : q = j
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      by_cases hqk : q = k
                      · subst q
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                      ·
                        by_cases hql : q = l
                        · subst q
                          simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                        ·
                          simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                ·
                  by_cases hpk : p = k
                  · subst p
                    by_cases hqi : q = i
                    · subst q
                      simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      by_cases hqj : q = j
                      · subst q
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                      ·
                        by_cases hqk : q = k
                        · subst q
                          simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                        ·
                          by_cases hql : q = l
                          · subst q
                            simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                          ·
                            simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                  ·
                    by_cases hpl : p = l
                    · subst p
                      by_cases hqi : q = i
                      · subst q
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                      ·
                        by_cases hqj : q = j
                        · subst q
                          simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                        ·
                          by_cases hqk : q = k
                          · subst q
                            simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                          ·
                            by_cases hql : q = l
                            · subst q
                              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                            ·
                              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                    ·
                      by_cases hqi : q = i
                      · subst q
                        simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                      ·
                        by_cases hqj : q = j
                        · subst q
                          simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                        ·
                          by_cases hqk : q = k
                          · subst q
                            simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                          ·
                            by_cases hql : q = l
                            · subst q
                              simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                            ·
                              by_cases hqp : q = p
                              · subst q
                                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num
                              ·
                                simp_all [Finset.prod_insert, gaussMom, Nat.doubleFactorial, eq_comm] <;> norm_num

set_option maxHeartbeats 2000000 in
private lemma six_moment (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (i j k l p q : Fin n) : (∫ x, x i * x j * x k * x l * x p * x q ∂μ) =
    ((if i = j ∧ k = l ∧ p = q then 1 else 0) +
      (if i = j ∧ k = p ∧ l = q then 1 else 0) +
      (if i = j ∧ k = q ∧ l = p then 1 else 0) +
      (if i = k ∧ j = l ∧ p = q then 1 else 0) +
      (if i = k ∧ j = p ∧ l = q then 1 else 0) +
      (if i = k ∧ j = q ∧ l = p then 1 else 0) +
      (if i = l ∧ j = k ∧ p = q then 1 else 0) +
      (if i = l ∧ j = p ∧ k = q then 1 else 0) +
      (if i = l ∧ j = q ∧ k = p then 1 else 0) +
      (if i = p ∧ j = k ∧ l = q then 1 else 0) +
      (if i = p ∧ j = l ∧ k = q then 1 else 0) +
      (if i = p ∧ j = q ∧ k = l then 1 else 0) +
      (if i = q ∧ j = k ∧ l = p then 1 else 0) +
      (if i = q ∧ j = l ∧ k = p then 1 else 0) +
      (if i = q ∧ j = p ∧ k = l then 1 else 0)) / ((n : ℝ) * (n + 2) * (n + 4)) := by
  classical
  have hm := hμ.mom 6 (by omega) ![i, j, k, l, p, q]
  have hs : Finset.univ.image (![i, j, k, l, p, q] : Fin 6 → Fin n) =
      {i, j, k, l, p, q} := by
    ext a
    simp [Fin.exists_fin_succ, eq_comm]
  rw [moment_numerator_support, hs] at hm
  have hc (a : Fin n) : (Finset.univ.filter
      fun s : Fin 6 => (![i, j, k, l, p, q] : Fin 6 → Fin n) s = a).card =
      (if i = a then 1 else 0) + (if j = a then 1 else 0) + (if k = a then 1 else 0) + (if l = a then 1 else 0) + (if p = a then 1 else 0) + (if q = a then 1 else 0) := by
    by_cases hia : i = a <;> by_cases hja : j = a <;>
      by_cases hka : k = a <;> by_cases hla : l = a <;>
      by_cases hpa : p = a <;> by_cases hqa : q = a <;>
      simp [Fin.card_filter_univ_succ', hia, hja, hka, hla, hpa, hqa]
  simp_rw [hc] at hm
  rw [six_numerator] at hm
  simpa [Fin.prod_univ_succ, Finset.prod_range_succ, mul_assoc, show (2 : ℝ) * 2 = 4 by norm_num] using hm


private lemma triple_integrable (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (i j k : Fin n) : Integrable (fun x => x i * x j * x k) μ := by
  simpa [Fin.prod_univ_succ, mul_assoc] using hμ.integ 3 (by omega) ![i, j, k]

private lemma four_integrable (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (i j k l : Fin n) : Integrable (fun x => x i * x j * x k * x l) μ := by
  simpa [Fin.prod_univ_succ, mul_assoc] using hμ.integ 4 (by omega) ![i, j, k, l]

private lemma triple_moment (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (i j k : Fin n) : (∫ x, x i * x j * x k ∂μ) = 0 := by
  simpa [Fin.prod_univ_succ, mul_assoc] using
    odd_product_moment μ hμ 3 (by omega) (by decide) ![i, j, k]

private lemma five_integrable (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (i j k l p : Fin n) : Integrable (fun x => x i * x j * x k * x l * x p) μ := by
  simpa [Fin.prod_univ_succ, mul_assoc] using hμ.integ 5 (by omega) ![i, j, k, l, p]

private lemma five_moment (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (i j k l p : Fin n) : (∫ x, x i * x j * x k * x l * x p ∂μ) = 0 := by
  simpa [Fin.prod_univ_succ, mul_assoc] using
    odd_product_moment μ hμ 5 (by omega) (by decide) ![i, j, k, l, p]

private lemma six_integrable (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (i j k l p q : Fin n) :
    Integrable (fun x => x i * x j * x k * x l * x p * x q) μ := by
  simpa [Fin.prod_univ_succ, mul_assoc] using hμ.integ 6 (by omega) ![i, j, k, l, p, q]

private lemma sphereMoments_of_prod6 (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ) :
    SphereMoments n μ where
  int1 := coord_integrable μ hμ
  int2 := pair_integrable μ hμ
  int3 := triple_integrable μ hμ
  int4 := four_integrable μ hμ
  m1 := coord_moment μ hμ
  m2 := pair_moment μ hμ
  m3 := triple_moment μ hμ
  m4 := four_moment μ hμ

local notation "lin" => (fun (a : Fin n → ℝ) (x : Fin n → ℝ) => ∑ i, a i * x i)
local notation "quad" => (fun (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) =>
  ∑ i, ∑ j, A i j * (x i * x j))

private lemma integrable_lin (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (a : Fin n → ℝ) : Integrable (lin a) μ :=
  integrable_finsetSum _ (fun i _ => (h.int1 i).const_mul (a i))

private lemma integrable_quad (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (A : Matrix (Fin n) (Fin n) ℝ) : Integrable (quad A) μ :=
  integrable_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (h.int2 i j).const_mul (A i j)))

private lemma integrable_ll (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (a b : Fin n → ℝ) : Integrable (fun x => lin a x * lin b x) μ := by
  dsimp only
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  convert (h.int2 i j).const_mul (a i * b j) using 1
  funext x
  ring

private lemma integrable_lq (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (a : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => lin a x * quad A x) μ := by
  dsimp only
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro k _
  convert (h.int3 i j k).const_mul (a i * A j k) using 1
  funext x
  ring

private lemma integrable_qq (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (A B : Matrix (Fin n) (Fin n) ℝ) :
    Integrable (fun x => quad A x * quad B x) μ := by
  dsimp only
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro l _
  convert (h.int4 i j k l).const_mul (A i j * B k l) using 1
  funext x
  ring

private lemma int_lin (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (a : Fin n → ℝ) : ∫ x, lin a x ∂μ = 0 := by
  dsimp only
  rw [integral_finsetSum _ (fun i _ => (h.int1 i).const_mul (a i))]
  simp [integral_const_mul, h.m1]

private lemma int_quad (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (A : Matrix (Fin n) (Fin n) ℝ) :
    ∫ x, quad A x ∂μ = (∑ i, A i i) / n := by
  dsimp only
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (h.int2 i j).const_mul (A i j)))]
  simp_rw [integral_finsetSum _ (fun j _ => (h.int2 _ j).const_mul (A _ j)),
    integral_const_mul, h.m2]
  simp [mul_ite, div_eq_mul_inv, Finset.sum_mul]

private lemma int_ll (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (a b : Fin n → ℝ) :
    ∫ x, lin a x * lin b x ∂μ = (∑ i, a i * b i) / n := by
  have expand (x : Fin n → ℝ) : lin a x * lin b x =
      ∑ i, ∑ j, (a i * b j) * (x i * x j) := by
    dsimp only
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [expand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => (h.int2 i j).const_mul (a i * b j)))]
  simp_rw [integral_finsetSum _ (fun j _ => (h.int2 _ j).const_mul _),
    integral_const_mul, h.m2]
  simp [mul_ite, div_eq_mul_inv, Finset.sum_mul]

private lemma int_lq (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (a : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    ∫ x, lin a x * quad A x ∂μ = 0 := by
  have expand (x : Fin n → ℝ) : lin a x * quad A x =
      ∑ i, ∑ j, ∑ k, (a i * A j k) * (x i * x j * x k) := by
    dsimp only
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [expand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => integrable_finsetSum _ (fun k _ =>
      (h.int3 i j k).const_mul (a i * A j k))))]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _
    (fun k _ => (h.int3 _ j k).const_mul _)),
    integral_finsetSum _ (fun k _ => (h.int3 _ _ k).const_mul _),
    integral_const_mul, h.m3]
  simp

private lemma int_qq (μ : Measure (Fin n → ℝ)) (h : SphereMoments n μ)
    (A B : Fin n → Fin n → ℝ) (hB : Matrix.IsSymm B) :
    ∫ x, quad A x * quad B x ∂μ =
      ((∑ i, A i i) * (∑ j, B j j) + 2 * ∑ i, ∑ j, A i j * B j i) /
        ((n : ℝ) * (n + 2)) := by
  have expand (x : Fin n → ℝ) : quad A x * quad B x =
      ∑ i, ∑ j, ∑ k, ∑ l, (A i j * B k l) * (x i * x j * x k * x l) := by
    dsimp only
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [expand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _
    (fun j _ => integrable_finsetSum _ (fun k _ => integrable_finsetSum _
      (fun l _ => (h.int4 i j k l).const_mul (A i j * B k l)))))]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _
    (fun k _ => integrable_finsetSum _ (fun l _ => (h.int4 _ j k l).const_mul _))),
    integral_finsetSum _ (fun k _ => integrable_finsetSum _
      (fun l _ => (h.int4 _ _ k l).const_mul _)),
    integral_finsetSum _ (fun l _ => (h.int4 _ _ _ l).const_mul _),
    integral_const_mul, h.m4]
  simp only [← mul_div_assoc, ← Finset.sum_div]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [ite_and, mul_ite, mul_one, mul_zero]
  simp (config := { maxSteps := 1000000 }) only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  simp only [hB.apply]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  ring

private lemma mapM_eq (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) (k : Fin n) :
    mapM c L Q x k = c k + lin (L k) x + quad (Q k) x := by
  simp only [mapM, mul_assoc]

private lemma integrable_map (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h : SphereMoments n μ) (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    Integrable (fun x => mapM c L Q x k) μ := by
  simp_rw [mapM_eq]
  exact ((integrable_const _).add (integrable_lin μ h _)).add (integrable_quad μ h _)

private lemma int_map (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h : SphereMoments n μ) (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    ∫ x, mapM c L Q x k ∂μ = c k + (∑ i, Q k i i) / n := by
  simp_rw [mapM_eq]
  rw [integral_add (f := fun x => c k + lin (L k) x) (g := fun x => quad (Q k) x)
    ((integrable_const (c k)).add (integrable_lin μ h (L k)))
    (integrable_quad μ h (Q k)), integral_add (integrable_const (c k)) (integrable_lin μ h (L k))]
  simp [int_lin, int_quad, h]

private lemma integrable_pair (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h : SphereMoments n μ) (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (k l : Fin n) :
    Integrable (fun x => mapM c L Q x k * mapM c L Q x l) μ := by
  have hlk := integrable_lin μ h (L k)
  have hll := integrable_lin μ h (L l)
  have hqk := integrable_quad μ h (Q k)
  have hql := integrable_quad μ h (Q l)
  have hll' := integrable_ll μ h (L k) (L l)
  have hlq := integrable_lq μ h (L k) (Q l)
  have hql' : Integrable (fun x => quad (Q k) x * lin (L l) x) μ := by
    simpa only [mul_comm] using integrable_lq μ h (L l) (Q k)
  have hqq := integrable_qq μ h (Q k) (Q l)
  simp only [mapM_eq, add_mul, mul_add]
  fun_prop

private lemma int_pair (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (h : SphereMoments n μ) (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ k, (Q k).IsSymm)
    (k l : Fin n) :
    ∫ x, mapM c L Q x k * mapM c L Q x l ∂μ =
      c k * c l + c k * ((∑ i, Q l i i) / n) + ((∑ i, Q k i i) / n) * c l
      + (∑ i, L k i * L l i) / n
      + ((∑ i, Q k i i) * (∑ j, Q l j j) + 2 * ∑ i, ∑ j, Q k i j * Q l j i) /
        ((n : ℝ) * (n + 2)) := by
  have hlk := integrable_lin μ h (L k)
  have hll := integrable_lin μ h (L l)
  have hqk := integrable_quad μ h (Q k)
  have hql := integrable_quad μ h (Q l)
  have hll' := integrable_ll μ h (L k) (L l)
  have hlq := integrable_lq μ h (L k) (Q l)
  have hql' : Integrable (fun x => quad (Q k) x * lin (L l) x) μ := by
    simpa only [mul_comm] using integrable_lq μ h (L l) (Q k)
  have hqq := integrable_qq μ h (Q k) (Q l)
  simp only [mapM_eq, add_mul, mul_add]
  simp (disch := fun_prop) only [integral_add]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul,
    integral_const_mul, integral_mul_const, int_lin μ h, int_quad μ h,
    int_ll μ h, int_lq μ h]
  have hz : (∫ x, quad (Q k) x * lin (L l) x ∂μ) = 0 := by
    simpa only [mul_comm] using int_lq μ h (L l) (Q k)
  rw [hz]
  have hv := int_qq μ h (Q k) (Q l) (hQ l)
  dsimp only at hv
  rw [hv]
  ring


private lemma integrable_lll (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (a b c : Fin n → ℝ) : Integrable (fun x => lin a x * lin b x * lin c x) μ := by
  have expand (x : Fin n → ℝ) : lin a x * lin b x * lin c x =
      ∑ i, ∑ j, ∑ k, (a i * b j * c k) * (x i * x j * x k) := by
    rw [mul_assoc]
    dsimp only
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [expand]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro k _
  exact (triple_integrable μ hμ i j k).const_mul _

private lemma int_lll (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (a b c : Fin n → ℝ) : (∫ x, lin a x * lin b x * lin c x ∂μ) =
      0 := by
  have expand (x : Fin n → ℝ) : lin a x * lin b x * lin c x =
      ∑ i, ∑ j, ∑ k, (a i * b j * c k) * (x i * x j * x k) := by
    rw [mul_assoc]
    dsimp only
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp_rw [expand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => (triple_integrable μ hμ i j k).const_mul (a i * b j * c k))))]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => (triple_integrable μ hμ _ j k).const_mul (a _ * b j * c k))),
    integral_finsetSum _ (fun k _ => (triple_integrable μ hμ _ _ k).const_mul (a _ * b _ * c k)), integral_const_mul, triple_moment μ hμ]
  simp


private lemma integrable_llq (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (a b : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) : Integrable (fun x => lin a x * lin b x * quad A x) μ := by
  have expand (x : Fin n → ℝ) : lin a x * lin b x * quad A x =
      ∑ i, ∑ j, ∑ k, ∑ l, (a i * b j * A k l) * (x i * x j * x k * x l) := by
    rw [mul_assoc]
    dsimp only
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [expand]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro l _
  exact (four_integrable μ hμ i j k l).const_mul _

private lemma int_llq (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (a b : Fin n → ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) : (∫ x, lin a x * lin b x * quad A x ∂μ) =
      ((∑ i, a i * b i) * (∑ i, A i i) + 2 * ∑ i, ∑ j, a i * A i j * b j) / ((n : ℝ) * (n + 2)) := by
  have expand (x : Fin n → ℝ) : lin a x * lin b x * quad A x =
      ∑ i, ∑ j, ∑ k, ∑ l, (a i * b j * A k l) * (x i * x j * x k * x l) := by
    rw [mul_assoc]
    dsimp only
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    ring
  simp_rw [expand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => (four_integrable μ hμ i j k l).const_mul (a i * b j * A k l)))))]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => (four_integrable μ hμ _ j k l).const_mul (a _ * b j * A k l)))),
    integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => (four_integrable μ hμ _ _ k l).const_mul (a _ * b _ * A k l))),
    integral_finsetSum _ (fun l _ => (four_integrable μ hμ _ _ _ l).const_mul (a _ * b _ * A _ l)), integral_const_mul, four_moment μ hμ]
  simp only [← mul_div_assoc, ← Finset.sum_div]
  congr 1
  simp only [mul_add, Finset.sum_add_distrib]
  simp only [ite_and, mul_ite, mul_one, mul_zero]
  simp (config := { maxSteps := 1000000 }) only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  simp only [hA.apply]
  simp only [← Finset.sum_mul, ← Finset.mul_sum]
  have term (i j : Fin n) : a i * b j * A i j = a i * A i j * b j := by ring
  simp_rw [term]
  ring


private lemma integrable_lqq (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (a : Fin n → ℝ) (A B : Matrix (Fin n) (Fin n) ℝ) : Integrable (fun x => lin a x * quad A x * quad B x) μ := by
  have expand (x : Fin n → ℝ) : lin a x * quad A x * quad B x =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ p, (a i * A j k * B l p) * (x i * x j * x k * x l * x p) := by
    rw [mul_assoc]
    dsimp only
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro p _
    ring
  simp_rw [expand]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro l _
  apply integrable_finsetSum
  intro p _
  exact (five_integrable μ hμ i j k l p).const_mul _

private lemma int_lqq (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (a : Fin n → ℝ) (A B : Matrix (Fin n) (Fin n) ℝ) : (∫ x, lin a x * quad A x * quad B x ∂μ) =
      0 := by
  have expand (x : Fin n → ℝ) : lin a x * quad A x * quad B x =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ p, (a i * A j k * B l p) * (x i * x j * x k * x l * x p) := by
    rw [mul_assoc]
    dsimp only
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro p _
    ring
  simp_rw [expand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => integrable_finsetSum _ (fun p _ => (five_integrable μ hμ i j k l p).const_mul (a i * A j k * B l p))))))]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => integrable_finsetSum _ (fun p _ => (five_integrable μ hμ _ j k l p).const_mul (a _ * A j k * B l p))))),
    integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => integrable_finsetSum _ (fun p _ => (five_integrable μ hμ _ _ k l p).const_mul (a _ * A _ k * B l p)))),
    integral_finsetSum _ (fun l _ => integrable_finsetSum _ (fun p _ => (five_integrable μ hμ _ _ _ l p).const_mul (a _ * A _ _ * B l p))),
    integral_finsetSum _ (fun p _ => (five_integrable μ hμ _ _ _ _ p).const_mul (a _ * A _ _ * B _ p)), integral_const_mul, five_moment μ hμ]
  simp


private lemma integrable_qqq (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (A B C : Matrix (Fin n) (Fin n) ℝ) : Integrable (fun x => quad A x * quad B x * quad C x) μ := by
  have expand (x : Fin n → ℝ) : quad A x * quad B x * quad C x =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ p, ∑ q, (A i j * B k l * C p q) * (x i * x j * x k * x l * x p * x q) := by
    rw [mul_assoc]
    dsimp only
    simp only [Finset.sum_mul]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  simp_rw [expand]
  apply integrable_finsetSum
  intro i _
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro k _
  apply integrable_finsetSum
  intro l _
  apply integrable_finsetSum
  intro p _
  apply integrable_finsetSum
  intro q _
  exact (six_integrable μ hμ i j k l p q).const_mul _

set_option maxHeartbeats 2000000 in
private lemma int_qqq (μ : Measure (Fin n → ℝ)) (hμ : SphereProd6 n μ)
    (A B C : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm) (hB : B.IsSymm)
    (hC : C.IsSymm) : (∫ x, quad A x * quad B x * quad C x ∂μ) =
      ((∑ i, A i i) * (∑ i, B i i) * (∑ i, C i i)
        + 2 * (∑ i, A i i) * (∑ i, ∑ j, B i j * C j i)
        + 2 * (∑ i, B i i) * (∑ i, ∑ j, A i j * C j i)
        + 2 * (∑ i, C i i) * (∑ i, ∑ j, A i j * B j i)
        + 8 * ∑ i, ∑ j, ∑ k, A i j * B j k * C k i) /
      ((n : ℝ) * (n + 2) * (n + 4)) := by
  have expand (x : Fin n → ℝ) : quad A x * quad B x * quad C x =
      ∑ i, ∑ j, ∑ k, ∑ l, ∑ p, ∑ q,
        (A i j * B k l * C p q) * (x i * x j * x k * x l * x p * x q) := by
    rw [mul_assoc]
    dsimp only
    simp (config := { maxSteps := 1000000 }) only [Finset.sum_mul]
    simp (config := { maxSteps := 1000000 }) only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    apply Finset.sum_congr rfl
    intro p _
    apply Finset.sum_congr rfl
    intro q _
    ring
  simp_rw [expand]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => integrable_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => (six_integrable μ hμ i j k l p q).const_mul (A i j * B k l * C p q)))))))]
  simp_rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => integrable_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => (six_integrable μ hμ _ j k l p q).const_mul (A _ j * B k l * C p q)))))),
    integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => integrable_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => (six_integrable μ hμ _ _ k l p q).const_mul (A _ _ * B k l * C p q))))),
    integral_finsetSum _ (fun l _ => integrable_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => (six_integrable μ hμ _ _ _ l p q).const_mul (A _ _ * B _ l * C p q)))),
    integral_finsetSum _ (fun p _ => integrable_finsetSum _ (fun q _ => (six_integrable μ hμ _ _ _ _ p q).const_mul (A _ _ * B _ _ * C p q))),
    integral_finsetSum _ (fun q _ => (six_integrable μ hμ _ _ _ _ _ q).const_mul (A _ _ * B _ _ * C _ q)), integral_const_mul, six_moment μ hμ]
  simp (config := { maxSteps := 1000000 }) only [← mul_div_assoc, ← Finset.sum_div]
  congr 1
  simp (config := { maxSteps := 1000000 }) only [mul_add, Finset.sum_add_distrib]
  simp (config := { maxSteps := 1000000 }) only [ite_and, mul_ite, mul_one, mul_zero]
  simp (config := { maxSteps := 1000000 }) only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true]
  simp (config := { maxSteps := 1000000 }) only [hB.apply, hC.apply]
  simp (config := { maxSteps := 1000000 }) only [← Finset.sum_mul, ← Finset.mul_sum]
  have hcdiag : (∑ i, ∑ j, ∑ k, A i i * B j k * C j k) =
      (∑ i, A i i) * (∑ j, ∑ k, B j k * C j k) := by
    simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul]
  have hbdiag : (∑ i, ∑ j, (A i j * ∑ k, B k k) * C i j) =
      (∑ k, B k k) * (∑ i, ∑ j, A i j * C i j) := by
    have term (i j : Fin n) : (A i j * ∑ k, B k k) * C i j =
        (∑ k, B k k) * (A i j * C i j) := by ring
    simp_rw [term]
    simp only [← Finset.mul_sum]
  have ht : (∑ i, ∑ j, ∑ k, A i j * B i k * C j k) =
      ∑ i, ∑ j, ∑ k, A i j * B j k * C i k := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [hA.apply]
  simp_rw [hcdiag, hbdiag, ht]
  ring

private lemma map_triple_expand (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (x : Fin n → ℝ) (k l p : Fin n) :
    mapM c L Q x k * mapM c L Q x l * mapM c L Q x p =
      c k * c l * c p +
      (c k * c l) * ((lin (L p) x)) +
      (c k * c l) * ((quad (Q p) x)) +
      (c k * c p) * ((lin (L l) x)) +
      (c k) * ((lin (L l) x) * (lin (L p) x)) +
      (c k) * ((lin (L l) x) * (quad (Q p) x)) +
      (c k * c p) * ((quad (Q l) x)) +
      (c k) * ((lin (L p) x) * (quad (Q l) x)) +
      (c k) * ((quad (Q l) x) * (quad (Q p) x)) +
      (c l * c p) * ((lin (L k) x)) +
      (c l) * ((lin (L k) x) * (lin (L p) x)) +
      (c l) * ((lin (L k) x) * (quad (Q p) x)) +
      (c p) * ((lin (L k) x) * (lin (L l) x)) +
      (lin (L k) x) * (lin (L l) x) * (lin (L p) x) +
      (lin (L k) x) * (lin (L l) x) * (quad (Q p) x) +
      (c p) * ((lin (L k) x) * (quad (Q l) x)) +
      (lin (L k) x) * (lin (L p) x) * (quad (Q l) x) +
      (lin (L k) x) * (quad (Q l) x) * (quad (Q p) x) +
      (c l * c p) * ((quad (Q k) x)) +
      (c l) * ((lin (L p) x) * (quad (Q k) x)) +
      (c l) * ((quad (Q k) x) * (quad (Q p) x)) +
      (c p) * ((lin (L l) x) * (quad (Q k) x)) +
      (lin (L l) x) * (lin (L p) x) * (quad (Q k) x) +
      (lin (L l) x) * (quad (Q k) x) * (quad (Q p) x) +
      (c p) * ((quad (Q k) x) * (quad (Q l) x)) +
      (lin (L p) x) * (quad (Q k) x) * (quad (Q l) x) +
      (quad (Q k) x) * (quad (Q l) x) * (quad (Q p) x) := by
  simp only [mapM_eq]
  ring

set_option maxHeartbeats 2000000 in
private lemma integrable_map_triple (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : SphereProd6 n μ) (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (k l p : Fin n) :
    Integrable (fun x => mapM c L Q x k * mapM c L Q x l * mapM c L Q x p) μ := by
  let h := sphereMoments_of_prod6 μ hμ
  have hl (a : Fin n) := integrable_lin μ h (L a)
  have hq (a : Fin n) := integrable_quad μ h (Q a)
  have hll (a b : Fin n) := integrable_ll μ h (L a) (L b)
  have hlq (a b : Fin n) := integrable_lq μ h (L a) (Q b)
  have hqq (a b : Fin n) := integrable_qq μ h (Q a) (Q b)
  have hlll (a b d : Fin n) := integrable_lll μ hμ (L a) (L b) (L d)
  have hllq (a b d : Fin n) := integrable_llq μ hμ (L a) (L b) (Q d)
  have hlqq (a b d : Fin n) := integrable_lqq μ hμ (L a) (Q b) (Q d)
  have hqqq (a b d : Fin n) := integrable_qqq μ hμ (Q a) (Q b) (Q d)
  simp_rw [map_triple_expand]
  exact ((((((((((((((((((((((((((integrable_const (c k * c l * c p)).add ((hl p).const_mul (c k * c l))).add ((hq p).const_mul (c k * c l))).add ((hl l).const_mul (c k * c p))).add ((hll l p).const_mul (c k))).add ((hlq l p).const_mul (c k))).add ((hq l).const_mul (c k * c p))).add ((hlq p l).const_mul (c k))).add ((hqq l p).const_mul (c k))).add ((hl k).const_mul (c l * c p))).add ((hll k p).const_mul (c l))).add ((hlq k p).const_mul (c l))).add ((hll k l).const_mul (c p))).add (hlll k l p)).add (hllq k l p)).add ((hlq k l).const_mul (c p))).add (hllq k p l)).add (hlqq k l p)).add ((hq k).const_mul (c l * c p))).add ((hlq p k).const_mul (c l))).add ((hqq k p).const_mul (c l))).add ((hlq l k).const_mul (c p))).add (hllq l p k)).add (hlqq l k p)).add ((hqq k l).const_mul (c p))).add (hlqq p k l)).add (hqqq k l p)

set_option maxHeartbeats 2000000 in
private lemma int_map_triple (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : SphereProd6 n μ) (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ a, (Q a).IsSymm) (k l p : Fin n) :
    let t : Fin n → ℝ := fun k => ∑ i, Q k i i
    let K : Fin n → Fin n → ℝ := fun k l => ∑ i, ∑ j, Q k i j * Q l j i
    let LL : Fin n → Fin n → ℝ := fun k l => ∑ i, L k i * L l i
    let H : Fin n → Fin n → Fin n → ℝ := fun k l p =>
      ∑ i, ∑ j, L k i * Q p i j * L l j
    (∫ x, mapM c L Q x k * mapM c L Q x l * mapM c L Q x p ∂μ) =
      c k * c l * c p
      + (c l * c p * t k + c k * c p * t l + c k * c l * t p) / n
      + (c p * LL k l + c l * LL k p + c k * LL l p) / n
      + (c p * (t k * t l + 2 * K k l) + c l * (t k * t p + 2 * K k p)
          + c k * (t l * t p + 2 * K l p)) / ((n : ℝ) * (n + 2))
      + (LL k l * t p + 2 * H k l p + LL k p * t l + 2 * H k p l
          + LL l p * t k + 2 * H l p k) / ((n : ℝ) * (n + 2))
      + (t k * t l * t p + 2 * t k * K l p + 2 * t l * K k p
          + 2 * t p * K k l + 8 * ∑ i, ∑ j, ∑ r, Q k i j * Q l j r * Q p r i) /
        ((n : ℝ) * (n + 2) * (n + 4)) := by
  dsimp only
  let h := sphereMoments_of_prod6 μ hμ
  have hl (a : Fin n) := integrable_lin μ h (L a)
  have hq (a : Fin n) := integrable_quad μ h (Q a)
  have hll (a b : Fin n) := integrable_ll μ h (L a) (L b)
  have hlq (a b : Fin n) := integrable_lq μ h (L a) (Q b)
  have hqq (a b : Fin n) := integrable_qq μ h (Q a) (Q b)
  have hlll (a b d : Fin n) := integrable_lll μ hμ (L a) (L b) (L d)
  have hllq (a b d : Fin n) := integrable_llq μ hμ (L a) (L b) (Q d)
  have hlqq (a b d : Fin n) := integrable_lqq μ hμ (L a) (Q b) (Q d)
  have hqqq (a b d : Fin n) := integrable_qqq μ hμ (Q a) (Q b) (Q d)
  simp_rw [map_triple_expand]
  simp (disch := fun_prop) only [integral_add]
  have hqv (a b : Fin n) := int_qq μ h (Q a) (Q b) (hQ b)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul, integral_const_mul,
    int_lin μ h, int_quad μ h, int_ll μ h, int_lq μ h,
    hqv, int_lll μ hμ, int_llq μ hμ _ _ _ (hQ _),
    int_lqq μ hμ, int_qqq μ hμ _ _ _ (hQ _) (hQ _) (hQ _)]
  ring


set_option maxHeartbeats 2000000 in
private lemma int_map_triple_centered (hn : 1 ≤ n)
    (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ] (hμ : SphereProd6 n μ)
    (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ)
    (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ k, (Q k).IsSymm)
    (k l p : Fin n) :
    let ρ2 : ℝ := n * (n + 2)
    let ρ3 : ℝ := n * (n + 2) * (n + 4)
    let t : Fin n → ℝ := fun k => ∑ i, Q k i i
    let ν : Fin n → ℝ := fun k => c k + t k / n
    let K : Fin n → Fin n → ℝ := fun k l => ∑ i, ∑ j, Q k i j * Q l j i
    let LL : Fin n → Fin n → ℝ := fun k l => ∑ i, L k i * L l i
    let C : Fin n → Fin n → ℝ := fun k l =>
      LL k l / n + 2 / ρ2 * K k l - 2 / (n * ρ2) * t k * t l
    let H : Fin n → Fin n → Fin n → ℝ := fun k l p =>
      ∑ i, ∑ j, L k i * Q p i j * L l j
    let γ : ℝ := 1 / ρ3 - 3 / (n * ρ2) + 2 / (n : ℝ) ^ 3
    (∫ x, mapM c L Q x k * mapM c L Q x l * mapM c L Q x p ∂μ) =
      ν k * ν l * ν p + ν k * C l p + ν l * C k p + ν p * C k l
      + 2 / ρ2 * (H k l p + H k p l + H l p k)
      - 2 / (n * ρ2) * (t p * LL k l + t l * LL k p + t k * LL l p)
      + 8 / ρ3 * (∑ i, ∑ j, ∑ r, Q k i j * Q l j r * Q p r i)
      - 8 / (n * ρ3) * (t p * K k l + t l * K k p + t k * K l p)
      + γ * t k * t l * t p := by
  dsimp only
  rw [int_map_triple μ hμ c L Q hQ k l p]
  dsimp only
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have hn4 : (n : ℝ) + 4 ≠ 0 := by positivity
  field_simp [hn0, hn2, hn4]
  ring

private lemma tensor_sum_swap12 (T : Fin n → Fin n → Fin n → ℝ) (hT : TSymm T)
    (U : Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, T a b c * U b a c) = ∑ a, ∑ b, ∑ c, T a b c * U a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [← (hT a b c).1]

private lemma tensor_sum_swap23 (T : Fin n → Fin n → Fin n → ℝ) (hT : TSymm T)
    (U : Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, T a b c * U a c b) = ∑ a, ∑ b, ∑ c, T a b c * U a b c := by
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [← (hT a b c).2]

private lemma tensor_sum_cycle (T : Fin n → Fin n → Fin n → ℝ) (hT : TSymm T)
    (U : Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, T a b c * U b c a) = ∑ a, ∑ b, ∑ c, T a b c * U a b c := by
  calc
    _ = ∑ a, ∑ b, ∑ c, T a b c * U a c b :=
      tensor_sum_swap12 T hT (fun a b c => U a c b)
    _ = _ := tensor_sum_swap23 T hT U

private lemma tensor_sum_cycle' (T : Fin n → Fin n → Fin n → ℝ) (hT : TSymm T)
    (U : Fin n → Fin n → Fin n → ℝ) :
    (∑ a, ∑ b, ∑ c, T a b c * U c a b) = ∑ a, ∑ b, ∑ c, T a b c * U a b c := by
  calc
    _ = ∑ a, ∑ b, ∑ c, T a b c * U b a c :=
      tensor_sum_swap23 T hT (fun a b c => U b a c)
    _ = _ := tensor_sum_swap12 T hT U


set_option maxHeartbeats 2000000 in
private lemma cubic_contraction (T : Fin n → Fin n → Fin n → ℝ) (hT : TSymm T)
    (ν t : Fin n → ℝ) (C K LL : Fin n → Fin n → ℝ)
    (H J : Fin n → Fin n → Fin n → ℝ) (ρ2 ρ3 γ : ℝ) :
    (∑ a, ∑ b, ∑ p, T a b p * (ν a * ν b * ν p + ν a * C b p + ν b * C a p + ν p * C a b
      + 2 / ρ2 * (H a b p + H a p b + H b p a)
      - 2 / ((n : ℝ) * ρ2) * (t p * LL a b + t b * LL a p + t a * LL b p)
      + 8 / ρ3 * J a b p
      - 8 / ((n : ℝ) * ρ3) * (t p * K a b + t b * K a p + t a * K b p)
      + γ * t a * t b * t p)) =
      (∑ a, ∑ b, ∑ p, T a b p * ν a * ν b * ν p)
      + 3 * (∑ a, ∑ b, ∑ p, T a b p * ν a * C b p)
      + 6 / ρ2 * (∑ a, ∑ b, ∑ p, T a b p * H a b p)
      - 6 / ((n : ℝ) * ρ2) * (∑ a, ∑ b, ∑ p, T a b p * t p * LL a b)
      + 8 / ρ3 * (∑ a, ∑ b, ∑ p, T a b p * J a b p)
      - 24 / ((n : ℝ) * ρ3) * (∑ a, ∑ b, ∑ p, T a b p * t p * K a b)
      + γ * (∑ a, ∑ b, ∑ p, T a b p * t a * t b * t p) := by
  have term (a b p : Fin n) : T a b p * (ν a * ν b * ν p + ν a * C b p + ν b * C a p + ν p * C a b
      + 2 / ρ2 * (H a b p + H a p b + H b p a)
      - 2 / ((n : ℝ) * ρ2) * (t p * LL a b + t b * LL a p + t a * LL b p)
      + 8 / ρ3 * J a b p
      - 8 / ((n : ℝ) * ρ3) * (t p * K a b + t b * K a p + t a * K b p)
      + γ * t a * t b * t p) =
      T a b p * ν a * ν b * ν p
      + T a b p * (ν a * C b p) + T a b p * (ν b * C a p)
      + T a b p * (ν p * C a b)
      + 2 / ρ2 * (T a b p * H a b p)
      + 2 / ρ2 * (T a b p * H a p b)
      + 2 / ρ2 * (T a b p * H b p a)
      - 2 / ((n : ℝ) * ρ2) * (T a b p * (t p * LL a b))
      - 2 / ((n : ℝ) * ρ2) * (T a b p * (t b * LL a p))
      - 2 / ((n : ℝ) * ρ2) * (T a b p * (t a * LL b p))
      + 8 / ρ3 * (T a b p * J a b p)
      - 8 / ((n : ℝ) * ρ3) * (T a b p * (t p * K a b))
      - 8 / ((n : ℝ) * ρ3) * (T a b p * (t b * K a p))
      - 8 / ((n : ℝ) * ρ3) * (T a b p * (t a * K b p))
      + γ * (T a b p * t a * t b * t p) := by ring
  simp_rw [term]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [mul_assoc]
  rw [tensor_sum_swap12 T hT (fun a b p => ν a * C b p),
    tensor_sum_cycle' T hT (fun a b p => ν a * C b p),
    tensor_sum_swap23 T hT H, tensor_sum_cycle T hT H,
    tensor_sum_swap23 T hT (fun a b p => t p * LL a b),
    tensor_sum_cycle T hT (fun a b p => t p * LL a b),
    tensor_sum_swap23 T hT (fun a b p => t p * K a b),
    tensor_sum_cycle T hT (fun a b p => t p * K a b)]
  ring

set_option maxHeartbeats 4000000 in
/-- **The exact formula at `(3,2)`** (part 21, Lemma 1.1). With `ρ₂ = n(n+2)`, `ρ₃ = n(n+2)(n+4)`, `t_k = tr Q_k`,
`μ = c + t/n`, `K_kl = tr(Q_kQ_l)`, `C = LLᵀ/n + (2/ρ₂)K − (2/(nρ₂)) ttᵀ`, `G₃ = Σ_c ⟨T_c, L Q_c Lᵀ⟩`,
`Δ = Σ T_abc tr(Q_aQ_bQ_c)`, `γ = 1/ρ₃ − 3/(nρ₂) + 2/n³`:
`B = f₀ + bᵀμ + F[μ,μ] + ⟨F,C⟩ + T[μ,μ,μ] + 3⟨T[μ],C⟩ + (6/ρ₂) G₃ − (6/(nρ₂)) ⟨T[t], LLᵀ⟩
     + (8/ρ₃) Δ − (24/(nρ₃)) ⟨T[t], K⟩ + γ T[t,t,t]`. -/
theorem exact_formula3 (hn : 1 ≤ n) (μ : Measure (Fin n → ℝ)) [IsProbabilityMeasure μ]
    (hμ : SphereProd6 n μ)
    (c : Fin n → ℝ) (L : Matrix (Fin n) (Fin n) ℝ) (Q : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hQ : ∀ k, (Q k).IsSymm) (f0 : ℝ) (b : Fin n → ℝ) (F : Matrix (Fin n) (Fin n) ℝ) (hF : F.IsSymm)
    (T : Fin n → Fin n → Fin n → ℝ) (hT : TSymm T) :
    let ρ2 : ℝ := n * (n + 2)
    let ρ3 : ℝ := n * (n + 2) * (n + 4)
    let t : Fin n → ℝ := fun k => ∑ i, Q k i i
    let ν : Fin n → ℝ := fun k => c k + t k / n
    let K : Fin n → Fin n → ℝ := fun k l => ∑ i, ∑ j, Q k i j * Q l j i
    let LL : Fin n → Fin n → ℝ := fun k l => ∑ i, L k i * L l i
    let C : Fin n → Fin n → ℝ := fun k l => LL k l / n + 2 / ρ2 * K k l - 2 / (n * ρ2) * t k * t l
    let G3 : ℝ := ∑ a, ∑ b', ∑ p, T a b' p * ∑ i, ∑ j, L a i * Q p i j * L b' j
    let Δ : ℝ := ∑ a, ∑ b', ∑ p, T a b' p * ∑ i, ∑ j, ∑ k, Q a i j * Q b' j k * Q p k i
    let γ : ℝ := 1 / ρ3 - 3 / (n * ρ2) + 2 / (n : ℝ) ^ 3
    ∫ x, funF3 f0 b F T (mapM c L Q x) ∂μ =
      f0 + ∑ k, b k * ν k + ∑ k, ∑ l, F k l * ν k * ν l + ∑ k, ∑ l, F k l * C k l
        + ∑ a, ∑ b', ∑ p, T a b' p * ν a * ν b' * ν p
        + 3 * ∑ a, ∑ b', ∑ p, T a b' p * ν a * C b' p
        + 6 / ρ2 * G3 - 6 / (n * ρ2) * ∑ a, ∑ b', ∑ p, T a b' p * t p * LL a b'
        + 8 / ρ3 * Δ - 24 / (n * ρ3) * ∑ a, ∑ b', ∑ p, T a b' p * t p * K a b'
        + γ * ∑ a, ∑ b', ∑ p, T a b' p * t a * t b' * t p := by
  dsimp only
  let ρ2 : ℝ := n * (n + 2)
  let ρ3 : ℝ := n * (n + 2) * (n + 4)
  let t : Fin n → ℝ := fun k => ∑ i, Q k i i
  let ν : Fin n → ℝ := fun k => c k + t k / n
  let K : Fin n → Fin n → ℝ := fun k l => ∑ i, ∑ j, Q k i j * Q l j i
  let LL : Fin n → Fin n → ℝ := fun k l => ∑ i, L k i * L l i
  let C : Fin n → Fin n → ℝ := fun k l => LL k l / n + 2 / ρ2 * K k l - 2 / (n * ρ2) * t k * t l
  let H : Fin n → Fin n → Fin n → ℝ := fun a b p =>
    ∑ i, ∑ j, L a i * Q p i j * L b j
  let J : Fin n → Fin n → Fin n → ℝ := fun a b p =>
    ∑ i, ∑ j, ∑ k, Q a i j * Q b j k * Q p k i
  let G3 : ℝ := ∑ a, ∑ b', ∑ p, T a b' p * H a b' p
  let Δ : ℝ := ∑ a, ∑ b', ∑ p, T a b' p * J a b' p
  let γ : ℝ := 1 / ρ3 - 3 / (n * ρ2) + 2 / (n : ℝ) ^ 3
  change (∫ x, funF3 f0 b F T (mapM c L Q x) ∂μ) =
      f0 + ∑ k, b k * ν k + ∑ k, ∑ l, F k l * ν k * ν l + ∑ k, ∑ l, F k l * C k l
        + ∑ a, ∑ b', ∑ p, T a b' p * ν a * ν b' * ν p
        + 3 * ∑ a, ∑ b', ∑ p, T a b' p * ν a * C b' p
        + 6 / ρ2 * G3 - 6 / (n * ρ2) * ∑ a, ∑ b', ∑ p, T a b' p * t p * LL a b'
        + 8 / ρ3 * Δ - 24 / (n * ρ3) * ∑ a, ∑ b', ∑ p, T a b' p * t p * K a b'
        + γ * ∑ a, ∑ b', ∑ p, T a b' p * t a * t b' * t p
  let h := sphereMoments_of_prod6 μ hμ
  have hi (k : Fin n) := (integrable_map μ h c L Q k).const_mul (b k)
  have hij (k l : Fin n) :
      Integrable (fun x => F k l * mapM c L Q x k * mapM c L Q x l) μ := by
    simpa only [mul_assoc] using (integrable_pair μ h c L Q k l).const_mul (F k l)
  have hijk (a b' p : Fin n) :
      Integrable (fun x => T a b' p * mapM c L Q x a * mapM c L Q x b' * mapM c L Q x p) μ := by
    simpa only [mul_assoc] using
      (integrable_map_triple μ hμ c L Q a b' p).const_mul (T a b' p)
  have hf : Integrable (fun x => funF f0 b F (mapM c L Q x)) μ := by
    exact ((integrable_const f0).add
      (integrable_finsetSum _ (fun k _ => hi k))).add
      (integrable_finsetSum _ (fun k _ => integrable_finsetSum _ (fun l _ => hij k l)))
  have ht : Integrable (fun x =>
      ∑ a, ∑ b', ∑ p, T a b' p * mapM c L Q x a * mapM c L Q x b' * mapM c L Q x p) μ :=
    integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b' _ =>
      integrable_finsetSum _ (fun p _ => hijk a b' p)))
  have hquad : (∫ x, funF f0 b F (mapM c L Q x) ∂μ) =
      f0 + ∑ k, b k * ν k + ∑ k, ∑ l, F k l * ν k * ν l +
        ∑ k, ∑ l, F k l * C k l := by
    rw [BstLean.Part29.exact_formula hn μ h c L Q hQ f0 b F hF]
    have term (k l : Fin n) : F k l * C k l =
        (F k l * LL k l) / n + 2 / ρ2 *
          (F k l * K k l - F k l * t k * t l / n) := by
      dsimp [C, ρ2]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
      have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
      field_simp [hn0, hn2]
      ring
    simp_rw [term]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_div,
      ← Finset.mul_sum]
    dsimp only [ν, t, LL, K, ρ2]
    ring
  have h3 (a b' p : Fin n) :
      (∫ x, mapM c L Q x a * mapM c L Q x b' * mapM c L Q x p ∂μ) =
      ν a * ν b' * ν p + ν a * C b' p + ν b' * C a p + ν p * C a b'
      + 2 / ρ2 * (H a b' p + H a p b' + H b' p a)
      - 2 / (n * ρ2) * (t p * LL a b' + t b' * LL a p + t a * LL b' p)
      + 8 / ρ3 * J a b' p
      - 8 / (n * ρ3) * (t p * K a b' + t b' * K a p + t a * K b' p)
      + γ * t a * t b' * t p :=
    int_map_triple_centered hn μ hμ c L Q hQ a b' p
  have hterm (a b' p : Fin n) :
      (∫ x, T a b' p * mapM c L Q x a * mapM c L Q x b' * mapM c L Q x p ∂μ) =
      T a b' p * (ν a * ν b' * ν p + ν a * C b' p + ν b' * C a p + ν p * C a b'
      + 2 / ρ2 * (H a b' p + H a p b' + H b' p a)
      - 2 / (n * ρ2) * (t p * LL a b' + t b' * LL a p + t a * LL b' p)
      + 8 / ρ3 * J a b' p
      - 8 / (n * ρ3) * (t p * K a b' + t b' * K a p + t a * K b' p)
      + γ * t a * t b' * t p) := by
    have hv := congrArg (fun z => T a b' p * z) (h3 a b' p)
    simpa only [mul_assoc, integral_const_mul] using hv
  change (∫ x, funF f0 b F (mapM c L Q x) +
    ∑ a, ∑ b', ∑ p, T a b' p * mapM c L Q x a * mapM c L Q x b' * mapM c L Q x p ∂μ) = _
  rw [integral_add hf ht, hquad]
  rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b' _ =>
    integrable_finsetSum _ (fun p _ => hijk a b' p)))]
  simp_rw [integral_finsetSum _ (fun b' _ => integrable_finsetSum _ (fun p _ => hijk _ b' p)),
    integral_finsetSum _ (fun p _ => hijk _ _ p), hterm]
  rw [cubic_contraction T hT ν t C K LL H J ρ2 ρ3 γ]
  dsimp only [G3, Δ]
  ring


end BstLean.Part33
