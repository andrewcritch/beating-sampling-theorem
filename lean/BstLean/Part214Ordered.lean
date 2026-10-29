import BstLean.Part214Variance
import Mathlib.Probability.Moments.Covariance

/-! The ordered-row variance formula counts each covariance class exactly. -/
namespace BstLean.Part214
open MeasureTheory ProbabilityTheory Real

noncomputable def pairCov {m : ℕ} (z₁ z₂ : ℝ) (p q : Fin m × Fin m) : ℝ :=
  if p.1 = p.2 ∨ q.1 = q.2 then 0
  else if (p.1 = q.1 ∧ p.2 = q.2) ∨ (p.1 = q.2 ∧ p.2 = q.1) then z₂
  else if p.1 = q.1 ∨ p.1 = q.2 ∨ p.2 = q.1 ∨ p.2 = q.2 then z₁
  else 0

lemma pairCov_section {m : ℕ} (z₁ z₂ : ℝ) (i j : Fin m) (hij : i ≠ j) :
    (∑ k : Fin m, ∑ l : Fin m, pairCov z₁ z₂ (i, j) (k, l)) =
      4 * ((m : ℝ) - 2) * z₁ + 2 * z₂ := by
  classical
  have hij' : j ≠ i := hij.symm
  have hinner : ∀ k : Fin m, (∑ l : Fin m, pairCov z₁ z₂ (i, j) (k, l)) =
      2 * z₁ + (if k = i then z₂ + ((m : ℝ) - 4) * z₁ else 0) +
        (if k = j then z₂ + ((m : ℝ) - 4) * z₁ else 0) := by
    intro k
    by_cases hki : k = i
    · subst k
      have he : ∀ l : Fin m, pairCov z₁ z₂ (i, j) (i, l) =
          z₁ + (if l = j then z₂ - z₁ else 0) + (if l = i then -z₁ else 0) := by
        intro l
        by_cases hli : l = i
        · subst l; simp [pairCov, hij, hij']
        · by_cases hlj : l = j
          · subst l; simp [pairCov, hij, hij'] <;> ring
          · simp [pairCov, hij, hij', hli, hlj, Ne.symm hli, Ne.symm hlj]
      simp_rw [he]
      simp [Finset.sum_add_distrib, hij, hij']
      ring
    · by_cases hkj : k = j
      · subst k
        have he : ∀ l : Fin m, pairCov z₁ z₂ (i, j) (j, l) =
            z₁ + (if l = i then z₂ - z₁ else 0) + (if l = j then -z₁ else 0) := by
          intro l
          by_cases hli : l = i
          · subst l; simp [pairCov, hij, hij'] <;> ring
          · by_cases hlj : l = j
            · subst l; simp [pairCov, hij, hij']
            · simp [pairCov, hij, hij', hli, hlj, Ne.symm hli, Ne.symm hlj]
        simp_rw [he]
        simp [Finset.sum_add_distrib, hij, hij']
        ring
      · have he : ∀ l : Fin m, pairCov z₁ z₂ (i, j) (k, l) =
            (if l = i then z₁ else 0) + (if l = j then z₁ else 0) := by
          intro l
          by_cases hli : l = i
          · subst l; simp [pairCov, hij, hij', hki, hkj, Ne.symm hki, Ne.symm hkj]
          · by_cases hlj : l = j
            · subst l; simp [pairCov, hij, hij', hki, hkj, Ne.symm hki, Ne.symm hkj]
            · simp [pairCov, hij, hki, hkj, hli, hlj, Ne.symm hki, Ne.symm hkj,
                Ne.symm hli, Ne.symm hlj]
        simp_rw [he]
        simp [Finset.sum_add_distrib, hki, hkj]
        ring
  simp_rw [hinner]
  simp [Finset.sum_add_distrib]
  ring

theorem pairCov_total (m : ℕ) (z₁ z₂ : ℝ) :
    (∑ p : Fin m × Fin m, ∑ q : Fin m × Fin m, pairCov z₁ z₂ p q) =
      4 * (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) * z₁ +
        2 * (m : ℝ) * ((m : ℝ) - 1) * z₂ := by
  classical
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  have he : ∀ i j : Fin m, (∑ k : Fin m, ∑ l : Fin m, pairCov z₁ z₂ (i, j) (k, l)) =
      if i = j then 0 else 4 * ((m : ℝ) - 2) * z₁ + 2 * z₂ := by
    intro i j
    by_cases hij : i = j
    · subst j; simp [pairCov]
    · rw [if_neg hij]; exact pairCov_section z₁ z₂ i j hij
  simp_rw [he]
  have hsum : ∀ i : Fin m, (∑ j : Fin m,
      if i = j then (0 : ℝ) else 4 * ((m : ℝ) - 2) * z₁ + 2 * z₂) =
      ((m : ℝ) - 1) * (4 * ((m : ℝ) - 2) * z₁ + 2 * z₂) := by
    intro i
    have hh : ∀ j : Fin m, (if i = j then (0 : ℝ) else 4 * ((m : ℝ) - 2) * z₁ + 2 * z₂) =
        (4 * ((m : ℝ) - 2) * z₁ + 2 * z₂) -
          (if i = j then 4 * ((m : ℝ) - 2) * z₁ + 2 * z₂ else 0) := by
      intro j; split_ifs <;> ring
    simp_rw [hh]
    simp [Finset.sum_sub_distrib]
    ring
  simp_rw [hsum]
  simp
  ring

/-- The probability identity follows once the shared-row covariance identities are supplied. -/
theorem ordered_pair_variance_of_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {m : ℕ}
    (Y : (Fin m × Fin m) → Ω → ℝ) (hY : ∀ p, MemLp (Y p) 2 P) (z₁ z₂ : ℝ)
    (hcov : ∀ p q, covariance (Y p) (Y q) P = pairCov z₁ z₂ p q) :
    Var[fun x => ∑ p, Y p x; P] =
      4 * (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) * z₁ +
        2 * (m : ℝ) * ((m : ℝ) - 1) * z₂ := by
  have he : (fun x => ∑ p, Y p x) = ∑ p, Y p := by
    funext x
    simp only [Finset.sum_apply]
  rw [he, variance_sum hY]
  simp_rw [hcov]
  exact pairCov_total m z₁ z₂

end BstLean.Part214
#print axioms BstLean.Part214.pairCov_total
#print axioms BstLean.Part214.ordered_pair_variance_of_covariance
