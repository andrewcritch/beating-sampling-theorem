import BstLean.Part218Rows

/-! The ordered-pair covariance classes follow from whole-row independence. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory
open BstLean.Part214

section
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
variable {m : ℕ} {φ : X × X → ℝ} (hφ : Measurable φ)
variable (iφ : MemLp φ 2 (μ.prod μ)) (hsym : ∀ x y, φ (x, y) = φ (y, x))
variable {z₁ z₂ : ℝ}
variable (h₂ : (∫ p, φ p ^ 2 ∂μ.prod μ) - (∫ p, φ p ∂μ.prod μ) ^ 2 = z₂)
variable (h₁ : (∫ p : X × (X × X), φ (p.1, p.2.1) * φ (p.1, p.2.2)
  ∂μ.prod (μ.prod μ)) - (∫ p, φ p ∂μ.prod μ) ^ 2 = z₁)

noncomputable def orderedRow (φ : X × X → ℝ) (p : Fin m × Fin m) (x : Fin m → X) : ℝ :=
  if p.1 = p.2 then 0 else φ (x p.1, x p.2)

include iφ in
lemma orderedRow_memLp (p : Fin m × Fin m) :
    MemLp (orderedRow φ p) 2 (Measure.pi fun _ : Fin m => μ) := by
  classical
  unfold orderedRow
  split_ifs with hp
  · exact memLp_const 0
  · exact pair_memLp μ iφ hp

include hφ iφ hsym h₂ h₁ in
theorem orderedRow_covariance (p q : Fin m × Fin m) :
    covariance (orderedRow φ p) (orderedRow φ q) (Measure.pi fun _ : Fin m => μ) =
      pairCov z₁ z₂ p q := by
  classical
  obtain ⟨i, j⟩ := p
  obtain ⟨k, l⟩ := q
  have hs : ∀ a b : Fin m, (fun x : Fin m → X => φ (x a, x b)) =
      fun x => φ (x b, x a) := by
    intro a b; funext x; exact hsym _ _
  by_cases hij : i = j
  · subst j
    simp [orderedRow, pairCov, covariance]
  by_cases hkl : k = l
  · subst l
    simp [orderedRow, pairCov, covariance]
  change covariance (fun x : Fin m → X => if i = j then 0 else φ (x i, x j))
    (fun x => if k = l then 0 else φ (x k, x l)) _ = _
  simp only [hij, hkl, ite_false]
  by_cases hik : i = k
  · subst k
    by_cases hjl : j = l
    · subst l
      rw [pair_cov_same μ hφ iφ hij, h₂]
      simp [pairCov, hij]
    · rw [pair_cov_shared μ hφ iφ hij hkl hjl, h₁]
      simp [pairCov, hij, hkl, hjl, Ne.symm hij]
  by_cases hil : i = l
  · subst l
    by_cases hjk : j = k
    · subst k
      rw [hs j i, pair_cov_same μ hφ iφ hij, h₂]
      simp [pairCov, hij, Ne.symm hij]
    · rw [hs k i, pair_cov_shared μ hφ iφ hij hik hjk, h₁]
      simp [pairCov, hij, hik, hjk, Ne.symm hij, Ne.symm hik]
  by_cases hjk : j = k
  · subst k
    rw [hs i j, pair_cov_shared μ hφ iφ (Ne.symm hij) hkl hil, h₁]
    simp [pairCov, hij, hkl, hil, Ne.symm hij]
  by_cases hjl : j = l
  · subst l
    rw [hs i j, hs k j, pair_cov_shared μ hφ iφ (Ne.symm hij) (Ne.symm hkl) hik, h₁]
    simp [pairCov, hij, hkl, hik, hjk, Ne.symm hij]
  rw [pair_cov_disjoint μ hφ iφ hij hkl hik hil hjk hjl]
  simp [pairCov, hij, hkl, hik, hil, hjk, hjl]

include hφ iφ hsym h₂ h₁ in
/-- The full ordered-row variance has no assumed covariance-class identities. -/
theorem iid_ordered_pair_variance :
    Var[fun x : Fin m → X => ∑ p : Fin m × Fin m, orderedRow φ p x;
      Measure.pi fun _ : Fin m => μ] =
      4 * (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2) * z₁ +
        2 * (m : ℝ) * ((m : ℝ) - 1) * z₂ := by
  exact ordered_pair_variance_of_covariance _ _ (orderedRow_memLp μ iφ) z₁ z₂
    (orderedRow_covariance μ hφ iφ hsym h₂ h₁)

end
end BstLean.Part218
#print axioms BstLean.Part218.iid_ordered_pair_variance
