import BstLean.Part160MFU

/-!
# Part 160 (file `MFPR`): Lemma PR for two linear forms, with the input-dependent remainder

Do not use `sorry`, `native_decide` or `axiom`.

* `PRvecU`: `Cov(relu(a + ⟨z, g⟩), relu(a′ + ⟨z, g′⟩)) ≤ ⟨g, g′⟩Φ(a/|g|)Φ(a′/|g′|) +
  ⟨g, g′⟩²/(|g||g′|)·√U(a/|g|)·√U(a′/|g′|)`. The proof is the proof of `PRvec_of` of Part 154
  without its last step (`√U√U ≤ K`).
* `PRvec_exp`: the same with `K₀·exp(−((a/|g|)² + (a′/|g′|)²)/4)` (Lemma `t7:p05:PR`).
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real Set Filter Topology
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part137 BstLean.Part153 BstLean.Part154
open BstLean.Part105 (BM sC sC_nonneg sC_sq gaussLin105)

theorem PRvecU (m : ℕ) (g g' : Fin m → ℝ) (a a' : ℝ) :
    ∫ z, relu (a + z ⬝ᵥ g) * relu (a' + z ⬝ᵥ g') ∂stdGauss (Fin m) -
        psiS (nrm g) a * psiS (nrm g') a' ≤
      (g ⬝ᵥ g') * PhiG (a / nrm g) * PhiG (a' / nrm g') +
        (g ⬝ᵥ g') ^ 2 / (nrm g * nrm g') * (√(Ures (a / nrm g)) * √(Ures (a' / nrm g'))) := by
  set σ := nrm g with hσd
  set σ' := nrm g' with hσd'
  set ρ := (g ⬝ᵥ g') / (σ * σ') with hρd
  have hσ0 : 0 ≤ σ := nrm_nonneg g
  have hσ0' : 0 ≤ σ' := nrm_nonneg g'
  have s1 : ∑ x, g x * g x = σ ^ 2 := by
    rw [hσd, nrm_sq]; unfold normSq; exact Finset.sum_congr rfl fun i _ => by ring
  have s4 : ∑ x, g' x * g' x = σ' ^ 2 := by
    rw [hσd', nrm_sq]; unfold normSq; exact Finset.sum_congr rfl fun i _ => by ring
  have hCS : (g ⬝ᵥ g') ^ 2 ≤ (σ * σ') ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g g'
    rw [mul_pow, hσd, hσd', nrm_sq, nrm_sq]
    exact this
  have hdot : σ * σ' * ρ = g ⬝ᵥ g' := by
    by_cases h0 : σ * σ' = 0
    · rw [h0, zero_pow two_ne_zero] at hCS
      have : g ⬝ᵥ g' = 0 := by nlinarith [sq_nonneg (g ⬝ᵥ g')]
      rw [this, h0, zero_mul]
    · rw [hρd, mul_div_assoc']; exact mul_div_cancel_left₀ _ h0
  have hρ2 : ρ ^ 2 ≤ 1 := by
    by_cases h0 : σ * σ' = 0
    · rw [hρd, h0, div_zero]; norm_num
    · rw [hρd, div_pow, div_le_one (by positivity)]; exact hCS
  have hρ : |ρ| ≤ 1 := (sq_le_one_iff_abs_le_one ρ).mp hρ2
  have hsq : √(1 - ρ ^ 2) ^ 2 = 1 - ρ ^ 2 := Real.sq_sqrt (by linarith)
  have s2 : ∑ x, g x * g' x = σ * σ' * ρ := by rw [hdot]; rfl
  have s3 : ∑ x, g' x * g x = σ * σ' * ρ := by
    rw [← s2]; exact Finset.sum_congr rfl fun i _ => by ring
  have law : ∫ z, relu (a + z ⬝ᵥ g) * relu (a' + z ⬝ᵥ g') ∂stdGauss (Fin m) =
      ∫ p : ℝ × ℝ, relu (a + σ * p.1) * relu (a' + σ' * (ρ * p.1 + √(1 - ρ ^ 2) * p.2))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    let A : Matrix (Fin 2) (Fin m) ℝ := Matrix.of ![g, g']
    let B : Matrix (Fin 2) (Fin 2) ℝ := !![σ, 0; σ' * ρ, σ' * √(1 - ρ ^ 2)]
    have hAB : A * A.transpose = B * B.transpose := by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [A, B, Matrix.mul_apply, Fin.sum_univ_two, s1, s2, s3, s4] <;> nlinarith
    have hl := gaussLin105 (Fin m) (Fin 2) (Fin 2) A B hAB
    let H : (Fin 2 → ℝ) → ℝ := fun y => relu (a + y 0) * relu (a' + y 1)
    have hH : Measurable H :=
      (measurable_relu.comp (measurable_const.add (measurable_pi_apply 0))).mul
        (measurable_relu.comp (measurable_const.add (measurable_pi_apply 1)))
    let G : ℝ × ℝ → ℝ := fun p =>
      relu (a + σ * p.1) * relu (a' + σ' * (ρ * p.1 + √(1 - ρ ^ 2) * p.2))
    have e1 : ∫ z, relu (a + z ⬝ᵥ g) * relu (a' + z ⬝ᵥ g') ∂stdGauss (Fin m) =
        ∫ z, H (A.mulVec z) ∂stdGauss (Fin m) := by
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp [H, A, dotProduct_comm]
    have e2 : ∫ z, H (A.mulVec z) ∂stdGauss (Fin m) =
        ∫ η, H (B.mulVec η) ∂stdGauss (Fin 2) := by
      rw [← integral_map (φ := fun ξ => A.mulVec ξ) (by fun_prop) hH.aestronglyMeasurable, hl,
        integral_map (φ := fun ξ => B.mulVec ξ) (by fun_prop) hH.aestronglyMeasurable]
    have e3 : ∫ η, H (B.mulVec η) ∂stdGauss (Fin 2) =
        ∫ p, G p ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
      have h := (measurePreserving_finTwoArrow (gaussianReal 0 1)).integral_comp' G
      rw [← h]
      refine integral_congr_ae (Eventually.of_forall fun η => ?_)
      show H (B.mulVec η) = G (η 0, η 1)
      have b0 : B.mulVec η 0 = σ * η 0 := by
        simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      have b1 : B.mulVec η 1 = σ' * (ρ * η 0 + √(1 - ρ ^ 2) * η 1) := by
        simp [B, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
        ring
      show relu (a + B.mulVec η 0) * relu (a' + B.mulVec η 1) = _
      rw [b0, b1]
    rw [e1, e2, e3]
  rw [law]
  rcases (mul_nonneg hσ0 hσ0').eq_or_lt with h0 | hpos
  · have hρ0 : ρ = 0 := by rw [hρd, ← h0, div_zero]
    have hd0 : g ⬝ᵥ g' = 0 := by rw [← hdot, hρ0, mul_zero]
    have e : ∫ p : ℝ × ℝ, relu (a + σ * p.1) * relu (a' + σ' * (ρ * p.1 + √(1 - ρ ^ 2) * p.2))
        ∂((gaussianReal 0 1).prod (gaussianReal 0 1)) = psiS σ a * psiS σ' a' := by
      rw [hρ0]
      simp only [zero_mul, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        sub_zero, Real.sqrt_one, one_mul]
      exact integral_prod_mul (fun z => relu (a + σ * z)) (fun z => relu (a' + σ' * z))
    rw [e, hd0]
    simp
  · have hσ : 0 < σ := by
      rcases hσ0.eq_or_lt with h | h
      · rw [← h, zero_mul] at hpos; exact absurd hpos (lt_irrefl _)
      · exact h
    have hσ' : 0 < σ' := by
      rcases hσ0'.eq_or_lt with h | h
      · rw [← h, mul_zero] at hpos; exact absurd hpos (lt_irrefl _)
      · exact h
    have h := (abs_le.mp (PR_scalar hρ a a' hσ hσ')).2
    have e : (g ⬝ᵥ g') ^ 2 / (σ * σ') = ρ ^ 2 * σ * σ' := by
      rw [← hdot]; field_simp
    rw [e, ← hdot]
    linarith

/-- **Lemma PR⁺ for two linear forms**: the remainder is at most
`K₀·⟨g, g′⟩²/(|g||g′|)·exp(−((a/|g|)² + (a′/|g′|)²)/4)`. -/
theorem PRvec_exp (m : ℕ) (g g' : Fin m → ℝ) (a a' : ℝ) :
    ∫ z, relu (a + z ⬝ᵥ g) * relu (a' + z ⬝ᵥ g') ∂stdGauss (Fin m) -
        psiS (nrm g) a * psiS (nrm g') a' ≤
      (g ⬝ᵥ g') * PhiG (a / nrm g) * PhiG (a' / nrm g') +
        (g ⬝ᵥ g') ^ 2 / (nrm g * nrm g') *
          (K0 * rexp (-((a / nrm g) ^ 2 + (a' / nrm g') ^ 2) / 4)) := by
  refine (PRvecU m g g' a a').trans ?_
  have h0 : 0 ≤ (g ⬝ᵥ g') ^ 2 / (nrm g * nrm g') :=
    div_nonneg (sq_nonneg _) (mul_nonneg (nrm_nonneg _) (nrm_nonneg _))
  have := mul_le_mul_of_nonneg_left (sqrt_Ures_mul_le (a / nrm g) (a' / nrm g')) h0
  linarith

end BstLean.Part160

open BstLean.Part160 in
#print axioms PRvecU
open BstLean.Part160 in
#print axioms PRvec_exp
