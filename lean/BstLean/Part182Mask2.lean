import BstLean.Part182Mask
import BstLean.Part182Norm
import BstLean.Part153PP

/-!
# Part 182 (file `Mask2`): the second-layer mask overlap of Lemma TI on the joint Agent weights

No proof is left open; no `native_decide` or `axiom` is used.

Paper: Lemma `t7:p04:ti`, tail table row "second marginal masks; second intersection count": given
`A₁` with `a = ReLU(A₁x) ≠ 0`, `a' = ReLU(A₁x') ≠ 0` and `q = cos(a, a') ≤ c₁⁺`, the count
`tr(D₂D₂') = #{i : (A₂a)_i > 0, (A₂a')_i > 0}` is at most `m(κ̇(c₁⁺)/2 + η)` except with
probability `e^{−2η²m}`.

* **`mask_second_joint`**: the bound under the joint distribution `nuA n` of `(A₁, A₂)` (Fubini
  over `A₁`, Fork E's `mask_second` for each fixed `A₁`).
* **`mask_second_tail`**: with Fork F's `nm_overlap_tail` (the first-layer event `q ≤ c₁⁺`, five
  tails): `Pr(tr(D₂D₂') > m(κ̇(c₁⁺)/2 + η)) ≤ 5e^{−τ} + e^{−2η²m}`.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (mask measurable_mask)
open BstLean.Part153 (nrm nuA)

variable {n : ℕ}

/-- The cosine of the two first-layer vectors. -/
noncomputable def cosA (x x' : Fin n → ℝ) (A : Matrix (Fin (mA n)) (Fin n) ℝ) : ℝ :=
  (reluV (A *ᵥ x) ⬝ᵥ reluV (A *ᵥ x')) / (nmA x A * nmA x' A)

/-- The second-layer overlap count. -/
noncomputable def cnt2 (x x' : Fin n → ℝ) (θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
    Matrix (Fin (mA n)) (Fin (mA n)) ℝ) : ℝ :=
  ∑ i, mask ((θ.2 *ᵥ reluV (θ.1 *ᵥ x)) i) * mask ((θ.2 *ᵥ reluV (θ.1 *ᵥ x')) i)

lemma measurable_nmA (x : Fin n → ℝ) :
    Measurable (fun A : Matrix (Fin (mA n)) (Fin n) ℝ => nmA x A) := by
  unfold nmA nrm normSq reluV relu
  fun_prop

lemma measurable_cosA (x x' : Fin n → ℝ) : Measurable (cosA x x') := by
  unfold cosA
  refine Measurable.div ?_ ((measurable_nmA x).mul (measurable_nmA x'))
  unfold reluV relu
  simp only [dotProduct]
  fun_prop

lemma measurable_cnt2 (x x' : Fin n → ℝ) : Measurable (cnt2 x x') := by
  unfold cnt2
  refine Finset.measurable_sum _ fun i _ => ?_
  have h1 : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => (θ.2 *ᵥ reluV (θ.1 *ᵥ x)) i) := by
    unfold reluV relu; simp only [Matrix.mulVec, dotProduct]; fun_prop
  have h2 : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ => (θ.2 *ᵥ reluV (θ.1 *ᵥ x')) i) := by
    unfold reluV relu; simp only [Matrix.mulVec, dotProduct]; fun_prop
  exact (measurable_mask.comp h1).mul (measurable_mask.comp h2)

/-- **The second-layer overlap under `nuA`**, on the first-layer event `a, a' ≠ 0`,
`cos(a, a') ≤ q₊`. -/
theorem mask_second_joint (x x' : Fin n → ℝ) {qp η : ℝ} (hqp : qp ≤ 1) (hη : 0 ≤ η) :
    (nuA n).real {θ | 0 < nmA x θ.1 ∧ 0 < nmA x' θ.1 ∧ cosA x x' θ.1 ≤ qp ∧
      ((mA n : ℕ) : ℝ) * (kdot qp / 2 + η) < cnt2 x x' θ} ≤
      exp (-2 * η ^ 2 * (mA n : ℕ)) := by
  classical
  have hP1 : IsProbabilityMeasure (gaussMat (mA n) n (2 / (n : ℝ))) := by
    unfold gaussMat; infer_instance
  have hP2 : IsProbabilityMeasure (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) := by
    unfold gaussMat; infer_instance
  set S := {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      0 < nmA x θ.1 ∧ 0 < nmA x' θ.1 ∧ cosA x x' θ.1 ≤ qp ∧
      ((mA n : ℕ) : ℝ) * (kdot qp / 2 + η) < cnt2 x x' θ} with hS
  have hSm : MeasurableSet S := by
    have h1 : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
        Matrix (Fin (mA n)) (Fin (mA n)) ℝ => nmA x θ.1) := (measurable_nmA x).comp measurable_fst
    have h2 : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
        Matrix (Fin (mA n)) (Fin (mA n)) ℝ => nmA x' θ.1) := (measurable_nmA x').comp measurable_fst
    have h3 : Measurable (fun θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
        Matrix (Fin (mA n)) (Fin (mA n)) ℝ => cosA x x' θ.1) :=
      (measurable_cosA x x').comp measurable_fst
    exact (measurableSet_lt measurable_const h1).inter ((measurableSet_lt measurable_const h2).inter
      ((measurableSet_le h3 measurable_const).inter
        (measurableSet_lt measurable_const (measurable_cnt2 x x'))))
  have hB : 0 ≤ exp (-2 * η ^ 2 * (mA n : ℕ)) := (exp_pos _).le
  rw [Measure.real]
  unfold nuA
  rw [Measure.prod_apply hSm]
  have hle : ∫⁻ A, (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) (Prod.mk A ⁻¹' S)
      ∂gaussMat (mA n) n (2 / (n : ℝ)) ≤
      ∫⁻ _A, ENNReal.ofReal (exp (-2 * η ^ 2 * (mA n : ℕ))) ∂gaussMat (mA n) n (2 / (n : ℝ)) := by
    refine lintegral_mono fun A => ?_
    by_cases hA : 0 < nmA x A ∧ 0 < nmA x' A ∧ cosA x x' A ≤ qp
    · obtain ⟨h1, h2, h3⟩ := hA
      have ha : reluV (A *ᵥ x) ≠ 0 := by
        intro h0; rw [nmA, h0] at h1; simp [nrm, normSq] at h1
      have ha' : reluV (A *ᵥ x') ≠ 0 := by
        intro h0; rw [nmA, h0] at h2; simp [nrm, normSq] at h2
      have hq : (∑ j, reluV (A *ᵥ x) j * reluV (A *ᵥ x') j) /
          (√(normSq (reluV (A *ᵥ x))) * √(normSq (reluV (A *ᵥ x')))) ≤ qp := h3
      have hm := mask_second ha ha' hq hqp hη
      have e : Prod.mk A ⁻¹' S = {B | ((mA n : ℕ) : ℝ) * (kdot qp / 2 + η) <
          ∑ i, mask ((B *ᵥ reluV (A *ᵥ x)) i) * mask ((B *ᵥ reluV (A *ᵥ x')) i)} := by
        ext B
        simp only [hS, Set.mem_preimage, Set.mem_setOf_eq, cnt2]
        constructor
        · intro h; exact h.2.2.2
        · intro h; exact ⟨h1, h2, h3, h⟩
      rw [e, ← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal hm
    · have e : Prod.mk A ⁻¹' S = ∅ := by
        ext B
        simp only [hS, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hA ⟨h.1, h.2.1, h.2.2.1⟩
      rw [e, measure_empty]
      exact bot_le
  rw [lintegral_const, measure_univ, mul_one] at hle
  calc (∫⁻ A, (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) (Prod.mk A ⁻¹' S)
        ∂gaussMat (mA n) n (2 / (n : ℝ))).toReal
      ≤ (ENNReal.ofReal (exp (-2 * η ^ 2 * (mA n : ℕ)))).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
    _ = exp (-2 * η ^ 2 * (mA n : ℕ)) := ENNReal.toReal_ofReal hB

/-- **The second-layer overlap tail of Lemma TI**: with the first-layer event of Fork F
(`nm_overlap_tail`: `a, a' ≠ 0`, `cos(a, a') ≤ c₁⁺`, five tails `e^{−τ}`),
`Pr_{A₁,A₂}(tr(D₂D₂') > m(κ̇(c₁⁺)/2 + η)) ≤ 5e^{−τ} + e^{−2η²m}`. Here `c₁⁺ = (2a₊² − d₋²)/(2a₋²)`
with the paper's `a₊`, `a₋`, `d₋` (at the pair's own `κ(x·x')`). -/
theorem mask_second_tail (hn : 1 ≤ n) {x x' : Fin n → ℝ} (hx : normSq x = 1)
    (hx' : normSq x' = 1) {τ η : ℝ} (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (ham : 0 < √((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ)))
    (hdm : 0 ≤ √(2 * n * (1 - kappa (x ⬝ᵥ x')) - 4 * (2 / n)) - 2 * (√(2 * τ) * √(2 / (n : ℝ))))
    (h6 : (√(2 * n * (1 - kappa (x ⬝ᵥ x')) - 4 * (2 / n)) - 2 * (√(2 * τ) * √(2 / (n : ℝ)))) ^ 2 ≤
      2 * (√(n : ℝ) + √(2 * τ) * √(2 / (n : ℝ))) ^ 2)
    (hc1 : (2 * (√(n : ℝ) + √(2 * τ) * √(2 / (n : ℝ))) ^ 2 -
            (√(2 * n * (1 - kappa (x ⬝ᵥ x')) - 4 * (2 / n)) -
              2 * (√(2 * τ) * √(2 / (n : ℝ)))) ^ 2) /
          (2 * (√((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ))) ^ 2) ≤ 1) :
    (nuA n).real {θ | ((mA n : ℕ) : ℝ) * (kdot ((2 * (√(n : ℝ) + √(2 * τ) * √(2 / (n : ℝ))) ^ 2 -
            (√(2 * n * (1 - kappa (x ⬝ᵥ x')) - 4 * (2 / n)) -
              2 * (√(2 * τ) * √(2 / (n : ℝ)))) ^ 2) /
          (2 * (√((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ))) ^ 2)) / 2 + η) < cnt2 x x' θ} ≤
      5 * exp (-τ) + exp (-2 * η ^ 2 * (mA n : ℕ)) := by
  classical
  have hP1 : IsProbabilityMeasure (gaussMat (mA n) n (2 / (n : ℝ))) := by
    unfold gaussMat; infer_instance
  have hP2 : IsProbabilityMeasure (gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ))) := by
    unfold gaussMat; infer_instance
  set c1 := (2 * (√(n : ℝ) + √(2 * τ) * √(2 / (n : ℝ))) ^ 2 -
            (√(2 * n * (1 - kappa (x ⬝ᵥ x')) - 4 * (2 / n)) -
              2 * (√(2 * τ) * √(2 / (n : ℝ)))) ^ 2) /
          (2 * (√((n : ℝ) - 2 / n) - √(2 * τ) * √(2 / (n : ℝ))) ^ 2) with hc1d
  set Bad := {M : Matrix (Fin (mA n)) (Fin n) ℝ | ¬ (0 < nmA x M ∧ 0 < nmA x' M ∧
        (reluV (M *ᵥ x) ⬝ᵥ reluV (M *ᵥ x')) / (nmA x M * nmA x' M) ≤ c1)} with hBad
  have hfirst := nm_overlap_tail hn hx hx' hτ ham hdm h6
  rw [← hc1d] at hfirst
  have hBm : MeasurableSet Bad := by
    have h1 := measurable_nmA (n := n) x
    have h2 := measurable_nmA (n := n) x'
    have h3 := measurable_cosA (n := n) x x'
    exact ((measurableSet_lt measurable_const h1).inter ((measurableSet_lt measurable_const h2).inter
      (measurableSet_le h3 measurable_const))).compl
  have hsub : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      ((mA n : ℕ) : ℝ) * (kdot c1 / 2 + η) < cnt2 x x' θ} ⊆
      (Bad ×ˢ Set.univ) ∪ {θ | 0 < nmA x θ.1 ∧ 0 < nmA x' θ.1 ∧ cosA x x' θ.1 ≤ c1 ∧
        ((mA n : ℕ) : ℝ) * (kdot c1 / 2 + η) < cnt2 x x' θ} := by
    intro θ hθ
    by_cases h : θ.1 ∈ Bad
    · exact Or.inl ⟨h, Set.mem_univ _⟩
    · right
      simp only [hBad, Set.mem_setOf_eq, not_not] at h
      exact ⟨h.1, h.2.1, h.2.2, hθ⟩
  have hprod : (nuA n).real (Bad ×ˢ Set.univ) = (gaussMat (mA n) n (2 / (n : ℝ))).real Bad := by
    unfold nuA
    rw [Measure.real, Measure.prod_prod, measure_univ, mul_one]
    rfl
  calc (nuA n).real {θ | ((mA n : ℕ) : ℝ) * (kdot c1 / 2 + η) < cnt2 x x' θ}
      ≤ (nuA n).real ((Bad ×ˢ Set.univ) ∪ {θ | 0 < nmA x θ.1 ∧ 0 < nmA x' θ.1 ∧
          cosA x x' θ.1 ≤ c1 ∧ ((mA n : ℕ) : ℝ) * (kdot c1 / 2 + η) < cnt2 x x' θ}) :=
        measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ (nuA n).real (Bad ×ˢ Set.univ) + (nuA n).real {θ | 0 < nmA x θ.1 ∧ 0 < nmA x' θ.1 ∧
          cosA x x' θ.1 ≤ c1 ∧ ((mA n : ℕ) : ℝ) * (kdot c1 / 2 + η) < cnt2 x x' θ} :=
        measureReal_union_le _ _
    _ ≤ 5 * exp (-τ) + exp (-2 * η ^ 2 * (mA n : ℕ)) := by
        rw [hprod]
        exact add_le_add hfirst (mask_second_joint x x' hc1 hη)

end BstLean.Part182

open BstLean.Part182 in
#print axioms mask_second_joint
open BstLean.Part182 in
#print axioms mask_second_tail
