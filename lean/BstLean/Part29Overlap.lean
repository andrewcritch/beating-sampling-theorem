import Mathlib

/-!
# Part 29, layer L4 (F3a): the overlap count and Chebyshev for the parity floor

`proofs/option-m/28-explicit-22.tex`, Lemma (the repair of part 20's probability bound). The parity floor is
`Y ∝ Σ_S X_S` over the four-subsets `S` of `Fin n`, with `X_S = C_S²`. If `E X_S = m` and the covariance of
`X_S, X_T` depends only on `j = |S ∩ T|` (value `c j`, zero for `j ≤ 1`), then `Var Σ X_S` is
`C(n,4) (c 4 + 4 (n−4) c 3 + 6 C(n−4,2) c 2)`, and Chebyshev at half the mean gives the failure bound.
The Gaussian values of `m` and `c` (`12 v`, `288 v² + 288 r`, `96 r`, `32 r`) are hypotheses here.
-/

namespace BstLean.Part29

open MeasureTheory

private theorem overlap_fixed (n j : ℕ) (hj : j ≤ 4) (S : Finset (Fin n))
    (hS : S.card = 4) :
    ((Finset.univ.powersetCard 4).filter
      (fun T : Finset (Fin n) => (S ∩ T).card = j)).card =
      Nat.choose 4 j * (n - 4).choose (4 - j) := by
  classical
  have hbij : ((Finset.univ.powersetCard 4).filter
      (fun T : Finset (Fin n) => (S ∩ T).card = j)).card =
      (S.powersetCard j ×ˢ (Finset.univ \ S).powersetCard (4 - j)).card := by
    apply Finset.card_bij (fun T _ => (S ∩ T, T \ S))
    · intro T hT
      obtain ⟨hT, hST⟩ := Finset.mem_filter.mp hT
      have hTc := (Finset.mem_powersetCard.mp hT).2
      simp only [Finset.mem_product, Finset.mem_powersetCard]
      refine ⟨⟨Finset.inter_subset_left, hST⟩, ⟨?_, ?_⟩⟩
      · intro x hx
        simp only [Finset.mem_sdiff] at hx ⊢
        exact ⟨Finset.mem_univ _, hx.2⟩
      · rw [Finset.card_sdiff, hST, hTc]
    · intro T hT U hU h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      apply Finset.ext
      intro x
      have hi : (x ∈ S ∧ x ∈ T) ↔ (x ∈ S ∧ x ∈ U) := by
        simpa only [Finset.mem_inter] using (congrArg (fun V => x ∈ V) h1).to_iff
      have hd : (x ∈ T ∧ x ∉ S) ↔ (x ∈ U ∧ x ∉ S) := by
        simpa only [Finset.mem_sdiff] using (congrArg (fun V => x ∈ V) h2).to_iff
      tauto
    · rintro ⟨A, B⟩ hAB
      obtain ⟨⟨hAS, hAc⟩, hBU, hBc⟩ :=
        (Finset.mem_product.mp hAB).imp Finset.mem_powersetCard.mp Finset.mem_powersetCard.mp
      have hdis : Disjoint A B := by
        apply Finset.disjoint_left.mpr
        intro x hxA hxB
        exact (Finset.mem_sdiff.mp (hBU hxB)).2 (hAS hxA)
      have hi : S ∩ (A ∪ B) = A := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_union]
        have hb : x ∈ B → x ∉ S := fun hx => (Finset.mem_sdiff.mp (hBU hx)).2
        have ha : x ∈ A → x ∈ S := fun hx => hAS hx
        tauto
      have hd : (A ∪ B) \ S = B := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_union]
        have hb : x ∈ B → x ∉ S := fun hx => (Finset.mem_sdiff.mp (hBU hx)).2
        have ha : x ∈ A → x ∈ S := fun hx => hAS hx
        tauto
      refine ⟨A ∪ B, ?_, Prod.ext hi hd⟩
      simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
      rw [Finset.card_union_of_disjoint hdis, hAc, hBc, hi, hAc]
      exact ⟨by omega, rfl⟩
  rw [hbij, Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
    hS, Finset.card_sdiff_of_subset (Finset.subset_univ S)]
  simp [hS]

/-- The number of ordered pairs of four-subsets of `Fin n` with overlap `j`:
`C(n,4) · C(4,j) · C(n−4, 4−j)`. -/
theorem overlap_count (n j : ℕ) (hj : j ≤ 4) :
    ((Finset.univ.powersetCard 4 ×ˢ Finset.univ.powersetCard 4).filter
        (fun p : Finset (Fin n) × Finset (Fin n) => (p.1 ∩ p.2).card = j)).card =
      n.choose 4 * (Nat.choose 4 j * (n - 4).choose (4 - j)) := by
  classical
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  have hfixed : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard 4,
      (∑ T ∈ Finset.univ.powersetCard 4, if (S ∩ T).card = j then 1 else 0) =
        Nat.choose 4 j * (n - 4).choose (4 - j) := by
    intro S hS
    rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
    exact overlap_fixed n j hj S (Finset.mem_powersetCard.mp hS).2
  rw [Finset.sum_congr rfl hfixed, Finset.sum_const]
  simp

variable {Ω : Type*} [MeasurableSpace Ω]

private theorem weighted_overlap (n : ℕ) (S : Finset (Fin n)) (hS : S.card = 4)
    (c : ℕ → ℝ) (hc0 : c 0 = 0) (hc1 : c 1 = 0) :
    (∑ T ∈ Finset.univ.powersetCard 4, c (S ∩ T).card) =
      c 4 + 4 * (n - 4 : ℕ) * c 3 + 6 * ((n - 4).choose 2) * c 2 := by
  classical
  have hpoint : ∀ T : Finset (Fin n), c (S ∩ T).card =
      (if (S ∩ T).card = 4 then c 4 else 0) +
      (if (S ∩ T).card = 3 then c 3 else 0) +
      (if (S ∩ T).card = 2 then c 2 else 0) := by
    intro T
    have hle : (S ∩ T).card ≤ 4 := hS ▸ Finset.card_le_card Finset.inter_subset_left
    interval_cases h : (S ∩ T).card <;> simp [hc0, hc1]
  simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [overlap_fixed n 4 (by omega) S hS, overlap_fixed n 3 (by omega) S hS,
    overlap_fixed n 2 (by omega) S hS]
  norm_num [Nat.choose]

/-- **The variance of the sum**, from the overlap-dependent covariances. -/
theorem var_sum_overlap (n : ℕ) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Finset (Fin n) → Ω → ℝ) (m : ℝ) (c : ℕ → ℝ)
    (hX2 : ∀ S T, Integrable (fun ω => X S ω * X T ω) P) (hX : ∀ S, Integrable (X S) P)
    (hmean : ∀ S, ∫ ω, X S ω ∂P = m)
    (hcov : ∀ S ∈ Finset.univ.powersetCard 4, ∀ T ∈ Finset.univ.powersetCard 4,
      ∫ ω, X S ω * X T ω ∂P - m ^ 2 = c (S ∩ T).card)
    (hc0 : c 0 = 0) (hc1 : c 1 = 0) :
    ∫ ω, (∑ S ∈ Finset.univ.powersetCard 4, X S ω - n.choose 4 * m) ^ 2 ∂P =
      n.choose 4 * (c 4 + 4 * (n - 4 : ℕ) * c 3 + 6 * ((n - 4).choose 2) * c 2) := by
  classical
  have hLp : ∀ S, MemLp (X S) 2 P := by
    intro S
    apply (memLp_two_iff_integrable_sq (hX S).aestronglyMeasurable).mpr
    simpa only [pow_two] using hX2 S S
  have hsum : MemLp (fun ω => ∑ S ∈ Finset.univ.powersetCard 4, X S ω) 2 P := by
    exact memLp_finsetSum (Finset.univ.powersetCard 4) (fun S _ => hLp S)
  have hmeanSum : (∫ ω, (∑ S ∈ Finset.univ.powersetCard 4, X S ω) ∂P) =
      n.choose 4 * m := by
    rw [integral_finsetSum _ (fun S _ => hX S)]
    simp [hmean]
  rw [← hmeanSum, ← ProbabilityTheory.variance_eq_integral hsum.aemeasurable]
  rw [ProbabilityTheory.variance_fun_sum' (fun S _ => hLp S)]
  have hcov' : ∀ S ∈ Finset.univ.powersetCard 4, ∀ T ∈ Finset.univ.powersetCard 4,
      ProbabilityTheory.covariance (X S) (X T) P = c (S ∩ T).card := by
    intro S hS T hT
    rw [ProbabilityTheory.covariance_eq_sub (hLp S) (hLp T), hmean, hmean]
    simpa only [Pi.mul_apply, pow_two] using hcov S hS T hT
  calc
    (∑ S ∈ Finset.univ.powersetCard 4,
        ∑ T ∈ Finset.univ.powersetCard 4, ProbabilityTheory.covariance (X S) (X T) P) =
        ∑ S ∈ Finset.univ.powersetCard 4,
          (c 4 + 4 * (n - 4 : ℕ) * c 3 + 6 * ((n - 4).choose 2) * c 2) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.sum_congr rfl (fun T hT => hcov' S hS T hT)]
      exact weighted_overlap n S (Finset.mem_powersetCard.mp hS).2 c hc0 hc1
    _ = _ := by simp; ring

/-- **The failure bound of the parity floor.** With the Gaussian values `m = 12 v`, `c 4 = 288 v² + 288 r`,
`c 3 = 96 r`, `c 2 = 32 r`, `0 ≤ r ≤ v²`, `v > 0`, the probability that the sum falls below half its mean is at most
`(16 + (32/3)(n−4) + (16/3) C(n−4,2)) / C(n,4)`, part 28's `η'ₙ`. -/
theorem floor_failure (n : ℕ) (hn : 4 ≤ n) (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Finset (Fin n) → Ω → ℝ) (v r : ℝ) (hv : 0 < v) (hr : 0 ≤ r) (hrv : r ≤ v ^ 2)
    (hX2 : ∀ S T, Integrable (fun ω => X S ω * X T ω) P) (hX : ∀ S, Integrable (X S) P)
    (hXm : ∀ S, AEMeasurable (X S) P)
    (hmean : ∀ S, ∫ ω, X S ω ∂P = 12 * v)
    (hcov : ∀ S ∈ Finset.univ.powersetCard 4, ∀ T ∈ Finset.univ.powersetCard 4,
      ∫ ω, X S ω * X T ω ∂P - (12 * v) ^ 2 =
        if (S ∩ T).card = 4 then 288 * v ^ 2 + 288 * r
        else if (S ∩ T).card = 3 then 96 * r
        else if (S ∩ T).card = 2 then 32 * r else 0) :
    P {ω | ∑ S ∈ Finset.univ.powersetCard 4, X S ω < n.choose 4 * (12 * v) / 2} ≤
      ENNReal.ofReal ((16 + 32 / 3 * (n - 4 : ℝ) + 16 / 3 * ((n - 4).choose 2 : ℝ)) / n.choose 4) := by
  classical
  let A : Finset (Finset (Fin n)) := Finset.univ.powersetCard 4
  let Y : Ω → ℝ := fun ω => ∑ S ∈ A, X S ω
  let c : ℕ → ℝ := fun j => if j = 4 then 288 * v ^ 2 + 288 * r
    else if j = 3 then 96 * r else if j = 2 then 32 * r else 0
  have hLp : ∀ S, MemLp (X S) 2 P := by
    intro S
    apply (memLp_two_iff_integrable_sq (hXm S).aestronglyMeasurable).mpr
    simpa only [pow_two] using hX2 S S
  have hY : MemLp Y 2 P := by
    exact memLp_finsetSum A (fun S _ => hLp S)
  have hmeanY : (∫ ω, Y ω ∂P) = n.choose 4 * (12 * v) := by
    dsimp [Y]
    rw [integral_finsetSum _ (fun S _ => hX S)]
    simp [hmean, A]
  have hVar : ProbabilityTheory.variance Y P =
      n.choose 4 * (288 * v ^ 2 + 288 * r +
        4 * (n - 4 : ℕ) * (96 * r) + 6 * ((n - 4).choose 2) * (32 * r)) := by
    rw [ProbabilityTheory.variance_eq_integral hY.aemeasurable, hmeanY]
    have h := var_sum_overlap n P X (12 * v) c hX2 hX hmean hcov
      (by simp [c]) (by simp [c])
    simpa [c, Y, A] using h
  have hN : (0 : ℝ) < n.choose 4 := by exact_mod_cast Nat.choose_pos hn
  have hhalf : 0 < (n.choose 4 : ℝ) * (12 * v) / 2 := by positivity
  have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq hY hhalf
  have hsub : {ω | Y ω < n.choose 4 * (12 * v) / 2} ⊆
      {ω | n.choose 4 * (12 * v) / 2 ≤ |Y ω - ∫ ω, Y ω ∂P|} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq] at hω ⊢
    rw [hmeanY]
    have hneg : Y ω - n.choose 4 * (12 * v) ≤ 0 := by linarith
    rw [abs_of_nonpos hneg]
    linarith
  have hcast : ((n - 4 : ℕ) : ℝ) = (n : ℝ) - 4 := by
    exact_mod_cast Nat.cast_sub hn (R := ℝ)
  have hbound : ProbabilityTheory.variance Y P /
      ((n.choose 4 : ℝ) * (12 * v) / 2) ^ 2 ≤
      (16 + 32 / 3 * (n - 4 : ℝ) + 16 / 3 * ((n - 4).choose 2 : ℝ)) / n.choose 4 := by
    rw [hVar]
    have hK : (0 : ℝ) ≤ (n - 4 : ℕ) := Nat.cast_nonneg _
    have hC : (0 : ℝ) ≤ (n - 4).choose 2 := Nat.cast_nonneg _
    rw [div_le_div_iff₀ (sq_pos_of_pos hhalf) hN]
    rw [← hcast]
    have hkr : 0 ≤ ((n - 4 : ℕ) : ℝ) * (v ^ 2 - r) := mul_nonneg hK (sub_nonneg.mpr hrv)
    have hcr : 0 ≤ ((n - 4).choose 2 : ℝ) * (v ^ 2 - r) := mul_nonneg hC (sub_nonneg.mpr hrv)
    have hdiff : 0 ≤ (v ^ 2 - r) *
        (288 + 384 * ((n - 4 : ℕ) : ℝ) + 192 * ((n - 4).choose 2 : ℝ)) := by
      nlinarith [hr]
    have hdiffN := mul_nonneg (sq_nonneg (n.choose 4 : ℝ)) hdiff
    nlinarith
  exact (measure_mono hsub).trans (hcheb.trans (ENNReal.ofReal_le_ofReal hbound))

end BstLean.Part29
