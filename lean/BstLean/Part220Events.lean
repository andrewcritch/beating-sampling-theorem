import BstLean.Part216Weighted

/-! Weighted Markov events use one distribution and one charge per field. -/
namespace BstLean.Part220
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

variable {G Y : Type*} [MeasurableSpace G] [MeasurableSpace Y]

def momentBad (ν : Measure G) (error : G → Y → ℝ) (k : ℕ) (A : ℝ) : Set Y :=
  {y | ENNReal.ofReal (A ^ k) < ∫⁻ g, ENNReal.ofReal (|error g y| ^ k) ∂ν}

theorem measurableSet_momentBad (ν : Measure G) [SFinite ν]
    {error : G → Y → ℝ} (hm : Measurable (Function.uncurry error)) (k : ℕ) (A : ℝ) :
    MeasurableSet (momentBad ν error k A) :=
  measurableSet_lt measurable_const
    (((hm.abs.pow_const k).ennreal_ofReal).lintegral_prod_left)

/-- A finite collection of fields has a sum of Markov prices.
All fields use the same distribution. No independence premise enters the union. -/
theorem finite_weighted_markov {I : Type*} [Fintype I]
    (ν : Measure G) [SFinite ν] (σ : Measure Y) [IsProbabilityMeasure σ]
    (error : I → G → Y → ℝ) (k : I → ℕ) (B A : I → ℝ)
    (hm : ∀ i, Measurable (Function.uncurry (error i)))
    (hk : ∀ i, k i ≠ 0) (hB : ∀ i, 0 ≤ B i) (hA : ∀ i, 0 < A i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ y, ENNReal.ofReal (|error i g y| ^ k i) ∂σ ∂ν ≤
      ENNReal.ofReal (B i ^ k i)) :
    σ (⋃ i, momentBad ν (error i) (k i) (A i)) ≤
      ENNReal.ofReal (∑ i, (B i / A i) ^ k i) := by
  refine (measure_iUnion_le _).trans ?_
  rw [tsum_fintype]
  calc
    (∑ i, σ (momentBad ν (error i) (k i) (A i))) ≤
        ∑ i, ENNReal.ofReal ((B i / A i) ^ k i) := by
      exact Finset.sum_le_sum fun i _ =>
        BstLean.Part216.weighted_moment_charge (hm i) (hk i) (hB i) (hA i) (hM i)
    _ = _ := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro i _
      exact pow_nonneg (div_nonneg (hB i) (hA i).le) _

/-- The finite Markov price is also a real probability bound. -/
theorem finite_weighted_markov_real {I : Type*} [Fintype I]
    (ν : Measure G) [SFinite ν] (σ : Measure Y) [IsProbabilityMeasure σ]
    (error : I → G → Y → ℝ) (k : I → ℕ) (B A : I → ℝ)
    (hm : ∀ i, Measurable (Function.uncurry (error i)))
    (hk : ∀ i, k i ≠ 0) (hB : ∀ i, 0 ≤ B i) (hA : ∀ i, 0 < A i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ y, ENNReal.ofReal (|error i g y| ^ k i) ∂σ ∂ν ≤
      ENNReal.ofReal (B i ^ k i)) :
    σ.real (⋃ i, momentBad ν (error i) (k i) (A i)) ≤
      ∑ i, (B i / A i) ^ k i := by
  exact ENNReal.toReal_le_of_le_ofReal
    (Finset.sum_nonneg fun i _ => pow_nonneg (div_nonneg (hB i) (hA i).le) _)
    (finite_weighted_markov ν σ error k B A hm hk hB hA hM)

def biasOrder (i : Fin 4) : ℕ := ![24, 16, 18, 16] i

theorem biasOrder_pos (i : Fin 4) : 0 < biasOrder i := by
  fin_cases i <;> norm_num [biasOrder]

/-- These four orders are the orders in the new paper payment. -/
theorem four_bias_markov
    (ν : Measure G) [SFinite ν] (σ : Measure Y) [IsProbabilityMeasure σ]
    (error : Fin 4 → G → Y → ℝ) (B A : Fin 4 → ℝ)
    (hm : ∀ i, Measurable (Function.uncurry (error i)))
    (hB : ∀ i, 0 ≤ B i) (hA : ∀ i, 0 < A i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ y, ENNReal.ofReal (|error i g y| ^ biasOrder i) ∂σ ∂ν ≤
      ENNReal.ofReal (B i ^ biasOrder i)) :
    σ.real (⋃ i, momentBad ν (error i) (biasOrder i) (A i)) ≤
      (B 0 / A 0) ^ 24 + (B 1 / A 1) ^ 16 +
      (B 2 / A 2) ^ 18 + (B 3 / A 3) ^ 16 := by
  have h := finite_weighted_markov_real ν σ error biasOrder B A hm
    (fun i => (biasOrder_pos i).ne') hB hA hM
  simpa [Fin.sum_univ_succ, biasOrder, add_assoc] using h

/-- The three statistics read one first-layer distribution and pay one total price. -/
theorem three_statistics_markov
    (ν : Measure G) [SFinite ν] (σ : Measure Y) [IsProbabilityMeasure σ]
    (statistic : Fin 3 → G → Y → ℝ) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 < C)
    (hm : ∀ i, Measurable (Function.uncurry (statistic i)))
    (hM : ∀ i, ∫⁻ g, ∫⁻ y, ENNReal.ofReal (|statistic i g y| ^ 64) ∂σ ∂ν ≤
      ENNReal.ofReal (B ^ 64)) :
    σ.real (⋃ i, momentBad ν (statistic i) 64 C) ≤ 3 * (B / C) ^ 64 := by
  have h := finite_weighted_markov_real ν σ statistic (fun _ => 64)
    (fun _ => B) (fun _ => C) hm (by intros; norm_num) (fun _ => hB) (fun _ => hC) hM
  simpa using h

#print axioms finite_weighted_markov
#print axioms finite_weighted_markov_real
#print axioms four_bias_markov
#print axioms three_statistics_markov
end BstLean.Part220
