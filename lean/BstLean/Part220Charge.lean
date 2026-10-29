import BstLean.Part220Events

/-! Conditional charges and marginal transfer preserve one retained-data payment. -/
namespace BstLean.Part220
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal

/-- Each field can use its own complete row representation.
The four actual fields still use one shared target distribution. -/
theorem four_bias_markov_of_marginals
    {G Z : Type*} [MeasurableSpace G] [MeasurableSpace Z]
    (ν : Measure G) [SFinite ν] (τ : Measure Z) [IsProbabilityMeasure τ]
    (Y : Fin 4 → Type*) [∀ i, MeasurableSpace (Y i)]
    (σ : ∀ i, Measure (Y i)) (error : ∀ i, G → Y i → ℝ)
    (actual : Fin 4 → G → Z → ℝ) (B A : Fin 4 → ℝ)
    (ha : ∀ i, Measurable (Function.uncurry (actual i)))
    (he : ∀ i g, Measurable (error i g))
    (hmap : ∀ i g, τ.map (actual i g) = (σ i).map (error i g))
    (hB : ∀ i, 0 ≤ B i) (hA : ∀ i, 0 < A i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ y, ENNReal.ofReal (|error i g y| ^ biasOrder i) ∂σ i ∂ν ≤
      ENNReal.ofReal (B i ^ biasOrder i)) :
    τ.real (⋃ i, momentBad ν (actual i) (biasOrder i) (A i)) ≤
      (B 0 / A 0) ^ 24 + (B 1 / A 1) ^ 16 +
      (B 2 / A 2) ^ 18 + (B 3 / A 3) ^ 16 := by
  apply four_bias_markov ν τ actual B A ha hB hA
  intro i
  have ham : ∀ g, Measurable (actual i g) :=
    fun g => (ha i).comp (measurable_const.prodMk measurable_id)
  have ht := BstLean.Part216.weighted_marginal_transfer (ν := ν)
    (σ := σ i) (τ := τ) (actual := actual i) (error := error i)
    (he i) ham (hmap i) (biasOrder i)
  exact ht.le.trans (hM i)

/-- A conditional event pays its price only inside the retained good set. -/
theorem guarded_product_charge {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (σ : Measure Y) [IsProbabilityMeasure σ]
    {E : Set X} (hE : MeasurableSet E) {H : Set (X × Y)} (hH : MeasurableSet H)
    {δ : ℝ} (hδ : 0 ≤ δ) (hcond : ∀ x ∈ E, σ {y | (x, y) ∈ H} ≤ ENNReal.ofReal δ) :
    (μ.prod σ) {p | p.1 ∈ E ∧ p ∈ H} ≤ ENNReal.ofReal δ := by
  change (μ.prod σ) (Prod.fst ⁻¹' E ∩ H) ≤ _
  rw [Measure.prod_apply ((hE.preimage measurable_fst).inter hH)]
  calc
    _ ≤ ∫⁻ _x, ENNReal.ofReal δ ∂μ := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ E
      · simpa [Set.preimage, hx] using hcond x hx
      · simp [Set.preimage, hx]
    _ = _ := by simp

/-- The retained-data complement is paid once after the conditional event is integrated. -/
theorem retained_complement_charge {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (σ : Measure Y) [IsProbabilityMeasure σ]
    {E : Set X} (hE : MeasurableSet E) {H : Set (X × Y)} (hH : MeasurableSet H)
    {δE δ : ℝ} (hδE : 0 ≤ δE) (hδ : 0 ≤ δ)
    (hfirst : μ Eᶜ ≤ ENNReal.ofReal δE)
    (hcond : ∀ x ∈ E, σ {y | (x, y) ∈ H} ≤ ENNReal.ofReal δ) :
    (μ.prod σ).real {p | p.1 ∉ E ∨ p ∈ H} ≤ δE + δ := by
  have hcover : {p : X × Y | p.1 ∉ E ∨ p ∈ H} =
      (Eᶜ ×ˢ Set.univ) ∪ {p | p.1 ∈ E ∧ p ∈ H} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_prod,
      Set.mem_compl_iff, Set.mem_univ, and_true]
    tauto
  apply ENNReal.toReal_le_of_le_ofReal (add_nonneg hδE hδ)
  rw [hcover, ENNReal.ofReal_add hδE hδ]
  refine (measure_union_le _ _).trans (add_le_add ?_
    (guarded_product_charge μ σ hE hH hδ hcond))
  simpa only [Measure.prod_prod, measure_univ, mul_one] using hfirst

/-- The formula keeps the four Markov prices and the first-layer prices distinct. -/
noncomputable def biasCharge (B A : Fin 4 → ℝ) : ℝ :=
  3 * exp (-18) + 2 * exp (-12) + 1 / 10000 +
    (B 0 / A 0) ^ 24 + (B 1 / A 1) ^ 16 + (B 2 / A 2) ^ 18 + (B 3 / A 3) ^ 16

/-- The conditional four-event assembly has exactly the new paper charge.
The retained first-layer complement is counted once. -/
theorem conditional_four_bias_charge
    {X G Y : Type*} [MeasurableSpace X] [MeasurableSpace G] [MeasurableSpace Y]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure G) [SFinite ν]
    (σ : Measure Y) [IsProbabilityMeasure σ]
    (E : Set X) (hE : MeasurableSet E)
    (error : X → Fin 4 → G → Y → ℝ) (B A : Fin 4 → ℝ)
    (hm : ∀ x ∈ E, ∀ i, Measurable (Function.uncurry (error x i)))
    (hB : ∀ i, 0 ≤ B i) (hA : ∀ i, 0 < A i)
    (hM : ∀ x ∈ E, ∀ i,
      ∫⁻ g, ∫⁻ y, ENNReal.ofReal (|error x i g y| ^ biasOrder i) ∂σ ∂ν ≤
        ENNReal.ofReal (B i ^ biasOrder i))
    (hbad : MeasurableSet {p : X × Y |
      p.2 ∈ ⋃ i, momentBad ν (error p.1 i) (biasOrder i) (A i)})
    (hfirst : μ Eᶜ ≤ ENNReal.ofReal (3 * exp (-18) + 2 * exp (-12) + 1 / 10000)) :
    (μ.prod σ).real {p : X × Y | p.1 ∉ E ∨
      p.2 ∈ ⋃ i, momentBad ν (error p.1 i) (biasOrder i) (A i)} ≤ biasCharge B A := by
  have hδ : 0 ≤ ∑ i, (B i / A i) ^ biasOrder i :=
    Finset.sum_nonneg fun i _ => pow_nonneg (div_nonneg (hB i) (hA i).le) _
  have h := retained_complement_charge μ σ hE hbad
    (by positivity : 0 ≤ 3 * exp (-18) + 2 * exp (-12) + 1 / 10000)
    hδ hfirst (fun x hx =>
      finite_weighted_markov ν σ (error x) biasOrder B A (hm x hx)
        (fun i => (biasOrder_pos i).ne') hB hA (hM x hx))
  simpa [biasCharge, Fin.sum_univ_succ, biasOrder, add_assoc] using h

#print axioms four_bias_markov_of_marginals
#print axioms guarded_product_charge
#print axioms retained_complement_charge
#print axioms conditional_four_bias_charge
end BstLean.Part220
