import BstLean.Part220Charge
import BstLean.Part223MomentBounds

/-! Low-band table orders and event payment. The moment premises in this
module are explicit; this module does not assert their network suppliers. -/
namespace BstLean.Part292
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part220 BstLean.Part223

def tableOrder (i : Fin 4) : ℕ := ![24, 104, 18, 104] i

noncomputable def tableAllowance (i : Fin 4) : ℝ :=
  ![402594919 / 10^10, 70062727 / 10^10,
    1662297729 / 10^10, 63898575 / 10^10] i

theorem tableOrder_pos (i : Fin 4) : 0 < tableOrder i := by
  fin_cases i <;> norm_num [tableOrder]

theorem tableOrder_ge_eight (i : Fin 4) : 8 ≤ tableOrder i := by
  fin_cases i <;> norm_num [tableOrder]

theorem tableAllowance_pos (i : Fin 4) : 0 < tableAllowance i := by
  fin_cases i <;> norm_num [tableAllowance]

noncomputable def firstLayerCharge : ℝ :=
  3 * exp (-18) + 2 * exp (-12) + 1 / 10000

noncomputable def tableCharge (B : Fin 4 → ℝ) : ℝ :=
  firstLayerCharge + ∑ i, (B i / tableAllowance i) ^ tableOrder i

theorem tableCharge_eq (B : Fin 4 → ℝ) : tableCharge B =
    3 * exp (-18) + 2 * exp (-12) + 1 / 10000 +
    (B 0 / (402594919 / 10^10)) ^ 24 +
    (B 1 / (70062727 / 10^10)) ^ 104 +
    (B 2 / (1662297729 / 10^10)) ^ 18 +
    (B 3 / (63898575 / 10^10)) ^ 104 := by
  simp [tableCharge, firstLayerCharge, Fin.sum_univ_succ,
    tableAllowance, tableOrder, add_assoc]

variable {G Y : Type*} [MeasurableSpace G] [MeasurableSpace Y]

def tableBad (ν : Measure G) (error : Fin 4 → G → Y → ℝ) : Set Y :=
  ⋃ i, momentBad ν (error i) (tableOrder i) (tableAllowance i)

theorem tableBad_measurable (ν : Measure G) [SFinite ν]
    (error : Fin 4 → G → Y → ℝ)
    (hm : ∀ i, Measurable (Function.uncurry (error i))) :
    MeasurableSet (tableBad ν error) :=
  MeasurableSet.iUnion fun i => measurableSet_momentBad ν (hm i) _ _

theorem table_moments_on_good (ν : Measure G) (hν : ν univ ≤ 1)
    (error : Fin 4 → G → Y → ℝ)
    (hm : ∀ i y, Measurable (fun g => error i g y))
    {y : Y} (hy : y ∉ tableBad ν error) (i : Fin 4) :
    MomentBound ν 8 (fun g => error i g y) (tableAllowance i) := by
  have hi : y ∉ momentBad ν (error i) (tableOrder i) (tableAllowance i) :=
    fun h => hy (mem_iUnion.mpr ⟨i, h⟩)
  have hM : MomentBound ν (tableOrder i) (fun g => error i g y)
      (tableAllowance i) :=
    ⟨hm i y, (tableAllowance_pos i).le, le_of_not_gt hi⟩
  exact hM.lower (by norm_num) (tableOrder_ge_eight i) hν

theorem four_moment_charge (ν : Measure G) [SFinite ν]
    (σ : Measure Y) [IsProbabilityMeasure σ]
    (error : Fin 4 → G → Y → ℝ) (B : Fin 4 → ℝ)
    (hm : ∀ i, Measurable (Function.uncurry (error i)))
    (hB : ∀ i, 0 ≤ B i)
    (hM : ∀ i, ∫⁻ g, ∫⁻ y, ENNReal.ofReal
      (|error i g y| ^ tableOrder i) ∂σ ∂ν ≤
      ENNReal.ofReal (B i ^ tableOrder i)) :
    σ (tableBad ν error) ≤
      ENNReal.ofReal (∑ i, (B i / tableAllowance i) ^ tableOrder i) :=
  finite_weighted_markov ν σ error tableOrder B tableAllowance hm
    (fun i => (tableOrder_pos i).ne') hB tableAllowance_pos hM

theorem conditional_table_charge
    {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ]
    (ν : Measure G) [SFinite ν] (σ : Measure Y) [IsProbabilityMeasure σ]
    (E : Set X) (hE : MeasurableSet E)
    (error : X → Fin 4 → G → Y → ℝ) (B : Fin 4 → ℝ)
    (hm : ∀ x ∈ E, ∀ i, Measurable (Function.uncurry (error x i)))
    (hB : ∀ i, 0 ≤ B i)
    (hM : ∀ x ∈ E, ∀ i, ∫⁻ g, ∫⁻ y,
      ENNReal.ofReal (|error x i g y| ^ tableOrder i) ∂σ ∂ν ≤
      ENNReal.ofReal (B i ^ tableOrder i))
    (hbad : MeasurableSet {p : X × Y | p.2 ∈ tableBad ν (error p.1)})
    (hfirst : μ Eᶜ ≤ ENNReal.ofReal firstLayerCharge) :
    (μ.prod σ).real {p : X × Y | p.1 ∉ E ∨ p.2 ∈ tableBad ν (error p.1)} ≤
      tableCharge B := by
  apply retained_complement_charge μ σ hE hbad
    (by unfold firstLayerCharge; positivity)
    (Finset.sum_nonneg fun i _ =>
      pow_nonneg (div_nonneg (hB i) (tableAllowance_pos i).le) _) hfirst
  intro x hx
  exact four_moment_charge ν σ (error x) B (hm x hx) hB (hM x hx)

end BstLean.Part292

/-- info: 'BstLean.Part292.conditional_table_charge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part292.conditional_table_charge

/-- info: 'BstLean.Part292.table_moments_on_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part292.table_moments_on_good
