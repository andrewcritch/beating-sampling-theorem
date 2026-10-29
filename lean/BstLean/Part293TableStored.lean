import BstLean.Part292TableEvents
import BstLean.Part293TableAnalytic
import BstLean.Part293TableOperators

/-! The actual paid table event supplies the stored-error and variance caps
on every measurable subset of the clipped latitude interval. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part292

theorem table_variance_max {n : ℕ} (hn : 8000 ≤ n) (c : Ret n)
    (ht : c ∈ tableEvent n) (hw : tableWorldGuard c.1)
    (hb : normSq (bR c) ≠ 0) (a : Ix n) : |VR c a| ≤ 0.00411 := by
  have h := (ht hw).2
  exact table_variance_of_operators hn c (opB_of_opN _ h.1) (opB_of_opN _ h.2.1)
    (by unfold lowOperator; positivity) (by unfold lowSecondOperator; positivity)
    (operator_product_square_low hn) hb a

noncomputable def storedInputs_of_table {n : ℕ} (hn : 8000 ≤ n) (c : Ret n)
    (ht : c ∈ tableEvent n) (hw : tableWorldGuard c.1)
    {K : Set (Ix n)} (hK : MeasurableSet K) (hsub : K ⊆ bulkIx (paperDesignP n) c) :
    StoredInputs c K 0.1802 0.05125 := by
  have h := (ht hw).2
  have hA := opB_of_opN _ h.1
  have hB := opB_of_opN _ h.2.1
  have hO1 : 0 < lowOperator n := by
    unfold lowOperator
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  have hO2 : 0 < lowSecondOperator n := by
    unfold lowSecondOperator tA mA
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    positivity
  apply storedInputs_of_operator_bounds hn c hw hO1 hO2 hA hB
    (lowOperator_square hn) (operator_product_square_low hn) ?_ ?_ hK hsub
  · convert (ht hw).1.1 using 1 <;> norm_num [lowTableF, tableAllowance]
  · convert (ht hw).1.2 using 1 <;> norm_num [lowTableW, tableAllowance]

end BstLean.Part293
