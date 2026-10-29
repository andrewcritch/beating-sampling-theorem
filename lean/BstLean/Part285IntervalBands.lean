import BstLean.Part285World12225
import BstLean.Part285World12750
import BstLean.Part285World13337
import BstLean.Part285World14325
import BstLean.Part285World
import BstLean.Part285IntervalTable

/-! Sharp table charges on six bands, and a smaller dimension-dependent payment. -/
namespace BstLean.Part285.Interval
open MeasureTheory Real Set
open BstLean.Part157 BstLean.Part169 BstLean.Part280

noncomputable def bandTablePrice (n : ℕ) : ℝ :=
  if n ≤ 12224 then 9 / 10000
  else if n ≤ 12749 then 7642 / 10 ^ 7
  else if n ≤ 13336 then 5602 / 10 ^ 7
  else if n ≤ 14324 then 5522 / 10 ^ 7
  else if n ≤ 15324 then 2992 / 10 ^ 7
  else 1899 / 10 ^ 7

theorem sharpTable_band_charge {n : ℕ} (hn : 12000 ≤ n) (hn2 : n ≤ 16199) :
    (retDist (paperCentres n)).real (sharpTableN n)ᶜ ≤ bandTablePrice n := by
  unfold bandTablePrice
  split_ifs with h0 h1 h2 h3 h4
  · exact sharpTableN_ret_charge (by omega) h0
  · exact BstLean.Part285B12225.sharpTableK_ret_charge (by omega) h1
  · exact BstLean.Part285B12750.sharpTableK_ret_charge (by omega) h2
  · exact BstLean.Part285B13337.sharpTableK_ret_charge (by omega) h3
  · exact BstLean.Part285B14325.sharpTableK_ret_charge (by omega) h4
  · exact BstLean.Part285.sharpTableK_ret_charge (by omega) hn2

/-- Use the smaller payment whenever the exact dimension price improves a band cap. -/
noncomputable def smallerTablePrice (n : ℕ) : ℝ := min (bandTablePrice n) (tablePrice n)

theorem sharpTable_smaller_charge {n : ℕ} (hn : 12000 ≤ n) (hn2 : n ≤ 16199) :
    (retDist (paperCentres n)).real (sharpTableN n)ᶜ ≤ smallerTablePrice n :=
  le_min (sharpTable_band_charge hn hn2) (sharpTable_dimension_charge hn hn2)

theorem smallerTablePrice_le_band (n : ℕ) : smallerTablePrice n ≤ bandTablePrice n :=
  min_le_left _ _

end BstLean.Part285.Interval
