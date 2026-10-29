import BstLean.Part281Family
import BstLean.Part287All
import BstLean.Part289Transfer

/-! The unchanged high branch of the revised program has contiguous coverage. -/
namespace BstLean.Part293
open BstLean.Part130 BstLean.Part157 BstLean.Part289

theorem classifier_stated2_11883 {n : ℕ} (hn : 11883 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (statedDesign2 n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := by
  apply classifier_statedDesign2_of_stated hn
  by_cases hl : n ≤ 12224
  · exact BstLean.Part281.classifier_stated_11883_12224 n ⟨hn, hl⟩ t
  · exact BstLean.Part287.classifier_stated_12225 (by omega) t

/-- Once the low band is supplied, no further probability argument remains in the join. -/
theorem classifier_stated2_8000_of_low
    (low : ∀ n ∈ Set.Icc (8000 : ℕ) 11882, ∀ t : ℝ,
      99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
        {x | successNet x.1 t (progOut (statedDesign2 n) t BstLean.Part156.aL
          (10 ^ 12) x.1 x.2)}) :
    ∀ n ≥ 8000, ∀ t : ℝ,
      99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
        {x | successNet x.1 t (progOut (statedDesign2 n) t BstLean.Part156.aL
          (10 ^ 12) x.1 x.2)} := by
  intro n hn t
  by_cases hl : n ≤ 11882
  · exact low n ⟨hn, hl⟩ t
  · exact classifier_stated2_11883 (by omega) t

end BstLean.Part293

/-- info: 'BstLean.Part293.classifier_stated2_11883' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.classifier_stated2_11883
/-- info: 'BstLean.Part293.classifier_stated2_8000_of_low' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.classifier_stated2_8000_of_low
