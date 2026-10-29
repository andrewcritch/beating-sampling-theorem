import BstLean.Part286Partial
import BstLean.Part286Rows25
import BstLean.Part286Rows26
import BstLean.Part286Rows27
import BstLean.Part278Stated12225

/-! Lower-interval assembly from frame shards that have already passed. -/
namespace BstLean.Part287
open BstLean.Part130 BstLean.Part157

theorem classifier_stated_12225_13049 : ∀ n ∈ Set.Icc (12225 : ℕ) 13049, ∀ t : ℝ,
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := by
  intro n hn t
  by_cases h0 : n ≤ 12349
  · exact BstLean.Part278.classifier_stated_12225_12349 n ⟨hn.1, h0⟩ t
  by_cases h1 : n ≤ 12974
  · exact BstLean.Part286.classifier_stated_12350_12974 n ⟨by omega, h1⟩ t
  by_cases h2 : n ≤ 12999
  · exact BstLean.Part286.stated_shard25 n ⟨by omega, h2⟩ t
  by_cases h3 : n ≤ 13024
  · exact BstLean.Part286.stated_shard26 n ⟨by omega, h3⟩ t
  exact BstLean.Part286.stated_shard27 n ⟨by omega, hn.2⟩ t

end BstLean.Part287

/-- info: 'BstLean.Part287.classifier_stated_12225_13049' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part287.classifier_stated_12225_13049
