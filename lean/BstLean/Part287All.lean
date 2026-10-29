import BstLean.Part287Final
import BstLean.Part287LowerPartial
import BstLean.Part286Rows28
import BstLean.Part286Rows29
import BstLean.Part286Rows30
import BstLean.Part286Rows31
import BstLean.Part286Rows32
import BstLean.Part286Rows33
import BstLean.Part287Lower34
import BstLean.Part278Stated16200

/-! Contiguous coverage from 12225, with the uniform certificates from 13225. -/
namespace BstLean.Part287
open BstLean.Part130 BstLean.Part157

theorem classifier_stated_12225 {n : ℕ} (hn : 12225 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := by
  by_cases h0 : n ≤ 13049
  · exact classifier_stated_12225_13049 n ⟨hn, h0⟩ t
  by_cases h28 : n ≤ 13074
  · exact BstLean.Part286.stated_shard28 n ⟨by omega, h28⟩ t
  by_cases h29 : n ≤ 13099
  · exact BstLean.Part286.stated_shard29 n ⟨by omega, h29⟩ t
  by_cases h30 : n ≤ 13124
  · exact BstLean.Part286.stated_shard30 n ⟨by omega, h30⟩ t
  by_cases h31 : n ≤ 13149
  · exact BstLean.Part286.stated_shard31 n ⟨by omega, h31⟩ t
  by_cases h32 : n ≤ 13174
  · exact BstLean.Part286.stated_shard32 n ⟨by omega, h32⟩ t
  by_cases h33 : n ≤ 13199
  · exact BstLean.Part286.stated_shard33 n ⟨by omega, h33⟩ t
  by_cases h34 : n ≤ 13224
  · exact BstLean.Part287.Lower34.stated_shard34 n ⟨by omega, h34⟩ t
  by_cases h2 : n ≤ 16199
  · exact classifier_stated_13225_16199 n ⟨by omega, h2⟩ t
  exact BstLean.Part278.classifier_stated_16200 (by omega) t

end BstLean.Part287

/-! Guarded axiom audit. -/

/-- info: 'BstLean.Part287.classifier_stated_13484_16199' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part287.classifier_stated_13484_16199

/-- info: 'BstLean.Part287.classifier_stated_13225_16199' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part287.classifier_stated_13225_16199

/-- info: 'BstLean.Part287.classifier_stated_12225' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part287.classifier_stated_12225
