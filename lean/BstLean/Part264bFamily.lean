import BstLean.Part264bFrameShard0
import BstLean.Part264bFrameShard1
import BstLean.Part264bFrameShard2
import BstLean.Part264bFrameShard3
import BstLean.Part264bFrameShard4
/-! The actual local-frame family on the complete dimension interval. -/
namespace BstLean.Part264b
open Set
/-- The actual local-frame family for the final RowInputs assembly. -/
noncomputable def frameFamily (n : ℕ) (hn : n ∈ Icc 12225 12349) : FrameData n := by
  obtain ⟨hl, hu⟩ := hn
  by_cases h0 : n ≤ 12249
  · exact frameShard0 n (by constructor <;> omega)
  by_cases h1 : n ≤ 12274
  · exact frameShard1 n (by constructor <;> omega)
  by_cases h2 : n ≤ 12299
  · exact frameShard2 n (by constructor <;> omega)
  by_cases h3 : n ≤ 12324
  · exact frameShard3 n (by constructor <;> omega)
  exact frameShard4 n (by constructor <;> omega)
end BstLean.Part264b
