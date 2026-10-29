import BstLean.Part187All
import BstLean.Part161Fl
import BstLean.Part188R161Tail
import BstLean.Part188R161Red

/-! Part 187 (file `Part188R161Fl`): copy of `Part161Fl` re-proved at the floor `16200 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part188.Base161_R
open BstLean.Part161 BstLean.Part161.R

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part157
open BstLean.Part53 (unitF53 measurable_unitF)

variable {n : ℕ}

/-- **`REPLA_mix_hyp` from the scalar fluctuation hypothesis (items 1(c) and 2).** For
`n ≥ 16 384`: IF on `E` the World window holds and there are split data `d` and window constants
with `FLUCT_chi_hyp D c d ε₀ δ₀ s_low 0.002159` and `BIAS_hyp D c d 0.004295`, THEN
`REPLA_mix_hyp D t h_A E`, `h_A = 0.006583 + 10⁻²⁰`. -/
theorem repla_of_hyps_chi (hn : 16200 ≤ n) (D : Design n) (t : ℝ) {E : Set (Ret n)}
    (hw : ∀ c ∈ E, WINDOW D c)
    (hd : ∀ c ∈ E, ∃ (d : SplitData n) (ε₀ δ₀ slow : ℝ),
      FLUCT_chi_hyp D c d ε₀ δ₀ slow (2159 / 10 ^ 6) ∧ BIAS_hyp D c d (4295 / 10 ^ 6)) :
    REPLA_mix_hyp D t BstLean.Part156.hAL E := by
  refine repla_of_hyps hn D t hw fun c hc => ?_
  obtain ⟨d, ε₀, δ₀, slow, hF, hB⟩ := hd c hc
  exact ⟨d, fluct_of_chi D t c d hF, hB⟩

end BstLean.Part188.Base161_R

