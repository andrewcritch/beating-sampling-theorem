import BstLean.Part187All
import BstLean.Part161Red
import BstLean.Part188R161Tail

/-! Part 187 (file `Part188R161Red`): copy of `Part161Red` re-proved at the floor `16200 ≤ n` (was `16384 ≤ n`).
Only the declarations with the floor (and private helpers they use) are copied, in the nested
namespace `….R`. -/



namespace BstLean.Part188.Base161_R
open BstLean.Part161 BstLean.Part161.R

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part157
open BstLean.Part53 (unitF53 radF53 measurable_unitF)

variable {n : ℕ}

/-- **The tail hypothesis holds in the World window** (`n ≥ 16 384`), with `m_tail = 4e^{−20}`. -/
theorem tail_of_window (hn : 16200 ≤ n) (D : Design n) (c : Ret n) (hw : WINDOW D c) :
    TAIL_hyp D c (4 * exp (-20)) := by
  obtain ⟨hc, hτ, h1, h2⟩ := hw
  have ha : 0 < √(normSq c.1.2) := by
    refine Real.sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg _) (Ne.symm ?_))
    intro h0
    exact hc (BstLean.Part130.normSq_eq_zero h0)
  have hsq : √(normSq c.1.2) ^ 2 = normSq c.1.2 := Real.sq_sqrt (normSq_nonneg _)
  have h := latitude_tail hn ha hτ (by rw [hsq]; exact h1) (by rw [hsq]; exact h2)
  unfold TAIL_hyp bulkIx bulkI muI
  rw [hsq] at h
  convert h using 2
  ext p
  rfl


/-- **`REPLA_mix_hyp` from the named hypotheses (item 2).** For `n ≥ 16 384` and a set `E` of
retained data: IF on `E` the World window holds and there is split data `d` with
`FLUCT_hyp D t c d 0.002159` and `BIAS_hyp D c d 0.004295`, THEN
`REPLA_mix_hyp D t h_A E` with `h_A = 0.006583 + 10⁻²⁰`. The tail is proved
(`tail_of_window`). -/
theorem repla_of_hyps (hn : 16200 ≤ n) (D : Design n) (t : ℝ) {E : Set (Ret n)}
    (hw : ∀ c ∈ E, WINDOW D c)
    (hd : ∀ c ∈ E, ∃ d : SplitData n,
      FLUCT_hyp D t c d (2159 / 10 ^ 6) ∧ BIAS_hyp D c d (4295 / 10 ^ 6)) :
    REPLA_mix_hyp D t BstLean.Part156.hAL E := by
  intro c hc
  obtain ⟨d, hF, hB⟩ := hd c hc
  have hwc := hw c hc
  have h := repla_root_of_split (by omega) D t c hwc.1 hwc.2.1 d hF hB
    (tail_of_window hn D c hwc)
  exact h.trans repla_arith

end BstLean.Part188.Base161_R

