import BstLean.Part289Mix

/-! The replacement root for the revised stated design. -/
namespace BstLean.Part289
open Real MeasureTheory BstLean.Part130 BstLean.Part157 BstLean.Part161
open BstLean.Part169 BstLean.Part241 BstLean.Part228 BstLean.Part272
variable {n : ℕ}

/-- The exact target probability is unchanged by the residual floor. -/
theorem QStand_statedDesign2 (t : ℝ) (c : Ret n) :
    QStand (statedDesign2 n) t c = QStand (idealDesignFloor n (scaleFloor n)) t c := rfl

/-- A conditional-pass root and a table comparison give a root for the actual program.
The table comparison can be zero in even dimension. -/
theorem stated_root_of_passInputsFloor (hn : 2 ≤ n) (t : ℝ) (c : Ret n)
    (split : SplitData n) (hc : c.1.2 ≠ 0) {χ d ε vmax aw af Hf Cv hfl tl tu htable : ℝ}
    (P : PassInputsFloor (scaleFloor n) c split χ d ε vmax aw af Hf Cv)
    (hF : FLUCT_hyp (idealDesignFloor n (scaleFloor n)) t c split hfl)
    (hT : BulkChernoffDomain (idealDesignFloor n (scaleFloor n)) c tl tu)
    (hTable : |√(qTilde (statedDesign2 n) t c) -
      √(qTilde (idealDesignFloor n (scaleFloor n)) t c)| ≤ htable) :
    |√(QStand (statedDesign2 n) t c) - √(qTilde (statedDesign2 n) t c)| ≤
      hfl + biasRoot n χ d ε vmax aw af Hf Cv +
        bulkTailRoot (idealDesignFloor n (scaleFloor n)) c tl tu + htable := by
  rw [QStand_statedDesign2]
  have h := conditional_pass_root_floor hn (scaleFloor n) t c split hc P hF hT
  have htri := abs_sub_le (√(QStand (idealDesignFloor n (scaleFloor n)) t c))
    (√(qTilde (idealDesignFloor n (scaleFloor n)) t c)) (√(qTilde (statedDesign2 n) t c))
  rw [abs_sub_comm (√(qTilde (idealDesignFloor n (scaleFloor n)) t c))] at htri
  exact htri.trans (add_le_add h hTable)

theorem stated_root_even (hn : 8 ≤ n) (he : Even n) (t : ℝ) (c : Ret n)
    (split : SplitData n) (hc : c.1.2 ≠ 0) {χ d ε vmax aw af Hf Cv hfl tl tu : ℝ}
    (P : PassInputsFloor (scaleFloor n) c split χ d ε vmax aw af Hf Cv)
    (hF : FLUCT_hyp (idealDesignFloor n (scaleFloor n)) t c split hfl)
    (hT : BulkChernoffDomain (idealDesignFloor n (scaleFloor n)) c tl tu) :
    |√(QStand (statedDesign2 n) t c) - √(qTilde (statedDesign2 n) t c)| ≤
      hfl + biasRoot n χ d ε vmax aw af Hf Cv +
        bulkTailRoot (idealDesignFloor n (scaleFloor n)) c tl tu := by
  rw [statedDesign2_even hn he]
  exact conditional_pass_root_floor (by omega) (scaleFloor n) t c split hc P hF hT

/-- The same root bound gives the event-level supply used by the replacement junction. -/
theorem stated_root_on_event (hn : 2 ≤ n) (t H : ℝ) {E : Set (Ret n)}
    (h : ∀ c ∈ E, ∃ (split : SplitData n) (χ d ε vmax aw af Hf Cv hfl tl tu htable : ℝ),
      c.1.2 ≠ 0 ∧ PassInputsFloor (scaleFloor n) c split χ d ε vmax aw af Hf Cv ∧
      FLUCT_hyp (idealDesignFloor n (scaleFloor n)) t c split hfl ∧
      BulkChernoffDomain (idealDesignFloor n (scaleFloor n)) c tl tu ∧
      |√(qTilde (statedDesign2 n) t c) - √(qTilde (idealDesignFloor n (scaleFloor n)) t c)| ≤ htable ∧
      hfl + biasRoot n χ d ε vmax aw af Hf Cv +
        bulkTailRoot (idealDesignFloor n (scaleFloor n)) c tl tu + htable ≤ H) :
    REPLA_mix_hyp (statedDesign2 n) t H E := by
  intro c hc
  obtain ⟨split, χ, d, ε, vmax, aw, af, Hf, Cv, hfl, tl, tu, htable,
    hcentre, P, hF, hT, hTable, hsum⟩ := h c hc
  exact (stated_root_of_passInputsFloor hn t c split hcentre P hF hT hTable).trans hsum

end BstLean.Part289

/-- info: 'BstLean.Part289.stated_root_on_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.stated_root_on_event
/-- info: 'BstLean.Part289.stated_root_even' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.stated_root_even
