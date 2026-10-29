import BstLean.Part270StatedSubsetBridge

/-! Band assembly for the stated classifier. The base event can be the smaller
sharp-table event. Both parities use the same interval interface. -/
namespace BstLean.Part287

open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157

/-- Rows on a closed band, with the source-event inclusion needed for odd dimensions. -/
structure IntervalInputs (lo hi : ℕ) where
  dimension : 12000 ≤ lo
  row : ∀ n ∈ Icc lo hi, BstLean.Part259.RowInputs n
  source : ∀ n (hn : n ∈ Icc lo hi),
    (row n hn).baseEvent ⊆ BstLean.Part262.sourceBase n

noncomputable def IntervalInputs.family {lo hi : ℕ} (B : IntervalInputs lo hi) :
    BstLean.Part259.FamilyInputs (Icc lo hi) := ⟨B.row⟩

theorem IntervalInputs.classifier {lo hi : ℕ} (B : IntervalInputs lo hi) :
    ∀ n ∈ Icc lo hi, ∀ t : ℝ,
      99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
        {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t
          BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  BstLean.Part270.classifier_stated_of_source_subfamily B.family
    (fun _ hn => B.dimension.trans hn.1) B.source

/-- Restriction does not reconstruct analytic certificates. -/
noncomputable def IntervalInputs.restrict {lo hi a b : ℕ} (B : IntervalInputs lo hi)
    (ha : lo ≤ a) (hb : b ≤ hi) : IntervalInputs a b where
  dimension := B.dimension.trans ha
  row := fun n hn => B.row n ⟨ha.trans hn.1, hn.2.trans hb⟩
  source := fun n hn => B.source n ⟨ha.trans hn.1, hn.2.trans hb⟩

/-- Join adjacent bands without a split over their individual dimensions. -/
noncomputable def IntervalInputs.append {lo mid hi : ℕ}
    (A : IntervalInputs lo mid) (B : IntervalInputs (mid + 1) hi) :
    IntervalInputs lo hi where
  dimension := A.dimension
  row := fun n hn => if h : n ≤ mid then A.row n ⟨hn.1, h⟩
    else B.row n ⟨by omega, hn.2⟩
  source := by
    intro n hn
    split_ifs with h
    · exact A.source n ⟨hn.1, h⟩
    · exact B.source n ⟨by omega, hn.2⟩

end BstLean.Part287
