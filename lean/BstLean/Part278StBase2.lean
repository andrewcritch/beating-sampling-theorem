import BstLean.Part278StBase
import BstLean.Part177Split
import BstLean.Part188R161Red

/-!
# Part 278 (O5): the replacement root for the free-split bottoms (`hfl + hb ≤ 0.006454`)

`repla_st_hsum`: for `n ≥ 16 200`, FLUCT and BIAS for a design `D` with `hfl + hb ≤ 0.006454`,
the window, and the odd root `≤ 10⁻²⁰` on `E` give `REPLA_mix_hyp (statedDesign n) t hAL E`, when
`Q` of the two designs agrees. The `10⁻²⁰` is the reserve that `repla_arithG` leaves unused.
-/

namespace BstLean.Part278

open BstLean.Part157 BstLean.Part161

variable {n : ℕ}

theorem repla_st_hsum (hn : 16200 ≤ n) (D : Design n) (t : ℝ) {E : Set (Ret n)}
    {hfl hb : ℝ} (hsum : hfl + hb ≤ 6454 / 10 ^ 6)
    (hw : ∀ c ∈ E, WINDOW D c)
    (hd : ∀ c ∈ E, ∃ d : SplitData n, FLUCT_hyp D t c d hfl ∧ BIAS_hyp D c d hb)
    (hodd : ∀ c ∈ E,
      |√(qTilde (BstLean.Part272.statedDesign n) t c) - √(qTilde D t c)| ≤ 1 / 10 ^ 20)
    (hQ : ∀ c, QStand (BstLean.Part272.statedDesign n) t c = QStand D t c) :
    REPLA_mix_hyp (BstLean.Part272.statedDesign n) t BstLean.Part156.hAL E := by
  have h0 : REPLA_mix_hyp D t (6583 / 10 ^ 6) E := by
    intro c hc
    obtain ⟨d, hF, hB⟩ := hd c hc
    have hwc := hw c hc
    have h := repla_root_of_split (by omega) D t c hwc.1 hwc.2.1 d hF hB
      (BstLean.Part188.Base161_R.tail_of_window hn D c hwc)
    have ht := tail_root_num
    linarith
  have h1 := repla_transfer (D := D) (D' := BstLean.Part272.statedDesign n) hQ h0 hodd
  unfold BstLean.Part156.hAL
  exact h1

end BstLean.Part278
