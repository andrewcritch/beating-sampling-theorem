import BstLean.Part278St80k_21
import BstLean.Part278St80k_23
import BstLean.Part174CapEnd

/-!
# Part 278 (O5): the stated program for every `n ≥ 80 000`

Even `n`: `statedDesign n = paperDesignP n` (`Part272.statedDesign_even`), then
`Part174.Cap.classifier_paper_uncond_nocap`. Odd `n`: the generated `_st` chains
`Part172.classifier_paper_uncond_st` (`n ≤ 10²⁰`) and `Part174.Cap.classifier_paper_uncond_large_st`
(`n ≥ 10¹⁹`), with `hodd` from `Part278.odd_root_goodA`.
-/

namespace BstLean.Part278

open BstLean.Part130 BstLean.Part157

theorem classifier_stated_80000 {n : ℕ} (hn : 80000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := by
  rcases Nat.even_or_odd n with he | ho
  · rw [BstLean.Part272.statedDesign_even (by omega) he]
    exact BstLean.Part174.Cap.classifier_paper_uncond_nocap (by omega) t
  · have hodd : ∀ c ∈ BstLean.Part164.goodA n (BstLean.Part169.paperDesignP n) Set.univ,
        |√(qTilde (BstLean.Part272.statedDesign n) t c) -
          √(qTilde (BstLean.Part169.paperDesignP n) t c)| ≤ 1 / 10 ^ 20 :=
      fun c hc => odd_root_goodA (by omega) ho t c hc
    rcases le_total (n : ℝ) (10 ^ 20) with h | h
    · exact BstLean.Part172.classifier_paper_uncond_st (hodd := hodd) hn h t
    · exact BstLean.Part174.Cap.classifier_paper_uncond_large_st (hodd := hodd)
        (le_trans (by norm_num) h) t

end BstLean.Part278
