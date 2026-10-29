import BstLean.Part278StatedAll
import BstLean.Part278StBase3
import BstLean.Part278St16200_all

/-! # Part 278 (O5): the stated program for every `n ≥ 16200` (written by `reports/p278-stated.py`) -/

namespace BstLean.Part278

open BstLean.Part130 BstLean.Part157

theorem classifier_stated_16200 {n : ℕ} (hn : 16200 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := by
  rcases Nat.even_or_odd n with he | ho
  · exact classifier_stated_even_16200 (by omega) he t
  · exact BstLean.Part190.classifier_paper_uncond_16200_st
      (hodd := fun c hc => odd_root_goodA16200 (by omega) ho t c hc) hn t

end BstLean.Part278
