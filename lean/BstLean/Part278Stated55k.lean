import BstLean.Part278Stated80k
import BstLean.Part278St55k_21

/-!
# Part 278 (O5): the stated program for every `n ≥ 55 000`

Even `n`: `statedDesign_even` and `Part174.Cap.classifier_paper_uncond_nocap`. Odd `n`: the
generated `Part174.Cap.classifier_paper_uncond_nocap_st` with `hodd` from `odd_root_goodA`.
-/

namespace BstLean.Part278

open BstLean.Part130 BstLean.Part157

theorem classifier_stated_55000 {n : ℕ} (hn : 55000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := by
  rcases Nat.even_or_odd n with he | ho
  · rw [BstLean.Part272.statedDesign_even (by omega) he]
    exact BstLean.Part174.Cap.classifier_paper_uncond_nocap hn t
  · exact BstLean.Part174.Cap.classifier_paper_uncond_nocap_st
      (hodd := fun c hc => odd_root_goodA (by omega) ho t c hc) hn t

end BstLean.Part278
