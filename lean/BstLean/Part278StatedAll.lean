import BstLean.Part278Stated55k
import BstLean.Part190Uncond

/-!
# Part 278 (O5): what is proved for the stated program from `n ≥ 16 200`

* `classifier_stated_even_16200`: every even `n ≥ 16 200` (`statedDesign_even` and
  `Part190.classifier_paper_uncond_16200`).
* `classifier_stated_16200_even_or_large`: every `n ≥ 16 200` that is even or `≥ 55 000`.
  Odd `n` in `[16 200, 55 000)` is not covered here.
-/

namespace BstLean.Part278

open BstLean.Part130 BstLean.Part157

theorem classifier_stated_even_16200 {n : ℕ} (hn : 16200 ≤ n) (he : Even n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := by
  rw [BstLean.Part272.statedDesign_even (by omega) he]
  exact BstLean.Part190.classifier_paper_uncond_16200 hn t

theorem classifier_stated_16200_even_or_large {n : ℕ} (hn : 16200 ≤ n)
    (h : Even n ∨ 55000 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (BstLean.Part272.statedDesign n) t BstLean.Part156.aL
        (10 ^ 12) x.1 x.2)} := by
  rcases h with he | hl
  · exact classifier_stated_even_16200 hn he t
  · exact classifier_stated_55000 hl t

end BstLean.Part278
