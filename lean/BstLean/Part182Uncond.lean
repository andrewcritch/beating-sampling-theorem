import BstLean.Part182End21M
import BstLean.Part182TI

/-!
# Part 182 (file `Uncond`): the unconditional classifier theorem for every `n ≥ 21 500`

No proof is left open; no `native_decide` or `axiom` is used.

**`classifier_paper_uncond_21500`**: Part 172's conclusion for every `n ≥ 21 500`, every `t`,
with NO hypothesis and no upper end. Proof: `classifier_paper_TIM21500` (frame `≈ 2.09/n` at
21 000 from the Schur route with `λ = 0.72`; chain at 21 500; Part 181 above 22 000) with its
hypothesis discharged by `TI_lite_proved` (Lemma TI in Lean, upper singular values only).
-/

namespace BstLean.Part182

open BstLean.Part130 BstLean.Part157 BstLean.Part169

/-- **The classifier theorem with no hypothesis, for every `n ≥ 21 500` and every `t`.** -/
theorem classifier_paper_uncond_21500 {n : ℕ} (hn : 21500 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_TIM21500 (fun _ h => TI_lite_proved h) hn t

theorem uncond_21500_eq_172 {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_uncond_21500 (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

theorem uncond_21500_eq_181 {n : ℕ} (hn : 22000 ≤ n) (t : ℝ) :
    classifier_paper_uncond_21500 (by omega) t =
      BstLean.Part181.classifier_paper_uncond_nocap22 hn t :=
  rfl

/-- The statement written with Part 130/156/157/169 names only. -/
example {n : ℕ} (hn : 21500 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((BstLean.Part130.mlpTriple 2 n).prod (BstLean.Part157.sampMeas (10 ^ 12) n)).real
      {x | BstLean.Part157.successNet x.1 t (BstLean.Part157.progOut
        (BstLean.Part169.paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_uncond_21500 hn t

end BstLean.Part182

open BstLean.Part182 in
#print axioms classifier_paper_uncond_21500
