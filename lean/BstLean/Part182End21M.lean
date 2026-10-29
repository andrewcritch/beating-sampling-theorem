import BstLean.Part182Endc21M
import BstLean.Part182Comb21M
import BstLean.Part182End

/-!
# Part 182 (file `End21M`): the classifier theorem from `n ≥ 21 500`, CONDITIONAL on Lemma TI with
the TI-lite constant `λ = 0.72`

No proof is left open; no `native_decide` or `axiom` is used.

**`classifier_paper_TIM21500`**: Part 172's conclusion for every `n ≥ 21 500` and every `t`, GIVEN
`TI_hyp n 0.383 0.641 0.72 10⁻¹⁸` for every `n ≥ 21 000` (the constant a Lean proof of Lemma TI
without the Davidson–Szarek lower bound is expected to give). On `21 500 ≤ n < 22 000`: the chain
copy at 21 500 (`classifier_paper_uncond_21500HM`, room `roomT21M = 0.0018`) with
`HQF21M_stmt = ⟨hq_proved, FREE21M_of_TI hTI⟩` (frame `2.04/n`, ledger budget `0.008929`); for
`n ≥ 22 000`: Part 181 (no hypothesis used).
-/

namespace BstLean.Part182

open BstLean.Part130 BstLean.Part157 BstLean.Part169

theorem classifier_paper_TIM21500
    (hTI : ∀ n : ℕ, 21000 ≤ n → TI_hyp n (383 / 1000) (641 / 1000) (72 / 100) (1 / 10 ^ 18))
    {n : ℕ} (hn : 21500 ≤ n) (t : ℝ) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  rcases lt_or_ge n 22000 with h | h
  · have hR : (n : ℝ) < 22000 := by exact_mod_cast h
    exact classifier_paper_uncond_21500HM ⟨BstLean.Part180.hq_proved, FREE21M_of_TI hTI⟩ hn hR.le t
  · exact classifier_paper_uncond_182 h t

theorem TIM21500_eq_172
    (hTI : ∀ n : ℕ, 21000 ≤ n → TI_hyp n (383 / 1000) (641 / 1000) (72 / 100) (1 / 10 ^ 18))
    {n : ℕ} (hn : 80000 ≤ n) (hN : (n : ℝ) ≤ 10 ^ 20) (t : ℝ) :
    classifier_paper_TIM21500 hTI (by omega) t = BstLean.Part172.classifier_paper_uncond hn hN t :=
  rfl

end BstLean.Part182

open BstLean.Part182 in
#print axioms classifier_paper_TIM21500
