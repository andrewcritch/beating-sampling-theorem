import BstLean.Part180TopJ
import BstLean.Part180HQFl

/-!
# Part 180 (file `TopF`): the top theorem at `n ≥ 24 000` with Lemma HQ discharged

No proof is left open; no `native_decide` or `axiom` is used.

* `BstLean.Part180.HQ_holds : HQ_stmt` (from `fluct_of_latMom_hq`, file `HQFl`).
* **`BstLean.Part180.N24.classifier_paper_JM24`**: Part 179's `classifier_paper_JM49n` at
  `n ≥ 24 000` with `JM_hyp n 5` and the bias root `0.00533` (split `0.00112 + 0.00533`), room
  `BstLean.Part179.N30.N27.N26.N25.roomK`; it is `classifier_paper_JM24H HQ_holds`.
-/

namespace BstLean.Part180

/-- **Lemma HQ in the form `HQ_stmt`** (from `fluct_of_latMom_hq`, file `HQFl`). -/
theorem HQ_holds : HQ_stmt := by
  unfold HQ_stmt
  intro n hn D c t wl ws σl η hwl hws hσl h0 h1 hcA CA hCA hε q P lam lam' hl0 hl1 hl0' hl1' hfl hsum
  exact fluct_of_latMom_hq hn D c t hwl hws hσl h0 h1 hcA hCA hε P hl0 hl1 hl0' hl1' hsum

end BstLean.Part180

namespace BstLean.Part180.N24

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part156 BstLean.Part157 BstLean.Part160 BstLean.Part167
open BstLean.Part161 (BIAS_hyp)
open BstLean.Part162 (dPaper)
open BstLean.Part166 (goodD)

variable {n : ℕ}

/-- **The top theorem at `n ≥ 24 000` with Lemma HQ** (no `hHQ` argument). -/
theorem classifier_paper_JM24 (hn : 24000 ≤ n) (hJM : JM_hyp n 5)
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ BstLean.Part179.N30.N27.N26.N25.roomK)
    (hB : ∀ c ∈ goodD n (paperDesign n fT wT hf hw) EA,
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (452 / 1000))
          (1 / 50) (by norm_num) (by norm_num)) (533 / 10 ^ 5)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  BstLean.Part179.N30.N27.N26.N24.classifier_paper_JM24H BstLean.Part180.HQ_holds hn hJM fT wT hf hw
    t hEA hA hroom hB

end BstLean.Part180.N24
