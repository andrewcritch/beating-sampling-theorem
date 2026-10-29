import BstLean.Part180Split

/-!
# Part 181 (file `Def`): the interface of the frame junction at `n ≥ 22 000`

No proof is left open; no `native_decide` or `axiom` is used.

* `FREE22_stmt`: the statement of Part 163's `classifier_paper_free23` with the floor `22 000`
  in place of `23 000` and the room `roomA + roomX` (`roomX = 6·10⁻⁴`) in place of `roomA` (same
  free Agent event, same frame event `Eframe` in the set of the Agent replacement). It is proved as `BstLean.Part181.classifier_paper_free22`
  (file `Comb`).
* `HQF_stmt`: Lemma HQ (Part 180) and `FREE22_stmt` together. The chain files of this part take
  one argument `hHQ : HQF_stmt`; the end file discharges it.
-/

namespace BstLean.Part181

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160

/-- **The extra room `6·10⁻⁴`** that the frame junction at `22 000` gives to the free Agent
event: the frame constant `2.765` (in place of `3.05`) leaves this much of the tail budget of the
ledger unused. -/
noncomputable def roomX : ℝ := 6 / 10000

lemma roomX_eq : roomX = 6 / 10000 := rfl

/-- **The frame junction at `n ≥ 22 000`** (statement of `classifier_paper_free23` with the
floor `22 000`). -/
def FREE22_stmt : Prop :=
  ∀ {n : ℕ} (_hn : 22000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (_hEA : MeasurableSet EA) {δA : ℝ}
    (_hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (_hroom : δA ≤ BstLean.Part163.roomA + roomX)
    (_hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hAL
      (goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩
          BstLean.Part163.Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL)),
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)}

/-- Lemma HQ and the frame junction at `22 000`, as one argument of the chain theorems. -/
def HQF_stmt : Prop := BstLean.Part180.HQ_stmt ∧ FREE22_stmt

end BstLean.Part181
