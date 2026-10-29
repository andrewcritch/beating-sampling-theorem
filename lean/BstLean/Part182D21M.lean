import BstLean.Part181Def

/-!
# Part 182 (file `D21M`): the interface of the descent to `n ≥ 21 000` (CONDITIONAL on TI)

No proof is left open; no `native_decide` or `axiom` is used.

* `roomT21M = 0.0018`: the room for the free Agent event that the frame constant `c_f ≤ 2.09 (TI-lite constant `λ = 0.72`)`
  (Schur certificate, conditional on `TI_hyp`) leaves at `n ≥ 21 000`, after the charges `5·10⁻⁵`
  (the moment event at `21 000`) and `10⁻⁵` (the covariance event).
* `FREE21M_stmt`: Part 181's `FREE22_stmt` with the floor `21 000` and the room
  `roomA + roomX + roomT21M`. It is proved from `TI_hyp` (file `Frame21`/`Comb21`).
* `HQF21M_stmt`: Lemma HQ (Part 180) and `FREE21M_stmt`; the chain files at `21 000` take it as one
  argument.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part181

/-- **The extra room `0.0018` at `n ≥ 21 000`.** -/
noncomputable def roomT21M : ℝ := 18 / 10000

lemma roomT21M_eq : roomT21M = 18 / 10000 := rfl

/-- **The frame junction at `n ≥ 21 000`** (statement of `classifier_paper_free22` with the floor
`21 000` and the room `roomA + roomX + roomT21M`). -/
def FREE21M_stmt : Prop :=
  ∀ {n : ℕ} (_hn : 21000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (_hEA : MeasurableSet EA) {δA : ℝ}
    (_hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (_hroom : δA ≤ BstLean.Part163.roomA + roomX + roomT21M)
    (_hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hAL
      (goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩
          BstLean.Part163.Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL)),
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)}

/-- Lemma HQ and the frame junction at `21 000`, as one argument of the chain theorems. -/
def HQF21M_stmt : Prop := BstLean.Part180.HQ_stmt ∧ FREE21M_stmt

end BstLean.Part182
