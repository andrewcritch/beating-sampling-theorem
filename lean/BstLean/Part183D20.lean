import BstLean.Part182D21M

/-!
# Part 183 (file `D20`): the interface of the descent to `n ≥ 20 000`

No proof is left open; no `native_decide` or `axiom` is used.

* `roomT20 = 0.0005`: the room for the free Agent event that the frame side leaves at
  `n ≥ 20 000` (to be proved by the frame junction at `20 000`).
* `FREEn_stmt n₁`: Part 182's `FREE21M_stmt` with the floor `n₁` and the room
  `roomA + roomX + roomT20`; `FREE20_stmt = FREEn_stmt 20000`.
* `FREEn_of_21M`: Part 182's `FREE21M_stmt` gives `FREEn_stmt 21000` (`roomT20 ≤ roomT21M`).
* `HQFn_stmt n₁`: Lemma HQ (Part 180) and `FREEn_stmt n₁` (the argument of the chain at
  `n ≥ 20 000`); `HQF20_stmt = HQFn_stmt 20000`.
-/

namespace BstLean.Part183

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part181

/-- **The extra room `0.0005` at `n ≥ 20 000`.** -/
noncomputable def roomT20 : ℝ := 5 / 10000

lemma roomT20_eq : roomT20 = 5 / 10000 := rfl

/-- **The frame junction from the floor `n₁`** (Part 182's `FREE21M_stmt` with the floor `n₁` and
the room `roomA + roomX + roomT20`). -/
def FREEn_stmt (n₁ : ℕ) : Prop :=
  ∀ {n : ℕ} (_hn : n₁ ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (_hEA : MeasurableSet EA) {δA : ℝ}
    (_hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (_hroom : δA ≤ BstLean.Part163.roomA + roomX + roomT20)
    (_hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hAL
      (goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩
          BstLean.Part163.Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL)),
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)}

/-- **The frame junction at `n ≥ 20 000`.** -/
def FREE20_stmt : Prop := FREEn_stmt 20000

/-- Part 182's junction at `21 000` (room `+ 0.0018`) gives the junction from `21 000` with the
smaller room `+ 0.0005`. -/
theorem FREEn_of_21M (h : BstLean.Part182.FREE21M_stmt) : FREEn_stmt 21000 := by
  intro n hn fT wT hf hw t EA hEA δA hA hroom hRA
  refine h hn fT wT hf hw t hEA hA ?_ hRA
  have : roomT20 ≤ BstLean.Part182.roomT21M := by
    rw [roomT20_eq, BstLean.Part182.roomT21M_eq]; norm_num
  linarith

/-- Lemma HQ and the frame junction from `n₁`, as one argument of the chain theorems. -/
def HQFn_stmt (n₁ : ℕ) : Prop := BstLean.Part180.HQ_stmt ∧ FREEn_stmt n₁

/-- Lemma HQ and the frame junction at `20 000`. -/
def HQF20_stmt : Prop := HQFn_stmt 20000

/-- Part 182's `HQF21M_stmt` gives `HQFn_stmt 21000`. -/
theorem HQFn_of_21M (h : BstLean.Part182.HQF21M_stmt) : HQFn_stmt 21000 :=
  ⟨h.1, FREEn_of_21M h.2⟩

end BstLean.Part183
