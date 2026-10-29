import BstLean.Part183D20

/-!
# Part 183 (file `D19`): the interface of the descent to `n ≥ 19 000`

No proof is left open; no `native_decide` or `axiom` is used.

* `FREEg_stmt n₁ ρ`: Part 182's `FREE21M_stmt` with the floor `n₁` and the room
  `roomA + roomX + ρ`; `FREEg_stmt n₁ roomT20 = FREEn_stmt n₁` (`rfl`).
* `roomT19 = 0.0002`; `FREE19_stmt = FREEg_stmt 19000 roomT19`; `HQF19_stmt`.
* `FREEg_mono`: a higher floor and a smaller room give a weaker statement.
-/

namespace BstLean.Part183

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160 BstLean.Part181

/-- **The extra room `0.0002` at `n ≥ 19 000`.** -/
noncomputable def roomT19 : ℝ := 2 / 10000

lemma roomT19_eq : roomT19 = 2 / 10000 := rfl

/-- **The frame junction from the floor `n₁` with the extra room `ρ`.** -/
def FREEg_stmt (n₁ : ℕ) (ρ : ℝ) : Prop :=
  ∀ {n : ℕ} (_hn : n₁ ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (_hEA : MeasurableSet EA) {δA : ℝ}
    (_hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (_hroom : δA ≤ BstLean.Part163.roomA + roomX + ρ)
    (_hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hAL
      (goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩
          BstLean.Part163.Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL)),
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)}

lemma FREEg_roomT20 (n₁ : ℕ) : FREEg_stmt n₁ roomT20 = FREEn_stmt n₁ := rfl

/-- A higher floor and a smaller room give a weaker statement. -/
theorem FREEg_mono {n₁ n₂ : ℕ} {ρ₁ ρ₂ : ℝ} (hn : n₁ ≤ n₂) (hρ : ρ₂ ≤ ρ₁)
    (h : FREEg_stmt n₁ ρ₁) : FREEg_stmt n₂ ρ₂ := by
  intro n hn2 fT wT hf hw t EA hEA δA hA hroom hRA
  exact h (hn.trans hn2) fT wT hf hw t hEA hA (by linarith) hRA

/-- **The frame junction at `n ≥ 19 000`.** -/
def FREE19_stmt : Prop := FREEg_stmt 19000 roomT19

/-- Lemma HQ and the frame junction at `19 000`. -/
def HQF19_stmt : Prop := BstLean.Part180.HQ_stmt ∧ FREE19_stmt

end BstLean.Part183
