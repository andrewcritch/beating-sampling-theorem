import BstLean.Part169In

/-!
# Part 169 (file `Mom`): the end theorem with `BIAS_hyp` replaced by the moment inputs

No proof is left open; no `native_decide` or `axiom` is used.

* `MomIn c ε v_max a_ω a_f H_f C_v`: the inputs of Part 08 that are not yet proved in Lean, for
  the retained value `c`, on the kept indices `K = KR c` (measure `muI n`):
  `|V| ≤ v_max`; `∫_K (n(ω̄ − ω̃))⁸ ≤ a_ω⁸`; `∫_K (n(f̄ − f̃))⁸ ≤ a_f⁸`; `∫_K f̄⁴ ≤ H_f⁴`;
  `∫_K f̄²⁴ ≤ H_f²⁴`; `∫_K (nV)² ≤ C_v²`; and the integrability of the functions involved.
* **`biasP_goodD`**: on `goodD`, `MomIn` and `P_B ≤ 0.004295²` (with `d = dStar`,
  `χ = χ_A⁺`) give `BIASP c`. The floor `S̄ ≥ γ_A dStar` (`Sb_lower`) and the bound on `|c_A|²`
  (`cA_input`) are discharged.
* **`classifier_paper_mom80k`**: the classifier theorem for the paper's program, with a
  separate bias event `E_bias`, where `BIAS_hyp` is replaced by `MomIn` on
  `goodD n D (E_A ∩ E_bias)` and the numerical condition `P_B ≤ 0.004295²`.
-/

namespace BstLean.Part169

open MeasureTheory Real
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (muI)
open BstLean.Part166 (goodD)

variable {n : ℕ}

/-- **The moment inputs of Part 08** (not yet proved in Lean) for the retained value `c`. -/
structure MomIn (c : Ret n) (ε vmax aw af Hf Cv : ℝ) : Prop where
  hVm : ∀ a ∈ KR c, |VR c a| ≤ vmax
  iW2 : IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 2) (KR c) (muI n)
  iW6 : IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 6) (KR c) (muI n)
  iW8 : IntegrableOn (fun a => ((n : ℝ) * (wbR c a - wtR c a)) ^ 8) (KR c) (muI n)
  iF2 : IntegrableOn (fun a => ((n : ℝ) * (fbR c a - ftR c a)) ^ 2) (KR c) (muI n)
  iF4 : IntegrableOn (fun a => ((n : ℝ) * (fbR c a - ftR c a)) ^ 4) (KR c) (muI n)
  iF8 : IntegrableOn (fun a => ((n : ℝ) * (fbR c a - ftR c a)) ^ 8) (KR c) (muI n)
  if4 : IntegrableOn (fun a => fbR c a ^ 4) (KR c) (muI n)
  if24 : IntegrableOn (fun a => fbR c a ^ 24) (KR c) (muI n)
  ifF2 : IntegrableOn (fun a => fbR c a ^ 2 * ((n : ℝ) * (fbR c a - ftR c a)) ^ 2) (KR c)
    (muI n)
  ifF6 : IntegrableOn (fun a => fbR c a ^ 6 * ((n : ℝ) * (fbR c a - ftR c a)) ^ 6) (KR c)
    (muI n)
  iV : IntegrableOn (fun a => ((n : ℝ) * VR c a) ^ 2) (KR c) (muI n)
  hW8 : ∫ a in KR c, ((n : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI n ≤ aw ^ 8
  hF8 : ∫ a in KR c, ((n : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI n ≤ af ^ 8
  hf4 : ∫ a in KR c, fbR c a ^ 4 ∂muI n ≤ Hf ^ 4
  hf24 : ∫ a in KR c, fbR c a ^ 24 ∂muI n ≤ Hf ^ 24
  hV : ∫ a in KR c, ((n : ℝ) * VR c a) ^ 2 ∂muI n ≤ Cv ^ 2

/-- **`BIASP` on the good set from the moment inputs.** -/
theorem biasP_goodD (hn : 16384 ≤ n) {EA : Set (Ret n)} {c : Ret n}
    (hc : c ∈ goodD n (paperDesignP n) EA) {ε vmax aw af Hf Cv : ℝ} (hε1 : ε < 1)
    (hT : 0 < ε - vmax / dStar) (haw : 0 < aw) (haf : 0 < af) (hHf : 0 < Hf) (hCv : 0 < Cv)
    (hM : MomIn c ε vmax aw af Hf Cv)
    (hnum : PB n (BstLean.Part164.chiUp n / n) dStar ε vmax aw af Hf Cv ≤ (4295 / 10 ^ 6) ^ 2) :
    BIASP c := by
  obtain ⟨he, hcA⟩ := cA_input hn hc
  exact biasP_of_inputs (by omega) c he dStar_ge hε1 hT haw haf hHf hCv
    (fun a ha => Sb_lower (by omega) c ha) hcA hM.hVm hM.iW2 hM.iW6 hM.iW8 hM.iF2 hM.iF4 hM.iF8
    hM.if4 hM.if24 hM.ifF2 hM.ifF6 hM.iV hM.hW8 hM.hF8 hM.hf4 hM.hf24 hM.hV hnum

/-- **The classifier theorem for the paper's program, with `BIAS_hyp` replaced by the moment
inputs of Part 08** (every `n ≥ 80 000`). Remaining: the moment inputs `MomIn` on
`goodD n D (E_A ∩ E_bias)`, the numerical condition `P_B ≤ 0.004295²`, the charges of `E_A` and
of the bias event, and `δ_A + δ_bias ≤ roomE`. -/
theorem classifier_paper_mom80k (hn : 80000 ≤ n) (t : ℝ)
    {EA Eb : Set (Ret n)} (hEA : MeasurableSet EA) (hEb : MeasurableSet Eb) {δA δb : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hb : (retDist (paperCentres n)).real Ebᶜ ≤ δb)
    (hroom : δA + δb ≤ BstLean.Part167.roomE)
    {ε vmax aw af Hf Cv : ℝ} (hε1 : ε < 1)
    (hT : 0 < ε - vmax / dStar) (haw : 0 < aw) (haf : 0 < af) (hHf : 0 < Hf) (hCv : 0 < Cv)
    (hnum : PB n (BstLean.Part164.chiUp n / n) dStar ε vmax aw af Hf Cv ≤ (4295 / 10 ^ 6) ^ 2)
    (hM : ∀ c ∈ goodD n (paperDesignP n) (EA ∩ Eb), MomIn c ε vmax aw af Hf Cv) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_bias80k hn t hEA hEb hA hb hroom fun c hc =>
    biasP_goodD (by omega) hc hε1 hT haw haf hHf hCv (hM c hc) hnum

end BstLean.Part169
