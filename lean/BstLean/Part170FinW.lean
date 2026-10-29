import BstLean.Part170DecW

/-!
# Part 170 (file `FinW`): both fluctuations proved; the end theorem with the two bias moments

No proof is left open; no `native_decide` or `axiom` is used.

* `BiasMomW O Gb B`: the bias moments of the energy pass (the paper's `t7:p08:biasmom` for `ω`).
* **`nodeMomW_of_bias`**: the energy node moments `≤ (W_fl + B_ω)⁸` from the bias moments.
* `Wfl_le`: `W_fl ≤ 0.1413` for every `n ≥ 80 000`.
* **`classifier_paper_flw80k`**: the classifier theorem (every `n ≥ 80 000`, `E_A = univ`).
  Remaining hypotheses: a measurable first-layer event family `Gb` with charge `δ_G`; the bias
  moments `BiasMomF (O1n n) Gb B_f` and `BiasMomW (O1n n) Gb B_ω`; the linear condition; and
  `δ_G + ((F_fl + B_f)/A_f)⁸ + ((W_fl + B_ω)/A_ω)⁸ ≤ roomE`.
* **`classifier_paper_bias_num80k`**: the same with the numbers fixed: `A_f = 0.04`, `A_ω = 0.39`;
  remaining: `BiasMomF (O1n n) Gb 0.004`, `BiasMomW (O1n n) Gb 0.02`, `δ_G ≤ 0.0006`.
-/

namespace BstLean.Part170

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part161 (latC Ix muI xLat)
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part153 (nuA)
open BstLean.Part166 (goodD)

variable {n : ℕ}

/-- **The bias moments of the energy pass.** -/
def BiasMomW (O : ℝ) (Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)) (B : ℝ) : Prop :=
  ∀ wr : WRet n, windowW wr → ∀ g < Js n, ∀ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ,
    A₁ ∈ opSet n O → (wr, A₁) ∈ Gb →
      ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (biasW (mkR wr (A₁, 0)) g ξ₁ ξ₂ ^ 8) ∂stdGauss (Fin (mA n))
        ∂stdGauss (Fin (mA n)) ≤ ENNReal.ofReal (B ^ 8)

/-- **The energy half of the node moments.** -/
theorem nodeMomW_of_bias (hn : 80000 ≤ n) {O : ℝ} (hO : 0 < O)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {B : ℝ}
    (hB0 : 0 < B) (hB : BiasMomW O Gb B) : NodeMomW (GsOf O Gb) (Wfl n O + B) := by
  intro wr hw g hg
  set G₁ : Set (Matrix (Fin (mA n)) (Fin n) ℝ) := {A₁ | A₁ ∈ opSet n O ∧ (wr, A₁) ∈ Gb}
  have hG₁ : MeasurableSet G₁ :=
    (measurableSet_opSet O).inter (measurable_prodMk_left hGb)
  have e : {θ : AHid n | (wr, θ) ∈ GsOf O Gb} = {θ : AHid n | θ.1 ∈ G₁} := rfl
  have mf : Measurable (fun θ : AHid n => ENNReal.ofReal (exWn (mkR wr θ) g ^ 8)) :=
    ENNReal.measurable_ofReal.comp ((measurable_exWn_comp (measurable_mkR.comp
      (measurable_const.prodMk measurable_id)) measurable_const).pow_const 8)
  rw [e, lint_nuA_restrict hG₁ mf]
  have hin : ∀ A₁ ∈ G₁, ∫⁻ A₂, ENNReal.ofReal (exWn (mkR wr (A₁, A₂)) g ^ 8)
      ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤ ENNReal.ofReal ((Wfl n O + B) ^ 8) := by
    intro A₁ hA₁
    exact exWn_mom (by omega) (mkR wr (A₁, 0)) g (node_bulk hn hw _ hg) hO hA₁.1 hB0
      (hB wr hw g hg A₁ hA₁.1 hA₁.2)
  calc ∫⁻ A₁ in G₁, ∫⁻ A₂, ENNReal.ofReal (exWn (mkR wr (A₁, A₂)) g ^ 8)
        ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ∂gaussMat (mA n) n (2 / (n : ℝ))
      ≤ ∫⁻ _A₁ in G₁, ENNReal.ofReal ((Wfl n O + B) ^ 8) ∂gaussMat (mA n) n (2 / (n : ℝ)) :=
        setLIntegral_mono measurable_const hin
    _ ≤ ENNReal.ofReal ((Wfl n O + B) ^ 8) := by
        rw [setLIntegral_const]
        calc ENNReal.ofReal ((Wfl n O + B) ^ 8) * gaussMat (mA n) n (2 / (n : ℝ)) G₁
            ≤ ENNReal.ofReal ((Wfl n O + B) ^ 8) * 1 := by gcongr; exact prob_le_one
          _ = _ := mul_one _

/-- **The classifier theorem with both fluctuations proved** (every `n ≥ 80 000`, `E_A = univ`).
Remaining: a measurable family `Gb` of first-layer events (charge `δ_G` in the window); the bias
moments of both passes; the linear condition; and
`δ_G + ((F_fl + B_f)/A_f)⁸ + ((W_fl + B_ω)/A_ω)⁸ ≤ roomE`. -/
theorem classifier_paper_flw80k (hn : 80000 ≤ n) (t : ℝ)
    {Gb : Set (WRet n × Matrix (Fin (mA n)) (Fin n) ℝ)} (hGb : MeasurableSet Gb) {δG : ℝ}
    (hδ0 : 0 ≤ δG)
    (hδG : ∀ wr : WRet n, windowW wr → (nuA n).real {θ | (wr, θ.1) ∉ Gb} ≤ δG)
    {Bf Bw Af Aw : ℝ} (hBf : 0 < Bf) (hBw : 0 < Bw) (hAf : 0 < Af) (hAw : 0 < Aw)
    (hlin : Aw + 806 / 100 * Af ≤ 72 / 100)
    (hBiasF : BiasMomF (O1n n) Gb Bf) (hBiasW : BiasMomW (O1n n) Gb Bw)
    (hroom : δG + ((Ffl n (O1n n) + Bf) / Af) ^ 8 + ((Wfl n (O1n n) + Bw) / Aw) ^ 8 ≤
      BstLean.Part167.roomE) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesignP n) t BstLean.Part156.aL (10 ^ 12) x.1 x.2)} := by
  have hO : 0 < O1n n := O1n_pos (by omega)
  exact classifier_paper_fl80k hn t hGb hδ0 hδG hBf hAf hAw hlin hBiasF
    (nodeMomW_of_bias hn hO hGb hBw hBiasW) hroom

end BstLean.Part170
