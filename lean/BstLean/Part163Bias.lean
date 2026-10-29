import BstLean.Part163Comb
import BstLean.Part162All

/-!
# Part 163 (file `Bias`): the combination with Parts 161 and 162

Do not use `sorry`, `native_decide` or `axiom`.

* `classifier_paper_free23_fluct`: `classifier_paper_free23` with `REPLA_mix_hyp` replaced by the
  named hypotheses of Part 161 (`FLUCT_chi_hyp … 0.002159`, `BIAS_hyp … 0.004295`), asked on the
  same good set `goodSet (HP n) (E_{θ−} ∩ E_{θ+} ∩ E_A ∩ Eframe D) (HbarW D) hWL`.
* **`classifier_paper_free23_psi12e`**: the same with the hypothesis in the form of Part 162's
  `classifier_agent_psi12e` (the two order-12 certificates of Proposition LG, the eighth moment of
  `σ`, the mass below the floor, `|c_A|² ≤ C_A`, the root sum `≤ 0.002159` and `BIAS_hyp`). Every
  `n ≥ 23 000`; NO `FRAME_A_hyp`; one free Agent event `E_A` with `δ_A ≤ roomA`.
-/

namespace BstLean.Part163

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160
open BstLean.Part161 (FLUCT_chi_hyp BIAS_hyp SplitData muI repla_of_hyps_chi lamX sigX)
open BstLean.Part162

variable {n : ℕ}

/-- **The free-event classifier theorem with Part 161's named hypotheses (every `n ≥ 23 000`).** -/
theorem classifier_paper_free23_fluct (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomA)
    (hFl : ∀ c ∈ goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩ Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL,
      ∃ (d : SplitData n) (ε₀ δ₀ slow : ℝ),
        FLUCT_chi_hyp (paperDesign n fT wT hf hw) c d ε₀ δ₀ slow (2159 / 10 ^ 6) ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c d (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_paper_free23 hn fT wT hf hw t hEA hA hroom ?_
  refine repla_of_hyps_chi (by omega) _ t (fun c hc => ?_) hFl
  exact BstLean.Part161.window_paper (by omega) fT wT hf hw hc.1.1 hc.2.1.1.1 hc.2.1.1.2

/-- **The free-event classifier theorem with the Agent replacement in the form of Part 162's
`classifier_agent_psi12e` (every `n ≥ 23 000`).** IF `E_A` is a measurable event with
`Pr(HP n ∩ E_{θ−} ∩ E_{θ+} ∩ E_Aᶜ) ≤ δ_A ≤ roomA`, and for every `c` in
`goodSet (HP n) (E_{θ−} ∩ E_{θ+} ∩ E_A ∩ Eframe D) (HbarW D) hWL` there are constants with the two
order-12 certificates `‖Ψ_λ‖₁₂ ≤ C_λ/n`, `‖Ψ_σ‖₁₂ ≤ C_σ/n`, the eighth moment `∫∫σ⁸ ≤ E⁸`, the mass
below the floor `≤ β_low`, `0 < |c_A|² ≤ C_A`, `ε₀ < 1`, the root sum `≤ 0.002159` and
`BIAS_hyp … 0.004295`, THEN success `≥ 99/100`. -/
theorem classifier_paper_free23_psi12e (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomA)
    (hM : ∀ c ∈ goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩ Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL,
      ∃ (wl ws σl η CA CL CS E βlow : ℝ) (h0 : 0 < η) (h1 : η < 1) (hCL : 0 < CL)
        (hCS : 0 < CS) (hE : 0 ≤ E) (hβ : 0 ≤ βlow)
        (hL12 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 12)
        (hS12 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 12)
        (hE8 : ∫ a, ∫ v, sgA (paperDesign n fT wT hf hw) c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
          E ^ 8)
        (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA (paperDesign n fT wT hf hw) c a v < σl}
          ∂muI n ≤ βlow),
        0 < wl ∧ 0 < ws ∧ 0 < σl ∧ 0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ CA ∧
        eps0 ws σl < 1 ∧
        rootFL wl ws η CA (latMomOfPsi12e (by omega) (paperDesign n fT wT hf hw) c hCL hCS hE hβ
          hL12 hS12 hE8 hmass) ≤ 2159 / 10 ^ 6 ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_paper_free23_fluct hn fT wT hf hw t hEA hA hroom fun c hc => ?_
  obtain ⟨wl, ws, σl, η, CA, CL, CS, E, βlow, h0, h1, hCL, hCS, hE, hβ, hL12, hS12, hE8, hmass,
    hwl, hws, hσl, hcA, hCA, hε, hroot, hbias⟩ := hM c hc
  exact ⟨dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1, eps0 ws σl, 2 * wl, σl ^ 2,
    fluct_of_latMom (by omega) _ c hwl hws hσl h0 h1 hcA hCA hε
      (latMomOfPsi12e (by omega) _ c hCL hCS hE hβ hL12 hS12 hE8 hmass) hroot, hbias⟩

end BstLean.Part163

open BstLean.Part163 in
#print axioms classifier_paper_free23_fluct
open BstLean.Part163 in
#print axioms classifier_paper_free23_psi12e
