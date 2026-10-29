import BstLean.Part163Vac

/-!
# Part 163 (file `Vac2`): the hypotheses of Part 162's `classifier_paper_mom` and
`classifier_paper_psi` are false

Do not use `sorry`, `native_decide` or `axiom`.

The hypothesis `hM` of each theorem is copied verbatim; each is refuted through
`comb23_fluct_false` (the steps are those of the proofs in Part 162).
-/

namespace BstLean.Part163

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part156 BstLean.Part157 BstLean.Part159 BstLean.Part161
open BstLean.Part162

variable {n : ℕ}

/-- **The hypothesis `hM` of Part 162's `classifier_paper_mom` is false** (every `n ≥ 23 000`,
every `t`). -/
theorem paper_mom_hyp_false (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ) :
    ¬ (∀ c ∈ goodSet (HP n) (Ethm (paperCentres n) ∩ Ethp (paperCentres n))
        (HbarW (paperDesign n fT wT hf hw)) hWL,
      ∃ (wl ws σl η CA : ℝ) (q : ℕ) (h0 : 0 < η) (h1 : η < 1)
        (P : LatMom (paperDesign n fT wT hf hw) c σl q),
        0 < wl ∧ 0 < ws ∧ 0 < σl ∧ 0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ CA ∧
        eps0 ws σl < 1 ∧ rootFL wl ws η CA P ≤ 2159 / 10 ^ 6 ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1) (4295 / 10 ^ 6)) := by
  intro hM
  refine comb23_fluct_false (by omega) fT wT hf hw t fun c hc => ?_
  obtain ⟨wl, ws, σl, η, CA, q, h0, h1, P, hwl, hws, hσl, hcA, hCA, hε, hroot, hbias⟩ := hM c hc
  exact ⟨dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1, eps0 ws σl, 2 * wl, σl ^ 2,
    fluct_of_latMom (by omega) _ c hwl hws hσl h0 h1 hcA hCA hε P hroot, hbias⟩

/-- **The hypothesis `hM` of Part 162's `classifier_paper_psi` is false** (every `n ≥ 23 000`,
every `t`). -/
theorem paper_psi_hyp_false (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ) :
    ¬ (∀ c ∈ goodSet (HP n) (Ethm (paperCentres n) ∩ Ethp (paperCentres n))
        (HbarW (paperDesign n fT wT hf hw)) hWL,
      ∃ (wl ws σl η CA CL CS VS βlow : ℝ) (r : ℕ) (h0 : 0 < η) (h1 : η < 1) (hr1 : 1 ≤ r)
        (hr : r ≤ 12) (hCL : 0 < CL) (hCS : 0 < CS) (hVS0 : 0 ≤ VS) (hβ : 0 ≤ βlow)
        (hL2 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v ^ 2
          ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 2)
        (hL4 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v ^ 4
          ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 4)
        (hL6 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v ^ 6
          ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 6)
        (hLr : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v ^ r
          ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ r)
        (hS2 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v ^ 2
          ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 2)
        (hS4 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v ^ 4
          ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 4)
        (hS6 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v ^ 6
          ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 6)
        (hSr : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v ^ r
          ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ r)
        (hVS : ∫ a, (∫ v, (sA (paperDesign n fT wT hf hw) c a v -
            ∫ w, sA (paperDesign n fT wT hf hw) c a w ∂stdGauss (Fin (n - 1))) ^ 2
          ∂stdGauss (Fin (n - 1))) ^ 2 ∂muI n ≤ VS ^ 2)
        (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA (paperDesign n fT wT hf hw) c a v < σl}
          ∂muI n ≤ βlow),
        0 < wl ∧ 0 < ws ∧ 0 < σl ∧ 0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ CA ∧
        eps0 ws σl < 1 ∧
        rootFL wl ws η CA (latMomOfPsi (by omega) (paperDesign n fT wT hf hw) c hr1 hr hCL hCS
          hVS0 hβ hL2 hL4 hL6 hLr hS2 hS4 hS6 hSr hVS hmass) ≤ 2159 / 10 ^ 6 ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1) (4295 / 10 ^ 6)) := by
  intro hM
  refine paper_mom_hyp_false hn fT wT hf hw t fun c hc => ?_
  obtain ⟨wl, ws, σl, η, CA, CL, CS, VS, βlow, r, h0, h1, hr1, hr, hCL, hCS, hVS0, hβ, hL2, hL4,
    hL6, hLr, hS2, hS4, hS6, hSr, hVS, hmass, hwl, hws, hσl, hcA, hCA, hε, hroot, hbias⟩ := hM c hc
  exact ⟨wl, ws, σl, η, CA, 2 * r, h0, h1, latMomOfPsi (by omega) _ c hr1 hr hCL hCS hVS0 hβ hL2
    hL4 hL6 hLr hS2 hS4 hS6 hSr hVS hmass, hwl, hws, hσl, hcA, hCA, hε, hroot, hbias⟩

end BstLean.Part163

open BstLean.Part163 in
#print axioms paper_mom_hyp_false
open BstLean.Part163 in
#print axioms paper_psi_hyp_false
