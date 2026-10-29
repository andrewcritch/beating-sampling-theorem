import BstLean.Part162LG

/-!
# Part 162: the classifier theorem with an Agent event `E₁`

Role: `delegations/statements/p162-spec.md`, item 4. Do not use `sorry`, `native_decide` or
`axiom`.

`classifier_paper_comb23` (Part 160) asks `REPLA_mix_hyp` on a good set that constrains only the
World data (`HP n`, `HbarW`, the angle events); it does not restrict the Agent weights. The
latitude moments cannot hold for every Agent weight. Part 161's `classifier_paper_agent_fluct`
takes an arbitrary event `E₁` (charged inside `δ_extra`) and `FRAME_A_hyp`; the versions here
are built on it, so that `E₁` may contain the Agent events of the paper.

* **`classifier_agent_mom`**: with the interface `LatMom` on the good set with `E₁`.
* **`classifier_agent_psi`**: with the realized certificate `Ψ` on the good set with `E₁`.
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part157
open BstLean.Part161

variable {n : ℕ}

open BstLean.Part130 BstLean.Part156 BstLean.Part159 in
/-- **The classifier theorem with an Agent event `E₁` (every `n ≥ 16 384`) and the Agent
replacement reduced to the latitude-moment interface.** As Part 161's
`classifier_paper_agent_fluct`: `E₁` is any measurable retained-data event inside the angle
events whose complement (within `HP n`) has charge at most `δ_extra`. Unlike
`classifier_paper_mom`, `E₁` may contain the Agent events (`E_lat`, `E_{c_A}`, `E_base`) on
which the latitude moments hold. -/
theorem classifier_agent_mom (hn : 16384 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {E₁ : Set (Ret n)} (hE₁ : MeasurableSet E₁)
    (hextra : (retDist (paperCentres n)).real (HP n ∩ E₁ᶜ) ≤ δextraL)
    (hEθ : E₁ ⊆ Ethm (paperCentres n) ∩ Ethp (paperCentres n))
    (hFA : FRAME_A_hyp (paperDesign n fT wT hf hw) (cfL / n)
      (goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hWL))
    (hM : ∀ c ∈ goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hWL,
      ∃ (wl ws σl η CA : ℝ) (q : ℕ) (h0 : 0 < η) (h1 : η < 1)
        (P : LatMom (paperDesign n fT wT hf hw) c σl q),
        0 < wl ∧ 0 < ws ∧ 0 < σl ∧ 0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ CA ∧
        eps0 ws σl < 1 ∧ rootFL wl ws η CA P ≤ 2159 / 10 ^ 6 ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_paper_agent_fluct hn fT wT hf hw t hE₁ hextra hEθ hFA fun c hc => ?_
  obtain ⟨wl, ws, σl, η, CA, q, h0, h1, P, hwl, hws, hσl, hcA, hCA, hε, hroot, hbias⟩ := hM c hc
  exact ⟨dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1, eps0 ws σl, 2 * wl, σl ^ 2,
    fluct_of_latMom (by omega) _ c hwl hws hσl h0 h1 hcA hCA hε P hroot, hbias⟩

open BstLean.Part130 BstLean.Part156 BstLean.Part159 in
/-- **The classifier theorem with an Agent event `E₁` (every `n ≥ 16 384`) and the Agent
replacement reduced to the realized certificate `Ψ`**, `V_S`, the mass below the floor, the norm
of `c_A`, the root sum and the bias (on the good set with `E₁`). -/
theorem classifier_agent_psi (hn : 16384 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {E₁ : Set (Ret n)} (hE₁ : MeasurableSet E₁)
    (hextra : (retDist (paperCentres n)).real (HP n ∩ E₁ᶜ) ≤ δextraL)
    (hEθ : E₁ ⊆ Ethm (paperCentres n) ∩ Ethp (paperCentres n))
    (hFA : FRAME_A_hyp (paperDesign n fT wT hf hw) (cfL / n)
      (goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hWL))
    (hM : ∀ c ∈ goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hWL,
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
          (dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_agent_mom hn fT wT hf hw t hE₁ hextra hEθ hFA fun c hc => ?_
  obtain ⟨wl, ws, σl, η, CA, CL, CS, VS, βlow, r, h0, h1, hr1, hr, hCL, hCS, hVS0, hβ, hL2, hL4,
    hL6, hLr, hS2, hS4, hS6, hSr, hVS, hmass, hwl, hws, hσl, hcA, hCA, hε, hroot, hbias⟩ := hM c hc
  exact ⟨wl, ws, σl, η, CA, 2 * r, h0, h1, latMomOfPsi (by omega) _ c hr1 hr hCL hCS hVS0 hβ hL2
    hL4 hL6 hLr hS2 hS4 hS6 hSr hVS hmass, hwl, hws, hσl, hcA, hCA, hε, hroot, hbias⟩

end BstLean.Part162

open BstLean.Part162 in
#print axioms classifier_agent_mom
open BstLean.Part162 in
#print axioms classifier_agent_psi
