import BstLean.Part165Mass

/-!
# Part 165 (file `End`): the end theorem with the mass below the floor discharged

No proof is left open; no `native_decide` or `axiom` is used.

* `goodC n D EA = goodA n D (EA ∩ agentEv D (SXqN n 20))`: Part 164's good set with the new event.
* **`mass_of_goodC`**: on `goodC`, `∫_a ν{σ < √γ_A·sd} ≤ betaM n sd` for `0 ≤ sd < s0`.
* **`SX20_ret_charge`**: the charge of the new event on the retained data, `≤ 5·10⁻⁵`.
* `roomC = roomB − 5·10⁻⁵ ≥ 0.002992`.
* **`classifier_paper_free23_mass40`**: Part 164's `classifier_paper_free23_cA8` with the mass
  hypothesis REMOVED: the floor is `σ_l = √γ_A·sd` with a caller's `0 < sd < s0 = 0.5087`, and
  `β_low = betaM n sd` enters the root sum through its PROOF `mass_of_goodC`.
-/

namespace BstLean.Part165

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160
open BstLean.Part161 (muI lamX sigX BIAS_hyp)
open BstLean.Part162 (sgA psiA rootFL latMomOfPsi12e eps0 dPaper)
open BstLean.Part164 (goodA window_goodA goodC16_of_goodA hE8_of_good CAn E0 E0_nonneg roomB
  roomB_ge)

variable {n : ℕ}

/-- The good set of the end theorem: Part 164's `goodA` with the free event
`E_A ∩ agentEv D (SXqN n 20)`. -/
def goodC (n : ℕ) (D : Design n) (EA : Set (Ret n)) : Set (Ret n) :=
  goodA n D (EA ∩ agentEv D (SXqN n 20))

/-- **The mass below the floor on the good set**: `∫_a ν{σ < √γ_A·sd} ≤ betaM n sd`. -/
theorem mass_of_goodC (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {EA : Set (Ret n)} {c : Ret n} (hc : c ∈ goodC n (paperDesign n fT wT hf hw) EA)
    {sd : ℝ} (hsd0 : 0 ≤ sd) (hsd : sd < s0) :
    ∫ a, (stdGauss (Fin (n - 1))).real
        {v | sgA (paperDesign n fT wT hf hw) c a v < √(2 / (n : ℝ)) * sd} ∂muI n ≤
      betaM n sd := by
  set D := paperDesign n fT wT hf hw
  have hn16 : 16384 ≤ n := by omega
  obtain ⟨hτ, hθ0, hθ1⟩ := window_goodA hn16 fT wT hf hw _ c hc
  have hG := goodC16_of_goodA hn16 fT wT hf hw hc
  have hSc : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n := hc.2.2.1.1.2 hτ
  have hS20 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXqN n 20 := hc.2.1.2.1.1.2 hτ
  obtain ⟨hxi, -, -, hpos, hX4, hN22, -⟩ := centre16 hn16 hτ hθ0 hθ1 hG
  have heb := eb16_sharp hn16 hτ hθ0 hθ1 hG hSc
  have hb : D.bA c.1 c.2.1.1 =
      (1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) :=
    paperDesign_agentCentre fT wT hf hw c
  rw [← hb] at hxi hpos heb
  have hXi := (BstLean.Part153.XiS_le_Xi4 (by omega) c.2.1.1.1 c.2.1.1.2 c.1.2 hτ).trans hX4
  exact mass_order40 hn D c hτ hθ0 hθ1 hpos hXi heb hxi hN22 hS20 hsd0 hsd

/-- **The charge of the new event on the retained data**: `≤ 5·10⁻⁵` (`n ≥ 16 384`). -/
theorem SX20_ret_charge (hn : 16384 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) :
    (retDist (paperCentres n)).real (agentEv (paperDesign n fT wT hf hw) (SXqN n 20))ᶜ ≤
      5 / 100000 := by
  rw [agentEv_compl]
  exact retDist_agent_charge (paperDesign n fT wT hf hw) (paperDesign_tauWorld fT wT hf hw)
    (measurableSet_SXqN n 20) (by norm_num) (fun c τ hτ => SX20_charge hn c τ hτ)

/-- The room that remains for the free Agent event: `roomB − 5·10⁻⁵`. -/
noncomputable def roomC : ℝ := roomB - 5 / 100000

/-- **The room that remains**: `0.002992 ≤ roomC`. -/
theorem roomC_ge : (2992 : ℝ) / 10 ^ 6 ≤ roomC := by
  unfold roomC; have := roomB_ge; linarith

/-- **The free-event classifier theorem with the mass below the floor discharged (every
`n ≥ 23 000`).** IF `E_A` is a measurable event with
`Pr(HP n ∩ E_{θ−} ∩ E_{θ+} ∩ E_Aᶜ) ≤ δ_A ≤ roomC`, and for every `c` in the good set `goodC`
(which contains `E_A ∩ agentEv D (SXqN n 20) ∩ EcA ∩ Eop2 ∩ Eframe D`) there are constants with
the two order-12 certificates, a floor `σ_l = √γ_A·sd` with `0 < sd < s0 = 0.5087`, `ε₀ < 1`, the
root sum with `C_A = CAn n`, `E = E0 n` and `β_low = betaM n sd` `≤ 0.002159`, and
`BIAS_hyp … 0.004295`, THEN success `≥ 99/100`. The mass bound enters the root sum through its
PROOF `mass_of_goodC` on the good set. -/
theorem classifier_paper_free23_mass40 (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomC)
    (hM : ∀ (c : Ret n) (hc : c ∈ goodC n (paperDesign n fT wT hf hw) EA),
      ∃ (wl ws sd η CL CS : ℝ) (h0 : 0 < η) (h1 : η < 1) (hCL : 0 < CL)
        (hCS : 0 < CS) (hsd0 : 0 < sd) (hsd : sd < s0)
        (hL12 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 12)
        (hS12 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 12),
        0 < wl ∧ 0 < ws ∧ eps0 ws (√(2 / (n : ℝ)) * sd) < 1 ∧
        rootFL wl ws η (CAn n) (latMomOfPsi12e (by omega) (paperDesign n fT wT hf hw) c hCL hCS
          (E0_nonneg n) (betaM_nonneg n sd) hL12 hS12 (hE8_of_good (by omega) fT wT hf hw hc)
          (mass_of_goodC hn fT wT hf hw hc hsd0.le hsd)) ≤ 2159 / 10 ^ 6 ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws (√(2 / (n : ℝ)) * sd) η h0 h1)
          (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  set D := paperDesign n fT wT hf hw
  set S := BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
    BstLean.Part159.Ethp (paperCentres n)
  have hEA' : MeasurableSet (EA ∩ agentEv D (SXqN n 20)) :=
    hEA.inter (measurableSet_agentEv D (measurableSet_SXqN n 20))
  have hA' : (retDist (paperCentres n)).real (S ∩ (EA ∩ agentEv D (SXqN n 20))ᶜ) ≤
      δA + 5 / 100000 := by
    have hsub : S ∩ (EA ∩ agentEv D (SXqN n 20))ᶜ ⊆ (S ∩ EAᶜ) ∪ (agentEv D (SXqN n 20))ᶜ := by
      intro c hc
      by_cases h1 : c ∈ EA
      · exact Or.inr fun h2 => hc.2 ⟨h1, h2⟩
      · exact Or.inl ⟨hc.1, h1⟩
    refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
    have c1 := SX20_ret_charge (by omega) fT wT hf hw
    linarith
  have hroom' : δA + 5 / 100000 ≤ roomB := by unfold roomC at hroom; linarith
  refine BstLean.Part164.classifier_paper_free23_cA8 hn fT wT hf hw t hEA' hA' hroom'
    fun c hc => ?_
  obtain ⟨wl, ws, sd, η, CL, CS, h0, h1, hCL, hCS, hsd0, hsd, hL12, hS12, hwl, hws, hε, hroot,
    hbias⟩ := hM c hc
  have hσl : 0 < √(2 / (n : ℝ)) * sd := by
    have : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    positivity
  exact ⟨wl, ws, √(2 / (n : ℝ)) * sd, η, CL, CS, betaM n sd, h0, h1, hCL, hCS, betaM_nonneg n sd,
    hL12, hS12, mass_of_goodC hn fT wT hf hw hc hsd0.le hsd, hwl, hws, hσl, hε, hroot, hbias⟩

end BstLean.Part165
