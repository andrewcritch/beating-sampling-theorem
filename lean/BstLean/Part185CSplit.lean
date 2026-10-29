import BstLean.Part184Def2
import BstLean.Part183Def

/-!
# Part 185 (file `CSplit`): the Agent-replacement plumbing; `roomL = −0.00265`; `HQG n` (Lemma HQ, the frame junction from a floor `n₁ ≤ n` with room `roomL`, `EnB_stmt` and `EnFB_stmt`) is the argument of every chain theorem.

No proof is left open; no `native_decide` or `axiom` is used.

A copy of the Part 184 `M` chain (floor 17 500) for every `n ≥ 17 250` (statistics cap `n ≤ 17 500`), with the removal tolerance `η = 1/250` and the floor `sd = 0.4482` (file `Part185Q`),
namespaces `….J1725` / `BstLean.Part185.C`. The constants above are those of the Lean statements; the
docstrings of copied lemmas can carry older numbers, and the Lean statements are authoritative.
-/

namespace BstLean.Part185.C

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160
open BstLean.Part161 (FLUCT_hyp BIAS_hyp SplitData muI lamX sigX)
open BstLean.Part162
open BstLean.Part163 (Eframe)
open BstLean.Part180 (HQ_stmt rootFLH)
open BstLean.Part181 (roomX)

variable {n : ℕ}

/-- **The extra room `−0.0021` at `n ≥ 17 750`** (the frame junction is stated with this literal). -/
noncomputable def roomL : ℝ := -(265 / 100000)

lemma roomL_eq : roomL = -(265 / 100000) := rfl

/-- **The argument of the chain at `n`**: Lemma HQ (Part 180), the frame junction from some floor
`n₁ ≤ n` (room `roomA + roomX + roomT19`, file `D19`), and the centred energy bound `EnJ_stmt`
(file `Def`). -/
def HQG (n : ℕ) : Prop :=
  HQ_stmt ∧ (∃ n₁ : ℕ, n₁ ≤ n ∧ BstLean.Part183.FREEg_stmt n₁ BstLean.Part185.C.roomL) ∧ BstLean.Part184.EnB_stmt ∧
    BstLean.Part184.EnFB_stmt

/-- `HQG n` from Lemma HQ, the junction from `n₁ ≤ n` and `EnJ_stmt`. -/
theorem HQG_of {n₁ : ℕ} (h : HQ_stmt ∧ BstLean.Part183.FREEg_stmt n₁ BstLean.Part185.C.roomL) (hEn : BstLean.Part184.EnB_stmt)
    (hFn : BstLean.Part184.EnFB_stmt) (hn : n₁ ≤ n) : HQG n :=
  ⟨h.1, ⟨n₁, hn, h.2⟩, hEn, hFn⟩

/-- **The free-event classifier theorem with `FLUCT_hyp` (every `n ≥ 21 000`).** -/
theorem classifier_paper_free21_fluctHM (hF : ∃ n₁ : ℕ, n₁ ≤ n ∧ BstLean.Part183.FREEg_stmt n₁ BstLean.Part185.C.roomL) (hn : 17250 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ BstLean.Part163.roomA + roomX + BstLean.Part185.C.roomL) {hfl hb : ℝ} (hsum : hfl + hb ≤ 6454 / 10 ^ 6)
    (hFl : ∀ c ∈ goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩ Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL,
      ∃ d : SplitData n, FLUCT_hyp (paperDesign n fT wT hf hw) t c d hfl ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c d hb) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  obtain ⟨n₁, hn₁, hF⟩ := hF
  refine hF hn₁ fT wT hf hw t hEA hA hroom ?_
  refine BstLean.Part177.repla_of_hypsG (by omega) _ t hsum (fun c hc => ?_) hFl
  exact BstLean.Part161.window_paper (by omega) fT wT hf hw hc.1.1 hc.2.1.1.1 hc.2.1.1.2

/-- **The free-event classifier theorem with the Lemma HQ root (every `n ≥ 21 000`).** -/
theorem classifier_paper_free21_psi12eHM (hHQ : HQG n) (hn : 17250 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ BstLean.Part163.roomA + roomX + BstLean.Part185.C.roomL) {hfl hb : ℝ} (hsum : hfl + hb ≤ 6454 / 10 ^ 6)
    (hM : ∀ c ∈ goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩ Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL,
      ∃ (wl ws σl η CA CL CS E βlow lam lam' : ℝ) (h0 : 0 < η) (h1 : η < 1) (hCL : 0 < CL)
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
        eps0 ws σl < 1 ∧ 0 < lam ∧ lam < 1 ∧ 0 < lam' ∧ lam' < 1 ∧
        rootFLH wl ws η CA lam lam' (latMomOfPsi12e (by omega) (paperDesign n fT wT hf hw) c hCL hCS
          hE hβ hL12 hS12 hE8 hmass) ≤ hfl ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1) hb) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_paper_free21_fluctHM hHQ.2.1 hn fT wT hf hw t hEA hA hroom hsum fun c hc => ?_
  obtain ⟨wl, ws, σl, η, CA, CL, CS, E, βlow, lam, lam', h0, h1, hCL, hCS, hE, hβ, hL12, hS12, hE8,
    hmass, hwl, hws, hσl, hcA, hCA, hε, hl0, hl1, hl0', hl1', hroot, hbias⟩ := hM c hc
  exact ⟨dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1,
    hHQ.1 (by omega) _ c t hwl hws hσl h0 h1 hcA hCA hε
      (latMomOfPsi12e (by omega) _ c hCL hCS hE hβ hL12 hS12 hE8 hmass) hl0 hl1 hl0' hl1' hroot,
    hbias⟩

open BstLean.Part164 (goodA CAn roomB) in
/-- **Part 177's `N43.classifier_paper_free21_cA8EG` with the Lemma HQ root.** -/
theorem classifier_paper_free21_cA8EHM (hHQ : HQG n) (hn : 17250 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomB + roomX + BstLean.Part185.C.roomL) {hfl hb : ℝ} (hsum : hfl + hb ≤ 6454 / 10 ^ 6)
    (hM : ∀ (c : Ret n) (hc : c ∈ goodA n (paperDesign n fT wT hf hw) EA),
      ∃ (wl ws σl η CL CS βlow E lam lam' : ℝ) (h0 : 0 < η) (h1 : η < 1) (hCL : 0 < CL)
        (hCS : 0 < CS) (hβ : 0 ≤ βlow) (hE : 0 ≤ E)
        (hL12 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 12)
        (hS12 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 12)
        (hE8 : ∫ a, ∫ v, sgA (paperDesign n fT wT hf hw) c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
          E ^ 8)
        (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA (paperDesign n fT wT hf hw) c a v < σl}
          ∂muI n ≤ βlow),
        0 < wl ∧ 0 < ws ∧ 0 < σl ∧ eps0 ws σl < 1 ∧ 0 < lam ∧ lam < 1 ∧ 0 < lam' ∧ lam' < 1 ∧
        rootFLH wl ws η (CAn n) lam lam' (latMomOfPsi12e (by omega) (paperDesign n fT wT hf hw) c
          hCL hCS hE hβ hL12 hS12 hE8 hmass) ≤ hfl ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1) hb) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  set S := BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
    BstLean.Part159.Ethp (paperCentres n)
  have hEA' : MeasurableSet (EA ∩ BstLean.Part164.EcA (paperCentres n) ∩ BstLean.Part164.Eop2 n) :=
    (hEA.inter (BstLean.Part164.measurableSet_EcA _)).inter (BstLean.Part164.measurableSet_Eop2 n)
  have hA' : (retDist (paperCentres n)).real (S ∩ (EA ∩ BstLean.Part164.EcA (paperCentres n) ∩
      BstLean.Part164.Eop2 n)ᶜ) ≤ δA + 2 * rexp (-12) + rexp (-(25 / 2)) := by
    have hsub : S ∩ (EA ∩ BstLean.Part164.EcA (paperCentres n) ∩ BstLean.Part164.Eop2 n)ᶜ ⊆
        ((S ∩ EAᶜ) ∪ (BstLean.Part164.EcA (paperCentres n))ᶜ) ∪ (BstLean.Part164.Eop2 n)ᶜ := by
      intro c hc
      by_cases h1 : c ∈ EA
      · by_cases h2 : c ∈ BstLean.Part164.EcA (paperCentres n)
        · exact Or.inr fun h3 => hc.2 ⟨⟨h1, h2⟩, h3⟩
        · exact Or.inl (Or.inr h2)
      · exact Or.inl (Or.inl ⟨hc.1, h1⟩)
    refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
    have u1 := measureReal_union_le (μ := retDist (paperCentres n)) (S ∩ EAᶜ)
      (BstLean.Part164.EcA (paperCentres n))ᶜ
    have c1 := BstLean.Part164.EcA_charge (by omega) (paperCentres n)
    have c2 := BstLean.Part164.Eop2_charge (by omega) (paperCentres n)
    linarith
  have hroom' : δA + 2 * rexp (-12) + rexp (-(25 / 2)) ≤ BstLean.Part163.roomA + roomX + BstLean.Part185.C.roomL := by
    unfold roomB at hroom; linarith
  refine classifier_paper_free21_psi12eHM hHQ hn fT wT hf hw t hEA' hA' hroom' hsum
    fun c hc => ?_
  obtain ⟨wl, ws, σl, η, CL, CS, βlow, E, lam, lam', h0, h1, hCL, hCS, hβ, hE, hL12, hS12, hE8, hmass,
    hwl, hws, hσl, hε, hl0, hl1, hl0', hl1', hroot, hbias⟩ := hM c hc
  obtain ⟨hpos, hle⟩ := BstLean.Part164.cA_of_good (by omega) fT wT hf hw hc
  exact ⟨wl, ws, σl, η, CAn n, CL, CS, E, βlow, lam, lam', h0, h1, hCL, hCS, hE, hβ, hL12, hS12,
    hE8, hmass, hwl, hws, hσl, hpos, hle, hε, hl0, hl1, hl0', hl1', hroot, hbias⟩

end BstLean.Part185.C

open BstLean.Part185.C in
#print axioms classifier_paper_free21_cA8EHM
