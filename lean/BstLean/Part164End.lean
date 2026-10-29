import BstLean.Part164Bnd

/-!
# Part 164 (file `End`): the end theorem with `E_{c_A}` and the eighth moment discharged

No proof is left open; no `native_decide` or `axiom` is used.

* `goodA n D EA`: the good set of Part 163's `classifier_paper_free23_psi12e` with the free event
  `E_A ∩ EcA ∩ Eop2`.
* `hE8_of_good`: `∫∫σ⁸ ≤ (E0 n)⁸` on that good set; `cA_of_good`: `0 < |c_A|² ≤ CAn n` there.
* **`classifier_paper_free23_cA8`**: Part 163's `classifier_paper_free23_psi12e` with the
  hypotheses `0 < |c_A|²`, `|c_A|² ≤ C_A` and `∫∫σ⁸ ≤ E⁸` REMOVED: `C_A = CAn n`, `E = E0 n`; the
  charges `2e^{−12}` (`EcA`) and `e^{−25/2}` (`Eop2`) are added to the ledger.
* `roomB`: the room that remains, `roomB = roomA − 2e^{−12} − e^{−25/2} ≥ 0.003042`.
-/

namespace BstLean.Part164

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160
open BstLean.Part161 (muI lamX sigX BIAS_hyp)
open BstLean.Part162 (sgA psiA rootFL latMomOfPsi12e eps0 dPaper)
open BstLean.Part163 (roomA roomA_ge Eframe)

variable {n : ℕ}

/-- The good set of the end theorem: `goodSet (HP n) (E_{θ−} ∩ E_{θ+} ∩ (E_A ∩ EcA ∩ Eop2) ∩
Eframe D) (HbarW D) hWL` for the paper's design `D`. -/
def goodA (n : ℕ) (D : Design n) (EA : Set (Ret n)) : Set (Ret n) :=
  goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
    BstLean.Part159.Ethp (paperCentres n) ∩ (EA ∩ EcA (paperCentres n) ∩ Eop2 n) ∩ Eframe D)
    (HbarW D) hWL

lemma window_goodA (hn : 16384 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    (EA : Set (Ret n)) :
    WINDOW_hyp (paperDesign n fT wT hf hw) (goodA n (paperDesign n fT wT hf hw) EA) :=
  window_paper hn fT wT hf hw (fun _ hc => ⟨hc.1.1, hc.2.1.1.1, hc.2.1.1.2⟩)

lemma goodC16_of_goodA (hn : 16384 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {EA : Set (Ret n)} {c : Ret n} (hc : c ∈ goodA n (paperDesign n fT wT hf hw) EA) :
    (c.2.1.1.1, c.2.1.1.2) ∈ BstLean.Part154.GoodC16 n n c.1.2
      ((paperDesign n fT wT hf hw).tau0 c) :=
  hc.2.2.1.1.1.1.1.1 (window_goodA hn fT wT hf hw EA c hc).1

/-- **The eighth moment of `σ` on the good set**: `∫∫σ⁸ ≤ (E0 n)⁸`. -/
theorem hE8_of_good (hn : 16384 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {EA : Set (Ret n)} {c : Ret n} (hc : c ∈ goodA n (paperDesign n fT wT hf hw) EA) :
    ∫ a, ∫ v, sgA (paperDesign n fT wT hf hw) c a v ^ 8 ∂stdGauss (Fin (n - 1)) ∂muI n ≤
      E0 n ^ 8 :=
  sgA8_le (by omega) _ (eop_of_goodC16 (goodC16_of_goodA hn fT wT hf hw hc)) hc.2.1.2.2

/-- **The norm of `c_A` on the good set**: `0 < |c_A|² ≤ CAn n`. -/
theorem cA_of_good (hn : 16384 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {EA : Set (Ret n)} {c : Ret n} (hc : c ∈ goodA n (paperDesign n fT wT hf hw) EA) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ CAn n := by
  obtain ⟨hτ, hθ0, hθ1⟩ := window_goodA hn fT wT hf hw EA c hc
  exact cA_bounds hn _ (paperDesign_agentCentre fT wT hf hw) hτ hθ0 hθ1
    (goodC16_of_goodA hn fT wT hf hw hc) (hc.2.2.1.1.2 hτ) hc.2.1.2.1.2

/-- **The charge of the two new events in the form of item 2 of the specification**:
`Pr(HP n ∩ E_{θ−} ∩ E_{θ+} ∩ (EcA ∩ Eop2)ᶜ) ≤ 2e^{−12} + e^{−25/2}` (`n ≥ 1`). -/
theorem newEv_charge (hn : 1 ≤ n) :
    (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩
      (EcA (paperCentres n) ∩ Eop2 n)ᶜ) ≤ 2 * rexp (-12) + rexp (-(25 / 2)) := by
  rw [Set.compl_inter]
  refine (measureReal_mono Set.inter_subset_right).trans ((measureReal_union_le _ _).trans ?_)
  have c1 := EcA_charge hn (paperCentres n)
  have c2 := Eop2_charge hn (paperCentres n)
  linarith

/-- The room that remains for the free Agent event: `roomA − 2e^{−12} − e^{−25/2}`. -/
noncomputable def roomB : ℝ := roomA - 2 * rexp (-12) - rexp (-(25 / 2))

lemma exp_neg_25_2_le : rexp (-(25 / 2)) ≤ 379 / 10 ^ 8 := by
  have h1 : (2.7182818283 : ℝ) < rexp 1 := Real.exp_one_gt_d9
  have h2 : rexp (25 / 2) = rexp 1 ^ 12 * rexp (1 / 2) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have h3 : (1 : ℝ) + 1 / 2 + (1 / 2) ^ 2 / 2 ≤ rexp (1 / 2) :=
    Real.quadratic_le_exp_of_nonneg (by norm_num)
  have h4 : (2.7182818283 : ℝ) ^ 12 ≤ rexp 1 ^ 12 := pow_le_pow_left₀ (by norm_num) h1.le 12
  have h5 : (10 ^ 8 / 379 : ℝ) ≤ rexp (25 / 2) := by
    rw [h2]
    have : (10 ^ 8 / 379 : ℝ) ≤ 2.7182818283 ^ 12 * (1 + 1 / 2 + (1 / 2) ^ 2 / 2) := by norm_num
    exact this.trans (mul_le_mul h4 h3 (by norm_num) (by positivity))
  rw [Real.exp_neg]
  rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
  simpa using h5

/-- **The room that remains**: `0.003042 ≤ roomB`. -/
theorem roomB_ge : (3042 : ℝ) / 10 ^ 6 ≤ roomB := by
  unfold roomB
  have h1 := roomA_ge
  have h2 := BstLean.Part160.exp_neg_twelve_le
  have h3 := exp_neg_25_2_le
  linarith

/-- **The free-event classifier theorem with the norm event of `c_A` and the eighth moment of `σ`
discharged (every `n ≥ 23 000`).** IF `E_A` is a measurable event with
`Pr(HP n ∩ E_{θ−} ∩ E_{θ+} ∩ E_Aᶜ) ≤ δ_A ≤ roomB`, and for every `c` in the good set `goodA`
(which contains `E_A ∩ EcA ∩ Eop2 ∩ Eframe D`) there are constants with the two order-12
certificates `‖Ψ_λ‖₁₂ ≤ C_λ/n`, `‖Ψ_σ‖₁₂ ≤ C_σ/n`, the mass below the floor `≤ β_low`, `ε₀ < 1`,
the root sum with `C_A = CAn n` and `E = E0 n` `≤ 0.002159`, and `BIAS_hyp … 0.004295`, THEN
success `≥ 99/100`. The eighth moment enters the root sum through its PROOF `hE8_of_good` on the
good set; `|c_A|² ≤ CAn n` and `0 < |c_A|²` are proved on the good set (`cA_of_good`). -/
theorem classifier_paper_free23_cA8 (hn : 23000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomB)
    (hM : ∀ (c : Ret n) (hc : c ∈ goodA n (paperDesign n fT wT hf hw) EA),
      ∃ (wl ws σl η CL CS βlow : ℝ) (h0 : 0 < η) (h1 : η < 1) (hCL : 0 < CL)
        (hCS : 0 < CS) (hβ : 0 ≤ βlow)
        (hL12 : ∫ a, ∫ v, psiA (lamX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CL / n) ^ 12)
        (hS12 : ∫ a, ∫ v, psiA (sigX (paperDesign n fT wT hf hw) c) (paperDesign n fT wT hf hw) c a v
          ^ 12 ∂stdGauss (Fin (n - 1)) ∂muI n ≤ (CS / n) ^ 12)
        (hmass : ∫ a, (stdGauss (Fin (n - 1))).real {v | sgA (paperDesign n fT wT hf hw) c a v < σl}
          ∂muI n ≤ βlow),
        0 < wl ∧ 0 < ws ∧ 0 < σl ∧ eps0 ws σl < 1 ∧
        rootFL wl ws η (CAn n) (latMomOfPsi12e (by omega) (paperDesign n fT wT hf hw) c hCL hCS
          (E0_nonneg n) hβ hL12 hS12 (hE8_of_good (by omega) fT wT hf hw hc) hmass) ≤
          2159 / 10 ^ 6 ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c
          (dPaper (paperDesign n fT wT hf hw) c wl ws σl η h0 h1) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  set S := BstLean.Part159.HP n ∩ BstLean.Part159.Ethm (paperCentres n) ∩
    BstLean.Part159.Ethp (paperCentres n)
  have hEA' : MeasurableSet (EA ∩ EcA (paperCentres n) ∩ Eop2 n) :=
    (hEA.inter (measurableSet_EcA _)).inter (measurableSet_Eop2 n)
  have hA' : (retDist (paperCentres n)).real (S ∩ (EA ∩ EcA (paperCentres n) ∩ Eop2 n)ᶜ) ≤
      δA + 2 * rexp (-12) + rexp (-(25 / 2)) := by
    have hsub : S ∩ (EA ∩ EcA (paperCentres n) ∩ Eop2 n)ᶜ ⊆
        ((S ∩ EAᶜ) ∪ (EcA (paperCentres n))ᶜ) ∪ (Eop2 n)ᶜ := by
      intro c hc
      by_cases h1 : c ∈ EA
      · by_cases h2 : c ∈ EcA (paperCentres n)
        · exact Or.inr fun h3 => hc.2 ⟨⟨h1, h2⟩, h3⟩
        · exact Or.inl (Or.inr h2)
      · exact Or.inl (Or.inl ⟨hc.1, h1⟩)
    refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
    have u1 := measureReal_union_le (μ := retDist (paperCentres n)) (S ∩ EAᶜ)
      (EcA (paperCentres n))ᶜ
    have c1 := EcA_charge (by omega) (paperCentres n)
    have c2 := Eop2_charge (by omega) (paperCentres n)
    linarith
  have hroom' : δA + 2 * rexp (-12) + rexp (-(25 / 2)) ≤ roomA := by
    unfold roomB at hroom; linarith
  refine BstLean.Part163.classifier_paper_free23_psi12e hn fT wT hf hw t hEA' hA' hroom'
    fun c hc => ?_
  obtain ⟨wl, ws, σl, η, CL, CS, βlow, h0, h1, hCL, hCS, hβ, hL12, hS12, hmass, hwl, hws, hσl, hε,
    hroot, hbias⟩ := hM c hc
  obtain ⟨hpos, hle⟩ := cA_of_good (by omega) fT wT hf hw hc
  exact ⟨wl, ws, σl, η, CAn n, CL, CS, E0 n, βlow, h0, h1, hCL, hCS, E0_nonneg n, hβ, hL12, hS12,
    hE8_of_good (by omega) fT wT hf hw hc, hmass, hwl, hws, hσl, hpos, hle, hε, hroot, hbias⟩

end BstLean.Part164
