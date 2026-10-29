import BstLean.Part159Uncond

/-!
# Part 159 (file `Free`): the conditional theorem with FREE constants of the ledger

Role: `delegations/statements/p159-spec.md`, item 2 (a ledger with free constants). Do not use
`sorry`, `native_decide` or `axiom`.

Parts 157 and 158 state the conditional theorem at the constants of the numeric ledger of Part 156
(`a`, `h_W`, `τ_±`, `c_W = 1.377`, `c_frame = 1.743`, `h_A`, `d_s`, `k = 10¹²`). A later part can
prove the Agent hypotheses with other constants. This file gives the same theorem for EVERY choice
of these constants: the failure probability is at most
`δ_hid + v_W/h_W² + δ_extra + B_+(n) + B_−(n) + 2·exp(−k·d_s²)`.

* `classifier_networks_free`: every design, every `n ≥ 1`, free constants; hypotheses
  `EVENTS_hyp`, `FRAME_W_hyp`, `FRAME_A_hyp`, `REPLA_mix_hyp` and the side conditions of Part 156.
* `frame_w_paper_sharp`: `FRAME_W_hyp` for the centre of the paper with the constant `1.36/n`.
* **`classifier_paper_agent_free`**: `paperDesign`, every `n ≥ 16 384`, the World constants of
  this part (`δPap`, `vPap`, `c_W = 1.36`) and free Agent constants.
-/

namespace BstLean.Part159

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part156 BstLean.Part157 BstLean.Part158

variable {n : ℕ}

/-- **The conditional classifier theorem for the actual networks with free constants (every
`n ≥ 1`).** `D` is a design, `k` the number of draws, `a` the factor of the output rule. IF the
side conditions of Part 156 hold for `(a, h_A + d_s, h_W, c_W, c_frame, τ_+, τ_−)`, the events
have the charges `δ_hid`, `v_W`, `δ_extra` (with the Hellinger radius), and on
`H ∩ {H̄_W ≤ h_W} ∩ E₁` the two frame bounds `c_W/n`, `c_frame/n` and the Agent replacement root
`h_A` hold, THEN the failure probability of `progOut D t a k` is at most
`δ_hid + v_W/h_W² + δ_extra + B_+ + B_− + 2·exp(−k·d_s²)`. -/
theorem classifier_networks_free (hn : 1 ≤ n) (D : Design n) (t : ℝ) (k : ℕ)
    {H E₁ : Set (Ret n)} {δhid vW δextra cW cf hW hA ds a τp τm : ℝ}
    (hcW : 0 < cW) (hcf : 0 < cf) (hhW : 0 < hW) (hhA : 0 ≤ hA) (hds : 0 < ds) (ha : 1 < a)
    (hτp : 0 < τp) (hτm : τm < 0)
    (hside1 : (hA + ds) + hW < √(1 / 100 / a)) (hside2 : 2 * (hA + ds) ≤ √(1 / 100 / a))
    (hEp : Eplus a (hA + ds) hW cW cf τp ≤ 0) (hEm : Eminus a (hA + ds) hW cW cf τm ≤ 0)
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hFW : FRAME_W_hyp D.toCentres (cW / n) (goodSet H E₁ (HbarW D) hW))
    (hFA : FRAME_A_hyp D (cf / n) (goodSet H E₁ (HbarW D) hW))
    (hRA : REPLA_mix_hyp D t hA (goodSet H E₁ (HbarW D) hW)) :
    ((mlpTriple 2 n).prod (sampMeas k n)).real (failNet D t a k) ≤
      δhid + vW / hW ^ 2 + δextra + Bplus n a (hA + ds) hW cW cf τp +
        Bminus n a (hA + ds) hW cW cf τm + 2 * exp (-k * ds ^ 2) := by
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hGPW := gpw_of_frame hn gaussFrameMGF D.toCentres t (div_pos hcW hnpos) hFW
  have hGPA := gpa_of_frame hn gaussFrameMGF D t (div_pos hcf hnpos) hFA
  have hRW := replw_of_test hn D t (replw_test_of_Hbar hn D hW H E₁)
  have hRA' := repla_of_mix D t hRA
  obtain ⟨hH, hE₁, hHm, hhid, hHint, hvW, hextra⟩ := hEv
  have mr := measurable_retVal D.toCentres
  have hmap := noise_retVal D.toCentres
  have mpair : Measurable (fun x : Ret n × (ResW n × ResA n) => (retVal D.toCentres x.1, x.2)) :=
    (mr.comp measurable_fst).prodMk measurable_snd
  have hpm : Measurable (fun x : Ret n × (ResW n × ResA n) =>
      pRes D.toCentres t (retVal D.toCentres x.1) x.2) := by
    have h := (measurable_pRes D.toCentres t).comp mpair
    exact h
  have hp0 : ∀ x : Ret n × (ResW n × ResA n),
      0 ≤ pRes D.toCentres t (retVal D.toCentres x.1) x.2 := fun x => pRes_nonneg _ _ _ _
  have hp1 : ∀ x : Ret n × (ResW n × ResA n),
      pRes D.toCentres t (retVal D.toCentres x.1) x.2 ≤ 1 := fun x => pRes_le_one hn _ _ _ _
  have hPm : ∀ c : Ret n, Measurable (PStand D t (retVal D.toCentres c)) :=
    fun c => measurable_PStand D t _
  have hP0 : ∀ (c : Ret n) (x : ResA n), 0 ≤ PStand D t (retVal D.toCentres c) x :=
    fun c x => PStand_nonneg _ _ _ _
  have hP1 : ∀ (c : Ret n) (x : ResA n), PStand D t (retVal D.toCentres c) x ≤ 1 :=
    fun c x => PStand_le_one _ _ _ _
  have hXm : ∀ i : Fin k, Measurable (fun x : Ret n × (Fin k → DrawSp n) =>
      hits D t k i (retVal D.toCentres x.1, x.2)) := by
    intro i
    have h1 : Measurable (fun x : Ret n × (Fin k → DrawSp n) =>
        (retVal D.toCentres x.1, x.2)) := (mr.comp measurable_fst).prodMk measurable_snd
    have h2 := (measurable_hits D t k i).comp h1
    exact h2
  have hX01 : ∀ (i : Fin k) (x : Ret n × (Fin k → DrawSp n)),
      hits D t k i (retVal D.toCentres x.1, x.2) = 0 ∨
        hits D t k i (retVal D.toCentres x.1, x.2) = 1 :=
    fun i x => hits_01 D t k i _
  have hH' : MeasurableSet (retVal D.toCentres ⁻¹' H) := mr hH
  have hE₁' : MeasurableSet (retVal D.toCentres ⁻¹' E₁) := mr hE₁
  have hHm' : Measurable (fun c => HbarW D (retVal D.toCentres c)) := hHm.comp mr
  have hhid' : (noiseC n).real (retVal D.toCentres ⁻¹' H)ᶜ ≤ δhid := by
    have e : (retVal D.toCentres ⁻¹' H)ᶜ = retVal D.toCentres ⁻¹' Hᶜ := rfl
    rw [e, ← map_measureReal_apply mr hH.compl, hmap]
    exact hhid
  have hHint' : IntegrableOn (fun c => HbarW D (retVal D.toCentres c) ^ 2)
      (retVal D.toCentres ⁻¹' H) (noiseC n) := by
    have h1 : Integrable (fun c => HbarW D c ^ 2) ((retDist D.toCentres).restrict H) := hHint
    rw [← hmap, Measure.restrict_map mr hH] at h1
    exact (integrable_map_measure ((hHm.pow_const 2).aestronglyMeasurable) mr.aemeasurable).1 h1
  have hvW' : ∫ c in retVal D.toCentres ⁻¹' H, HbarW D (retVal D.toCentres c) ^ 2 ∂noiseC n ≤
      vW := by
    have h1 := setIntegral_map (μ := noiseC n) hH
      (f := fun c => HbarW D c ^ 2) (g := retVal D.toCentres)
      ((hHm.pow_const 2).aestronglyMeasurable) mr.aemeasurable
    rw [hmap] at h1
    rw [← h1]
    exact hvW
  have hextra' : (noiseC n).real (retVal D.toCentres ⁻¹' H ∩ (retVal D.toCentres ⁻¹' E₁)ᶜ) ≤
      δextra := by
    have e : retVal D.toCentres ⁻¹' H ∩ (retVal D.toCentres ⁻¹' E₁)ᶜ =
        retVal D.toCentres ⁻¹' (H ∩ E₁ᶜ) := rfl
    rw [e, ← map_measureReal_apply mr (hH.inter hE₁.compl), hmap]
    exact hextra
  have key := master_sampling (noiseC n) (resW n) (resA n) (sampMeas k n)
    (p := fun x : Ret n × (ResW n × ResA n) => pRes D.toCentres t (retVal D.toCentres x.1) x.2)
    hpm hp0 hp1
    (P := fun c => PStand D t (retVal D.toCentres c)) hPm hP0 hP1
    (X := fun i (x : Ret n × (Fin k → DrawSp n)) =>
      hits D t k i (retVal D.toCentres x.1, x.2)) hXm hX01
    (qt := fun c => qTilde D t (retVal D.toCentres c))
    (H := retVal D.toCentres ⁻¹' H) (E₁ := retVal D.toCentres ⁻¹' E₁) hH' hE₁'
    (Hbar := fun c => HbarW D (retVal D.toCentres c)) hHm'
    (n := (n : ℝ)) (cW := cW) (cf := cf) (hW := hW) (hA := hA) (ds := ds) (a := a)
    (τp := τp) (τm := τm) (δhid := δhid) (δextra := δextra) (vW := vW)
    hnpos hcW hcf hhW hhA hds ha hτp hτm hside1 hside2 hEp hEm hhid' hHint' hvW' hextra'
    (fun c hc ωA s => hGPW (retVal D.toCentres c) hc ωA s)
    (fun c hc u => hGPA (retVal D.toCentres c) hc u)
    (fun c hc ωA => hRW (retVal D.toCentres c) hc ωA)
    (fun c hc => hRA' (retVal D.toCentres c) hc)
    (fun c _ => hits_indep D t k (retVal D.toCentres c))
    (fun c _ i => hits_mean D t k (retVal D.toCentres c) i)
  rw [failNet_eq]
  exact key

/-- **`FRAME_W_hyp` for the World centre of the paper with the constant `1.36/n`** (every
`n ≥ 16 384`), on every set of retained data inside `HP n`. -/
theorem frame_w_paper_sharp (hn : 16384 ≤ n) (D : Centres n) (hD : D.bW = bWp)
    {E : Set (Ret n)} (hE : E ⊆ HP n) : FRAME_W_hyp D (136 / 100 / n) E := by
  refine frame_of_hid D (G := GPap n) (fun θ hθ w => ?_) hE
  rw [hD]
  exact pap_frame hn (constC (by omega)) hθ w

/-- **The conditional classifier theorem for the design of the paper's program with free Agent
constants (every `n ≥ 16 384`).** The World constants are those PROVED in this part: hidden charge
`δPap = 0.00163204`, Hellinger moment `vPap = 7.37·10⁻⁹`, frame constant `c_W = 1.36`. The
constants `a`, `h_W`, `τ_±`, `c_frame`, `h_A`, `d_s`, `k` are free. IF the side conditions of
Part 156 hold, `E₁` has `Pr(HP n ∩ E₁ᶜ) ≤ δ_extra`, and on `HP n ∩ {H̄_W ≤ h_W} ∩ E₁` the Agent
frame bound `c_frame/n` and the Agent replacement root `h_A` hold, THEN the failure probability
is at most `δPap + vPap/h_W² + δ_extra + B_+ + B_− + 2·exp(−k·d_s²)`. -/
theorem classifier_paper_agent_free (hn : 16384 ≤ n)
    (fT wT : Ret n → ℕ → ℝ) (hf : ∀ g, Measurable (fun c => fT c g))
    (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ) (k : ℕ) {E₁ : Set (Ret n)}
    (hE₁ : MeasurableSet E₁) {δextra cf hW hA ds a τp τm : ℝ}
    (hcf : 0 < cf) (hhW : 0 < hW) (hhA : 0 ≤ hA) (hds : 0 < ds) (ha : 1 < a)
    (hτp : 0 < τp) (hτm : τm < 0)
    (hside1 : (hA + ds) + hW < √(1 / 100 / a)) (hside2 : 2 * (hA + ds) ≤ √(1 / 100 / a))
    (hEp : Eplus a (hA + ds) hW (136 / 100) cf τp ≤ 0)
    (hEm : Eminus a (hA + ds) hW (136 / 100) cf τm ≤ 0)
    (hextra : (retDist (paperCentres n)).real (HP n ∩ E₁ᶜ) ≤ δextra)
    (hFA : FRAME_A_hyp (paperDesign n fT wT hf hw) (cf / n)
      (goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hW))
    (hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hA
      (goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hW)) :
    ((mlpTriple 2 n).prod (sampMeas k n)).real (failNet (paperDesign n fT wT hf hw) t a k) ≤
      δPap + vPap / hW ^ 2 + δextra + Bplus n a (hA + ds) hW (136 / 100) cf τp +
        Bminus n a (hA + ds) hW (136 / 100) cf τm + 2 * exp (-k * ds ^ 2) :=
  classifier_networks_free (by omega) (paperDesign n fT wT hf hw) t k (by norm_num) hcf hhW hhA
    hds ha hτp hτm hside1 hside2 hEp hEm
    (events_paper hn (constC (by omega)) (constK (by omega)) (paperDesign n fT wT hf hw) rfl
      (fun _ => rfl) hE₁
      hextra)
    (frame_w_paper_sharp hn (paperCentres n) rfl (fun _ hc => hc.1.1)) hFA hRA

end BstLean.Part159

open BstLean.Part159 in
#print axioms classifier_networks_free
open BstLean.Part159 in
#print axioms frame_w_paper_sharp
open BstLean.Part159 in
#print axioms classifier_paper_agent_free
