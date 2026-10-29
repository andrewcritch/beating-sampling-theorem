import BstLean.Part157Hell

/-!
# Part 157: the conditional theorem with free event charges

Do not use `sorry`, `native_decide` or `axiom`.

The theorems of `Part157Final` have the three event charges of the ledger of the paper
(`δ_hid = 0.001900001`, `v_W = 0.000741853·(0.004)²`, `δ_extra = 0.001104285235085`). A later
part can prove the events with other charges. This file gives the same theorem with FREE charges
`δ_hid`, `v_W`, `δ_extra`: the failure probability is at most
`δ_hid + v_W/h_W² + δ_extra + 0.00146335214251 + 0.001694618447832 + 2 e^{−100}`
(the two numbers are the endpoint tails `B_+`, `B_-` at `n = 16 384`, Part 156).

* `classifier_networks_charges`: from `EVENTS_hyp` with free charges and the hypotheses
  `GPW_hyp`, `GPA_hyp`, `REPL_W_hyp`, `REPL_A_hyp`.
* `classifier_networks_charges_hell`: from `GaussFrameMGF`, `EVENTS_hyp` with the Hellinger radius
  and free charges, `FRAME_W_hyp`, `FRAME_A_hyp`, `REPLA_mix_hyp`.
* `classifier_networks_charges_success`: success with probability at least `99/100` when
  `δ_hid + v_W/h_W² + δ_extra ≤ 0.0068`.
-/

namespace BstLean.Part157

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part156

variable {n : ℕ}

/-- **The conditional classifier theorem for the actual networks with free event charges (every
`n ≥ 16 384`).** As `classifier_networks_conditional_ge`, but `EVENTS_hyp` has any charges
`δ_hid`, `v_W`, `δ_extra`. The failure probability is at most
`δ_hid + v_W/h_W² + δ_extra + B_+ + B_- + 2 e^{−100}` with `h_W = 0.0024160420`,
`B_+ ≤ 0.00146335214251`, `B_- ≤ 0.001694618447832`. -/
theorem classifier_networks_charges (hn : 16384 ≤ n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {Hbar : Ret n → ℝ} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ Hbar δhid vW δextra)
    (hGPW : GPW_hyp D.toCentres t (cWL / n) (goodSet H E₁ Hbar hWL))
    (hGPA : GPA_hyp D t (cfL / n) (goodSet H E₁ Hbar hWL))
    (hRW : REPL_W_hyp D t hWL (goodSet H E₁ Hbar hWL))
    (hRA : REPL_A_hyp D t hAL (goodSet H E₁ Hbar hWL)) :
    ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real (failNet D t aL (10 ^ 12)) ≤
      δhid + vW / hWL ^ 2 + δextra + 146335214251 / 10 ^ 14 + 1694618447832 / 10 ^ 15 +
        2 * exp (-100) := by
  obtain ⟨hH, hE₁, hHm, hhid, hHint, hvW, hextra⟩ := hEv
  have hn1 : 1 ≤ n := by omega
  have mr := measurable_retVal D.toCentres
  have hmap := noise_retVal D.toCentres
  have hn' : (16384 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have mpair : Measurable (fun x : Ret n × (ResW n × ResA n) => (retVal D.toCentres x.1, x.2)) :=
    (mr.comp measurable_fst).prodMk measurable_snd
  have hpm : Measurable (fun x : Ret n × (ResW n × ResA n) =>
      pRes D.toCentres t (retVal D.toCentres x.1) x.2) := by
    have h := (measurable_pRes D.toCentres t).comp mpair
    exact h
  have hp0 : ∀ x : Ret n × (ResW n × ResA n),
      0 ≤ pRes D.toCentres t (retVal D.toCentres x.1) x.2 := fun x => pRes_nonneg _ _ _ _
  have hp1 : ∀ x : Ret n × (ResW n × ResA n),
      pRes D.toCentres t (retVal D.toCentres x.1) x.2 ≤ 1 := fun x => pRes_le_one hn1 _ _ _ _
  have hPm : ∀ c : Ret n, Measurable (PStand D t (retVal D.toCentres c)) :=
    fun c => measurable_PStand D t _
  have hP0 : ∀ (c : Ret n) (x : ResA n), 0 ≤ PStand D t (retVal D.toCentres c) x :=
    fun c x => PStand_nonneg _ _ _ _
  have hP1 : ∀ (c : Ret n) (x : ResA n), PStand D t (retVal D.toCentres c) x ≤ 1 :=
    fun c x => PStand_le_one _ _ _ _
  have hXm : ∀ i : Fin (10 ^ 12), Measurable (fun x : Ret n × (Fin (10 ^ 12) → DrawSp n) =>
      hits D t (10 ^ 12) i (retVal D.toCentres x.1, x.2)) := by
    intro i
    have h1 : Measurable (fun x : Ret n × (Fin (10 ^ 12) → DrawSp n) =>
        (retVal D.toCentres x.1, x.2)) := (mr.comp measurable_fst).prodMk measurable_snd
    have h2 := (measurable_hits D t (10 ^ 12) i).comp h1
    exact h2
  have hX01 : ∀ (i : Fin (10 ^ 12)) (x : Ret n × (Fin (10 ^ 12) → DrawSp n)),
      hits D t (10 ^ 12) i (retVal D.toCentres x.1, x.2) = 0 ∨
        hits D t (10 ^ 12) i (retVal D.toCentres x.1, x.2) = 1 :=
    fun i x => hits_01 D t (10 ^ 12) i _
  have hH' : MeasurableSet (retVal D.toCentres ⁻¹' H) := mr hH
  have hE₁' : MeasurableSet (retVal D.toCentres ⁻¹' E₁) := mr hE₁
  have hHm' : Measurable (fun c => Hbar (retVal D.toCentres c)) := hHm.comp mr
  have hhid' : (noiseC n).real (retVal D.toCentres ⁻¹' H)ᶜ ≤ δhid := by
    have e : (retVal D.toCentres ⁻¹' H)ᶜ = retVal D.toCentres ⁻¹' Hᶜ := rfl
    rw [e, ← map_measureReal_apply mr hH.compl, hmap]
    exact hhid
  have hHint' : IntegrableOn (fun c => Hbar (retVal D.toCentres c) ^ 2)
      (retVal D.toCentres ⁻¹' H) (noiseC n) := by
    have h1 : Integrable (fun c => Hbar c ^ 2) ((retDist D.toCentres).restrict H) := hHint
    rw [← hmap, Measure.restrict_map mr hH] at h1
    exact (integrable_map_measure ((hHm.pow_const 2).aestronglyMeasurable) mr.aemeasurable).1 h1
  have hvW' : ∫ c in retVal D.toCentres ⁻¹' H, Hbar (retVal D.toCentres c) ^ 2 ∂noiseC n ≤ vW := by
    have h1 := setIntegral_map (μ := noiseC n) hH
      (f := fun c => Hbar c ^ 2) (g := retVal D.toCentres)
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
  have key := master_sampling (noiseC n) (resW n) (resA n) (sampMeas (10 ^ 12) n)
    (p := fun x : Ret n × (ResW n × ResA n) => pRes D.toCentres t (retVal D.toCentres x.1) x.2)
    hpm hp0 hp1
    (P := fun c => PStand D t (retVal D.toCentres c)) hPm hP0 hP1
    (X := fun i (x : Ret n × (Fin (10 ^ 12) → DrawSp n)) =>
      hits D t (10 ^ 12) i (retVal D.toCentres x.1, x.2)) hXm hX01
    (qt := fun c => qTilde D t (retVal D.toCentres c))
    (H := retVal D.toCentres ⁻¹' H) (E₁ := retVal D.toCentres ⁻¹' E₁) hH' hE₁'
    (Hbar := fun c => Hbar (retVal D.toCentres c)) hHm'
    (n := (n : ℝ)) (cW := cWL) (cf := cfL) (hW := hWL) (hA := hAL) (ds := dsL) (a := aL)
    (τp := τpL) (τm := τmL) (δhid := δhid) (δextra := δextra) (vW := vW)
    (by linarith) (by unfold cWL; norm_num) (by unfold cfL; norm_num) (by unfold hWL; norm_num)
    (by unfold hAL; norm_num) (by unfold dsL; norm_num) (by unfold aL; norm_num)
    (by unfold τpL; norm_num) (by unfold τmL; norm_num) side1_ledger side2_ledger
    Eplus_ledger_neg.le Eminus_ledger_neg.le hhid' hHint' hvW' hextra'
    (fun c hc ωA s => hGPW (retVal D.toCentres c) hc ωA s)
    (fun c hc u => hGPA (retVal D.toCentres c) hc u)
    (fun c hc ωA => hRW (retVal D.toCentres c) hc ωA)
    (fun c hc => hRA (retVal D.toCentres c) hc)
    (fun c _ => hits_indep D t (10 ^ 12) (retVal D.toCentres c))
    (fun c _ i => hits_mean D t (10 ^ 12) (retVal D.toCentres c) i)
  have hk : 2 * exp (-((10 ^ 12 : ℕ) : ℝ) * dsL ^ 2) = 2 * exp (-100) := by
    unfold dsL; norm_num
  rw [hk] at key
  have h3 := Bplus_anti hn' Eplus_ledger_neg.le
  have h4 := Bminus_anti hn' Eminus_ledger_neg.le
  have h5 := Bplus_ledger
  have h6 := Bminus_ledger
  rw [failNet_eq]
  linarith

/-- The same with hypotheses on the retained data only and the Hellinger radius: IF
`GaussFrameMGF` holds, the events have the charges `δ_hid`, `v_W`, `δ_extra` (with the radius
`HbarW D`), and on `H ∩ {H̄_W ≤ h_W} ∩ E₁` the two frame bounds and the Agent replacement hold,
THEN the failure probability is at most
`δ_hid + v_W/h_W² + δ_extra + 0.00146335214251 + 0.001694618447832 + 2 e^{−100}`. -/
theorem classifier_networks_charges_hell (hn : 16384 ≤ n) (hG : GaussFrameMGF) (D : Design n)
    (t : ℝ) {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (cfL / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real (failNet D t aL (10 ^ 12)) ≤
      δhid + vW / hWL ^ 2 + δextra + 146335214251 / 10 ^ 14 + 1694618447832 / 10 ^ 15 +
        2 * exp (-100) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hLW : 0 < cWL / (n : ℝ) := div_pos (by unfold cWL; norm_num) hnpos
  have hLA : 0 < cfL / (n : ℝ) := div_pos (by unfold cfL; norm_num) hnpos
  exact classifier_networks_charges hn D t hEv
    (gpw_of_frame hn1 hG D.toCentres t hLW hFW) (gpa_of_frame hn1 hG D t hLA hFA)
    (replw_of_test hn1 D t (replw_test_of_Hbar hn1 D hWL H E₁)) (repla_of_mix D t hRA)

lemma two_exp_neg_100 : 2 * exp (-100) ≤ 1 / 10 ^ 6 := by
  have h1 : exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    have := Real.exp_one_gt_d9
    exact one_div_le_one_div_of_le (by norm_num) (by linarith)
  have h2 : exp (-100) = exp (-1) ^ 100 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have h3 : exp (-1) ^ 100 ≤ (1 / 2 : ℝ) ^ 100 := pow_le_pow_left₀ (exp_pos _).le h1 100
  rw [h2]
  have h4 : (1 / 2 : ℝ) ^ 100 ≤ 1 / (2 * 10 ^ 6) := by norm_num
  linarith

/-- **Success with free charges.** If the three charges have
`δ_hid + v_W/h_W² + δ_extra ≤ 0.0068`, the program succeeds with probability at least
`99/100`. -/
theorem classifier_networks_charges_success (hn : 16384 ≤ n) (hG : GaussFrameMGF) (D : Design n)
    (t : ℝ) {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 68 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (cfL / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have h := classifier_networks_charges_hell hn hG D t hEv hFW hFA hRA
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have hc : {x : Net3 n × (Fin (10 ^ 12) → DrawSp n) |
      successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} = (failNet D t aL (10 ^ 12))ᶜ := by
    ext x
    simp [failNet]
  have h2 := two_exp_neg_100
  rw [hc, measureReal_compl (measurableSet_failNet D t aL _), probReal_univ]
  norm_num at h ⊢
  linarith

end BstLean.Part157

open BstLean.Part157 in
#print axioms classifier_networks_charges
open BstLean.Part157 in
#print axioms classifier_networks_charges_hell
open BstLean.Part157 in
#print axioms classifier_networks_charges_success
