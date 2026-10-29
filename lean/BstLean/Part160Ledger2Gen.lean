import BstLean.Part160Ledger

/-!
# Part 160 (file `Ledger2Gen`): the ledger with free exponents `τ_±` for each frame constant

Role: `delegations/statements/p160-spec.md`, item 3. Do not use `sorry`, `native_decide` or
`axiom`.

`Part160Ledger` uses the scaled exponents `τ_± = (1.743/c_f)·τ_±^L`; this gives the threshold
`n ≥ 16384·c_f/1.743`. Here `τ_+`, `τ_-` are free, with certificates `E_+ ≤ −e_+`, `E_- ≤ −e_-`.

* `classifier_networks_frameconst2`: the conditional theorem with free `c_f`, `τ_±` and the tails
  `exp(−n e_+) ≤ B_+`, `exp(−n e_-) ≤ B_-`.
* `certP`, `certM`: certificates of `E_+ ≤ −e_+`, `E_- ≤ −e_-` from rational brackets.
* `tail8`: `exp(−n e) ≤ u⁸` for `n ≥ N₀` from `exp(−N₀ e/8) ≤ u`.
* `frame_entry`: the success form used by the table of `Part160Ledger2`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part156 BstLean.Part157

/-- `x₀^lo + h` at the ledger constants. -/
lemma hL_nonneg : (0 : ℝ) ≤ hAL + dsL := by rw [hL_eq]; norm_num

/-- **Certificate of `E_+ ≤ −e_+`** at the ledger constants, for a frame constant `cf` and an
exponent `τ > 0`, from an upper bound `eT` of `exp(τ c_W)`, a number `y` and an upper bound
`ehi` of `exp y`. -/
lemma certP {cf τ eT y ehi ep : ℝ} (hcf : 0 < cf) (hτ : 0 < τ) (heT : exp (τ * cWL) ≤ eT)
    (hy : cf * ((eT - 1) / cWL) *
      (1 + hWL / (66630010657559783 / 10 ^ 18 + (6593 / 10 ^ 6 + 1 / 10 ^ 20))) ≤ y)
    (he : exp y ≤ ehi)
    (hfin : -τ * (1 / 100) + ((eT - 1) / cWL *
        (hWL * (66630010657559784 / 10 ^ 18 + (6593 / 10 ^ 6 + 1 / 10 ^ 20)) + hWL ^ 2) +
        (66630010657559784 / 10 ^ 18 + (6593 / 10 ^ 6 + 1 / 10 ^ 20)) ^ 2 / cf * (ehi - 1)) ≤
      -ep) :
    Eplus aL (hAL + dsL) hWL cWL cf τ ≤ -ep := by
  have hcW : (0 : ℝ) < cWL := by unfold cWL; norm_num
  have hT : Tfun cWL τ ≤ (eT - 1) / cWL := by
    unfold Tfun
    exact div_le_div_of_nonneg_right (by linarith) hcW.le
  have h := Eplus_le_of_bounds (a := aL) (h := hAL + dsL) (hW := hWL) (cW := cWL) (cf := cf)
    (τ := τ) (x0lo := 66630010657559783 / 10 ^ 18) (x0hi := 66630010657559784 / 10 ^ 18)
    (Thi := (eT - 1) / cWL) (y := y) (ehi := ehi) hL_nonneg (by unfold hWL; norm_num) hcW hcf hτ
    (by norm_num) x0_lo x0_hi hT (by rw [hL_eq]; exact hy) he
  rw [hL_eq] at h ⊢
  exact h.trans hfin

/-- **Certificate of `E_- ≤ −e_-`** at the ledger constants, for a frame constant `cf` and an
exponent `τ < 0`, from brackets `eLo ≤ exp(τ c_W) ≤ eHi ≤ 1`, a number `y`, an upper bound `u`
of `exp(y/2)` and `u² ≤ ehi ≤ 1`. -/
lemma certM {cf τ eLo eHi y u ehi em : ℝ} (hcf : 0 < cf) (hτ : τ < 0)
    (hlo : eLo ≤ exp (τ * cWL)) (hhi : exp (τ * cWL) ≤ eHi) (hHi1 : eHi ≤ 1)
    (hy : cf * ((eHi - 1) / cWL) *
      (1 - hWL / (66630010657559783 / 10 ^ 18 - (6593 / 10 ^ 6 + 1 / 10 ^ 20))) ≤ y)
    (hu : exp (y / 2) ≤ u) (hehi : u ^ 2 ≤ ehi) (he1 : ehi ≤ 1)
    (hfin : -τ * (1 / 1000) + (-((eLo - 1) / cWL) *
        (hWL * (66630010657559784 / 10 ^ 18 - (6593 / 10 ^ 6 + 1 / 10 ^ 20))) +
        (66630010657559783 / 10 ^ 18 - (6593 / 10 ^ 6 + 1 / 10 ^ 20)) ^ 2 / cf * (ehi - 1)) ≤
      -em) :
    Eminus aL (hAL + dsL) hWL cWL cf τ ≤ -em := by
  have hcW : (0 : ℝ) < cWL := by unfold cWL; norm_num
  have hTlo : (eLo - 1) / cWL ≤ Tfun cWL τ := by
    unfold Tfun
    exact div_le_div_of_nonneg_right (by linarith) hcW.le
  have hThi : Tfun cWL τ ≤ (eHi - 1) / cWL := by
    unfold Tfun
    exact div_le_div_of_nonneg_right (by linarith) hcW.le
  have hThi0 : (eHi - 1) / cWL ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hcW.le
  have hexp : exp y ≤ ehi := by
    have e : exp y = exp (y / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [e]
    exact (pow_le_pow_left₀ (exp_pos _).le hu 2).trans hehi
  have h := Eminus_le_of_bounds (a := aL) (h := hAL + dsL) (hW := hWL) (cW := cWL) (cf := cf)
    (τ := τ) (x0lo := 66630010657559783 / 10 ^ 18) (x0hi := 66630010657559784 / 10 ^ 18)
    (Tlo := (eLo - 1) / cWL) (Thi := (eHi - 1) / cWL) (y := y) (ehi := ehi)
    (by unfold hWL; norm_num) hcW hcf hτ (by rw [hL_eq]; unfold hWL; norm_num) x0_lo x0_hi
    hTlo hThi hThi0 (by rw [hL_eq]; exact hy) hexp he1
  rw [hL_eq] at h ⊢
  exact h.trans hfin

/-- `exp(−n e) ≤ u⁸` for `n ≥ N₀`, `e ≥ 0`, from `exp(−N₀ e/8) ≤ u`. -/
lemma tail8 {n N0 e u : ℝ} (hn : N0 ≤ n) (he : 0 ≤ e) (hu : exp (-(N0 * e) / 8) ≤ u) :
    exp (-(n * e)) ≤ u ^ 8 := by
  calc exp (-(n * e)) ≤ exp (-(N0 * e)) :=
        exp_le_exp.2 (by have := mul_le_mul_of_nonneg_right hn he; linarith)
    _ = exp (-(N0 * e) / 8) ^ 8 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    _ ≤ u ^ 8 := pow_le_pow_left₀ (exp_pos _).le hu 8

variable {n : ℕ}

/-- **The conditional classifier theorem with a free Agent frame constant and free exponents.**
IF `E_+(cf, τ_+) ≤ −e_+`, `E_-(cf, τ_-) ≤ −e_-` (`e_± ≥ 0`), `exp(−n e_+) ≤ B_+`,
`exp(−n e_-) ≤ B_-`, the events have the charges `δ_hid`, `v_W`, `δ_extra` (with the Hellinger
radius), and on `H ∩ {H̄_W ≤ h_W} ∩ E₁` the World frame bound `1.377/n`, the Agent frame bound
`cf/n` and the Agent replacement hold, THEN the failure probability is at most
`δ_hid + v_W/h_W² + δ_extra + B_+ + B_- + 2 e^{−100}`. -/
theorem classifier_networks_frameconst2 (hn : 16384 ≤ n) {cf τp τm ep em Bp Bm : ℝ}
    (hcf : 0 < cf) (hτp : 0 < τp) (hτm : τm < 0)
    (hEp : Eplus aL (hAL + dsL) hWL cWL cf τp ≤ -ep)
    (hEm : Eminus aL (hAL + dsL) hWL cWL cf τm ≤ -em)
    (hep : 0 ≤ ep) (hem : 0 ≤ em) (hBp : exp (-(n * ep)) ≤ Bp) (hBm : exp (-(n * em)) ≤ Bm)
    (D : Design n) (t : ℝ) {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (cf / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real (failNet D t aL (10 ^ 12)) ≤
      δhid + vW / hWL ^ 2 + δextra + Bp + Bm + 2 * exp (-100) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hLW : 0 < cWL / (n : ℝ) := div_pos (by unfold cWL; norm_num) hnpos
  have hLA : 0 < cf / (n : ℝ) := div_pos hcf hnpos
  have hG := BstLean.Part158.gaussFrameMGF
  have hGPW := gpw_of_frame hn1 hG D.toCentres t hLW hFW
  have hGPA := gpa_of_frame hn1 hG D t hLA hFA
  have hRW := replw_of_test hn1 D t (replw_test_of_Hbar hn1 D hWL H E₁)
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
  have key := master_sampling (noiseC n) (resW n) (resA n) (sampMeas (10 ^ 12) n)
    (p := fun x : Ret n × (ResW n × ResA n) => pRes D.toCentres t (retVal D.toCentres x.1) x.2)
    hpm hp0 hp1
    (P := fun c => PStand D t (retVal D.toCentres c)) hPm hP0 hP1
    (X := fun i (x : Ret n × (Fin (10 ^ 12) → DrawSp n)) =>
      hits D t (10 ^ 12) i (retVal D.toCentres x.1, x.2)) hXm hX01
    (qt := fun c => qTilde D t (retVal D.toCentres c))
    (H := retVal D.toCentres ⁻¹' H) (E₁ := retVal D.toCentres ⁻¹' E₁) hH' hE₁'
    (Hbar := fun c => HbarW D (retVal D.toCentres c)) hHm'
    (n := (n : ℝ)) (cW := cWL) (cf := cf) (hW := hWL) (hA := hAL) (ds := dsL) (a := aL)
    (τp := τp) (τm := τm) (δhid := δhid) (δextra := δextra) (vW := vW)
    hnpos (by unfold cWL; norm_num) hcf (by unfold hWL; norm_num)
    (by unfold hAL; norm_num) (by unfold dsL; norm_num) (by unfold aL; norm_num)
    hτp hτm side1_ledger side2_ledger
    (hEp.trans (by linarith)) (hEm.trans (by linarith)) hhid' hHint' hvW' hextra'
    (fun c hc ωA s => hGPW (retVal D.toCentres c) hc ωA s)
    (fun c hc u => hGPA (retVal D.toCentres c) hc u)
    (fun c hc ωA => hRW (retVal D.toCentres c) hc ωA)
    (fun c hc => hRA' (retVal D.toCentres c) hc)
    (fun c _ => hits_indep D t (10 ^ 12) (retVal D.toCentres c))
    (fun c _ i => hits_mean D t (10 ^ 12) (retVal D.toCentres c) i)
  have hk : 2 * exp (-((10 ^ 12 : ℕ) : ℝ) * dsL ^ 2) = 2 * exp (-100) := by
    unfold dsL; norm_num
  rw [hk] at key
  have h3 : Bplus n aL (hAL + dsL) hWL cWL cf τp ≤ Bp := by
    unfold Bplus
    refine le_trans (exp_le_exp.2 ?_) hBp
    have := mul_le_mul_of_nonneg_left hEp hnpos.le
    linarith
  have h4 : Bminus n aL (hAL + dsL) hWL cWL cf τm ≤ Bm := by
    unfold Bminus
    refine le_trans (exp_le_exp.2 ?_) hBm
    have := mul_le_mul_of_nonneg_left hEm hnpos.le
    linarith
  rw [failNet_eq]
  linarith

/-- **One entry of the table**: success with probability `≥ 99/100` for every `n ≥ N₀`, from
the two certificates and the two tails `exp(−N₀ e_±/8) ≤ u_±` with `u_+⁸ + u_-⁸ ≤ 0.003699`,
when the three charges have `δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`. -/
theorem frame_entry {N0 : ℕ} (hN0 : 16384 ≤ N0) (hn : N0 ≤ n) {cf τp τm ep em up um : ℝ}
    (hcf : 0 < cf) (hτp : 0 < τp) (hτm : τm < 0)
    (hEp : Eplus aL (hAL + dsL) hWL cWL cf τp ≤ -ep)
    (hEm : Eminus aL (hAL + dsL) hWL cWL cf τm ≤ -em)
    (hep : 0 ≤ ep) (hem : 0 ≤ em)
    (hup : exp (-((N0 : ℝ) * ep) / 8) ≤ up) (hum : exp (-((N0 : ℝ) * em) / 8) ≤ um)
    (hB : up ^ 8 + um ^ 8 ≤ 3699 / 10 ^ 6)
    (D : Design n) (t : ℝ) {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (cf / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hnR : (N0 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h := classifier_networks_frameconst2 (by omega : 16384 ≤ n) hcf hτp hτm hEp hEm hep hem
    (tail8 hnR hep hup) (tail8 hnR hem hum) D t hEv hFW hFA hRA
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have hc : {x : Net3 n × (Fin (10 ^ 12) → DrawSp n) |
      successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} = (failNet D t aL (10 ^ 12))ᶜ := by
    ext x
    simp [failNet]
  have h2 := two_exp_neg_100
  rw [hc, measureReal_compl (measurableSet_failNet D t aL _), probReal_univ]
  norm_num at h2 ⊢
  linarith

end BstLean.Part160

open BstLean.Part160 in
#print axioms certP
open BstLean.Part160 in
#print axioms certM
open BstLean.Part160 in
#print axioms classifier_networks_frameconst2
open BstLean.Part160 in
#print axioms frame_entry
