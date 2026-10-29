import BstLean.Part160Final
import BstLean.Part160Cov8
import BstLean.Part160Ledger2
import BstLean.Part160Sc

/-!
# Part 160 (file `Best`): the frame constant with the first split and the ledger table

An intermediate form: the best frame constant and the least `n₀` of this part are in
`Part160Best4.lean`.

Do not use `sorry`, `native_decide` or `axiom`.

With the noncentral bounds of `Ξ`, `Ξ₄`, `Ξ₈` (`Part160Cov`, `Part160Cov8`), the centre energy
`e_b ≤ 0.772` (`Part160Eb`), the centre charge `0.485` (Part 154), the eighth moment of `σ`
(`Part160Mass8`) and the ledger table of `Part160Ledger2`:

* `frameA_46500`: `FRAME_A_hyp D (7.5/n) E`, every `n ≥ 46 500`.
* `classifier_agentframe_46500`: the conditional classifier theorem WITHOUT the Agent frame
  hypothesis, every `n ≥ 46 500`.
* `classifier_paper_agentframe_46500`: the same for `paperDesign` with the paper's charges.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part154 BstLean.Part157
open BstLean.Part153 (XiS Xi4)
open BstLean.Part156

variable {n : ℕ}

/-- **The Agent frame bound `7.5/n`, every `n ≥ 46 500`**: on `EA16 D` and the three events
`SXi`, `SXi4n`, `SXi8n` (noncentral bounds of `Ξ`, `Ξ₄`, `Ξ₈`), in the World window. Constants:
`N_cov = 0.679`, `ξ = 0.485`, `e_b ≤ 0.772`, `Ξ₄, Ξ₈ ≤ 0.681 γ_A/n`, cutoff `d = 0.402²`. -/
theorem frameA_46500 (hn : 46500 ≤ n) (D : Design n) (hD : AgentCentre154 D) {E : Set (Ret n)}
    (hWin : WINDOW_hyp D E) (hE : E ⊆ EA16 D) (hE' : E ⊆ agentEv D (SXi n))
    (hE4 : E ⊆ agentEv D (SXi4n n)) (hE8 : E ⊆ agentEv D (SXi8n n)) :
    FRAME_A_hyp D (15 / 2 / n) E := by
  intro c hc w
  obtain ⟨hτ, hθ0, hθ1⟩ := hWin c hc
  have hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c) := hE hc hτ
  have hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n := hE' hc hτ
  have hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n := hE4 hc hτ
  have hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n := hE8 hc hτ
  have hn16 : 16384 ≤ n := by omega
  have hnR : (46500 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hXi := XiS_noncentral hn16 hτ hθ0 hθ1 hS
  have hXi4 := Xi4_noncentral hn16 hτ hθ0 hθ1 hS4
  have hXi8 := Xi8_noncentral hn16 hτ hθ0 hθ1 hS8
  have hXi4' : Xi4 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ 681 / 1000 * (2 / (n : ℝ)) / n :=
    hXi4.trans (by
      have : (0 : ℝ) ≤ 2 / (n : ℝ) / n := by positivity
      have e1 : (679 : ℝ) / 1000 * (2 / (n : ℝ)) / n = 679 / 1000 * (2 / (n : ℝ) / n) := by ring
      have e2 : (681 : ℝ) / 1000 * (2 / (n : ℝ)) / n = 681 / 1000 * (2 / (n : ℝ) / n) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right (by norm_num) this)
  have heb := eb16 hn16 hτ hθ0 hθ1 hG
  obtain ⟨c1, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0 hθ1 hG
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 46500 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point8g (by omega) D hD c hτ (N := 679 / 1000) (a := 681 / 1000)
    (eb := 772 / 1000) (xi := 485 / 1000) (e1 := 8787 / 10000) (e2 := 323 / 100000)
    (N22 := 18334 / 1000 / 46500) (q := 2 * (679 / 1000) / 46500) (sd := 201 / 500)
    (s := 941 / 2000) (by norm_num) c4 hXi hXi4' hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (681 / 1000 : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (941 / 2000 - 201 / 500) ^ 8) ≤
      (1609 / 100 * (681 / 1000 : ℝ)) ^ 4 / (46500 ^ 3 * (941 / 2000 - 201 / 500) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- **The conditional classifier theorem WITHOUT the Agent frame hypothesis, every
`n ≥ 46 500`.** For a design with the Agent centre of Part 154 and a `τ₀` that is a function of
the World data: IF the events `H`, `E₁` of the caller have charges with
`δ_hid + v_W/h_W² + δ_extra + 0.0003 ≤ 0.0063`, and on `H ∩ {H̄_W ≤ h_W} ∩ E₁` the World window
(`τ₀ > 0`, `0.46 ≤ θ_in ≤ 0.55`), the World frame bound `1.377/n` and the Agent replacement hold,
THEN the program succeeds with probability at least `99/100`. The Agent frame bound `7.5/n` is
PROVED on four Agent events of total charge at most `0.0003`; the ledger is that of
`classifier_frame_75` (`Part160Ledger2`). -/
theorem classifier_agentframe_46500 (hn : 46500 ≤ n) (D : Design n) (hD : AgentCentre154 D)
    (hτ : TauWorld D) (t : ℝ) {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra + 30 / 100000 ≤ 63 / 10 ^ 4)
    (hWin : WINDOW_hyp D (goodSet H E₁ (HbarW D) hWL))
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hn16 : 16384 ≤ n := by omega
  have hEv1 := events_with_EA16 hn16 D hτ hEv
  have hEv2 := events_with_agent D hτ (measurableSet_SXi n) (by norm_num) (SXi_charge hn16) hEv1
  have hEv3 := events_with_agent D hτ (measurableSet_SXi4n n) (by norm_num)
    (SXi4n_charge hn16) hEv2
  have hEv4 := events_with_agent D hτ (measurableSet_SXi8n n) (by norm_num)
    (SXi8n_charge hn16) hEv3
  have hsub1 := goodSet_EA16_subset D H E₁ (HbarW D) hWL
  have hsub2 := goodSet_inter_subset H (E₁ ∩ EA16 D) (agentEv D (SXi n)) (HbarW D) hWL
  have hsub3 := goodSet_inter_subset H ((E₁ ∩ EA16 D) ∩ agentEv D (SXi n))
    (agentEv D (SXi4n n)) (HbarW D) hWL
  have hsub4 := goodSet_inter_subset H (((E₁ ∩ EA16 D) ∩ agentEv D (SXi n)) ∩
    agentEv D (SXi4n n)) (agentEv D (SXi8n n)) (HbarW D) hWL
  have hsub := ((hsub4.trans hsub3).trans hsub2).trans hsub1
  have hFA := frameA_46500 hn D hD (window_mono hsub hWin)
    (fun c hc => goodSet_EA16_mem D c (hsub2 (hsub3 (hsub4 hc))))
    (fun c hc => goodSet_inter_mem (hsub3 (hsub4 hc)))
    (fun c hc => goodSet_inter_mem (hsub4 hc)) (fun c hc => goodSet_inter_mem hc)
  exact classifier_frame_75 hn D t hEv4 (by linarith) (frameW_mono hsub hFW) hFA
    (repla_mono hsub hRA)

/-- `0.001900001 + v_W/h_W² + 0.001104285235085 + 0.0003 ≤ 0.0063`. -/
lemma ledger_charges_fit30 : δhidL + vWL / hWL ^ 2 + δextraL + 30 / 100000 ≤ 63 / 10 ^ 4 := by
  unfold δhidL vWL hWL δextraL
  norm_num

/-- **The paper's design and the paper's charges, every `n ≥ 46 500`**: no Agent frame
hypothesis. -/
theorem classifier_paper_agentframe_46500 (hn : 46500 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {H E₁ : Set (Ret n)}
    (hEv : EVENTS_hyp (paperDesign n fT wT hf hw).toCentres H E₁
      (HbarW (paperDesign n fT wT hf hw)) δhidL vWL δextraL)
    (hWin : WINDOW_hyp (paperDesign n fT wT hf hw)
      (goodSet H E₁ (HbarW (paperDesign n fT wT hf hw)) hWL))
    (hFW : FRAME_W_hyp (paperDesign n fT wT hf hw).toCentres (cWL / n)
      (goodSet H E₁ (HbarW (paperDesign n fT wT hf hw)) hWL))
    (hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hAL
      (goodSet H E₁ (HbarW (paperDesign n fT wT hf hw)) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_agentframe_46500 hn _ (paperDesign_agentCentre fT wT hf hw)
    (paperDesign_tauWorld fT wT hf hw) t hEv ledger_charges_fit30 hWin hFW hRA

/-! ## With the sharper first-layer variance (`Part160Sc`) -/

/-- **The Agent frame bound `13 / 2/n`, every `n ≥ 41500`**: on `EA16 D` and the four events
`SXi`, `SXi4n`, `SXi8n`, `SSc`, in the World window. Constants: `N_cov = 0.679`, `ξ = 0.485`,
`e_b ≤ 0.7315`, `Ξ₄, Ξ₈ ≤ 0.681 γ_A/n`, cutoff `d = (439 / 1000)²`. -/
theorem frameA_41500 (hn : 41500 ≤ n) (D : Design n) (hD : AgentCentre154 D) {E : Set (Ret n)}
    (hWin : WINDOW_hyp D E) (hE : E ⊆ EA16 D) (hE' : E ⊆ agentEv D (SXi n))
    (hE4 : E ⊆ agentEv D (SXi4n n)) (hE8 : E ⊆ agentEv D (SXi8n n))
    (hES : E ⊆ agentEv D (SSc n)) : FRAME_A_hyp D (13 / 2 / n) E := by
  intro c hc w
  obtain ⟨hτ, hθ0, hθ1⟩ := hWin c hc
  have hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c) := hE hc hτ
  have hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n := hE' hc hτ
  have hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n := hE4 hc hτ
  have hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n := hE8 hc hτ
  have hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n := hES hc hτ
  have hn16 : 16384 ≤ n := by omega
  have hnR : (41500 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hXi := XiS_noncentral hn16 hτ hθ0 hθ1 hS
  have hXi4 := Xi4_noncentral hn16 hτ hθ0 hθ1 hS4
  have hXi8 := Xi8_noncentral hn16 hτ hθ0 hθ1 hS8
  have hXi4' : Xi4 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ 681 / 1000 * (2 / (n : ℝ)) / n :=
    hXi4.trans (by
      have : (0 : ℝ) ≤ 2 / (n : ℝ) / n := by positivity
      have e1 : (679 : ℝ) / 1000 * (2 / (n : ℝ)) / n = 679 / 1000 * (2 / (n : ℝ) / n) := by ring
      have e2 : (681 : ℝ) / 1000 * (2 / (n : ℝ)) / n = 681 / 1000 * (2 / (n : ℝ) / n) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right (by norm_num) this)
  have heb := eb16_sharp hn16 hτ hθ0 hθ1 hG hSS
  obtain ⟨-, -, -, c4, -, c6, -⟩ := centre16 hn16 hτ hθ0 hθ1 hG
  have c1 := (centre16 hn16 hτ hθ0 hθ1 hG).1
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 41500 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point8g (by omega) D hD c hτ (N := 679 / 1000) (a := 681 / 1000)
    (eb := 7315 / 10000) (xi := 485 / 1000) (e1 := 8553 / 10000) (e2 := 171 / 50000)
    (N22 := 18334 / 1000 / 41500) (q := 2 * (679 / 1000) / 41500) (sd := 439 / 1000)
    (s := 1023 / 2000) (by norm_num) c4 hXi hXi4' hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (681 / 1000 : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (1023 / 2000 - 439 / 1000) ^ 8) ≤
      (1609 / 100 * (681 / 1000 : ℝ)) ^ 4 / (41500 ^ 3 * (1023 / 2000 - 439 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- **The conditional classifier theorem WITHOUT the Agent frame hypothesis, every
`n ≥ 41500`.** As `classifier_agentframe_46500`; the Agent frame bound `13 / 2/n` is PROVED on
five Agent events of total charge at most `32/100000`; the ledger is that of
`classifier_frame_65` (`Part160Ledger2`). -/
theorem classifier_agentframe_41500 (hn : 41500 ≤ n) (D : Design n) (hD : AgentCentre154 D)
    (hτ : TauWorld D) (t : ℝ) {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra + 32 / 100000 ≤ 63 / 10 ^ 4)
    (hWin : WINDOW_hyp D (goodSet H E₁ (HbarW D) hWL))
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hn16 : 16384 ≤ n := by omega
  have hEv1 := events_with_EA16 hn16 D hτ hEv
  have hEv2 := events_with_agent D hτ (measurableSet_SXi n) (by norm_num) (SXi_charge hn16) hEv1
  have hEv3 := events_with_agent D hτ (measurableSet_SXi4n n) (by norm_num)
    (SXi4n_charge hn16) hEv2
  have hEv4 := events_with_agent D hτ (measurableSet_SXi8n n) (by norm_num)
    (SXi8n_charge hn16) hEv3
  have hEv5 := events_with_agent D hτ (measurableSet_SSc n) (by norm_num)
    (SSc_charge_num hn16) hEv4
  have hsub1 := goodSet_EA16_subset D H E₁ (HbarW D) hWL
  have hsub2 := goodSet_inter_subset H (E₁ ∩ EA16 D) (agentEv D (SXi n)) (HbarW D) hWL
  have hsub3 := goodSet_inter_subset H ((E₁ ∩ EA16 D) ∩ agentEv D (SXi n))
    (agentEv D (SXi4n n)) (HbarW D) hWL
  have hsub4 := goodSet_inter_subset H (((E₁ ∩ EA16 D) ∩ agentEv D (SXi n)) ∩
    agentEv D (SXi4n n)) (agentEv D (SXi8n n)) (HbarW D) hWL
  have hsub5 := goodSet_inter_subset H ((((E₁ ∩ EA16 D) ∩ agentEv D (SXi n)) ∩
    agentEv D (SXi4n n)) ∩ agentEv D (SXi8n n)) (agentEv D (SSc n)) (HbarW D) hWL
  have hsub := (((hsub5.trans hsub4).trans hsub3).trans hsub2).trans hsub1
  have hFA := frameA_41500 hn D hD (window_mono hsub hWin)
    (fun c hc => goodSet_EA16_mem D c (hsub2 (hsub3 (hsub4 (hsub5 hc)))))
    (fun c hc => goodSet_inter_mem (hsub3 (hsub4 (hsub5 hc))))
    (fun c hc => goodSet_inter_mem (hsub4 (hsub5 hc)))
    (fun c hc => goodSet_inter_mem (hsub5 hc)) (fun c hc => goodSet_inter_mem hc)
  exact classifier_frame_65 hn D t hEv5 (by linarith) (frameW_mono hsub hFW) hFA
    (repla_mono hsub hRA)

/-- **The paper's design and the paper's charges, every `n ≥ 41500`**: no Agent frame
hypothesis. -/
theorem classifier_paper_agentframe_41500 (hn : 41500 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {H E₁ : Set (Ret n)}
    (hEv : EVENTS_hyp (paperDesign n fT wT hf hw).toCentres H E₁
      (HbarW (paperDesign n fT wT hf hw)) δhidL vWL δextraL)
    (hWin : WINDOW_hyp (paperDesign n fT wT hf hw)
      (goodSet H E₁ (HbarW (paperDesign n fT wT hf hw)) hWL))
    (hFW : FRAME_W_hyp (paperDesign n fT wT hf hw).toCentres (cWL / n)
      (goodSet H E₁ (HbarW (paperDesign n fT wT hf hw)) hWL))
    (hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hAL
      (goodSet H E₁ (HbarW (paperDesign n fT wT hf hw)) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_agentframe_41500 hn _ (paperDesign_agentCentre fT wT hf hw)
    (paperDesign_tauWorld fT wT hf hw) t hEv
    (by unfold δhidL vWL hWL δextraL; norm_num) hWin hFW hRA

end BstLean.Part160

open BstLean.Part160 in
#print axioms frameA_46500
open BstLean.Part160 in
#print axioms classifier_agentframe_46500
open BstLean.Part160 in
#print axioms classifier_paper_agentframe_46500
open BstLean.Part160 in
#print axioms frameA_41500
open BstLean.Part160 in
#print axioms classifier_agentframe_41500
open BstLean.Part160 in
#print axioms classifier_paper_agentframe_41500
