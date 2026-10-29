import BstLean.Part160Best
import BstLean.Part160Split2
import BstLean.Part160Ledger3
import BstLean.Part160MFAll

/-!
# Part 160 (file `Best2`): the frame constant by the split of second order

Do not use `sorry`, `native_decide` or `axiom`. This file is generated from a template; the
rational constants were chosen outside Lean; Lean checks every inequality.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part154 BstLean.Part157
open BstLean.Part153 (XiS Xi4)
open BstLean.Part156

variable {n : ℕ}

/-- **The Agent frame bound `(560 / 100)/n`, every `n ≥ 36500`, by the split of second order**: on
`EA16 D` and the four events `SXi`, `SXi4n`, `SXi8n`, `SSc`, in the World window. Constants:
`N_cov = 0.679`, `ξ = 0.485 (Part 154)`, `e_b ≤ 0.7315`, `Ξ₄, Ξ₈ ≤ 0.681 γ_A/n`, typical value
`s = 511 / 1000`, cutoff `sd = 419 / 1000`. -/
theorem frameA2_36500 (hn : 36500 ≤ n) (D : Design n) (hD : AgentCentre154 D) {E : Set (Ret n)}
    (hWin : WINDOW_hyp D E) (hE : E ⊆ EA16 D) (hE' : E ⊆ agentEv D (SXi n))
    (hE4 : E ⊆ agentEv D (SXi4n n)) (hE8 : E ⊆ agentEv D (SXi8n n))
    (hES : E ⊆ agentEv D (SSc n)) : FRAME_A_hyp D (560 / 100 / n) E := by
  intro c hc w
  obtain ⟨hτ, hθ0, hθ1⟩ := hWin c hc
  have hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c) := hE hc hτ
  have hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n := hE' hc hτ
  have hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n := hE4 hc hτ
  have hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n := hE8 hc hτ
  have hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n := hES hc hτ
  have hn16 : 16384 ≤ n := by omega
  have hnR : (36500 : ℝ) ≤ n := by exact_mod_cast hn
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
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 36500 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point2 (by omega) D hD c hτ (N := 679 / 1000) (a := 681 / 1000)
    (eb := 7315 / 10000) (xi := 485 / 1000) (e1 := 8553 / 10000) (e2 := 73 / 20000)
    (N22 := 18334 / 1000 / 36500) (q := 2 * (679 / 1000) / 36500) (sd := 419 / 1000)
    (s := 511 / 1000) (r := 15219 / 10000) (η := 41 / 100) (κ := 1147 / 200) (ρ := 27 / 6250)
    (by norm_num) c4 hXi hXi4' hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num)) ?_ w
  have h1 : (1609 / 100 * (681 / 1000 : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (511 / 1000 - 419 / 1000) ^ 8) ≤
      (1609 / 100 * (681 / 1000 : ℝ)) ^ 4 / (36500 ^ 3 * (511 / 1000 - 419 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- **The conditional classifier theorem WITHOUT the Agent frame hypothesis, every
`n ≥ 36500`** (split of second order). As `classifier_agentframe_46500`; the Agent frame bound
`(560 / 100)/n` is PROVED on five Agent events of total charge at most `32/100000`; the
ledger is that of `classifier_frame_560`. -/
theorem classifier_agentframe2_36500 (hn : 36500 ≤ n) (D : Design n) (hD : AgentCentre154 D)
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
  have hFA := frameA2_36500 hn D hD (window_mono hsub hWin)
    (fun c hc => goodSet_EA16_mem D c (hsub2 (hsub3 (hsub4 (hsub5 hc)))))
    (fun c hc => goodSet_inter_mem (hsub3 (hsub4 (hsub5 hc))))
    (fun c hc => goodSet_inter_mem (hsub4 (hsub5 hc)))
    (fun c hc => goodSet_inter_mem (hsub5 hc)) (fun c hc => goodSet_inter_mem hc)
  exact classifier_frame_560 hn D t hEv5 (by linarith) (frameW_mono hsub hFW) hFA
    (repla_mono hsub hRA)

/-- **The paper's design and the paper's charges, every `n ≥ 36500`**: no Agent frame
hypothesis. -/
theorem classifier_paper_agentframe2_36500 (hn : 36500 ≤ n) (fT wT : Ret n → ℕ → ℝ)
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
  classifier_agentframe2_36500 hn _ (paperDesign_agentCentre fT wT hf hw)
    (paperDesign_tauWorld fT wT hf hw) t hEv
    (by unfold δhidL vWL hWL δextraL; norm_num) hWin hFW hRA

/-- **The Agent frame bound `(9 / 2)/n`, every `n ≥ 30500`, by the split of second order**: on
`EA16 D` and the four events `SXi`, `SXi4n`, `SXi8n`, `SSc`, in the World window. Constants:
`N_cov = 0.679`, `ξ = 0.221 (the integrated remainder, `Part160MF`)`, `e_b ≤ 0.7315`, `Ξ₄, Ξ₈ ≤ 0.681 γ_A/n`, typical value
`s = 1281 / 2500`, cutoff `sd = 207 / 500`. -/
theorem frameA2_30500 (hn : 30500 ≤ n) (D : Design n) (hD : AgentCentre154 D) {E : Set (Ret n)}
    (hWin : WINDOW_hyp D E) (hE : E ⊆ EA16 D) (hE' : E ⊆ agentEv D (SXi n))
    (hE4 : E ⊆ agentEv D (SXi4n n)) (hE8 : E ⊆ agentEv D (SXi8n n))
    (hES : E ⊆ agentEv D (SSc n)) : FRAME_A_hyp D (9 / 2 / n) E := by
  intro c hc w
  obtain ⟨hτ, hθ0, hθ1⟩ := hWin c hc
  have hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c) := hE hc hτ
  have hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n := hE' hc hτ
  have hS4 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi4n n := hE4 hc hτ
  have hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8n n := hE8 hc hτ
  have hSS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SSc n := hES hc hτ
  have hn16 : 16384 ≤ n := by omega
  have hnR : (30500 : ℝ) ≤ n := by exact_mod_cast hn
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
  have c1 := centre16_int hn16 hτ hθ0 hθ1 hG
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 30500 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point2 (by omega) D hD c hτ (N := 679 / 1000) (a := 681 / 1000)
    (eb := 7315 / 10000) (xi := 221 / 1000) (e1 := 8553 / 10000) (e2 := 27 / 10000)
    (N22 := 18334 / 1000 / 30500) (q := 2 * (679 / 1000) / 30500) (sd := 207 / 500)
    (s := 1281 / 2500) (r := 15219 / 10000) (η := 7 / 25) (κ := 2351 / 500) (ρ := 59 / 12500)
    (by norm_num) c4 hXi hXi4' hXi8 heb c1 (c6.trans (hinv _ (by norm_num)))
    (by norm_num) (by norm_num) (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num)) ?_ w
  have h1 : (1609 / 100 * (681 / 1000 : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (1281 / 2500 - 207 / 500) ^ 8) ≤
      (1609 / 100 * (681 / 1000 : ℝ)) ^ 4 / (30500 ^ 3 * (1281 / 2500 - 207 / 500) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- **The conditional classifier theorem WITHOUT the Agent frame hypothesis, every
`n ≥ 30500`** (split of second order). As `classifier_agentframe_46500`; the Agent frame bound
`(9 / 2)/n` is PROVED on five Agent events of total charge at most `32/100000`; the
ledger is that of `classifier_frame_45`. -/
theorem classifier_agentframe2_30500 (hn : 30500 ≤ n) (D : Design n) (hD : AgentCentre154 D)
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
  have hFA := frameA2_30500 hn D hD (window_mono hsub hWin)
    (fun c hc => goodSet_EA16_mem D c (hsub2 (hsub3 (hsub4 (hsub5 hc)))))
    (fun c hc => goodSet_inter_mem (hsub3 (hsub4 (hsub5 hc))))
    (fun c hc => goodSet_inter_mem (hsub4 (hsub5 hc)))
    (fun c hc => goodSet_inter_mem (hsub5 hc)) (fun c hc => goodSet_inter_mem hc)
  exact classifier_frame_45 hn D t hEv5 (by linarith) (frameW_mono hsub hFW) hFA
    (repla_mono hsub hRA)

/-- **The paper's design and the paper's charges, every `n ≥ 30500`**: no Agent frame
hypothesis. -/
theorem classifier_paper_agentframe2_30500 (hn : 30500 ≤ n) (fT wT : Ret n → ℕ → ℝ)
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
  classifier_agentframe2_30500 hn _ (paperDesign_agentCentre fT wT hf hw)
    (paperDesign_tauWorld fT wT hf hw) t hEv
    (by unfold δhidL vWL hWL δextraL; norm_num) hWin hFW hRA

end BstLean.Part160

open BstLean.Part160 in
#print axioms frameA2_36500
open BstLean.Part160 in
#print axioms classifier_agentframe2_36500
open BstLean.Part160 in
#print axioms classifier_paper_agentframe2_36500
open BstLean.Part160 in
#print axioms frameA2_30500
open BstLean.Part160 in
#print axioms classifier_agentframe2_30500
open BstLean.Part160 in
#print axioms classifier_paper_agentframe2_30500
