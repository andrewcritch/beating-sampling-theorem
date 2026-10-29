import BstLean.Part160Final

/-!
# Part 160 (file `Supply`): the three scalar hypotheses from the library, every `n ≥ 16 384`

Role: `delegations/statements/p160-spec.md`, item 2. Do not use `sorry`, `native_decide` or
`axiom`.

For a design with the Agent centre of Part 154 (`AgentCentre154`), on a set `E` of retained
values with the World window (`WINDOW_hyp`) and inside the Agent events:

* `cov_hyp_lib`: `COV_hyp D 1.1911 E` on `EA16` (charge `≤ 0.00015` for all of `EA16`).
* `cov_hyp_noncentral`: `COV_hyp D 0.679 E` on `agentEv D (SXi n)` (charge `≤ 0.00005`).
* `centre_hyp_lib`: `CENTRE_hyp D 0.485 E` on `EA16`.
* `mass_hyp_16384`: `MASS_hyp D 0.347² 0.84 E` on the three events (`SXi8`: charge `≤ 0.00005`):
  cutoff `d = 0.120409`, `n·β_d ≤ 0.84`.
* `frameA_16384`: `FRAME_A_hyp D (10.6/n) E`, every `n ≥ 16 384`, from `frameA_of_three`.

The paper has `N_cov = 0.341973`, `ξ′ = 0.0832`, `d = 0.258897`, `n β_d ≤ 0.1`, frame constant
`1.743`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part154 BstLean.Part157
open BstLean.Part153 (XiS Xi4)

variable {n : ℕ}

/-- **(COV) from the library, `N_cov = 1.1911`** (Gaussian Poincaré and Lemma PP). -/
theorem cov_hyp_lib (hn : 16384 ≤ n) (D : Design n) {E : Set (Ret n)} (hWin : WINDOW_hyp D E)
    (hE : E ⊆ EA16 D) : COV_hyp D (11911 / 10000) E :=
  fun c hc => cov16_at hn D c (hWin c hc).1 (hE hc (hWin c hc).1)

/-- **(COV) with the noncentral inverse radius moment, `N_cov = 0.679`** (paper: Lemma
`t7:p04:radius`, which has `0.596` in the paper's window). -/
theorem cov_hyp_noncentral (hn : 16384 ≤ n) (D : Design n) {E : Set (Ret n)}
    (hWin : WINDOW_hyp D E) (hE' : E ⊆ agentEv D (SXi n)) : COV_hyp D (679 / 1000) E := by
  intro c hc
  obtain ⟨hτ, hθ0, hθ1⟩ := hWin c hc
  have hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n := hE' hc hτ
  exact cov_at_of_XiS (by omega) D c hτ (XiS_noncentral hn hτ hθ0 hθ1 hS)

/-- **(CENTRE) from the library, `ξ = 0.485`** (the mean-field lemma of Part 154). -/
theorem centre_hyp_lib (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D)
    {E : Set (Ret n)} (hWin : WINDOW_hyp D E) (hE : E ⊆ EA16 D) :
    CENTRE_hyp D (485 / 1000) E := by
  intro c hc
  obtain ⟨hτ, hθ0, hθ1⟩ := hWin c hc
  exact centre16_at hn D hD c hτ hθ0 hθ1 (hE hc hτ)

/-- **(MASS) from the eighth moment of `σ`, every `n ≥ 16 384`**: cutoff `d = 0.347²`,
`n·β_d ≤ 0.84`. The paper has the cutoff `0.258897` with `n β_d ≤ 0.1` (moments of order 320 and
the fixed-pair bounds, not in Lean). -/
theorem mass_hyp_16384 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D)
    {E : Set (Ret n)} (hWin : WINDOW_hyp D E) (hE : E ⊆ EA16 D)
    (hE' : E ⊆ agentEv D (SXi n)) (hE8 : E ⊆ agentEv D (SXi8 n)) :
    MASS_hyp D ((347 / 1000) ^ 2) (84 / 100) E := by
  intro c hc
  obtain ⟨hτ, hθ0, hθ1⟩ := hWin c hc
  have hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c) := hE hc hτ
  have hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n := hE' hc hτ
  have hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8 n := hE8 hc hτ
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hXi := XiS_noncentral hn hτ hθ0 hθ1 hS
  have heb := eb16 hn hτ hθ0 hθ1 hG
  obtain ⟨c1, -, -, c4, c5, c6, -⟩ := centre16 hn hτ hθ0 hθ1 hG
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 16384 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  unfold MASS_at
  rw [hD c]
  have hq : 2 * (679 / 1000 : ℝ) / n ≤ 2 * (679 / 1000) / 16384 := hinv _ (by norm_num)
  have hN22 : (18334 / 1000 : ℝ) / n ≤ 18334 / 1000 / 16384 := hinv _ (by norm_num)
  have hm := mass_bound8 (by omega) c.2.1.1.1 c.2.1.1.2 c.1.2 hτ c4 (N := 679 / 1000)
    (a := 11911 / 10000) (eb := 772 / 1000) (xi := 485 / 1000) (N22 := 18334 / 1000 / 16384)
    (e1 := 8787 / 10000) (e2 := 55 / 10000) (sd := 347 / 1000) (s := 4646 / 10000)
    hXi c5 (mem_SXi8 hS8) heb c1 (c6.trans hN22) (by norm_num) (by norm_num) (by norm_num)
    ((hinv _ (by norm_num)).trans (by norm_num)) (by norm_num) (by norm_num)
    (by
      have h0 : (4646 / 10000 : ℝ) ^ 2 ≤ 1 - 18334 / 1000 / 16384 * (2 + 18334 / 1000 / 16384) -
          (8787 / 10000 + 55 / 10000) ^ 2 - 2 * (679 / 1000) / 16384 := by norm_num
      linarith)
  refine hm.trans ?_
  have h1 : (1609 / 100 * (11911 / 10000 : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (4646 / 10000 - 347 / 1000) ^ 8) ≤
      (1609 / 100 * (11911 / 10000 : ℝ)) ^ 4 / (16384 ^ 3 * (4646 / 10000 - 347 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  exact h1.trans (by norm_num)

/-- **The Agent frame bound in the frontier range, every `n ≥ 16 384`: constant `10.6`.** From
`frameA_of_three` with the three scalar bounds of this file:
`(0.679 + 0.485)/0.347² + 0.84 ≤ 10.6`. The ledger of Part 156 needs `1.743`. -/
theorem frameA_16384 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D)
    {E : Set (Ret n)} (hWin : WINDOW_hyp D E) (hE : E ⊆ EA16 D)
    (hE' : E ⊆ agentEv D (SXi n)) (hE8 : E ⊆ agentEv D (SXi8 n)) :
    FRAME_A_hyp D (106 / 10 / n) E :=
  frameA_of_three (by omega) D (by norm_num) (by norm_num)
    (cov_hyp_noncentral hn D hWin hE') (centre_hyp_lib hn D hD hWin hE)
    (mass_hyp_16384 hn D hD hWin hE hE' hE8) (by norm_num)

end BstLean.Part160

open BstLean.Part160 in
#print axioms cov_hyp_lib
open BstLean.Part160 in
#print axioms cov_hyp_noncentral
open BstLean.Part160 in
#print axioms centre_hyp_lib
open BstLean.Part160 in
#print axioms mass_hyp_16384
open BstLean.Part160 in
#print axioms frameA_16384
