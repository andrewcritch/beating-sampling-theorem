import BstLean.Part160Mass
import BstLean.Part160Ledger
import BstLean.Part160Cov
import BstLean.Part160Eb
import BstLean.Part160Mass8

/-!
# Part 160 (file `Final`): the Agent frame bound from the library, and the classifier theorem
without the Agent frame hypothesis for large `n`

Role: `delegations/statements/p160-spec.md`, items 2, 3 and 4.
Do not use `sorry`, `native_decide` or `axiom`.

* `cov_at_of_XiS`: `COV_at D c N` from `Ξ ≤ N γ_A/n` (Gaussian Poincaré).
* `frameA_point`: the frame bound at one retained value from the bounds of Parts 153, 154 and
  the fourth-moment mass bound, with free numbers.
* `frameA_lib` (item 2/3): `FRAME_A_hyp D (18/n)` on the event `EA16`, `n ≥ 170 000`, with the
  library constants for the covariance, the centre and the centre energy (`N_cov = 1.1911`,
  `ξ = 0.485`, `e_b ≤ 0.82`); the mass bound is new in Part 160 (fourth moment of `σ`).
* `frameA_sharp` (item 4): `FRAME_A_hyp D (10.5/n)` on `EA16` and the event `SXi`,
  `n ≥ 100 000`, with `N_cov = 0.679` (noncentral inverse radius moment) and `e_b ≤ 0.772`.
* `classifier_agentframe_lib`, `classifier_agentframe_sharp`: the conditional classifier
  theorem WITHOUT the hypothesis `FRAME_A_hyp`, for `n ≥ 170 000` and for `n ≥ 100 000`.
  The remaining hypotheses are `EVENTS_hyp` (the events `H`, `E₁` are parameters; `E₁` can hold
  further Agent events of the caller), the World hypotheses `WINDOW_hyp`, `FRAME_W_hyp`, and the
  Agent replacement `REPLA_mix_hyp`. With the paper's charge `δ_extraL` (which already counts the
  paper's Agent events) the Agent events of this part are paid a second time: this is sound.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part154 BstLean.Part157
open BstLean.Part134 (lam res sig eDir)
open BstLean.Part153 (nrm XiS Xi4 N2 sq2 hid2Mean_cr)
open BstLean.Part156

variable {n : ℕ}

/-- `COV_at D c N` from `Ξ ≤ N·γ_A/n` (the Gaussian Poincaré inequality, `cov_hid2_le`). -/
theorem cov_at_of_XiS (hn : 6 ≤ n) (D : Design n) (c : Ret n) (hτ : 0 < D.tau0 c) {N : ℝ}
    (hX : XiS c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ N * (2 / (n : ℝ)) / n) :
    COV_at D c N := by
  intro w
  have hn1 : 1 ≤ n := by omega
  have h1 := BstLean.Part153.cov_hid2_le hn c.2.1.1.1 c.2.1.1.2 c.1.2 hτ w
  have e : ∀ ξ, ∑ j, (hStand D c ξ j - muStand D c j) * w j =
      w ⬝ᵥ hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ)) -
        ∫ ξ', w ⬝ᵥ hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ')) ∂stdGauss (Fin n) := by
    intro ξ
    rw [BstLean.Part153.integral_dot_hid2_cr hn1]
    unfold dotProduct
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    change (hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ)) j -
      hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) j) * w j = _
    ring
  simp_rw [e]
  exact h1.trans (mul_le_mul_of_nonneg_right hX (normSq_nonneg w))

/-- **The frame bound at one retained value, with free numbers.** On `GoodC16`, in the window,
for the centre of Part 154: IF `Ξ ≤ N γ_A/n`, `e_b ≤ eb ≤ e₁²`, `0.485/n ≤ e₂²`,
`18.334/n ≤ N22`, `2N/n ≤ q`, `s² ≤ 1 − N22(2 + N22) − (e₁ + e₂)² − q`, `sd < s`,
`(2·1.1911 + r)² ≤ K` with `4·1.1911² + N² ≤ r²`, and
`(N + 0.485)/sd² + K/(n (s − sd)⁴) ≤ c_f`, THEN `∫ ⟨e_A, w⟩² dν′ ≤ (c_f/n)|w|²`. -/
theorem frameA_point (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100)
    (h : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    {N eb e1 e2 N22 q sd s r K cf : ℝ} (hN0 : 0 ≤ N)
    (hXi : XiS c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ N * (2 / (n : ℝ)) / n)
    (heb : 2 / (mA n : ℝ) * normSq ((1 / rhoC c.1.2 (D.tau0 c)) •
      bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)) ≤ 2 / (n : ℝ) * eb)
    (he1 : 0 ≤ e1) (he1' : eb ≤ e1 ^ 2) (he2 : 0 ≤ e2) (he2' : 485 / 1000 / (n : ℝ) ≤ e2 ^ 2)
    (hN22 : 18334 / 1000 / (n : ℝ) ≤ N22) (hq : 2 * N / n ≤ q)
    (hsd : 0 < sd) (hs : sd < s) (hs2 : s ^ 2 ≤ 1 - N22 * (2 + N22) - (e1 + e2) ^ 2 - q)
    (hr : 0 ≤ r) (hr2 : 4 * (11911 / 10000 : ℝ) ^ 2 + N ^ 2 ≤ r ^ 2)
    (hK : (2 * (11911 / 10000 : ℝ) + r) ^ 2 ≤ K)
    (hsum : (N + 485 / 1000) / sd ^ 2 + K / (n * (s - sd) ^ 4) ≤ cf) (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      cf / n * ∑ j, w j ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hn6 : 6 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨c1, -, -, c4, c5, c6, -⟩ := centre16 hn hτ hθ0 hθ1 h
  have hcov := cov_at_of_XiS hn6 D c hτ hXi
  have hcen := centre16_at hn D hD c hτ hθ0 hθ1 h
  have hgap : 0 < s - sd := by linarith
  have hmass : MASS_at D c (sd ^ 2) (K / (n * (s - sd) ^ 4)) := by
    unfold MASS_at
    rw [hD c]
    have hm := mass_bound4 hn6 c.2.1.1.1 c.2.1.1.2 c.1.2 hτ c4 (N := N)
      (a := 11911 / 10000) (eb := eb) (xi := 485 / 1000) (N22 := N22) (e1 := e1) (e2 := e2)
      (sd := sd) (s := s) hXi c5 heb c1 (c6.trans hN22) he1 he1' he2 he2' hsd.le hs
      (by
        have : -(2 * N / (n : ℝ)) ≥ -q := by linarith
        linarith)
    refine hm.trans ?_
    have h1 := sharp_const_le (a := 11911 / 10000) (N := N) (r := r) (by norm_num) hr hr2
    exact div_le_div_of_nonneg_right (h1.trans hK) (by positivity)
  exact frameA_at hn1 D c (by positivity) hN0 hcov hcen hmass hsum w

/-! ## The library constants: `n ≥ 170 000`, frame constant `18` -/

/-- **(item 2/3) The Agent frame bound with the library constants for the covariance, the centre
and the centre energy (the mass bound is the fourth-moment bound of Part 160)**: for a design with
the Agent
centre of Part 154, on every set `E` of retained values inside the event `EA16 D` and with the
World window (`τ₀ > 0`, `0.46 ≤ θ_in ≤ 0.55`): `FRAME_A_hyp D (18/n) E`, every `n ≥ 170 000`.
Constants: `N_cov = 1.1911`, `ξ = 0.485`, `e_b ≤ 0.82`, cutoff `d = 0.3285²`, fourth moment of
`σ`. -/
theorem frameA_lib (hn : 170000 ≤ n) (D : Design n) (hD : AgentCentre154 D) {E : Set (Ret n)}
    (hWin : WINDOW_hyp D E) (hE : E ⊆ EA16 D) : FRAME_A_hyp D (18 / n) E := by
  intro c hc w
  obtain ⟨hτ, hθ0, hθ1⟩ := hWin c hc
  have hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c) := hE hc hτ
  have hn16 : 16384 ≤ n := by omega
  have hnR : (170000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hXi := BstLean.Part153.AStage16_Xi hn16 hτ hG.2
  have heb := (centre16 hn16 hτ hθ0 hθ1 hG).2.2.1
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 170000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point hn16 D hD c hτ hθ0 hθ1 hG (N := 11911 / 10000) (eb := 82 / 100)
    (e1 := 9056 / 10000) (e2 := 17 / 10000) (N22 := 18334 / 1000 / 170000)
    (q := 2 * (11911 / 10000) / 170000) (sd := 3285 / 10000) (s := 42 / 100)
    (r := 26634 / 10000) (K := 2546 / 100) (by norm_num) hXi heb (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num)) (hinv _ (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ w
  have h1 : (2546 / 100 : ℝ) / (n * (42 / 100 - 3285 / 10000) ^ 4) ≤
      2546 / 100 / (170000 * (42 / 100 - 3285 / 10000) ^ 4) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right hnR (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-! ## The sharpened constants: `n ≥ 100 000`, frame constant `10.5` -/

/-- **(item 4) The Agent frame bound with the noncentral covariance bound and the sharper
centre energy**: on `EA16 D` and the event `agentEv D (SXi n)`, in the World window:
`FRAME_A_hyp D (10.5/n) E`, every `n ≥ 100 000`. Constants: `N_cov = 0.679`, `ξ = 0.485`,
`e_b ≤ 0.772`, cutoff `d = 0.359²`, fourth moment of `σ`. -/
theorem frameA_sharp (hn : 100000 ≤ n) (D : Design n) (hD : AgentCentre154 D) {E : Set (Ret n)}
    (hWin : WINDOW_hyp D E) (hE : E ⊆ EA16 D) (hE' : E ⊆ agentEv D (SXi n)) :
    FRAME_A_hyp D (105 / 10 / n) E := by
  intro c hc w
  obtain ⟨hτ, hθ0, hθ1⟩ := hWin c hc
  have hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c) := hE hc hτ
  have hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n := hE' hc hτ
  have hn16 : 16384 ≤ n := by omega
  have hnR : (100000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hXi := XiS_noncentral hn16 hτ hθ0 hθ1 hS
  have heb := eb16 hn16 hτ hθ0 hθ1 hG
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 100000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point hn16 D hD c hτ hθ0 hθ1 hG (N := 679 / 1000) (eb := 772 / 1000)
    (e1 := 8787 / 10000) (e2 := 221 / 100000) (N22 := 18334 / 1000 / 100000)
    (q := 2 * (679 / 1000) / 100000) (sd := 359 / 1000) (s := 4728 / 10000)
    (r := 24772 / 10000) (K := 2362 / 100) (by norm_num) hXi heb (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num)) (hinv _ (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) ?_ w
  have h1 : (2362 / 100 : ℝ) / (n * (4728 / 10000 - 359 / 1000) ^ 4) ≤
      2362 / 100 / (100000 * (4728 / 10000 - 359 / 1000) ^ 4) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right hnR (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-! ## The classifier theorem without the Agent frame hypothesis -/

lemma frameW_mono {D : Centres n} {L : ℝ} {E E' : Set (Ret n)} (h : E' ⊆ E)
    (hF : FRAME_W_hyp D L E) : FRAME_W_hyp D L E' := fun c hc => hF c (h hc)

lemma repla_mono {D : Design n} {t hA : ℝ} {E E' : Set (Ret n)} (h : E' ⊆ E)
    (hF : REPLA_mix_hyp D t hA E) : REPLA_mix_hyp D t hA E' := fun c hc => hF c (h hc)

lemma window_mono {D : Design n} {E E' : Set (Ret n)} (h : E' ⊆ E)
    (hF : WINDOW_hyp D E) : WINDOW_hyp D E' := fun c hc => hF c (h hc)

/-- **(item 3) The conditional classifier theorem WITHOUT the Agent frame hypothesis, library
constants, every `n ≥ 170 000`.** For a design whose Agent centre is the centre of Part 154
(`AgentCentre154`; `paperDesign` has it) and whose `τ₀` is a function of the World data
(`TauWorld`): IF the World events have charges with
`δ_hid + v_W/h_W² + δ_extra + 0.00015 ≤ 0.0063`, and on `H ∩ {H̄_W ≤ h_W} ∩ E₁` the World window
(`τ₀ > 0`, `0.46 ≤ θ_in ≤ 0.55`), the World frame bound `1.377/n` and the Agent replacement hold,
THEN the program succeeds with probability at least `99/100`. The Agent frame bound is PROVED
(constant `18/n`) on an Agent event of charge at most `0.00015`. -/
theorem classifier_agentframe_lib (hn : 170000 ≤ n) (D : Design n) (hD : AgentCentre154 D)
    (hτ : TauWorld D) (t : ℝ) {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra + 15 / 100000 ≤ 63 / 10 ^ 4)
    (hWin : WINDOW_hyp D (goodSet H E₁ (HbarW D) hWL))
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (170000 : ℝ) ≤ n := by exact_mod_cast hn
  have hEv' := events_with_EA16 hn16 D hτ hEv
  have hsub := goodSet_EA16_subset D H E₁ (HbarW D) hWL
  have hFA : FRAME_A_hyp D (18 / n) (goodSet H (E₁ ∩ EA16 D) (HbarW D) hWL) :=
    frameA_lib hn D hD (window_mono hsub hWin) (fun c hc => goodSet_EA16_mem D c hc)
  exact classifier_networks_frameconst_success hn16 (cf := 18) (by unfold cfL; norm_num)
    (by unfold cfL; linarith) D t hEv' (by linarith) (frameW_mono hsub hFW) hFA
    (repla_mono hsub hRA)

/-- **(items 3 and 4) The conditional classifier theorem WITHOUT the Agent frame hypothesis,
sharpened constants, every `n ≥ 100 000`.** As `classifier_agentframe_lib`, with the Agent frame
bound `10.5/n` PROVED on two Agent events of total charge at most `0.0002`. -/
theorem classifier_agentframe_sharp (hn : 100000 ≤ n) (D : Design n) (hD : AgentCentre154 D)
    (hτ : TauWorld D) (t : ℝ) {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra + 20 / 100000 ≤ 63 / 10 ^ 4)
    (hWin : WINDOW_hyp D (goodSet H E₁ (HbarW D) hWL))
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (100000 : ℝ) ≤ n := by exact_mod_cast hn
  have hEv1 := events_with_EA16 hn16 D hτ hEv
  have hEv2 := events_with_agent D hτ (measurableSet_SXi n) (by norm_num) (SXi_charge hn16) hEv1
  have hsub1 := goodSet_EA16_subset D H E₁ (HbarW D) hWL
  have hsub2 := goodSet_inter_subset H (E₁ ∩ EA16 D) (agentEv D (SXi n)) (HbarW D) hWL
  have hsub := hsub2.trans hsub1
  have hFA : FRAME_A_hyp D (105 / 10 / n)
      (goodSet H ((E₁ ∩ EA16 D) ∩ agentEv D (SXi n)) (HbarW D) hWL) :=
    frameA_sharp hn D hD (window_mono hsub hWin)
      (fun c hc => goodSet_EA16_mem D c (hsub2 hc)) (fun c hc => goodSet_inter_mem hc)
  exact classifier_networks_frameconst_success hn16 (cf := 105 / 10) (by unfold cfL; norm_num)
    (by unfold cfL; linarith) D t hEv2 (by linarith) (frameW_mono hsub hFW) hFA
    (repla_mono hsub hRA)

/-! ## The eighth moment: `n ≥ 75 000`, frame constant `7.75` -/

/-- **The mass bound from the eighth moment** (Part160Mass8): with `Ξ₄, Ξ₈ ≤ a γ_A/n`,
cutoff `d = sd²`: `n·Pr(t_A|r|² < γ_A·sd²) ≤ (16.09·a)⁴/(n³·(s − sd)⁸)`. -/
theorem mass_bound8 (hn : 10 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {b : Fin (mA n) → ℝ} (hb : 0 < normSq b) {N a eb xi N22 e1 e2 sd s : ℝ}
    (hXi : XiS A₁ A₂ c τ ≤ N * (2 / (n : ℝ)) / n)
    (hXi4 : Xi4 A₁ A₂ c τ ≤ a * (2 / (n : ℝ)) / n)
    (hXi8 : Xi8 A₁ A₂ c τ ≤ a * (2 / (n : ℝ)) / n)
    (heb : 2 / (mA n : ℝ) * normSq b ≤ 2 / (n : ℝ) * eb)
    (hxi : 2 / (mA n : ℝ) * normSq (hid2Mean_cr A₁ A₂ c τ - b) ≤ xi * (2 / (n : ℝ)) / n)
    (hN22 : N2 2 A₁ A₂ c τ ≤ N22)
    (he1 : 0 ≤ e1) (he1' : eb ≤ e1 ^ 2) (he2 : 0 ≤ e2) (he2' : xi / n ≤ e2 ^ 2)
    (hsd : 0 ≤ sd) (hs : sd < s)
    (hs2 : s ^ 2 ≤ 1 - N22 * (2 + N22) - (e1 + e2) ^ 2 - 2 * N / n) :
    (n : ℝ) * (stdGauss (Fin n)).real
        {ξ | 2 / (mA n : ℝ) * normSq (res b (hid2 A₁ A₂ (sphPt (c + τ • ξ)))) <
          2 / (n : ℝ) * sd ^ 2} ≤
      (1609 / 100 * a) ^ 4 / ((n : ℝ) ^ 3 * (s - sd) ^ 8) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hγ : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hd : 0 < s - sd := by linarith
  have h := mass_bound_gen (by omega : 6 ≤ n) A₁ A₂ c hτ hb hXi heb hxi hN22 he1 he1' he2 he2'
    hsd hs hs2
    (T := fun g => (1609 / 100 * (a * (2 / (n : ℝ)) / n)) ^ 4 / g ^ 8)
    (fun g hg => sigD_markov8 hn A₁ A₂ c hτ hb hXi4 hXi8 hg)
  beta_reduce at h
  have e3 : (√(2 / (n : ℝ)) * (s - sd)) ^ 8 = (2 / (n : ℝ)) ^ 4 * (s - sd) ^ 8 := by
    have h2 : √(2 / (n : ℝ)) ^ 2 = 2 / (n : ℝ) := Real.sq_sqrt hγ.le
    calc (√(2 / (n : ℝ)) * (s - sd)) ^ 8 = (√(2 / (n : ℝ)) ^ 2) ^ 4 * (s - sd) ^ 8 := by ring
      _ = _ := by rw [h2]
  rw [e3] at h
  have e4 : (1609 / 100 * (a * (2 / (n : ℝ)) / n)) ^ 4 / ((2 / (n : ℝ)) ^ 4 * (s - sd) ^ 8) =
      (1609 / 100 * a) ^ 4 / ((n : ℝ) ^ 3 * (s - sd) ^ 8) / n := by
    field_simp
  rw [e4] at h
  calc (n : ℝ) * _ ≤ n * ((1609 / 100 * a) ^ 4 / ((n : ℝ) ^ 3 * (s - sd) ^ 8) / n) :=
        mul_le_mul_of_nonneg_left h hnR.le
    _ = _ := by field_simp

/-- The frame bound at one retained value with the eighth-moment mass bound, free numbers. -/
theorem frameA_point8 (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) (hθ0 : 46 / 100 ≤ thetaC c.1.2 (D.tau0 c))
    (hθ1 : thetaC c.1.2 (D.tau0 c) ≤ 55 / 100)
    (h : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c))
    (h8 : Xi8 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ 11911 / 10000 * (2 / (n : ℝ)) / n)
    {N eb e1 e2 N22 q sd s cf : ℝ} (hN0 : 0 ≤ N)
    (hXi : XiS c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ N * (2 / (n : ℝ)) / n)
    (heb : 2 / (mA n : ℝ) * normSq ((1 / rhoC c.1.2 (D.tau0 c)) •
      bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)) ≤ 2 / (n : ℝ) * eb)
    (he1 : 0 ≤ e1) (he1' : eb ≤ e1 ^ 2) (he2 : 0 ≤ e2) (he2' : 485 / 1000 / (n : ℝ) ≤ e2 ^ 2)
    (hN22 : 18334 / 1000 / (n : ℝ) ≤ N22) (hq : 2 * N / n ≤ q)
    (hsd : 0 < sd) (hs : sd < s) (hs2 : s ^ 2 ≤ 1 - N22 * (2 + N22) - (e1 + e2) ^ 2 - q)
    (hsum : (N + 485 / 1000) / sd ^ 2 +
      (1609 / 100 * (11911 / 10000 : ℝ)) ^ 4 / ((n : ℝ) ^ 3 * (s - sd) ^ 8) ≤ cf)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      cf / n * ∑ j, w j ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hn6 : 6 ≤ n := by omega
  obtain ⟨c1, -, -, c4, c5, c6, -⟩ := centre16 hn hτ hθ0 hθ1 h
  have hcov := cov_at_of_XiS hn6 D c hτ hXi
  have hcen := centre16_at hn D hD c hτ hθ0 hθ1 h
  have hmass : MASS_at D c (sd ^ 2)
      ((1609 / 100 * (11911 / 10000 : ℝ)) ^ 4 / ((n : ℝ) ^ 3 * (s - sd) ^ 8)) := by
    unfold MASS_at
    rw [hD c]
    exact mass_bound8 (by omega) c.2.1.1.1 c.2.1.1.2 c.1.2 hτ c4 (N := N)
      (a := 11911 / 10000) (eb := eb) (xi := 485 / 1000) (N22 := N22) (e1 := e1) (e2 := e2)
      (sd := sd) (s := s) hXi c5 h8 heb c1 (c6.trans hN22) he1 he1' he2 he2' hsd.le hs
      (by
        have : -(2 * N / (n : ℝ)) ≥ -q := by linarith
        linarith)
  exact frameA_at hn1 D c (by positivity) hN0 hcov hcen hmass hsum w

/-- **The frame bound at one retained value, every number free** (the general form of
`frameA_point8`): from `Ξ ≤ N γ_A/n`, `Ξ₄, Ξ₈ ≤ a γ_A/n`, `e_b ≤ eb`, the centre charge `ξ`,
`N₂₂ ≤ N22`, `b ≠ 0`. No event occurs in the statement. -/
theorem frameA_point8g (hn : 10 ≤ n) (D : Design n) (hD : AgentCentre154 D) (c : Ret n)
    (hτ : 0 < D.tau0 c) {N a eb xi e1 e2 N22 q sd s cf : ℝ} (hN0 : 0 ≤ N)
    (hb : 0 < normSq ((1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)))
    (hXi : XiS c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ N * (2 / (n : ℝ)) / n)
    (hXi4 : Xi4 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ a * (2 / (n : ℝ)) / n)
    (hXi8 : Xi8 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ a * (2 / (n : ℝ)) / n)
    (heb : 2 / (mA n : ℝ) * normSq ((1 / rhoC c.1.2 (D.tau0 c)) •
      bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)) ≤ 2 / (n : ℝ) * eb)
    (hxi : 2 / (mA n : ℝ) * normSq (hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) -
      (1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)) ≤
        xi * (2 / (n : ℝ)) / n)
    (hN2 : N2 2 c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) ≤ N22)
    (he1 : 0 ≤ e1) (he1' : eb ≤ e1 ^ 2) (he2 : 0 ≤ e2) (he2' : xi / (n : ℝ) ≤ e2 ^ 2)
    (hq : 2 * N / n ≤ q)
    (hsd : 0 < sd) (hs : sd < s) (hs2 : s ^ 2 ≤ 1 - N22 * (2 + N22) - (e1 + e2) ^ 2 - q)
    (hsum : (N + xi) / sd ^ 2 + (1609 / 100 * a) ^ 4 / ((n : ℝ) ^ 3 * (s - sd) ^ 8) ≤ cf)
    (w : Fin (mA n) → ℝ) :
    ∫ ξ, (∑ j, eDir (D.bA c.1 c.2.1.1) (hStand D c ξ) j * w j) ^ 2 ∂stdGauss (Fin n) ≤
      cf / n * ∑ j, w j ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hn6 : 6 ≤ n := by omega
  have hcov := cov_at_of_XiS hn6 D c hτ hXi
  have hcen : CENTRE_at D c xi := by
    unfold CENTRE_at
    rw [hD c, muStand_eq]
    exact hxi
  have hmass : MASS_at D c (sd ^ 2) ((1609 / 100 * a) ^ 4 / ((n : ℝ) ^ 3 * (s - sd) ^ 8)) := by
    unfold MASS_at
    rw [hD c]
    exact mass_bound8 hn c.2.1.1.1 c.2.1.1.2 c.1.2 hτ hb (N := N)
      (a := a) (eb := eb) (xi := xi) (N22 := N22) (e1 := e1) (e2 := e2)
      (sd := sd) (s := s) hXi hXi4 hXi8 heb hxi hN2 he1 he1' he2 he2' hsd.le hs
      (by
        have : -(2 * N / (n : ℝ)) ≥ -q := by linarith
        linarith)
  exact frameA_at hn1 D c (by positivity) hN0 hcov hcen hmass hsum w

/-- **(item 4) The Agent frame bound with the eighth moment**: on `EA16 D` and the events
`agentEv D (SXi n)`, `agentEv D (SXi8 n)`, in the World window: `FRAME_A_hyp D (7.75/n) E`,
every `n ≥ 75 000`. Constants: `N_cov = 0.679`, `ξ = 0.485`, `e_b ≤ 0.772`, cutoff
`d = 0.398²`, eighth moment of `σ`. -/
theorem frameA_sharp8 (hn : 75000 ≤ n) (D : Design n) (hD : AgentCentre154 D) {E : Set (Ret n)}
    (hWin : WINDOW_hyp D E) (hE : E ⊆ EA16 D) (hE' : E ⊆ agentEv D (SXi n))
    (hE8 : E ⊆ agentEv D (SXi8 n)) : FRAME_A_hyp D (775 / 100 / n) E := by
  intro c hc w
  obtain ⟨hτ, hθ0, hθ1⟩ := hWin c hc
  have hG : (c.2.1.1.1, c.2.1.1.2) ∈ GoodC16 n n c.1.2 (D.tau0 c) := hE hc hτ
  have hS : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi n := hE' hc hτ
  have hS8 : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SXi8 n := hE8 hc hτ
  have hn16 : 16384 ≤ n := by omega
  have hnR : (75000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hXi := XiS_noncentral hn16 hτ hθ0 hθ1 hS
  have heb := eb16 hn16 hτ hθ0 hθ1 hG
  have hinv : ∀ a : ℝ, 0 ≤ a → a / (n : ℝ) ≤ a / 75000 := fun a ha =>
    div_le_div_of_nonneg_left ha (by norm_num) hnR
  refine frameA_point8 hn16 D hD c hτ hθ0 hθ1 hG (mem_SXi8 hS8) (N := 679 / 1000)
    (eb := 772 / 1000) (e1 := 8787 / 10000) (e2 := 255 / 100000)
    (N22 := 18334 / 1000 / 75000) (q := 2 * (679 / 1000) / 75000) (sd := 398 / 1000)
    (s := 4721 / 10000) (by norm_num) hXi heb (by norm_num) (by norm_num)
    (by norm_num) ((hinv _ (by norm_num)).trans (by norm_num)) (hinv _ (by norm_num))
    (hinv _ (by norm_num)) (by norm_num) (by norm_num) (by norm_num) ?_ w
  have h1 : (1609 / 100 * (11911 / 10000 : ℝ)) ^ 4 /
      ((n : ℝ) ^ 3 * (4721 / 10000 - 398 / 1000) ^ 8) ≤
      (1609 / 100 * (11911 / 10000 : ℝ)) ^ 4 / (75000 ^ 3 * (4721 / 10000 - 398 / 1000) ^ 8) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num)
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by norm_num) hnR 3) (by norm_num))
  refine (add_le_add le_rfl h1).trans ?_
  norm_num

/-- **(items 3 and 4) The conditional classifier theorem WITHOUT the Agent frame hypothesis,
every `n ≥ 75 000`.** As `classifier_agentframe_lib`, with the Agent frame bound `7.75/n` PROVED
on three Agent events of total charge at most `0.00025`. -/
theorem classifier_agentframe_sharp8 (hn : 75000 ≤ n) (D : Design n) (hD : AgentCentre154 D)
    (hτ : TauWorld D) (t : ℝ) {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra + 25 / 100000 ≤ 63 / 10 ^ 4)
    (hWin : WINDOW_hyp D (goodSet H E₁ (HbarW D) hWL))
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have hn16 : 16384 ≤ n := by omega
  have hnR : (75000 : ℝ) ≤ n := by exact_mod_cast hn
  have hEv1 := events_with_EA16 hn16 D hτ hEv
  have hEv2 := events_with_agent D hτ (measurableSet_SXi n) (by norm_num) (SXi_charge hn16) hEv1
  have hEv3 := events_with_agent D hτ (measurableSet_SXi8 n) (by norm_num) (SXi8_charge hn16) hEv2
  have hsub1 := goodSet_EA16_subset D H E₁ (HbarW D) hWL
  have hsub2 := goodSet_inter_subset H (E₁ ∩ EA16 D) (agentEv D (SXi n)) (HbarW D) hWL
  have hsub3 := goodSet_inter_subset H ((E₁ ∩ EA16 D) ∩ agentEv D (SXi n)) (agentEv D (SXi8 n))
    (HbarW D) hWL
  have hsub := (hsub3.trans hsub2).trans hsub1
  have hFA : FRAME_A_hyp D (775 / 100 / n)
      (goodSet H (((E₁ ∩ EA16 D) ∩ agentEv D (SXi n)) ∩ agentEv D (SXi8 n)) (HbarW D) hWL) :=
    frameA_sharp8 hn D hD (window_mono hsub hWin)
      (fun c hc => goodSet_EA16_mem D c (hsub2 (hsub3 hc)))
      (fun c hc => goodSet_inter_mem (hsub3 hc)) (fun c hc => goodSet_inter_mem hc)
  exact classifier_networks_frameconst_success hn16 (cf := 775 / 100) (by unfold cfL; norm_num)
    (by unfold cfL; linarith) D t hEv3 (by linarith) (frameW_mono hsub hFW) hFA
    (repla_mono hsub hRA)

/-- The three charges of the ledger of the paper and the Agent charge `0.00025` fit:
`0.001900001 + v_W/h_W² + 0.001104285235085 + 0.00025 ≤ 0.0063`. -/
lemma ledger_charges_fit : δhidL + vWL / hWL ^ 2 + δextraL + 25 / 100000 ≤ 63 / 10 ^ 4 := by
  unfold δhidL vWL hWL δextraL
  norm_num

/-- **The paper's design and the paper's World charges, every `n ≥ 75 000`.** For
`paperDesign n fT wT` (the centres and `τ₀` of the paper's program; any measurable stored
tables): IF the World events have the charges of the ledger, and on the good set the World
window, the World frame bound and the Agent replacement hold, THEN the program succeeds with
probability at least `99/100`. No Agent frame hypothesis. -/
theorem classifier_paper_agentframe (hn : 75000 ≤ n) (fT wT : Ret n → ℕ → ℝ)
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
  classifier_agentframe_sharp8 hn _ (paperDesign_agentCentre fT wT hf hw)
    (paperDesign_tauWorld fT wT hf hw) t hEv ledger_charges_fit hWin hFW hRA

end BstLean.Part160

open BstLean.Part160 in
#print axioms frameA_point
open BstLean.Part160 in
#print axioms frameA_lib
open BstLean.Part160 in
#print axioms frameA_sharp
open BstLean.Part160 in
#print axioms classifier_agentframe_lib
open BstLean.Part160 in
#print axioms classifier_agentframe_sharp
open BstLean.Part160 in
#print axioms mass_bound8
open BstLean.Part160 in
#print axioms frameA_sharp8
open BstLean.Part160 in
#print axioms classifier_agentframe_sharp8
open BstLean.Part160 in
#print axioms classifier_paper_agentframe
open BstLean.Part160 in
#print axioms frameA_point8g
