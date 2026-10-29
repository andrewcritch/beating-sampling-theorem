import BstLean.Part163Comb

/-!
# Part 163 (file `Sane`): the repaired good set excludes the degenerate Agent weights

Do not use `sorry`, `native_decide` or `axiom`.

* `worldGood_agent_free`: the good set of Part 160's `classifier_paper_comb23`,
  `goodSet (HP n) (E_{θ−} ∩ E_{θ+}) (HbarW D) hWL`, is a condition on the World data only: with `c`
  it contains `(c.1, y)` for EVERY Agent and `F` data `y` (for example `A₂ = 0`).
* `mean_energy_Eframe`: on `goodSet H (E₁ ∩ Eframe D)` with the window, the mean `μ = E_ξ h(ξ)` of
  the last hidden Agent vector at the stand-in input has `t_A|μ|² ≥ 0.32·γ_A` (`t_A = 2/m_A`,
  `γ_A = 2/n`), so `μ ≠ 0` and `A₂ ≠ 0`.
* `repaired_excludes_A2_zero`: a retained value with `A₂ = 0` is never in the repaired good set
  `goodSet (HP n) (E_{θ−} ∩ E_{θ+} ∩ E_A ∩ Eframe D) (HbarW D) hWL` of `classifier_paper_free23`,
  for every `E_A`; and `comb23_set_has_A2_zero`: the old good set contains such a value as soon as
  it is not empty.
-/

namespace BstLean.Part163

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160

variable {n : ℕ}

/-- **The old good set is a condition on the World data only.** -/
theorem worldGood_agent_free (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {c : Ret n}
    (hc : c ∈ goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
      BstLean.Part159.Ethp (paperCentres n)) (HbarW (paperDesign n fT wT hf hw)) hWL)
    (y : ARet n × FPar n) :
    ((c.1, y) : Ret n) ∈ goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
      BstLean.Part159.Ethp (paperCentres n)) (HbarW (paperDesign n fT wT hf hw)) hWL :=
  hc

lemma normSq_le_two (u v : Fin k → ℝ) : normSq v ≤ 2 * normSq u + 2 * normSq (u - v) := by
  unfold normSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  simp only [Pi.sub_apply]
  nlinarith [sq_nonneg (2 * u i - v i)]

/-- **On the frame event the mean of the last hidden Agent vector is not small**:
`t_A|μ|² ≥ 0.32·γ_A` with `μ = muStand D c = E_ξ hStand D c ξ`. From `t_A|b|² ≥ 0.6425·γ_A`
(`eb16_lower`, events `GoodC16`, `SScU`) and `t_A|μ − b|² ≤ 0.485·γ_A/n` (`centre16`). -/
theorem mean_energy_Eframe (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D)
    {H E₁ : Set (Ret n)} (hWin : WINDOW_hyp D (goodSet H (E₁ ∩ Eframe D) (HbarW D) hWL))
    {c : Ret n} (hc : c ∈ goodSet H (E₁ ∩ Eframe D) (HbarW D) hWL) :
    2 / (n : ℝ) * (32 / 100) ≤ 2 / (mA n : ℝ) * normSq (muStand D c) := by
  obtain ⟨hτ, hθ0, hθ1⟩ := hWin c hc
  have hE := hc.2.2
  have hG : (c.2.1.1.1, c.2.1.1.2) ∈ BstLean.Part154.GoodC16 n n c.1.2 (D.tau0 c) :=
    hE.1.1.1.1.1.1 hτ
  have hU : ((c.1.2, D.tau0 c), (c.2.1.1.1, c.2.1.1.2)) ∈ SScU n := hE.1.2 hτ
  have hlo := eb16_lower hn hτ (le_trans (by norm_num) hθ0) (hθ1.trans (by norm_num)) hG hU
  obtain ⟨c1, -, -, -, -, -, -⟩ := centre16 hn hτ hθ0 hθ1 hG
  have hb : D.bA c.1 c.2.1.1 =
      (1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) := hD c
  have hmu : muStand D c = BstLean.Part153.hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c) := rfl
  set b := (1 / rhoC c.1.2 (D.tau0 c)) • bT n n c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)
  set μ := BstLean.Part153.hid2Mean_cr c.2.1.1.1 c.2.1.1.2 c.1.2 (D.tau0 c)
  have h2 := normSq_le_two μ b
  have hm0 : (0 : ℝ) < 2 / (mA n : ℝ) := by
    have : (0 : ℝ) < (mA n : ℝ) := by
      have : 0 < mA n := by unfold mA; positivity
      exact_mod_cast this
    positivity
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h3 : 2 / (mA n : ℝ) * normSq b ≤
      2 * (2 / (mA n : ℝ) * normSq μ) + 2 * (2 / (mA n : ℝ) * normSq (μ - b)) := by
    nlinarith
  have h4 : (485 / 1000 : ℝ) * (2 / (n : ℝ)) / n ≤ (485 / 1000) * (2 / (n : ℝ)) / 16384 :=
    div_le_div_of_nonneg_left (by positivity) (by norm_num) hnR
  rw [hmu]
  have h5 : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  nlinarith

/-- **On the frame event `A₂ ≠ 0` and the mean `μ` is not `0`.** -/
theorem A2_ne_zero_Eframe (hn : 16384 ≤ n) (D : Design n) (hD : AgentCentre154 D)
    {H E₁ : Set (Ret n)} (hWin : WINDOW_hyp D (goodSet H (E₁ ∩ Eframe D) (HbarW D) hWL))
    {c : Ret n} (hc : c ∈ goodSet H (E₁ ∩ Eframe D) (HbarW D) hWL) :
    muStand D c ≠ 0 ∧ c.2.1.1.2 ≠ 0 := by
  have h := mean_energy_Eframe hn D hD hWin hc
  have hn0 : (0 : ℝ) < n := by
    have : (16384 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hpos : (0 : ℝ) < 2 / (n : ℝ) * (32 / 100) := by positivity
  have hne : muStand D c ≠ 0 := by
    intro h0
    rw [h0] at h
    simp [normSq] at h
    linarith
  refine ⟨hne, fun hA => hne ?_⟩
  funext j
  show ∫ ξ, hid2 c.2.1.1.1 c.2.1.1.2 (sphPt (c.1.2 + D.tau0 c • ξ)) j ∂stdGauss (Fin n) = 0
  rw [hA]
  simp [hid2, reluV, relu]

/-- **The repaired good set of `classifier_paper_free23` contains no retained value with
`A₂ = 0`**, for every free Agent event `E_A` (`n ≥ 16 384`). -/
theorem repaired_excludes_A2_zero (hn : 16384 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    (EA : Set (Ret n)) {c : Ret n}
    (hc : c ∈ goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩ Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL) :
    c.2.1.1.2 ≠ 0 := by
  have hWin : WINDOW_hyp (paperDesign n fT wT hf hw)
      (goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
        BstLean.Part159.Ethp (paperCentres n) ∩ EA ∩ Eframe (paperDesign n fT wT hf hw))
        (HbarW (paperDesign n fT wT hf hw)) hWL) :=
    window_paper hn fT wT hf hw (fun c hc => ⟨hc.1.1, hc.2.1.1.1, hc.2.1.1.2⟩)
  exact (A2_ne_zero_Eframe hn _ (paperDesign_agentCentre fT wT hf hw) hWin hc).2

/-- **The old good set contains a retained value with `A₂ = 0`** as soon as it is not empty. -/
theorem comb23_set_has_A2_zero (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g))
    {c : Ret n}
    (hc : c ∈ goodSet (BstLean.Part159.HP n) (BstLean.Part159.Ethm (paperCentres n) ∩
      BstLean.Part159.Ethp (paperCentres n)) (HbarW (paperDesign n fT wT hf hw)) hWL) :
    ∃ c' : Ret n, c'.2.1.1.2 = 0 ∧ c' ∈ goodSet (BstLean.Part159.HP n)
      (BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n))
      (HbarW (paperDesign n fT wT hf hw)) hWL :=
  ⟨(c.1, ((c.2.1.1.1, 0), c.2.1.2), c.2.2), rfl, worldGood_agent_free fT wT hf hw hc _⟩

end BstLean.Part163

open BstLean.Part163 in
#print axioms worldGood_agent_free
open BstLean.Part163 in
#print axioms mean_energy_Eframe
open BstLean.Part163 in
#print axioms A2_ne_zero_Eframe
open BstLean.Part163 in
#print axioms repaired_excludes_A2_zero
open BstLean.Part163 in
#print axioms comb23_set_has_A2_zero
