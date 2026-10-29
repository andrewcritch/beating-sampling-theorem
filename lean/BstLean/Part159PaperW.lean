import BstLean.Part159PaperF

/-!
# Part 159 (file `PaperW`): the retained World window for the centre of the paper

Role: `delegations/statements/p159-spec.md`, item 3. Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `theorem7-02-world.tex`, Lemma `t7:p02:window`.

* `theta_window_paper`: for a design with the World centre `bWp` and the scalar `tau0p` of the
  paper, `n ≥ 16 384`, IF `ConstC n` and `ConstK n`: on `HP n`: `τ₀ > 0`, `τ₀² = t_W|b_W|²·w₀`
  with `w₀ = t_W|b_W|²·c − 1`, `0.994 ≤ w₀ ≤ 1.057` (the paper: `0.977865 ≤ w₀ ≤ 1.065383`); on
  `HP n ∩ E_{θ−}`: `θ_in ≥ 0.465`; on `HP n ∩ E_{θ+}`: `θ_in ≤ 0.528` (the paper:
  `0.461033 < θ_in < 0.530036`).
* `classifier_paper_conditional_agent_window`: the conditional theorem for `paperDesign` with
  the two angle events proved.
-/

namespace BstLean.Part159

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss mW_ge_million)
open BstLean.Part156 BstLean.Part157 BstLean.Part158

variable {n : ℕ}

/-- **The retained World window for the centre and the scalar of the paper (every
`n ≥ 16 384`)**, IF `ConstC n` and `ConstK n`. -/
theorem theta_window_paper (hn : 16384 ≤ n) (hC : ConstC n) (hK : ConstK n) (D : Design n)
    (hD : D.bW = bWp) (hτ : ∀ c : Ret n, D.tau0 c = tau0p c.1.1) {c : Ret n} (hc : c ∈ HP n) :
    0 < D.tau0 c ∧
      D.tau0 c ^ 2 = 2 / (mW n : ℝ) * normSq (D.bW c.1.1) *
        (2 / (mW n : ℝ) * normSq (D.bW c.1.1) * ccP n c.1.1 - 1) ∧
      994 / 1000 ≤ 2 / (mW n : ℝ) * normSq (D.bW c.1.1) * ccP n c.1.1 - 1 ∧
      2 / (mW n : ℝ) * normSq (D.bW c.1.1) * ccP n c.1.1 - 1 ≤ 1057 / 1000 ∧
      (c ∈ Ethm D.toCentres → 465 / 1000 ≤ thetaIn D c) ∧
      (c ∈ Ethp D.toCentres → thetaIn D c ≤ 528 / 1000) := by
  have hθ : c.1.1 ∈ GPap n := hc
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  obtain ⟨-, hA1, hA2⟩ := pap_window hn hC hK hθ
  obtain ⟨t2, t1⟩ := pap_tau hn hC hK hθ
  rw [hD, hτ]
  set B := 2 / (mW n : ℝ) * normSq (bWp c.1.1) with hB
  set w0 := B * ccP n c.1.1 - 1 with hw0
  have t3 : 994 / 1000 ≤ w0 := by linarith
  have t4 : w0 ≤ 1057 / 1000 := by linarith
  have hBnn : 0 ≤ B := mul_nonneg (by positivity) (normSq_nonneg _)
  have hBpos : 0 < B := by
    rcases hBnn.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at hA1; norm_num at hA1
    · exact h0
  have hnB : 0 < (n : ℝ) * B := by positivity
  refine ⟨t1, t2, t3, t4, ?_, ?_⟩
  · intro hm
    have h1 : normSq c.1.2 ≤ cUp * n * B := by
      have : normSq c.1.2 ≤ cUp * n * (2 / (mW n : ℝ) * normSq (D.bW c.1.1)) := hm
      rwa [hD] at this
    have hcu : cUp ≤ 1143166 / 1000000 := by
      unfold cUp
      have := sqrt45_bounds.2
      linarith
    unfold thetaIn
    rw [hτ, t2, le_div_iff₀ (by
      have : 0 ≤ normSq c.1.2 := normSq_nonneg _
      have : 0 < (n : ℝ) * (B * w0) := by positivity
      linarith)]
    have h2 : normSq c.1.2 ≤ 1143166 / 1000000 * ((n : ℝ) * B) := by
      have := mul_le_mul_of_nonneg_right hcu hnB.le
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left t3 hnB.le]
  · intro hp
    have h1 : (1 - 2 * √(12 / (n : ℝ))) * n * B ≤ normSq c.1.2 := by
      have : (1 - 2 * √(12 / (n : ℝ))) * n * (2 / (mW n : ℝ) * normSq (D.bW c.1.1)) ≤
          normSq c.1.2 := hp
      rwa [hD] at this
    have hcl : (945872 / 1000000 : ℝ) ≤ 1 - 2 * √(12 / (n : ℝ)) := by
      have := sqrt12n_le hn
      linarith
    unfold thetaIn
    rw [hτ, t2, div_le_iff₀ (by
      have : 0 ≤ normSq c.1.2 := normSq_nonneg _
      have : 0 < (n : ℝ) * (B * w0) := by positivity
      linarith)]
    have h2 : 945872 / 1000000 * ((n : ℝ) * B) ≤ normSq c.1.2 := by
      have := mul_le_mul_of_nonneg_right hcl hnB.le
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left t4 hnB.le]

/-- **The conditional classifier theorem for the design of the paper's program, with the World
window (every `n ≥ 16 384`).** As `classifier_paper_conditional_agent`, with the two angle events
`E_{θ−}`, `E_{θ+}` and their charges PROVED: the Agent hypotheses are needed only on
`HP n ∩ {H̄_W ≤ h_W} ∩ (E_{θ−} ∩ E_{θ+} ∩ E_A)` (where `theta_window_paper` gives
`0.465 ≤ θ_in ≤ 0.528`), and the event `E_A` needs
`6.146·10⁻⁶ + Pr(HP n ∩ E_{θ−} ∩ E_{θ+} ∩ E_Aᶜ) ≤ δ_extra`. -/
theorem classifier_paper_conditional_agent_window (hn : 16384 ≤ n) (hC : ConstC n)
    (hK : ConstK n) (fT wT : Ret n → ℕ → ℝ) (hf : ∀ g, Measurable (fun c => fT c g))
    (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ) {EA : Set (Ret n)}
    (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real
      (HP n ∩ Ethm (paperCentres n) ∩ Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hsum : δAng + δA ≤ δextraL)
    (hFA : FRAME_A_hyp (paperDesign n fT wT hf hw) (cfL / n)
      (goodSet (HP n) (Ethm (paperCentres n) ∩ Ethp (paperCentres n) ∩ EA)
        (HbarW (paperDesign n fT wT hf hw)) hWL))
    (hRA : REPLA_mix_hyp (paperDesign n fT wT hf hw) t hAL
      (goodSet (HP n) (Ethm (paperCentres n) ∩ Ethp (paperCentres n) ∩ EA)
        (HbarW (paperDesign n fT wT hf hw)) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_conditional_agent hn hC hK fT wT hf hw t
    (((measurableSet_Ethm (paperCentres n)).inter (measurableSet_Ethp (paperCentres n))).inter
      hEA)
    (((extra_angle hn (paperCentres n) (HP n) EA).trans (by linarith)).trans hsum) hFA hRA

end BstLean.Part159

open BstLean.Part159 in
#print axioms theta_window_paper
open BstLean.Part159 in
#print axioms classifier_paper_conditional_agent_window
