import BstLean.Part151VAprob2
import BstLean.Part151Inputs

/-!
# Part 151, Proposition VA (b), stage (d): the hypothesis `H2` from hypotheses on the `A` stage

Role: `delegations/statements/p151-spec.md`, items 3 and 4. Paper source:
`proofs/option-n/theorem5-13-events-final.tex`, Proposition VA (b) and the event table.

* `EVA`: the event `E`: the complement of the union of the eight bad events of
  `Part151VAprob`.
* **`H2_of_Astage`**: `H2 n k bh univ E c_V p₂` with `c_V = vbar·n²/4` and
  `p₂ = p12 + p3 + 2e^{−u_F²/2} + 3·chF n δ + 3e^{−L_c}`. The only hypotheses are on the `A`
  stage: a set `X12` of values of `(W, (A₁, A₂))` on which the centre is not `0` and
  `‖C_r‖_op ≤ Mr`, and a set `X3` of values of `(W, A)` on which `𝔇_c ≤ D̄` and
  `|c_A|² + nσ_p² ≤ Ē`.
* **`theorem5_frame`**: with `condLeanSamp151`: a success bound for the estimator
  `gSampH bh k` whose only hypotheses are `X12`, `X3`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part131
open BstLean.Part136 (HidParam hidGauss)
open BstLean.Part139 (gamK)
open BstLean.Part149 (thA tauOutOf)
open BstLean.Part150 (CMap gSampH)

section fin

variable {k n : ℕ} {bh : CMap n}

/-- **The event `E` of Proposition VA**: none of the eight bad events holds. -/
def EVA (k : ℕ) (bh : CMap n) (X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n)))
    (X3 : Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n)) (δ uF Mr Lc : ℝ) :
    Set (Fix k n) :=
  (B12 k X12 ∪ B3 k X3 ∪ BON k uF ∪ BTm k bh X12 δ ∪ BFE k bh δ ∪ BJU k bh δ ∪
    Bs k bh uF Lc ∪ BU k bh X12 uF Mr Lc)ᶜ

lemma EVA_meas (hbh : Measurable bh)
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    {X3 : Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n)} (h3 : MeasurableSet X3)
    (δ uF Mr Lc : ℝ) : MeasurableSet (EVA k bh X12 X3 δ uF Mr Lc) := by
  have h := (((((((B12_meas (k := k) h12).union (B3_meas h3)).union (BON_meas uF)).union
    (BTm_meas hbh h12 δ)).union (BFE_meas hbh δ)).union (BJU_meas hbh δ)).union
    (Bs_meas hbh uF Lc)).union (BU_meas hbh h12 uF Mr Lc)
  exact h.compl

/-- On the event `E` the conditions `GoodVA` hold. -/
lemma good_of_EVA {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))}
    (hb : ∀ x ∈ X12, bh x ≠ 0) {Mr : ℝ}
    (hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 → CrOK bh W A₁ A₂ Mr)
    {X3 : Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n)} {Dbar Ebar : ℝ}
    (hD : ∀ W A, (W, A) ∈ X3 → Dc bh W A ≤ Dbar)
    (hE : ∀ W A, (W, A) ∈ X3 → normSq (cAv bh W A) + n * sigP bh W A ^ 2 ≤ Ebar)
    {δ uF Lc : ℝ} {ω : Fix k n} (hω : ω ∈ EVA k bh X12 X3 δ uF Mr Lc) :
    GoodVA bh k δ Dbar Ebar (LFc n uF) Mr Lc ω.1.1 ω.1.2.1 ω.1.2.2 ω.2 := by
  have h12 : (ω.1.1, thA ω.1.2.1) ∈ X12 := by
    by_contra h
    exact hω (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))))
  have h3 : (ω.1.1, ω.1.2.1) ∈ X3 := by
    by_contra h
    exact hω (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h)))))))
  have hON : ω.1.2.2 ∈ EON n (mF n) uF := by
    by_contra h
    exact hω (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr h))))))
  refine ⟨hb _ h12, hCr _ _ _ h12, hD _ _ h3, hE _ _ h3, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    exact hω (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨h12, h⟩)))))
  · intro h
    exact hω (Or.inl (Or.inl (Or.inl (Or.inr h))))
  · intro h
    exact hω (Or.inl (Or.inl (Or.inr h)))
  · intro h
    exact hω (Or.inl (Or.inr ⟨hON, h⟩))
  · by_contra h
    exact hω (Or.inr ⟨h12, hON, h⟩)

lemma vbar_pos (n k : ℕ) {δ Dbar Ebar LF Mr Lc : ℝ} (hδ : 0 < δ) (hMr0 : 0 < Mr) :
    0 < vbar n k δ Dbar Ebar LF Mr Lc := by
  have h1 : 0 < √(Mr * (2 * (1 + δ) * (1 + δ))) := Real.sqrt_pos.mpr (by positivity)
  have hu := uU_nonneg n LF Mr Lc
  have hs : 0 ≤ tauS n k δ Ebar LF Lc := by
    unfold tauS
    exact add_nonneg (Real.sqrt_nonneg _) (uS_nonneg _ _ _ _)
  have hm : 0 ≤ tauM n δ Dbar := Real.sqrt_nonneg _
  have hU : 0 < tauU n δ LF Mr Lc := by unfold tauU; linarith
  unfold vbar
  positivity

/-- **Proposition VA (b): the hypothesis `H2` from hypotheses on the `A` stage only.**
`X12` is a measurable set of values of `(W, (A₁, A₂))` with `Pr(X12ᶜ) ≤ p12`, on which the
centre `b` is not `0` and `‖C_r‖_op ≤ Mr`; `X3` is a measurable set of values of `(W, A)` with
`Pr(X3ᶜ) ≤ p3`, on which `𝔇_c ≤ D̄` and `|c_A|² + nσ_p² ≤ Ē`. Then, for `δ > 0`, `u_F ≥ 0`,
`L_c ≥ 0`: `H2` holds for the event `EVA`, with `c_V = vbar·n²/4` and
`p₂ = p12 + p3 + 2e^{−u_F²/2} + 3·chF n δ + 3e^{−L_c}`. -/
theorem H2_of_Astage (hn : 1 ≤ n) (hk : 1 ≤ k) (hbh : Measurable bh)
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    {p12 : ℝ}
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ p12)
    (hb : ∀ x ∈ X12, bh x ≠ 0) {Mr : ℝ} (hMr0 : 0 < Mr)
    (hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 → CrOK bh W A₁ A₂ Mr)
    {X3 : Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n)} (h3 : MeasurableSet X3)
    {p3 : ℝ} (hp3 : ((mlpGauss (2 * n) (mW n) n).prod (mlpGauss n (mA n) n)).real X3ᶜ ≤ p3)
    {Dbar Ebar : ℝ} (hD : ∀ W A, (W, A) ∈ X3 → Dc bh W A ≤ Dbar)
    (hE : ∀ W A, (W, A) ∈ X3 → normSq (cAv bh W A) + n * sigP bh W A ^ 2 ≤ Ebar)
    {δ uF Lc : ℝ} (hδ : 0 < δ) (huF : 0 ≤ uF) (hLc : 0 ≤ Lc) :
    H2 n k bh univ (EVA k bh X12 X3 δ uF Mr Lc)
      (vbar n k δ Dbar Ebar (LFc n uF) Mr Lc * (n : ℝ) ^ 2 / 4)
      (p12 + p3 + 2 * Real.exp (-uF ^ 2 / 2) + 3 * chF n δ + 3 * Real.exp (-Lc)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  refine ⟨EVA_meas hbh h12 h3 δ uF Mr Lc, ?_, ?_, fun _ _ => mem_univ _⟩
  · -- the probability
    have e : (EVA k bh X12 X3 δ uF Mr Lc)ᶜ =
        B12 k X12 ∪ B3 k X3 ∪ BON k uF ∪ BTm k bh X12 δ ∪ BFE k bh δ ∪ BJU k bh δ ∪
          Bs k bh uF Lc ∪ BU k bh X12 uF Mr Lc := compl_compl _
    rw [e]
    have q1 := prob_X12 (k := k) h12 hp12
    have q2 := prob_X3 (k := k) h3 hp3
    have q3 := prob_ON (k := k) hn huF
    have q4 := prob_Tm (k := k) hn hbh h12 hb hδ
    have q5 := prob_FE (k := k) hn hbh hδ
    have q6 := prob_JU (k := k) hn hbh hδ
    have q7 := prob_s hn hk hbh huF hLc
    have q8 := prob_U (k := k) hn hbh h12 hb hMr0 hCr huF hLc
    have u1 := measureReal_union_le (μ := fixP k n)
      (B12 k X12 ∪ B3 k X3 ∪ BON k uF ∪ BTm k bh X12 δ ∪ BFE k bh δ ∪ BJU k bh δ ∪
        Bs k bh uF Lc) (BU k bh X12 uF Mr Lc)
    have u2 := measureReal_union_le (μ := fixP k n)
      (B12 k X12 ∪ B3 k X3 ∪ BON k uF ∪ BTm k bh X12 δ ∪ BFE k bh δ ∪ BJU k bh δ)
      (Bs k bh uF Lc)
    have u3 := measureReal_union_le (μ := fixP k n)
      (B12 k X12 ∪ B3 k X3 ∪ BON k uF ∪ BTm k bh X12 δ ∪ BFE k bh δ) (BJU k bh δ)
    have u4 := measureReal_union_le (μ := fixP k n)
      (B12 k X12 ∪ B3 k X3 ∪ BON k uF ∪ BTm k bh X12 δ) (BFE k bh δ)
    have u5 := measureReal_union_le (μ := fixP k n)
      (B12 k X12 ∪ B3 k X3 ∪ BON k uF) (BTm k bh X12 δ)
    have u6 := measureReal_union_le (μ := fixP k n) (B12 k X12 ∪ B3 k X3) (BON k uF)
    have u7 := measureReal_union_le (μ := fixP k n) (B12 k X12) (B3 k X3)
    linarith
  · -- the variance bound
    intro ω hω
    have hg := good_of_EVA (Dbar := Dbar) (Ebar := Ebar) hb hCr hD hE hω
    have hv : vHat bh k ω ≤ vbar n k δ Dbar Ebar (LFc n uF) Mr Lc :=
      vHat_le_of_good hn hk hδ hMr0.le hg
    refine hv.trans (le_of_eq ?_)
    field_simp

/-- **The frame of Theorem 5 with hypotheses on the `A` stage only.** For every `n ≥ 4096`,
`k ≥ 1`, every measurable centre map `bh`, sets `X12`, `X3` as in `H2_of_Astage`, and
`0 < ε_W < 1/2`, `0 < θ < 1`: the estimator `gSampH bh k` (the mean of `k` values
`F(A₃b + σ_pη_j)`; no forward pass of `A`) satisfies
`Pr(|g − B| ≤ sd/2) ≥ 1 − (1/n + w₀/(ε_W²θq₀)/n + p₂ + 2e₀²/((1 − θ)q₀)²/n
+ 2Φ̄((1/2 − ε_W)·√(n·θ·q₀/c_V)))`, with `c_V = vbar·n²/4` and
`p₂ = p12 + p3 + 2e^{−u_F²/2} + 3·chF n δ + 3e^{−L_c}`. -/
theorem theorem5_frame (hn : 4096 ≤ n) (hk : 1 ≤ k) (hbh : Measurable bh)
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    {p12 : ℝ}
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ p12)
    (hb : ∀ x ∈ X12, bh x ≠ 0) {Mr : ℝ} (hMr0 : 0 < Mr)
    (hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 → CrOK bh W A₁ A₂ Mr)
    {X3 : Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n)} (h3 : MeasurableSet X3)
    {p3 : ℝ} (hp3 : ((mlpGauss (2 * n) (mW n) n).prod (mlpGauss n (mA n) n)).real X3ᶜ ≤ p3)
    {Dbar Ebar : ℝ} (hD : ∀ W A, (W, A) ∈ X3 → Dc bh W A ≤ Dbar)
    (hE : ∀ W A, (W, A) ∈ X3 → normSq (cAv bh W A) + n * sigP bh W A ^ 2 ≤ Ebar)
    {δ uF Lc : ℝ} (hδ : 0 < δ) (huF : 0 ≤ uF) (hLc : 0 ≤ Lc) {εW θ : ℝ} (hεW0 : 0 < εW)
    (hεW : εW < 1 / 2) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    1 - (1 / (n : ℝ) + 4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n +
        (p12 + p3 + 2 * Real.exp (-uF ^ 2 / 2) + 3 * chF n δ + 3 * Real.exp (-Lc)) +
        2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - εW) * √(n * (θ * (222757 / 1000000)) /
          (vbar n k δ Dbar Ebar (LFc n uF) Mr Lc * (n : ℝ) ^ 2 / 4)))) ≤
      (jointP k n).real {p | |gSampH bh k p.1.1 p.1.2.1 p.1.2.2 p.2 -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have h2 := H2_of_Astage hn1 hk hbh h12 hp12 hb hMr0 hCr h3 hp3 hD hE hδ huF hLc
  have hcV : 0 < vbar n k δ Dbar Ebar (LFc n uF) Mr Lc * (n : ℝ) ^ 2 / 4 := by
    have := vbar_pos n k (Dbar := Dbar) (Ebar := Ebar) (LF := LFc n uF) (Lc := Lc) hδ hMr0
    positivity
  exact condLeanSamp151 hn hbh h2 hcV hεW0 hεW hθ0 hθ1

end fin

end BstLean.Part151
