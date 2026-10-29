import BstLean.Part151G
import BstLean.Part151VA2

/-!
# Part 151: the frame of Theorem 5 for the program, with the Gaussian step for the `W` term

`theorem5_frameProgG`: `theorem5_frameProg` (`Part151VA2`) with the `W` term multiplied by the
constant `κ` of the Gaussian tail (`condLeanProg151G` of `Part151G`). This file imports
Part 152 through `Part151VA2`; `Part151G` and `Part151G2` do not.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss hbar)
open BstLean.Part138 (cheapIn)
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142 BstLean.Part143 BstLean.Part145
open BstLean.Part149 BstLean.Part150

variable {k n : ℕ}

/-- **The frame of Theorem 5 for the program `fullProg150 k n J`, hypotheses on
`(W, A₁, A₂)` only, with the `W` term multiplied by `κ`.** -/
theorem theorem5_frameProgG {κ : ℝ} (hκ : ∀ a : ℝ, 0 < a → 2 * PhiBar a ≤ κ / a ^ 2)
    (hn : 4096 ≤ n) (hk : 1 ≤ k) {J : ℕ}
    {X12 : Set (MlpParam (2 * n) (mW n) n × HidParam n (mA n))} (h12 : MeasurableSet X12)
    {p12 : ℝ}
    (hp12 : ((mlpGauss (2 * n) (mW n) n).prod (hidGauss n (mA n))).real X12ᶜ ≤ p12)
    (hb : ∀ x ∈ X12, bTW J x ≠ 0)
    (he : ∀ x ∈ X12, 2 / (mA n : ℝ) * normSq (bTW J x) ≤ 2 / (n : ℝ))
    (hτ : ∀ x ∈ X12, 0 < tauWA x.1) {Mr : ℝ} (hMr0 : 0 < Mr)
    (hCr : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 → CrOK (bTW J) W A₁ A₂ Mr)
    {Dvbar : ℝ}
    (hDv : ∀ W A₁ A₂, (W, ((A₁, A₂) : HidParam n (mA n))) ∈ X12 →
      Dv (bTW J) W A₁ A₂ ≤ Dvbar)
    {δ uF Lc : ℝ} (hδ : 0 < δ) (huF : 0 ≤ uF) (hLc : 0 ≤ Lc) {εW θ : ℝ} (hεW0 : 0 < εW)
    (hεW : εW < 1 / 2) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    1 - (1 / (n : ℝ) + κ * (4849 / 20000 / (εW ^ 2 * (θ * (222757 / 1000000))) / n) +
        (p12 + Real.exp (-Lc) + 2 * Real.exp (-uF ^ 2 / 2) + 3 * chF n δ +
          3 * Real.exp (-Lc)) +
        2 * (78728 / 100000) ^ 2 / ((1 - θ) * (222757 / 1000000)) ^ 2 / n +
        2 * PhiBar ((1 / 2 - εW) * √(n * (θ * (222757 / 1000000)) /
          (vbar n k δ ((1 + deltaC n Lc) * Dvbar) (2 * (1 + deltaC n Lc)) (LFc n uF) Mr Lc *
            (n : ℝ) ^ 2 / 4)))) ≤
      (jointP k n).real {p | |(fullProg150 k n J).eval (fullVal p.1.1 p.1.2.1 p.1.2.2 p.2) () -
        Bn p.1.1 p.1.2.1 p.1.2.2| ≤ sdn p.1.1 p.1.2.1 p.1.2.2 / 2} := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have h2 := H2_of_A12 (k := k) hn1 hk (measurable_bTW J) h12 hp12 hb he hMr0 hCr hDv hδ huF hLc
  have hcV := (vbar_pos' n k (Dbar := (1 + deltaC n Lc) * Dvbar)
    (Ebar := 2 * (1 + deltaC n Lc)) (LF := LFc n uF) (Lc := Lc) hδ hMr0).resolve_right hn0.ne'
  have hτE : ∀ ω ∈ EVA k (bTW J) X12 (X3c (bTW J) X12 Lc) δ uF Mr Lc, 0 < tauWA ω.1.1 := by
    intro ω hω
    have h12ω : (ω.1.1, thA ω.1.2.1) ∈ X12 := by
      by_contra h
      exact hω (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl h)))))))
    exact hτ (ω.1.1, thA ω.1.2.1) h12ω
  exact condLeanProg151G hκ hn h2 hτE hcV hεW0 hεW hθ0 hθ1

end BstLean.Part151
