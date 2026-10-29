import BstLean.Part161Fl
import BstLean.Part159All

/-!
# Part 161: the classifier theorem of Part 159 with `REPLA_mix_hyp` replaced by the named
fluctuation and bias hypotheses

Role: `delegations/statements/p161-spec.md`, item 2. Do not use `sorry`, `native_decide` or
`axiom`.

* `window_paper`: the World window `WINDOW` holds on `HP n ∩ E_{θ−} ∩ E_{θ+}` for the paper's
  design (from `world_window_up` of Part 159).
* **`classifier_paper_agent_fluct`**: Part 159's `classifier_paper_agent` with the hypothesis
  `REPLA_mix_hyp` replaced by: `E₁ ⊆ E_{θ−} ∩ E_{θ+}` and, on the good set, split data with
  `FLUCT_chi_hyp … 0.002159` and `BIAS_hyp … 0.004295`. It is still CONDITIONAL
  (`FRAME_A_hyp`, the charge of `E₁`, `FLUCT_chi_hyp`, `BIAS_hyp`).
-/

namespace BstLean.Part161

open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part134
open BstLean.Part156 BstLean.Part157 BstLean.Part158 BstLean.Part159

variable {n : ℕ}

/-- **The World window for the paper's design** on `HP n ∩ E_{θ−} ∩ E_{θ+}` (`n ≥ 13 225`). -/
theorem window_paper (hn : 13225 ≤ n) (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) {c : Ret n}
    (hc : c ∈ HP n) (hm : c ∈ Ethm (paperDesign n fT wT hf hw).toCentres)
    (hp : c ∈ Ethp (paperDesign n fT wT hf hw).toCentres) :
    WINDOW (paperDesign n fT wT hf hw) c := by
  obtain ⟨-, hc2, hτ, -, -, h1, h2⟩ := world_window_up hn (paperDesign n fT wT hf hw) rfl
    (fun _ => rfl) hc hm hp
  have hne : c.1.2 ≠ 0 := by
    intro h0; rw [h0] at hc2; simp [normSq] at hc2
  set D := paperDesign n fT wT hf hw
  have hpos : 0 < normSq c.1.2 + n * D.tau0 c ^ 2 := by positivity
  unfold thetaIn at h1 h2
  refine ⟨hne, hτ, ?_, ?_⟩
  · rw [le_div_iff₀ hpos] at h1; linarith
  · rw [div_le_iff₀ hpos] at h2; linarith

/-- **The classifier theorem for the paper's design with the Agent replacement reduced to the
named fluctuation and bias hypotheses (every `n ≥ 16 384`).** As `classifier_paper_agent` of
Part 159, with `REPLA_mix_hyp` replaced by: the retained-data event `E₁` lies inside the angle
events `E_{θ−} ∩ E_{θ+}` (their charge is then part of `δ_extra`), and on the good set there
are split data `d` and window constants with `FLUCT_chi_hyp D c d ε₀ δ₀ s_low 0.002159` and
`BIAS_hyp D c d 0.004295`. -/
theorem classifier_paper_agent_fluct (hn : 16384 ≤ n)
    (fT wT : Ret n → ℕ → ℝ) (hf : ∀ g, Measurable (fun c => fT c g))
    (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ) {E₁ : Set (Ret n)}
    (hE₁ : MeasurableSet E₁)
    (hextra : (retDist (paperCentres n)).real (HP n ∩ E₁ᶜ) ≤ δextraL)
    (hEθ : E₁ ⊆ Ethm (paperCentres n) ∩ Ethp (paperCentres n))
    (hFA : FRAME_A_hyp (paperDesign n fT wT hf hw) (cfL / n)
      (goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hWL))
    (hFl : ∀ c ∈ goodSet (HP n) E₁ (HbarW (paperDesign n fT wT hf hw)) hWL,
      ∃ (d : SplitData n) (ε₀ δ₀ slow : ℝ),
        FLUCT_chi_hyp (paperDesign n fT wT hf hw) c d ε₀ δ₀ slow (2159 / 10 ^ 6) ∧
        BIAS_hyp (paperDesign n fT wT hf hw) c d (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} := by
  refine classifier_paper_agent hn fT wT hf hw t hE₁ hextra hFA ?_
  refine repla_of_hyps_chi hn _ t (fun c hc => ?_) hFl
  have hcH : c ∈ HP n := hc.1.1
  have hcE : c ∈ E₁ := hc.2
  exact window_paper (by omega) fT wT hf hw hcH (hEθ hcE).1 (hEθ hcE).2

end BstLean.Part161

open BstLean.Part161 in
#print axioms window_paper
open BstLean.Part161 in
#print axioms classifier_paper_agent_fluct
