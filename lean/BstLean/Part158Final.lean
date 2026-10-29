import BstLean.Part158Deriv
import BstLean.Part158Smooth
import BstLean.Part158Approx

/-!
# Part 158 (file `Final`): the Gaussian inequality (GP) and the classifier theorem without it

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-02-world.tex`, Lemma `t7:p02:GP` (for the maps `B_x G = G e(x)`).

* `gpSmooth`: (GP) for a finite measure, unit vectors and differentiable `f(x, ·)` with a bounded
  gradient.
* `gpMeas`: (GP) for a finite measure on `ℝ^N`, unit vectors and measurable `f` with
  `0 < a ≤ f ≤ b`.
* **`gaussGP`**: `BstLean.Part157.GaussGP`, the named hypothesis of Part 157. PROVED.
* `gaussFrameMGF`: the bound of the moment generating function (Corollary `t7:p02:MGF`).
* **`classifier_networks_conditional_frames`**: the headline of Part 157 with the hypothesis
  `GaussGP` removed. The other four hypotheses (`EVENTS_hyp`, `FRAME_W_hyp`, `FRAME_A_hyp`,
  `REPLA_mix_hyp`) remain: it is still a CONDITIONAL theorem.
-/

namespace BstLean.Part158

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part134 BstLean.Part156 BstLean.Part157

/-- **(GP) for differentiable functions**: a finite measure `μ`, unit vectors `e(x)`, `f(x, ·)`
differentiable with a gradient bounded by `C`, `0 < a ≤ f ≤ b`. -/
theorem gpSmooth : GPSmoothStmt := gp_smooth_of_deriv psiDeriv

/-- **(GP) for measurable functions**: a finite measure `μ` on `ℝ^N`, unit vectors `e(x)`, `f`
measurable with `0 < a ≤ f ≤ b`, the frame bound `∫ ⟨e(x), w⟩² dμ ≤ L·|w|²`, `L > 0`. -/
theorem gpMeas {N q m : ℕ} (μ : Measure (Fin N → ℝ)) [IsFiniteMeasure μ]
    (e : (Fin N → ℝ) → Fin m → ℝ) (he : Measurable e) (hunit : ∀ x, normSq (e x) = 1)
    (f : (Fin N → ℝ) × (Fin q → ℝ) → ℝ) (hf : Measurable f) {a b : ℝ} (ha : 0 < a)
    (hfa : ∀ y, a ≤ f y) (hfb : ∀ y, f y ≤ b) {L : ℝ} (hL : 0 < L)
    (hframe : ∀ w : Fin m → ℝ, ∫ x, (∑ j, e x j * w j) ^ 2 ∂μ ≤ L * ∑ j, w j ^ 2) :
    ∫ G, exp (1 / L * ∫ x, log (f (x, G.mulVec (e x))) ∂μ) ∂gaussMat q m 1 ≤
      exp (1 / L * ∫ x, log (∫ z, f (x, z) ∂stdGauss (Fin q)) ∂μ) :=
  gp_meas_of_smooth gpSmooth μ e he hunit f hf ha hfa hfb hL hframe

/-- **The Gaussian inequality (GP) of Part 157 (Lemma `t7:p02:GP` for the maps
`B_x G = G e(x)`): proved.** -/
theorem gaussGP : BstLean.Part157.GaussGP := gaussGP_of_smooth gpSmooth

/-- **The bound of the moment generating function of the indicator mean** (Corollary
`t7:p02:MGF`), with no hypothesis. -/
theorem gaussFrameMGF : GaussFrameMGF := mgf_of_gp gaussGP

variable {n : ℕ}

/-- **The conditional classifier theorem for the actual networks without the hypothesis
`GaussGP` (every `n ≥ 16 384`).** The statement of
`BstLean.Part157.classifier_networks_conditional_gp` with `GaussGP` proved. The hypotheses
`EVENTS_hyp`, `FRAME_W_hyp`, `FRAME_A_hyp`, `REPLA_mix_hyp` remain. -/
theorem classifier_networks_conditional_frames (hn : 16384 ≤ n)
    (D : Design n) (t : ℝ) {H E₁ : Set (Ret n)}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhidL vWL δextraL)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (cfL / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  classifier_networks_conditional_gp hn gaussGP D t hEv hFW hFA hRA

/-- The same at `n = 16 384`. -/
theorem classifier_networks_conditional_frames_16384
    (D : Design 16384) (t : ℝ) {H E₁ : Set (Ret 16384)}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhidL vWL δextraL)
    (hFW : FRAME_W_hyp D.toCentres (cWL / 16384) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (cfL / 16384) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 16384).prod (sampMeas (10 ^ 12) 16384)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  classifier_networks_conditional_gp_16384 gaussGP D t hEv hFW hFA hRA

end BstLean.Part158

open BstLean.Part158 in
#print axioms psiDeriv
open BstLean.Part158 in
#print axioms gpSmooth
open BstLean.Part158 in
#print axioms gpMeas
open BstLean.Part158 in
#print axioms gaussGP
open BstLean.Part158 in
#print axioms gaussFrameMGF
open BstLean.Part158 in
#print axioms classifier_networks_conditional_frames
open BstLean.Part158 in
#print axioms classifier_networks_conditional_frames_16384
