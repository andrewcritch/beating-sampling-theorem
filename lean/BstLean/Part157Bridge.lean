import BstLean.Part157Mgf
import BstLean.Part136Final

/-!
# Part 157, item 4: what the earlier Lean parts already give for the World hypotheses

Do not use `sorry`, `native_decide` or `axiom`.

Part 136 has, for the EXACT mean centre `h̄^W = E_u a₂^W(u)` of the last hidden layer of `W`
(`hbarW`; an oracle: it is not computed by a program of bounded cost), a hidden event `good136 n`
of probability at least `0.998` on which the frame bound is `(13/25)/n` (`n ≥ 16 384`).

* `H136 n`: the retained data whose hidden World matrices are in `good136 n`.
* `frame_w_exact`: `FRAME_W_hyp D (1.377/n) E` for every `E ⊆ H136 n`, when the World centre of
  the design is the exact mean centre.
* `retDist_hid`: the hidden World matrices of the retained data have the distribution `hidGauss`.
* `hidden_charge_136`: `Pr((H136 n)ᶜ) ≤ 0.002` under the distribution of the retained data (the
  ledger of the paper has `0.001900001` for its event `H_W`).
* `integrableOn_HbarW_sq`: the integrability item of `EVENTS_hyp` holds for the Hellinger radius.
* `classifier_networks_exactW`: the conditional theorem for a design with the exact mean World
  centre. The World frame bound and the hidden charge are PROVED (from Part 136); the remaining
  hypotheses are `GaussGP`, the Hellinger moment, the charge of the other events, and the two
  Agent hypotheses.

This is NOT the design of the paper: the paper's World centre is the binomial centre `bWp`
(`Part157Paper`). For the computed centre `ψ_s(M₂ h̄₁)` Part 140 (`lamHat140`) has the frame
constant `1.83/n`, which is larger than the `1.377/n` that the ledger of Part 156 needs.
-/

namespace BstLean.Part157

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part134
open BstLean.Part136 (HidParam hidGauss hbarW good136 good136_meas good136_prob lamOne136_16384)
open BstLean.Part156

variable {n : ℕ}

/-- The retained data whose hidden World matrices `(W₁, W₂)` are in the event `good136 n` of
Part 136. -/
def H136 (n : ℕ) : Set (Ret n) := {c | c.1.1 ∈ good136 n}

lemma measurableSet_H136 (hn : 1 ≤ n) : MeasurableSet (H136 n) :=
  (measurable_fst.comp measurable_fst : Measurable (fun c : Ret n => c.1.1)) (good136_meas hn)

/-- **The World frame bound is PROVED for the exact mean centre** (from `lamOne136_16384` of
Part 136): on every set of retained data inside `H136 n`, `n ≥ 16 384`. -/
theorem frame_w_exact (hn : 16384 ≤ n) (D : Centres n) (hD : D.bW = hbarW) {E : Set (Ret n)}
    (hE : E ⊆ H136 n) : FRAME_W_hyp D (cWL / n) E := by
  intro c hc w
  have h := (lamOne136_16384 hn (hE hc)).2.1 w
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hS : (0 : ℝ) ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hc' : (13 / 25 / (n : ℝ)) ≤ cWL / (n : ℝ) :=
    div_le_div_of_nonneg_right (by unfold cWL; norm_num) hnpos.le
  rw [hD]
  exact h.trans (mul_le_mul_of_nonneg_right hc' hS)

/-- The hidden World matrices of the retained data have the distribution `hidGauss`. -/
theorem retDist_hid (D : Centres n) :
    (retDist D).map (fun c : Ret n => c.1.1) = hidGauss (2 * n) (mW n) := by
  have m1 : Measurable (fun c : Ret n => c.1.1) := measurable_fst.comp measurable_fst
  rw [← noise_retVal D, Measure.map_map m1 (measurable_retVal D)]
  have e : ((fun c : Ret n => c.1.1) ∘ retVal D) = Prod.fst ∘ Prod.fst := rfl
  rw [e, ← Measure.map_map measurable_fst measurable_fst]
  unfold noiseC cWm
  rw [Measure.map_fst_prod, measure_univ, one_smul, Measure.map_fst_prod, measure_univ, one_smul]

/-- **The hidden charge from Part 136**: `Pr((H136 n)ᶜ) ≤ 0.002` under the distribution of the
retained data, every `n ≥ 4096`. -/
theorem hidden_charge_136 (hn : 4096 ≤ n) (D : Centres n) :
    (retDist D).real (H136 n)ᶜ ≤ 2 / 1000 := by
  have m1 : Measurable (fun c : Ret n => c.1.1) := measurable_fst.comp measurable_fst
  have hm := good136_meas (n := n) (by omega)
  have e : (H136 n)ᶜ = (fun c : Ret n => c.1.1) ⁻¹' (good136 n)ᶜ := rfl
  rw [e, ← map_measureReal_apply m1 hm.compl, retDist_hid D, measureReal_compl hm,
    probReal_univ]
  have := good136_prob hn
  linarith

/-- The integrability item of `EVENTS_hyp` holds for the Hellinger radius (`0 ≤ H̄_W² ≤ 2`). -/
theorem integrableOn_HbarW_sq (hn : 1 ≤ n) (D : Design n) (H : Set (Ret n)) :
    IntegrableOn (fun c => HbarW D c ^ 2) H (retDist D.toCentres) := by
  have hprob := BstLean.Part29.uniformSphere_isProbability (2 * n) (by omega)
  refine Integrable.integrableOn ?_
  refine Integrable.of_bound ((measurable_HbarW D).pow_const 2).aestronglyMeasurable 2
    (Filter.Eventually.of_forall fun c => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), HbarW_sq]
  unfold HbarW2
  by_cases hi : Integrable (fun u : Fin (2 * n) → ℝ =>
      hu2 n (lamWu D.toCentres c u) (sigWu D.toCentres c u) (D.tau0 c)) (uniformSphere (2 * n))
  · have := integral_mono hi (integrable_const (2 : ℝ)) (fun u => hu2_le_two _ _ _ _)
    simpa using this
  · rw [integral_undef hi]; norm_num

/-- **`EVENTS_hyp` for the Hellinger radius from the three charges alone.** `H`, `E₁` measurable;
`Pr(Hᶜ) ≤ δ_hid`, `E[1_H H̄_W²] ≤ v_W` (written with `HbarW2 D = E_u H_u²`),
`Pr(H ∩ E₁ᶜ) ≤ δ_extra`.
The measurability of the radius and the integrability item are proved. -/
theorem events_hbarW (hn : 1 ≤ n) (D : Design n) {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hH : MeasurableSet H) (hE₁ : MeasurableSet E₁)
    (h1 : (retDist D.toCentres).real Hᶜ ≤ δhid)
    (h2 : ∫ c in H, HbarW2 D c ∂retDist D.toCentres ≤ vW)
    (h3 : (retDist D.toCentres).real (H ∩ E₁ᶜ) ≤ δextra) :
    EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra := by
  refine ⟨hH, hE₁, measurable_HbarW D, h1, integrableOn_HbarW_sq hn D H, ?_, h3⟩
  simp_rw [HbarW_sq]
  exact h2

/-- **The conditional classifier theorem for a design with the exact mean World centre (every
`n ≥ 16 384`).** The World frame bound and the hidden charge `0.002` are PROVED in Lean (Part 136).
IF `GaussGP` holds, the Hellinger moment has `E[1_{H136} H̄_W²] ≤ v_W`, the other retained-data
events have `Pr(H136 ∩ E₁ᶜ) ≤ δ_extra`, with `0.002 + v_W/h_W² + δ_extra ≤ 0.0068`, and on
`H136 ∩ {H̄_W ≤ h_W} ∩ E₁` the Agent frame bound and the Agent replacement hold, THEN the program
succeeds with probability at least `99/100`. The exact mean centre is an oracle (no program of
bounded cost computes it); this is not the design of the paper. -/
theorem classifier_networks_exactW (hn : 16384 ≤ n) (hGP : GaussGP) (D : Design n)
    (hD : D.bW = hbarW) (t : ℝ) {E₁ : Set (Ret n)} {vW δextra : ℝ} (hE₁ : MeasurableSet E₁)
    (hmom : ∫ c in H136 n, HbarW D c ^ 2 ∂retDist D.toCentres ≤ vW)
    (hextra : (retDist D.toCentres).real (H136 n ∩ E₁ᶜ) ≤ δextra)
    (hsum : 2 / 1000 + vW / hWL ^ 2 + δextra ≤ 68 / 10 ^ 4)
    (hFA : FRAME_A_hyp D (cfL / n) (goodSet (H136 n) E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet (H136 n) E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} :=
  classifier_networks_charges_success hn (mgf_of_gp hGP) D t (δhid := 2 / 1000)
    ⟨measurableSet_H136 (by omega), hE₁, measurable_HbarW D,
      hidden_charge_136 (by omega) D.toCentres, integrableOn_HbarW_sq (by omega) D _, hmom,
      hextra⟩
    hsum (frame_w_exact hn D.toCentres hD (fun _ hc => hc.1.1)) hFA hRA

end BstLean.Part157

open BstLean.Part157 in
#print axioms frame_w_exact
open BstLean.Part157 in
#print axioms hidden_charge_136
open BstLean.Part157 in
#print axioms classifier_networks_exactW
open BstLean.Part157 in
#print axioms events_hbarW
