import BstLean.Part131Integrable

/-!
# Part 131, items 4 to 6: the reduction of Theorem C to two numbers, and the estimator consequence

Role: `delegations/statements/p131-spec.md`. Paper source: round onW4c ("Confirmed probability
argument", §7).

The probability space of the four networks is `lawAll N mW n mA mF` (`Part131Space`).

* `thmC_of_meanVar` (item 4): `E J ≥ j > 0`, `Var J ≤ V` give `Pr(separation) ≥ (3/25)·j²/(j²+V)`.
  `J` has a finite second moment (`memLp_Jall`), so there is no integrability hypothesis.
* `noReadA_of_separation` (item 5), `thmC_conditional` (item 6), `thmC_conditional_levels`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part131

open MeasureTheory ProbabilityTheory Set Matrix
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130

universe w

variable {N mW n mA mF : ℕ}

/-! ## Item 4: the reduction of Theorem C to two numbers -/

/-- **Item 4 (`thmC_of_meanVar`).** If `E J ≥ j > 0` and `Var J ≤ V` (`J = D − T̄`; it has a finite
second moment by `memLp_Jall`), then the separation of two independent copies of the Agent network has
probability at least `(3/25)·j²/(j² + V)` over `(W, F, A, A′)`. -/
theorem thmC_of_meanVar (hn : 1 ≤ n) (hN : 1 ≤ N) {j V : ℝ} (hj : 0 < j)
    (hmean : j ≤ ∫ t, Jall t ∂lawAll N mW n mA mF)
    (hvar : Var[Jall; lawAll N mW n mA mF] ≤ V) :
    3 / 25 * (j ^ 2 / (j ^ 2 + V)) ≤ (lawAll N mW n mA mF).real sepEvent := by
  have hc := cantelli_of_bounds (lawAll N mW n mA mF) Jall (memLp_Jall hn hN) hj hmean hvar
  have hT : MeasurableSet {t : (MlpParam N mW n × MlpParam n mF 1) × MlpParam n mA n ×
      MlpParam n mA n | 0 < Jall t} := measurableSet_lt measurable_const (measurable_Jall hN)
  have hfub := prob_ge_of_cond (mlpGauss N mW n) (gaussMat mF n (2 / (n : ℝ)))
    (gaussMat mF mF (2 / (mF : ℝ))) (gaussMat 1 mF (2 / (mF : ℝ)))
    ((mlpGauss n mA n).prod (mlpGauss n mA n)) sepEvent
    {t | 0 < Jall t} (measurableSet_sepEvent hN) hT (κ := 3 / 25) (by norm_num)
    (fun x y z w t ht => (sep_cond hn hN x t.1 t.2 y z (sub_pos.mp ht)).le)
  have hfub' : 3 / 25 * (lawAll N mW n mA mF).real {t | 0 < Jall t} ≤
      (lawAll N mW n mA mF).real sepEvent := hfub
  exact (mul_le_mul_of_nonneg_left hc (by norm_num)).trans hfub'

/-! ## Item 5: the estimator consequence -/

/-- **Item 5 (`noReadA_of_separation`).** If the separation has probability at least `p` over
`(W, F, A, A′)` and `0 < η < p`, then the set `{(W, F) | Δ(W, F) ≥ η}` is measurable, has
probability at least `(p − η)/(1 − η)`, and for every `(W, F)` in it, EVERY estimator that reads
nothing of `A` fails at accuracy `1/2` with probability at least `η/2` over `(A, ω)`.

**The class of estimators:** for the fixed `(W, F)`: any measurable space `Ω'` of random bits, any
probability measure `ν` on it, any measurable `c : Ω' → ℝ`; `Ω'`, `ν`, `c` may depend on `(W, F)`
in any way; `ω` is independent of `A` (the product measure). Failure: `|c(ω) − B_A| > s_A/2`. -/
theorem noReadA_of_separation (hN : 1 ≤ N) {p η : ℝ} (hη : 0 < η) (hηp : η < p)
    (hp : p ≤ (lawAll N mW n mA mF).real sepEvent) :
    MeasurableSet {x : MlpParam N mW n × MlpParam n mF 1 | η ≤ sepProbN mA x.1 x.2} ∧
    (p - η) / (1 - η) ≤ (lawWF N mW n mF).real {x | η ≤ sepProbN mA x.1 x.2} ∧
    ∀ (W : MlpParam N mW n) (F : MlpParam n mF 1), η ≤ sepProbN mA W F →
      ∀ (Ω' : Type w) [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
        (c : Ω' → ℝ), Measurable c →
        η / 2 ≤ ((mlpGauss n mA n).prod ν).real
          {q : MlpParam n mA n × Ω' | sdn W q.1 F / 2 < |c q.2 - Bn W q.1 F|} := by
  obtain ⟨h1, h2, h3⟩ := noReadA_abstract.{w} (lawWF N mW n mF) (mlpGauss n mA n)
    (fun (x : MlpParam N mW n × MlpParam n mF 1) (A : MlpParam n mA n) => Bn x.1 A x.2)
    (fun (x : MlpParam N mW n × MlpParam n mF 1) (A : MlpParam n mA n) => sdn x.1 A x.2)
    (measurable_Bn' hN) (measurable_sdn' hN) hη hηp hp
  exact ⟨h1, h2, fun W F hWF => h3 (W, F) hWF⟩

/-! ## Item 6: Theorem C, conditional on the two numbers -/

/-- **Item 6 (`thmC_conditional`).** From two numbers `j`, `V` with `E J ≥ j > 0`, `Var J ≤ V`
and `(3/25)·j²/(j² + V) ≥ 1/16`: the set `{(W, F) | Δ(W, F) ≥ 1/40}` is measurable and has
probability at least `1/26`, and for every `(W, F)` in it every estimator that reads nothing of
`A` (the class of `noReadA_of_separation`) fails at accuracy `1/2` with probability at least
`1/80` over `(A, ω)`. -/
theorem thmC_conditional (hn : 1 ≤ n) (hN : 1 ≤ N) {j V : ℝ} (hj : 0 < j)
    (hmean : j ≤ ∫ t, Jall t ∂lawAll N mW n mA mF)
    (hvar : Var[Jall; lawAll N mW n mA mF] ≤ V)
    (hjV : 1 / 16 ≤ 3 / 25 * (j ^ 2 / (j ^ 2 + V))) :
    MeasurableSet {x : MlpParam N mW n × MlpParam n mF 1 | 1 / 40 ≤ sepProbN mA x.1 x.2} ∧
    1 / 26 ≤ (lawWF N mW n mF).real {x | 1 / 40 ≤ sepProbN mA x.1 x.2} ∧
    ∀ (W : MlpParam N mW n) (F : MlpParam n mF 1), 1 / 40 ≤ sepProbN mA W F →
      ∀ (Ω' : Type w) [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
        (c : Ω' → ℝ), Measurable c →
        1 / 80 ≤ ((mlpGauss n mA n).prod ν).real
          {q : MlpParam n mA n × Ω' | sdn W q.1 F / 2 < |c q.2 - Bn W q.1 F|} := by
  have hp := hjV.trans (thmC_of_meanVar hn hN hj hmean hvar)
  obtain ⟨h1, h2, h3⟩ := noReadA_of_separation.{w} hN (p := 1 / 16) (η := 1 / 40)
    (by norm_num) (by norm_num) hp
  refine ⟨h1, ?_, fun W F hWF Ω' _ ν _ c hc => ?_⟩
  · norm_num at h2 ⊢; exact h2
  · have := h3 W F hWF Ω' ν c hc
    norm_num at this ⊢; exact this

/-- **No estimator that reads nothing of `A` has levels `(99/100, 99/100)`** (under the hypotheses
of `thmC_conditional`). An estimator is any family: for each `(W, F)` a measurable `c (W, F) : Ω' →
ℝ` (no measurability in `(W, F)` is needed). The set of `(W, F)` on which it is accurate
(`|c − B_A| ≤ s_A/2`) with probability at least `99/100` over `(A, ω)` lies in a measurable set of
probability at most `25/26`. -/
theorem thmC_conditional_levels (hn : 1 ≤ n) (hN : 1 ≤ N) {j V : ℝ} (hj : 0 < j)
    (hmean : j ≤ ∫ t, Jall t ∂lawAll N mW n mA mF)
    (hvar : Var[Jall; lawAll N mW n mA mF] ≤ V)
    (hjV : 1 / 16 ≤ 3 / 25 * (j ^ 2 / (j ^ 2 + V)))
    (Ω' : Type w) [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (c : MlpParam N mW n × MlpParam n mF 1 → Ω' → ℝ) (hc : ∀ x, Measurable (c x)) :
    (lawWF N mW n mF).real {x | 99 / 100 ≤ ((mlpGauss n mA n).prod ν).real
      {q : MlpParam n mA n × Ω' | |c x q.2 - Bn x.1 q.1 x.2| ≤ sdn x.1 q.1 x.2 / 2}} ≤ 25 / 26 := by
  obtain ⟨h1, h2, h3⟩ := thmC_conditional.{w} hn hN hj hmean hvar hjV
  set E : Set (MlpParam N mW n × MlpParam n mF 1) := {x | 1 / 40 ≤ sepProbN mA x.1 x.2} with hE
  have hsub : {x : MlpParam N mW n × MlpParam n mF 1 | 99 / 100 ≤ ((mlpGauss n mA n).prod ν).real
      {q : MlpParam n mA n × Ω' | |c x q.2 - Bn x.1 q.1 x.2| ≤ sdn x.1 q.1 x.2 / 2}} ⊆ Eᶜ := by
    intro x hx hxE
    have hfail := h3 x.1 x.2 hxE Ω' ν (c x) (hc x)
    have hcompl : {q : MlpParam n mA n × Ω' | |c x q.2 - Bn x.1 q.1 x.2| ≤ sdn x.1 q.1 x.2 / 2} =
        {q : MlpParam n mA n × Ω' | sdn x.1 q.1 x.2 / 2 < |c x q.2 - Bn x.1 q.1 x.2|}ᶜ := by
      ext q; simp only [mem_ofPred_eq, mem_compl_iff, not_lt]
    have hx' : 99 / 100 ≤ ((mlpGauss n mA n).prod ν).real
      {q : MlpParam n mA n × Ω' | |c x q.2 - Bn x.1 q.1 x.2| ≤ sdn x.1 q.1 x.2 / 2} := hx
    have hBx : Measurable fun A : MlpParam n mA n => Bn x.1 A x.2 := measurable_Bn_A hN x.1 x.2
    have hsx : Measurable fun A : MlpParam n mA n => sdn x.1 A x.2 := measurable_sdn_A hN x.1 x.2
    have hmeas : MeasurableSet
        {q : MlpParam n mA n × Ω' | sdn x.1 q.1 x.2 / 2 < |c x q.2 - Bn x.1 q.1 x.2|} :=
      measurableSet_lt ((hsx.comp measurable_fst).div_const 2)
        (((hc x).comp measurable_snd).sub (hBx.comp measurable_fst)).abs
    rw [hcompl, measureReal_compl hmeas, probReal_univ] at hx'
    linarith
  have h4 := measureReal_mono (μ := lawWF N mW n mF) hsub
  rw [measureReal_compl h1, probReal_univ] at h4
  linarith

end BstLean.Part131

open BstLean.Part131 in
#print axioms thmC_of_meanVar
open BstLean.Part131 in
#print axioms noReadA_of_separation
open BstLean.Part131 in
#print axioms thmC_conditional
open BstLean.Part131 in
#print axioms thmC_conditional_levels
