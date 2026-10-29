import BstLean.Part139Explicit

/-!
# Part 139: the two-stage form (the quantifier order of Option A)

Role: `delegations/statements/p139-spec.md`; `MM.md`, Option A:
"for most `(W, F)` there is `g_{W,F}` such that for most `A`: `|g_{W,F}(A) − B| ≤ ε·sd`".
Here `g_{W,F}(A) = gCheap W A F`. The step from the joint probability is Markov's inequality.

* `twoStage`: for a measurable event `E` of `(x, y)` with `Pr(E) ≥ 1 − p` and `q > 0`:
  `Pr_x(Pr_y(E) > 1 − q) ≥ 1 − p/q`.
* `triple_map`: `((W, F), A) ↦ (W, A, F)` maps `lawWF ⊗ (distribution of A)` to `mlpTriple`.
* **`optA139`**: for `n ≥ 4096` and `q > 0`:
  `Pr_{W,F}(Pr_A(|g₀ − B| ≤ sd/2) > 1 − q) ≥ 1 − (0.002 + 1951/n)/q`.
* **`optA139_explicit`**: the same for the explicit scale:
  `Pr_{W,F}(Pr_A(|g₀ − B| ≤ ε·√(S(1 − Q))) > 1 − q) ≥ 1 − (0.002 + 9/(ε²n))/q`;
  `optA139_explicit_frontier`: levels `(93/100, 93/100)` at `ε = 1/2` for `n ≥ 16384`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part139

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133 BstLean.Part136
open BstLean.Part138

/-- **From a joint probability to two stages** (Markov). -/
lemma twoStage {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {E : Set (α × β)}
    (hE : MeasurableSet E) {p q : ℝ} (hq : 0 < q) (hp : 1 - p ≤ (μ.prod ν).real E) :
    1 - p / q ≤ μ.real {x | 1 - q < ν.real {y | (x, y) ∈ E}} := by
  have hEc : MeasurableSet Eᶜ := hE.compl
  set f : α → ℝ≥0∞ := fun x => ν (Prod.mk x ⁻¹' Eᶜ) with hf
  have mf : Measurable f := measurable_measure_prodMk_left hEc
  have hint : ∫⁻ x, f x ∂μ = (μ.prod ν) Eᶜ := (Measure.prod_apply hEc).symm
  have hpc : (μ.prod ν).real Eᶜ ≤ p := by
    rw [measureReal_compl hE, probReal_univ]
    linarith
  have hmark := mul_meas_ge_le_lintegral (μ := μ) mf (ENNReal.ofReal q)
  rw [hint] at hmark
  have h1 : q * μ.real {x | ENNReal.ofReal q ≤ f x} ≤ p := by
    have h2 := ENNReal.toReal_mono (measure_ne_top _ _) hmark
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq.le] at h2
    exact h2.trans hpc
  have h3 : μ.real {x | ENNReal.ofReal q ≤ f x} ≤ p / q := by
    rw [le_div_iff₀ hq]
    linarith
  have hsub : {x | ENNReal.ofReal q ≤ f x}ᶜ ⊆ {x | 1 - q < ν.real {y | (x, y) ∈ E}} := by
    intro x hx
    have hx' : f x < ENNReal.ofReal q := not_le.mp hx
    have hsec : MeasurableSet {y | (x, y) ∈ E} := measurable_prodMk_left hE
    have e : ν.real {y | (x, y) ∈ E}ᶜ = (f x).toReal := rfl
    have h4 : (f x).toReal < q := by
      have := (ENNReal.toReal_lt_toReal (measure_ne_top _ _) ENNReal.ofReal_ne_top).mpr hx'
      rwa [ENNReal.toReal_ofReal hq.le] at this
    have h5 := measureReal_compl (μ := ν) hsec
    rw [probReal_univ] at h5
    change 1 - q < ν.real {y | (x, y) ∈ E}
    linarith
  have h6 : 1 ≤ μ.real {x | ENNReal.ofReal q ≤ f x} + μ.real {x | ENNReal.ofReal q ≤ f x}ᶜ := by
    have a1 := measureReal_union_le (μ := μ) {x | ENNReal.ofReal q ≤ f x}
      {x | ENNReal.ofReal q ≤ f x}ᶜ
    rw [Set.union_compl_self, probReal_univ] at a1
    exact a1
  have h7 := measureReal_mono (μ := μ) hsub (measure_ne_top _ _)
  linarith

section triple

variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  (μ : Measure α) (ν : Measure β) (τ : Measure γ) [SFinite μ] [SFinite ν] [SFinite τ]

/-- `((w, f), a) ↦ (w, (a, f))` maps `(μ ⊗ τ) ⊗ ν` to `μ ⊗ (ν ⊗ τ)`. -/
lemma map_wfa :
    ((μ.prod τ).prod ν).map (fun p : (α × γ) × β => (p.1.1, (p.2, p.1.2))) =
      μ.prod (ν.prod τ) := by
  have h1 : ((μ.prod τ).prod ν).map MeasurableEquiv.prodAssoc = μ.prod (τ.prod ν) :=
    Measure.prodAssoc_prod
  have h2 := Measure.map_prod_map μ (τ.prod ν) (f := id) (g := Prod.swap) measurable_id
    measurable_swap
  rw [Measure.map_id, Measure.prod_swap] at h2
  rw [h2, ← h1, Measure.map_map (by fun_prop) MeasurableEquiv.prodAssoc.measurable]
  rfl

end triple

/-- `((W, F), A) ↦ (W, A, F)` maps `lawWF ⊗ (distribution of A)` to the distribution of the
three networks. -/
lemma triple_map (n : ℕ) :
    ((lawWF (2 * n) (mW n) n (mF n)).prod (mlpGauss n (mA n) n)).map
        (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mF n) 1) × MlpParam n (mA n) n =>
          (p.1.1, (p.2, p.1.2))) = mlpTriple 2 n :=
  map_wfa (mlpGauss (2 * n) (mW n) n) (mlpGauss n (mA n) n) (mlpGauss n (mF n) 1)

/-- **The two-stage form for an event of `(W, A, F)`.** If a measurable event `E` has joint
probability at least `1 − p`, then for `q > 0`:
`Pr_{W,F}(Pr_A((W, A, F) ∈ E) > 1 − q) ≥ 1 − p/q`. -/
theorem twoStage139 {n : ℕ}
    {E : Set (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1)}
    (hE : MeasurableSet E) {p q : ℝ} (hq : 0 < q) (hp : 1 - p ≤ (mlpTriple 2 n).real E) :
    1 - p / q ≤ (lawWF (2 * n) (mW n) n (mF n)).real
      {x | 1 - q < (mlpGauss n (mA n) n).real {A | (x.1, A, x.2) ∈ E}} := by
  have mπ : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mF n) 1) ×
      MlpParam n (mA n) n => (p.1.1, (p.2, p.1.2))) := by fun_prop
  have hE' : MeasurableSet ((fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mF n) 1) ×
      MlpParam n (mA n) n => (p.1.1, (p.2, p.1.2))) ⁻¹' E) := mπ hE
  have hp' : 1 - p ≤ ((lawWF (2 * n) (mW n) n (mF n)).prod (mlpGauss n (mA n) n)).real
      ((fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mF n) 1) ×
        MlpParam n (mA n) n => (p.1.1, (p.2, p.1.2))) ⁻¹' E) := by
    rw [← map_measureReal_apply mπ hE, triple_map]
    exact hp
  exact twoStage (lawWF (2 * n) (mW n) n (mF n)) (mlpGauss n (mA n) n) hE' hq hp'

lemma measurableSet_okSet {n : ℕ} (hn : 1 ≤ n) : MeasurableSet (okSet n) := by
  have hN : 1 ≤ 2 * n := by omega
  exact measurableSet_le (((measurable_gCheap hN).sub (measurable_Bn hN)).abs)
    ((measurable_sdn hN).div_const 2)

/-- **Option A form, relative to the realized spread.** For `n ≥ 4096` and `q > 0`:
`Pr_{W,F}(Pr_A(|g₀ − B| ≤ sd/2) > 1 − q) ≥ 1 − (0.002 + 1951/n)/q`. -/
theorem optA139 {n : ℕ} (hn : 4096 ≤ n) {q : ℝ} (hq : 0 < q) :
    1 - (2 / 1000 + 1951 / (n : ℝ)) / q ≤ (lawWF (2 * n) (mW n) n (mF n)).real
      {x | 1 - q < (mlpGauss n (mA n) n).real
        {A | |gCheap x.1 A x.2 - Bn x.1 A x.2| ≤ sdn x.1 A x.2 / 2}} :=
  twoStage139 (measurableSet_okSet (by omega)) hq (standInSucceeds139_rate hn)

/-- **Option A form, relative to the explicit scale.** For `n ≥ 4096`, `ε > 0`, `q > 0`:
`Pr_{W,F}(Pr_A(|g₀ − B| ≤ ε·√(S(1 − Q))) > 1 − q) ≥ 1 − (0.002 + 9/(ε²n))/q`. -/
theorem optA139_explicit {n : ℕ} (hn : 4096 ≤ n) {ε : ℝ} (hε : 0 < ε) {q : ℝ} (hq : 0 < q) :
    1 - (2 / 1000 + 9 / (ε ^ 2 * (n : ℝ))) / q ≤ (lawWF (2 * n) (mW n) n (mF n)).real
      {x | 1 - q < (mlpGauss n (mA n) n).real
        {A | |gCheap x.1 A x.2 - Bn x.1 A x.2| ≤ ε * scale139 n}} := by
  have hN : 1 ≤ 2 * n := by omega
  have hE : MeasurableSet {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 | |gCheap t.1 t.2.1 t.2.2 - Bn t.1 t.2.1 t.2.2| ≤ ε * scale139 n} :=
    measurableSet_le (((measurable_gCheap hN).sub (measurable_Bn hN)).abs) measurable_const
  exact twoStage139 hE hq (standInExplicit139 hn hε)

/-- Levels `(93/100, 93/100)` at tolerance `1/2` of the explicit scale, for `n ≥ 16384`. -/
theorem optA139_explicit_frontier {n : ℕ} (hn : 16384 ≤ n) :
    93 / 100 ≤ (lawWF (2 * n) (mW n) n (mF n)).real
      {x | 93 / 100 < (mlpGauss n (mA n) n).real
        {A | |gCheap x.1 A x.2 - Bn x.1 A x.2| ≤ 1 / 2 * scale139 n}} := by
  have h := optA139_explicit (n := n) (by omega) (ε := 1 / 2) (by norm_num)
    (q := 7 / 100) (by norm_num)
  have hx : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have h9 : 9 / ((1 / 2 : ℝ) ^ 2 * (n : ℝ)) ≤ 22 / 10000 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have e : (1 : ℝ) - 7 / 100 = 93 / 100 := by norm_num
  rw [e] at h
  refine le_trans ?_ h
  have : (2 / 1000 + 9 / ((1 / 2 : ℝ) ^ 2 * (n : ℝ))) / (7 / 100) ≤ 7 / 100 := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  linarith

end BstLean.Part139

open BstLean.Part139 in
#print axioms twoStage139
open BstLean.Part139 in
#print axioms optA139
open BstLean.Part139 in
#print axioms optA139_explicit
open BstLean.Part139 in
#print axioms optA139_explicit_frontier
