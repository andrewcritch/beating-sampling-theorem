import BstLean.Part131Tail

/-!
# Part 151, item 2: the final Gaussian step, in an abstract form

Role: `delegations/statements/p151-spec.md`, item 2. Paper source:
`proofs/option-n/theorem5-13-events-final.tex`, Proposition "The union bound" (`prop:final`).

Setting. `(Ω, P)` carries all random variables except the last row `f₃` of `F`. `(R, ν)` carries
the last row. `lin ω w` is the linear form `f₃·Δ(ω)`; the only fact used about it is that, for a
fixed `ω` of the event `E`, its distribution under `ν` is the centred Gaussian distribution with
variance `V ω` (`V ω = t_F·|Δ(ω)|²` in the application). The joint space is `(T, Q)` with two
measurable maps `rest : T → Ω`, `row : T → R` such that the distribution of `(rest, row)` under
`Q` is the product `P ⊗ ν` (in the application `T` is the space of `((W, A, F), η)`).

* `PhiBar a = Φ̄(a)`: the upper tail of the standard Gaussian distribution.
* `gauss_abs_tail`: a centred Gaussian variable with variance `V ≤ v` is above `c` in absolute
  value with probability at most `2Φ̄(c/√v)`.
* `gaussStep`: `Pr(ω ∈ E, |lin| > c) ≤ 2Φ̄(c/√v)·Pr(E)`, if `V ≤ v` on `E`.
* `finalStep`: `Pr(|g − B| > (ε_W + ε_A)·sd) ≤ Pr(|B′ − B| > ε_W·sd) + Pr(Eᶜ) + Pr(G, sd < d)
  + 2Φ̄(ε_A·d/√v)`, if `g − B′ = lin` on `E` and `E ⊂ G`.
* `finalStep_success`: the same as a lower bound of `Pr(|g − B| ≤ (ε_W + ε_A)·sd)`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal
open BstLean.Part131 (tail_neg)

/-- `Φ̄(a)`: the probability that a standard Gaussian variable is above `a`. -/
noncomputable def PhiBar (a : ℝ) : ℝ := (gaussianReal 0 1).real (Ioi a)

lemma PhiBar_nonneg (a : ℝ) : 0 ≤ PhiBar a := measureReal_nonneg

lemma PhiBar_le_one (a : ℝ) : PhiBar a ≤ 1 := measureReal_le_one

/-- `Pr(|Z| > a) ≤ 2Φ̄(a)` for a standard Gaussian variable `Z` (equality for `a ≥ 0`). -/
lemma std_abs_tail (a : ℝ) : (gaussianReal 0 1).real {x | a < |x|} ≤ 2 * PhiBar a := by
  have hsub : {x : ℝ | a < |x|} ⊆ Ioi a ∪ Iio (-a) := by
    intro x hx
    simp only [mem_ofPred_eq] at hx
    rcases lt_abs.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr (by simp only [mem_Iio]; linarith)
  calc (gaussianReal 0 1).real {x | a < |x|}
      ≤ (gaussianReal 0 1).real (Ioi a ∪ Iio (-a)) := measureReal_mono hsub
    _ ≤ (gaussianReal 0 1).real (Ioi a) + (gaussianReal 0 1).real (Iio (-a)) :=
        measureReal_union_le _ _
    _ = 2 * PhiBar a := by rw [tail_neg]; unfold PhiBar; ring

/-- **A centred Gaussian variable with variance `V ≤ v`**: `Pr(|X| > c) ≤ 2Φ̄(c/√v)`. -/
theorem gauss_abs_tail {V v c : ℝ} (hV0 : 0 ≤ V) (hVv : V ≤ v) (hv : 0 < v) (hc : 0 < c) :
    (gaussianReal 0 V.toNNReal).real {x | c < |x|} ≤ 2 * PhiBar (c / √v) := by
  have hsv : 0 < √v := Real.sqrt_pos.mpr hv
  rcases hV0.eq_or_lt with h0 | hVpos
  · rw [← h0]
    simp only [Real.toNNReal_zero, gaussianReal_zero_var]
    have : (Measure.dirac (0 : ℝ)).real {x | c < |x|} = 0 := by
      have hms0 : MeasurableSet {x : ℝ | c < |x|} :=
        measurableSet_lt measurable_const measurable_id.abs
      rw [measureReal_def, Measure.dirac_apply' _ hms0]
      simp [not_lt.mpr hc.le]
    rw [this]
    exact mul_nonneg (by norm_num) (PhiBar_nonneg _)
  have hsV : 0 < √V := Real.sqrt_pos.mpr hVpos
  have hmap : gaussianReal 0 V.toNNReal = (gaussianReal 0 1).map (fun x => √V * x) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext
      simp [Real.sq_sqrt hV0, Real.coe_toNNReal _ hV0]
  have hms : MeasurableSet {x : ℝ | c < |x|} := measurableSet_lt measurable_const measurable_id.abs
  rw [hmap, map_measureReal_apply (by fun_prop) hms]
  refine le_trans (measureReal_mono ?_) (std_abs_tail (c / √v))
  intro x hx
  simp only [mem_preimage, mem_ofPred_eq] at hx ⊢
  rw [abs_mul, abs_of_pos hsV] at hx
  rw [div_lt_iff₀ hsv]
  have h1 : √V ≤ √v := Real.sqrt_le_sqrt hVv
  calc c < √V * |x| := hx
    _ ≤ √v * |x| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = |x| * √v := mul_comm _ _

section step

variable {Ω R : Type*} [MeasurableSpace Ω] [MeasurableSpace R]

/-- **The Gaussian step.** `P` is the distribution of the variables that are fixed, `ν` the
distribution of the last row. For `ω` in the event `E`, the variable `lin ω` is centred Gaussian
under `ν` with variance `V ω ≤ v`. Then
`Pr(ω ∈ E and |lin| > c) ≤ 2Φ̄(c/√v)·Pr(E)`. -/
theorem gaussStep (P : Measure Ω) [IsProbabilityMeasure P] (ν : Measure R)
    [IsProbabilityMeasure ν] {lin : Ω → R → ℝ} (hlin : Measurable fun p : Ω × R => lin p.1 p.2)
    {V : Ω → ℝ} {E : Set Ω} (hE : MeasurableSet E) (hV0 : ∀ ω ∈ E, 0 ≤ V ω)
    (hg : ∀ ω ∈ E, ν.map (lin ω) = gaussianReal 0 (V ω).toNNReal) {v c : ℝ} (hv : 0 < v)
    (hc : 0 < c) (hVE : ∀ ω ∈ E, V ω ≤ v) :
    (P.prod ν).real {p | p.1 ∈ E ∧ c < |lin p.1 p.2|} ≤ 2 * PhiBar (c / √v) * P.real E := by
  have hS : MeasurableSet {p : Ω × R | p.1 ∈ E ∧ c < |lin p.1 p.2|} :=
    (measurable_fst hE).inter (measurableSet_lt measurable_const hlin.abs)
  have hb0 : 0 ≤ 2 * PhiBar (c / √v) := mul_nonneg (by norm_num) (PhiBar_nonneg _)
  have hpt : ∀ ω, ν (Prod.mk ω ⁻¹' {p : Ω × R | p.1 ∈ E ∧ c < |lin p.1 p.2|}) ≤
      E.indicator (fun _ => ENNReal.ofReal (2 * PhiBar (c / √v))) ω := by
    intro ω
    by_cases hω : ω ∈ E
    · rw [indicator_of_mem hω]
      have hlω : Measurable (lin ω) := hlin.comp (measurable_const.prodMk measurable_id)
      have hms : MeasurableSet {x : ℝ | c < |x|} :=
        measurableSet_lt measurable_const measurable_id.abs
      have e : Prod.mk ω ⁻¹' {p : Ω × R | p.1 ∈ E ∧ c < |lin p.1 p.2|} =
          lin ω ⁻¹' {x | c < |x|} := by
        ext w; simp [hω]
      rw [e, ← Measure.map_apply hlω hms, hg ω hω]
      have h := gauss_abs_tail (hV0 ω hω) (hVE ω hω) hv hc
      rw [measureReal_def] at h
      exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hb0).mpr h
    · rw [indicator_of_notMem hω]
      have e : Prod.mk ω ⁻¹' {p : Ω × R | p.1 ∈ E ∧ c < |lin p.1 p.2|} = ∅ := by
        ext w; simp [hω]
      rw [e]; simp
  have hle : (P.prod ν) {p : Ω × R | p.1 ∈ E ∧ c < |lin p.1 p.2|} ≤
      ENNReal.ofReal (2 * PhiBar (c / √v)) * P E := by
    rw [Measure.prod_apply hS]
    calc ∫⁻ ω, ν (Prod.mk ω ⁻¹' {p : Ω × R | p.1 ∈ E ∧ c < |lin p.1 p.2|}) ∂P
        ≤ ∫⁻ ω, E.indicator (fun _ => ENNReal.ofReal (2 * PhiBar (c / √v))) ω ∂P :=
          lintegral_mono hpt
      _ = ENNReal.ofReal (2 * PhiBar (c / √v)) * P E := by
          rw [lintegral_indicator hE, setLIntegral_const]
  rw [measureReal_def, measureReal_def]
  have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top P E)) hle
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hb0] at h2

end step

section final

variable {T Ω R : Type*} [MeasurableSpace T] [MeasurableSpace Ω] [MeasurableSpace R]

/-- **The final Gaussian step with the union bound** (Proposition "The union bound" of the
document, abstract form). `Q` is the joint distribution; `rest` gives all variables except the
last row, `row` the last row; under `Q` the pair `(rest, row)` has the product distribution
`P ⊗ ν`. On the event `E` (a set of values of `rest`): `g − B′ = lin` and the conditional
variance `V` of `lin` is at most `v`. `G` is any event that contains `E` (the document: the
hidden event of `W`; take `G = univ` for the plain form). Then
`Pr(|g − B| > (ε_W + ε_A)·sd) ≤ Pr(|B′ − B| > ε_W·sd) + Pr(Eᶜ) + Pr(G and sd < d)
+ 2Φ̄(ε_A·d/√v)`.
No measurability of `g`, `B`, `B′`, `sd`, `G` is needed, and none of them is assumed
independent of the last row. -/
theorem finalStep (Q : Measure T) [IsProbabilityMeasure Q] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure R) [IsProbabilityMeasure ν] {rest : T → Ω}
    {row : T → R} (hrest : Measurable rest) (hrow : Measurable row)
    (hmap : Q.map (fun t => (rest t, row t)) = P.prod ν) {lin : Ω → R → ℝ}
    (hlin : Measurable fun p : Ω × R => lin p.1 p.2) {V : Ω → ℝ} {E : Set Ω}
    (hE : MeasurableSet E) (hV0 : ∀ ω ∈ E, 0 ≤ V ω)
    (hg : ∀ ω ∈ E, ν.map (lin ω) = gaussianReal 0 (V ω).toNNReal) {v : ℝ} (hv : 0 < v)
    (hVE : ∀ ω ∈ E, V ω ≤ v) (g B B' sd : T → ℝ)
    (hst : ∀ t, rest t ∈ E → g t - B' t = lin (rest t) (row t)) (G : Set T)
    (hEG : ∀ t, rest t ∈ E → t ∈ G) (εW : ℝ) {εA d : ℝ} (hεA : 0 < εA) (hd : 0 < d) :
    Q.real {t | (εW + εA) * sd t < |g t - B t|} ≤
      Q.real {t | εW * sd t < |B' t - B t|} + P.real Eᶜ + Q.real (G ∩ {t | sd t < d}) +
        2 * PhiBar (εA * d / √v) := by
  have hpair : Measurable fun t => (rest t, row t) := hrest.prodMk hrow
  -- the inclusion
  have hincl : {t | (εW + εA) * sd t < |g t - B t|} ⊆
      (({t | εW * sd t < |B' t - B t|} ∪ rest ⁻¹' Eᶜ) ∪ (G ∩ {t | sd t < d})) ∪
        (fun t => (rest t, row t)) ⁻¹' {p | p.1 ∈ E ∧ εA * d < |lin p.1 p.2|} := by
    intro t ht
    simp only [mem_ofPred_eq] at ht
    by_cases h1 : εW * sd t < |B' t - B t|
    · exact Or.inl (Or.inl (Or.inl h1))
    by_cases h2 : rest t ∈ E
    swap
    · exact Or.inl (Or.inl (Or.inr h2))
    by_cases h3 : sd t < d
    · exact Or.inl (Or.inr ⟨hEG t h2, h3⟩)
    refine Or.inr ⟨h2, ?_⟩
    show εA * d < |lin (rest t) (row t)|
    rw [← hst t h2]
    have h1' : |B' t - B t| ≤ εW * sd t := not_lt.mp h1
    have h3' : d ≤ sd t := not_lt.mp h3
    have htri : |g t - B t| ≤ |g t - B' t| + |B' t - B t| := by
      have := abs_add_le (g t - B' t) (B' t - B t)
      rwa [sub_add_sub_cancel] at this
    have : εA * d ≤ εA * sd t := mul_le_mul_of_nonneg_left h3' hεA.le
    nlinarith
  -- the probabilities
  have hEc : Q.real (rest ⁻¹' Eᶜ) = P.real Eᶜ := by
    have h1 : P = Q.map rest := by
      have h := congrArg (Measure.map Prod.fst) hmap
      rw [Measure.map_map measurable_fst hpair] at h
      have e : (Prod.fst ∘ fun t => (rest t, row t)) = rest := rfl
      rw [e] at h
      rw [h]; simp
    rw [h1, map_measureReal_apply hrest hE.compl]
  have hS : MeasurableSet {p : Ω × R | p.1 ∈ E ∧ εA * d < |lin p.1 p.2|} :=
    (measurable_fst hE).inter (measurableSet_lt measurable_const hlin.abs)
  have hG4 : Q.real ((fun t => (rest t, row t)) ⁻¹'
      {p | p.1 ∈ E ∧ εA * d < |lin p.1 p.2|}) ≤ 2 * PhiBar (εA * d / √v) := by
    rw [← map_measureReal_apply hpair hS, hmap]
    refine (gaussStep P ν hlin hE hV0 hg hv (mul_pos hεA hd) hVE).trans ?_
    have hb0 : 0 ≤ 2 * PhiBar (εA * d / √v) := mul_nonneg (by norm_num) (PhiBar_nonneg _)
    calc 2 * PhiBar (εA * d / √v) * P.real E ≤ 2 * PhiBar (εA * d / √v) * 1 :=
          mul_le_mul_of_nonneg_left measureReal_le_one hb0
      _ = _ := mul_one _
  calc Q.real {t | (εW + εA) * sd t < |g t - B t|}
      ≤ Q.real ((({t | εW * sd t < |B' t - B t|} ∪ rest ⁻¹' Eᶜ) ∪ (G ∩ {t | sd t < d})) ∪
        (fun t => (rest t, row t)) ⁻¹' {p | p.1 ∈ E ∧ εA * d < |lin p.1 p.2|}) :=
        measureReal_mono hincl
    _ ≤ Q.real {t | εW * sd t < |B' t - B t|} + Q.real (rest ⁻¹' Eᶜ) +
          Q.real (G ∩ {t | sd t < d}) +
        Q.real ((fun t => (rest t, row t)) ⁻¹' {p | p.1 ∈ E ∧ εA * d < |lin p.1 p.2|}) := by
        refine (measureReal_union_le _ _).trans ?_
        gcongr
        refine (measureReal_union_le _ _).trans ?_
        gcongr
        exact measureReal_union_le _ _
    _ ≤ _ := by rw [hEc]; linarith

/-- **The success form of `finalStep`**:
`Pr(|g − B| ≤ (ε_W + ε_A)·sd) ≥ 1 − (Pr(|B′ − B| > ε_W·sd) + Pr(Eᶜ) + Pr(G, sd < d)
+ 2Φ̄(ε_A·d/√v))`. -/
theorem finalStep_success (Q : Measure T) [IsProbabilityMeasure Q] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure R) [IsProbabilityMeasure ν] {rest : T → Ω}
    {row : T → R} (hrest : Measurable rest) (hrow : Measurable row)
    (hmap : Q.map (fun t => (rest t, row t)) = P.prod ν) {lin : Ω → R → ℝ}
    (hlin : Measurable fun p : Ω × R => lin p.1 p.2) {V : Ω → ℝ} {E : Set Ω}
    (hE : MeasurableSet E) (hV0 : ∀ ω ∈ E, 0 ≤ V ω)
    (hg : ∀ ω ∈ E, ν.map (lin ω) = gaussianReal 0 (V ω).toNNReal) {v : ℝ} (hv : 0 < v)
    (hVE : ∀ ω ∈ E, V ω ≤ v) (g B B' sd : T → ℝ)
    (hst : ∀ t, rest t ∈ E → g t - B' t = lin (rest t) (row t)) (G : Set T)
    (hEG : ∀ t, rest t ∈ E → t ∈ G) (εW : ℝ) {εA d : ℝ} (hεA : 0 < εA) (hd : 0 < d) :
    1 - (Q.real {t | εW * sd t < |B' t - B t|} + P.real Eᶜ + Q.real (G ∩ {t | sd t < d}) +
        2 * PhiBar (εA * d / √v)) ≤ Q.real {t | |g t - B t| ≤ (εW + εA) * sd t} := by
  have h := finalStep Q P ν hrest hrow hmap hlin hE hV0 hg hv hVE g B B' sd hst G hEG εW hεA hd
  have hu : (1 : ℝ) ≤ Q.real {t | |g t - B t| ≤ (εW + εA) * sd t} +
      Q.real {t | (εW + εA) * sd t < |g t - B t|} := by
    have e : {t | |g t - B t| ≤ (εW + εA) * sd t} ∪ {t | (εW + εA) * sd t < |g t - B t|} =
        univ := by
      ext t
      simp only [mem_union, mem_ofPred_eq, mem_univ, iff_true]
      exact le_or_gt _ _
    have h1 := measureReal_union_le (μ := Q) {t | |g t - B t| ≤ (εW + εA) * sd t}
      {t | (εW + εA) * sd t < |g t - B t|}
    rw [e] at h1
    simpa using h1
  linarith

end final

end BstLean.Part151
