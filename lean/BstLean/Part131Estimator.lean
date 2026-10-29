import BstLean.Part130Sym

/-!
# Part 131, the estimator consequence (abstract form)

Role: `delegations/statements/p131-spec.md`, item 5 (paper: `onW4c-cx.md` §7).

Setting: `X` is the space of what the estimator may read (`(W, F)` in the application), with a
probability measure `P`; `Y` is the space of what it does not read (`A`), with a probability
measure `μ`; `B x y` is the target and `s x y` the spread.

* `sepProb μ B s x`: the probability over two independent copies `y, y'` that
  `|B x y − B x y'| > (s x y + s x y')/2` (the paper's `Δ`).
* `fail_ge_half_sepProb`: for every real `c`: `Pr_y(|c − B x y| > s x y / 2) ≥ Δ(x)/2`.
* `fail_ge_half_sepProb_rand`: the same for `c = c(ω)`, `ω` independent of `y`.
* `noReadA_abstract`: if `Pr(separation) ≥ p` and `0 < η < p`, the level set `{Δ ≥ η}` has
  probability at least `(p − η)/(1 − η)`, and on it every randomized estimator fails with
  probability at least `η/2`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part131

open MeasureTheory ProbabilityTheory

universe w

/-- The conditional probability of separation given `x`: two independent copies `y, y'` with
distribution `μ`, event `|B x y − B x y'| > (s x y + s x y')/2`. -/
noncomputable def sepProb {X Y : Type*} [MeasurableSpace Y] (μ : Measure Y) (B s : X → Y → ℝ)
    (x : X) : ℝ :=
  (μ.prod μ).real {q : Y × Y | (s x q.1 + s x q.2) / 2 < |B x q.1 - B x q.2|}

section

variable {X Y : Type*} [MeasurableSpace Y]

lemma measurableSet_sep [MeasurableSpace X] (B s : X → Y → ℝ) (hB : Measurable (Function.uncurry B))
    (hs : Measurable (Function.uncurry s)) :
    MeasurableSet {t : X × Y × Y |
      (s t.1 t.2.1 + s t.1 t.2.2) / 2 < |B t.1 t.2.1 - B t.1 t.2.2|} := by
  have h1 : Measurable fun t : X × Y × Y => s t.1 t.2.1 :=
    hs.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have h2 : Measurable fun t : X × Y × Y => s t.1 t.2.2 :=
    hs.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  have h3 : Measurable fun t : X × Y × Y => B t.1 t.2.1 :=
    hB.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  have h4 : Measurable fun t : X × Y × Y => B t.1 t.2.2 :=
    hB.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))
  exact measurableSet_lt ((h1.add h2).div_const 2) (h3.sub h4).abs

/-- `x ↦ Δ(x)` is measurable. -/
theorem measurable_sepProb [MeasurableSpace X] (μ : Measure Y) [IsProbabilityMeasure μ] (B s : X → Y → ℝ)
    (hB : Measurable (Function.uncurry B)) (hs : Measurable (Function.uncurry s)) :
    Measurable (sepProb μ B s) := by
  have h := measurable_measure_prodMk_left (ν := μ.prod μ) (measurableSet_sep B s hB hs)
  exact h.ennreal_toReal

lemma sepProb_le_one (μ : Measure Y) [IsProbabilityMeasure μ] (B s : X → Y → ℝ) (x : X) :
    sepProb μ B s x ≤ 1 := measureReal_le_one

lemma sepProb_nonneg (μ : Measure Y) (B s : X → Y → ℝ) (x : X) :
    0 ≤ sepProb μ B s x := measureReal_nonneg

/-- **For every real `c`, one of the two copies fails**: pointwise in `x` and `c`,
`Pr_y(|c − B x y| > s x y / 2) ≥ Δ(x)/2`. No measurability hypothesis is needed. -/
theorem fail_ge_half_sepProb (μ : Measure Y) [IsProbabilityMeasure μ] (B s : X → Y → ℝ)
    (x : X) (c : ℝ) :
    sepProb μ B s x / 2 ≤ μ.real {y | s x y / 2 < |c - B x y|} := by
  set F : Set Y := {y | s x y / 2 < |c - B x y|} with hF
  have hsub : {q : Y × Y | (s x q.1 + s x q.2) / 2 < |B x q.1 - B x q.2|} ⊆
      (F ×ˢ Set.univ) ∪ (Set.univ ×ˢ F) := by
    intro q hq
    by_contra hcon
    simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, true_and, not_or, hF,
      Set.mem_ofPred_eq, not_lt] at hcon
    have hq' : (s x q.1 + s x q.2) / 2 < |B x q.1 - B x q.2| := hq
    have h1 := hcon.1
    have h2 := hcon.2
    have h3 : |B x q.1 - B x q.2| ≤ |c - B x q.1| + |c - B x q.2| := by
      have : B x q.1 - B x q.2 = (c - B x q.2) - (c - B x q.1) := by ring
      rw [this]
      exact (abs_sub _ _).trans (by rw [add_comm])
    linarith
  have h := (measureReal_mono (μ := μ.prod μ) hsub).trans (measureReal_union_le _ _)
  rw [measureReal_prod_prod, measureReal_prod_prod] at h
  simp only [probReal_univ, mul_one, one_mul] at h
  unfold sepProb
  linarith

/-- **A randomized estimator that reads nothing of `y`**: random bits `ω` with any distribution
`ν`, independent of `y` (product measure), estimate `c ω`. Its failure probability over `(y, ω)`
is at least `Δ(x)/2`. -/
theorem fail_ge_half_sepProb_rand (μ : Measure Y) [IsProbabilityMeasure μ] (B s : X → Y → ℝ)
    (x : X) (hBx : Measurable (B x)) (hsx : Measurable (s x))
    {Ω' : Type w} [MeasurableSpace Ω'] (ν : Measure Ω') [IsProbabilityMeasure ν] (c : Ω' → ℝ)
    (hc : Measurable c) :
    sepProb μ B s x / 2 ≤ (μ.prod ν).real {q : Y × Ω' | s x q.1 / 2 < |c q.2 - B x q.1|} := by
  have hT : MeasurableSet {q : Y × Ω' | s x q.1 / 2 < |c q.2 - B x q.1|} :=
    measurableSet_lt ((hsx.comp measurable_fst).div_const 2)
      ((hc.comp measurable_snd).sub (hBx.comp measurable_fst)).abs
  have hle : ENNReal.ofReal (sepProb μ B s x / 2) ≤
      (μ.prod ν) {q : Y × Ω' | s x q.1 / 2 < |c q.2 - B x q.1|} := by
    rw [Measure.prod_apply_symm hT]
    calc ENNReal.ofReal (sepProb μ B s x / 2)
        = ∫⁻ _ : Ω', ENNReal.ofReal (sepProb μ B s x / 2) ∂ν := by simp
      _ ≤ _ := by
        refine lintegral_mono fun ω => ?_
        exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr
          (fail_ge_half_sepProb μ B s x (c ω))
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp hle

/-- **The estimator consequence (abstract).** If the separation of two independent copies has
probability at least `p` over `(x, y, y')` and `0 < η < p`, then the level set `{x | η ≤ Δ(x)}`
is measurable, has probability at least `(p − η)/(1 − η)`, and for every `x` in it EVERY
measurable randomized estimator `c : Ω' → ℝ` (random bits of any distribution `ν`, independent of
`y`) fails at accuracy `s/2` with probability at least `η/2` over `(y, ω)`. -/
theorem noReadA_abstract [MeasurableSpace X] (P : Measure X) [IsProbabilityMeasure P] (μ : Measure Y)
    [IsProbabilityMeasure μ] (B s : X → Y → ℝ) (hB : Measurable (Function.uncurry B))
    (hs : Measurable (Function.uncurry s)) {p η : ℝ} (hη : 0 < η) (hηp : η < p)
    (hp : p ≤ (P.prod (μ.prod μ)).real {t : X × Y × Y |
      (s t.1 t.2.1 + s t.1 t.2.2) / 2 < |B t.1 t.2.1 - B t.1 t.2.2|}) :
    MeasurableSet {x | η ≤ sepProb μ B s x} ∧
    (p - η) / (1 - η) ≤ P.real {x | η ≤ sepProb μ B s x} ∧
    ∀ x, η ≤ sepProb μ B s x → ∀ (Ω' : Type w) [MeasurableSpace Ω'] (ν : Measure Ω')
      [IsProbabilityMeasure ν] (c : Ω' → ℝ), Measurable c →
      η / 2 ≤ (μ.prod ν).real {q : Y × Ω' | s x q.1 / 2 < |c q.2 - B x q.1|} := by
  have _ := hη
  have hΔ := measurable_sepProb μ B s hB hs
  have hE : MeasurableSet {x | η ≤ sepProb μ B s x} := measurableSet_le measurable_const hΔ
  refine ⟨hE, ?_, ?_⟩
  · set E : Set X := {x | η ≤ sepProb μ B s x} with hEdef
    have hS := measurableSet_sep B s hB hs
    have hint : (P.prod (μ.prod μ)).real {t : X × Y × Y |
        (s t.1 t.2.1 + s t.1 t.2.2) / 2 < |B t.1 t.2.1 - B t.1 t.2.2|} =
        ∫ x, sepProb μ B s x ∂P := by
      rw [measureReal_def, Measure.prod_apply hS,
        ← integral_toReal (measurable_measure_prodMk_left hS).aemeasurable
          (Filter.Eventually.of_forall fun x => measure_lt_top _ _)]
      rfl
    have hΔi : Integrable (sepProb μ B s) P :=
      Integrable.of_bound hΔ.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sepProb_nonneg μ B s x)]
        exact sepProb_le_one μ B s x)
    have hind : Integrable (fun x => η + (1 - η) * E.indicator (fun _ => (1 : ℝ)) x) P :=
      (integrable_const η).add (((integrable_const (1 : ℝ)).indicator hE).const_mul _)
    have hp1 : p ≤ 1 := hp.trans measureReal_le_one
    have hmono : ∫ x, sepProb μ B s x ∂P ≤
        ∫ x, η + (1 - η) * E.indicator (fun _ => (1 : ℝ)) x ∂P := by
      refine integral_mono hΔi hind fun x => ?_
      by_cases hx : x ∈ E
      · simp only [Set.indicator_of_mem hx]
        linarith [sepProb_le_one μ B s x]
      · simp only [Set.indicator_of_notMem hx]
        have : sepProb μ B s x < η := not_le.mp hx
        linarith
    have hval : ∫ x, η + (1 - η) * E.indicator (fun _ => (1 : ℝ)) x ∂P =
        η + (1 - η) * P.real E := by
      rw [integral_add (integrable_const η) (((integrable_const (1 : ℝ)).indicator hE).const_mul _),
        integral_const_mul, integral_indicator hE]
      simp
    have h1η : 0 < 1 - η := by linarith
    rw [div_le_iff₀ h1η]
    rw [hint] at hp
    nlinarith [hp.trans (hmono.trans_eq hval)]
  · intro x hx Ω' _ ν _ c hc
    have hBx : Measurable (B x) := hB.comp (measurable_const.prodMk measurable_id)
    have hsx : Measurable (s x) := hs.comp (measurable_const.prodMk measurable_id)
    have := fail_ge_half_sepProb_rand μ B s x hBx hsx ν c hc
    linarith

end

end BstLean.Part131

open BstLean.Part131 in
#print axioms measurable_sepProb
open BstLean.Part131 in
#print axioms fail_ge_half_sepProb
open BstLean.Part131 in
#print axioms fail_ge_half_sepProb_rand
open BstLean.Part131 in
#print axioms noReadA_abstract
