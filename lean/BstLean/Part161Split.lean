import BstLean.Part161Root

/-!
# Part 161, item 1(d): the split of the root into its parts (abstract kernels, no network)

Role: `delegations/statements/p161-spec.md`. Do not use `sorry`, `native_decide` or `axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, Lemma `t7:p07:split`.

Setting. `(A, μ)` is the probability space of the indices (the latitude), `(V, ν)` the probability
space of the directions; the pair `(a, v)` has the product distribution. One event is fixed.
`p (a, v)` is the probability of the event under the component of the pair `(a, v)`;
`q0 a`, `qb a`, `qt a` are the probabilities of the event under three reference distributions of
the index `a` (the paper: `Q_s`, `Q̄_s`, `Q̃_s`). `good` is the good set, `I` the bulk set of
indices, `η` the level of the removed mass.

* `removed ν good a = ν{v | (a, v) ∉ good}`: the removed mass `β(a)`.
* `keptSet ν good I η = {a ∈ I | β(a) ≤ η}`: the kept indices.
* `goodMean ν good p a`: the probability of the event under the normalized good-set mixture
  `P_a^g` (the paper: `E[· | a, 𝒳_a]`).
* **`root_split`**: `|√(E p) − √(E qt)| ≤ √(2(1 + 1/η)B) + √(E_kept K_χ) + √(E_kept K_D) +
  √(E_kept K_B) + √(2 m_tail)`.
-/

namespace BstLean.Part161

open MeasureTheory ProbabilityTheory Real

variable {A V : Type*} [MeasurableSpace A] [MeasurableSpace V]

/-- **The removed mass** `β(a) = ν{v | (a, v) ∉ good}`. -/
noncomputable def removed (ν : Measure V) (good : Set (A × V)) (a : A) : ℝ :=
  ν.real {v | (a, v) ∉ good}

/-- **The kept indices**: `a` in the bulk set `I` with removed mass at most `η`. -/
def keptSet (ν : Measure V) (good : Set (A × V)) (I : Set A) (η : ℝ) : Set A :=
  {a | a ∈ I ∧ removed ν good a ≤ η}

/-- **The probability of the event under the normalized good-set mixture**:
`(∫_{good_a} p (a, v) dν(v))/(1 − β(a))`. -/
noncomputable def goodMean (ν : Measure V) (good : Set (A × V)) (p : A × V → ℝ) (a : A) : ℝ :=
  (∫ v, good.indicator p (a, v) ∂ν) / (1 - removed ν good a)

omit [MeasurableSpace A] in
lemma removed_nonneg (ν : Measure V) (good : Set (A × V)) (a : A) : 0 ≤ removed ν good a :=
  measureReal_nonneg

omit [MeasurableSpace A] in
lemma removed_le_one (ν : Measure V) [IsProbabilityMeasure ν] (good : Set (A × V)) (a : A) :
    removed ν good a ≤ 1 := measureReal_le_one

lemma measurable_removed (ν : Measure V) [IsProbabilityMeasure ν] {good : Set (A × V)}
    (hgood : MeasurableSet good) : Measurable (removed ν good) :=
  (measurable_measure_prodMk_left (ν := ν) hgood.compl).ennreal_toReal

lemma measurableSet_keptSet (ν : Measure V) [IsProbabilityMeasure ν] {good : Set (A × V)}
    (hgood : MeasurableSet good) {I : Set A} (hI : MeasurableSet I) (η : ℝ) :
    MeasurableSet (keptSet ν good I η) :=
  hI.inter (measurableSet_le (measurable_removed ν hgood) measurable_const)

lemma measurable_goodMean (ν : Measure V) [IsProbabilityMeasure ν] {good : Set (A × V)}
    (hgood : MeasurableSet good) {p : A × V → ℝ} (hp : Measurable p) :
    Measurable (goodMean ν good p) := by
  unfold goodMean
  exact ((hp.indicator hgood).stronglyMeasurable.integral_prod_right').measurable.div
    (measurable_const.sub (measurable_removed ν hgood))

/-- The parts of the mean at one index: `0 ≤ ∫_{good} p ≤ 1 − β` and
`0 ≤ ∫ p − ∫_{good} p ≤ β`. -/
lemma good_parts (ν : Measure V) [IsProbabilityMeasure ν] {good : Set (A × V)}
    (hgood : MeasurableSet good) {p : A × V → ℝ} (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∀ x, p x ≤ 1) (a : A) :
    0 ≤ ∫ v, good.indicator p (a, v) ∂ν ∧
      ∫ v, good.indicator p (a, v) ∂ν ≤ 1 - removed ν good a ∧
      0 ≤ ∫ v, p (a, v) ∂ν - ∫ v, good.indicator p (a, v) ∂ν ∧
      ∫ v, p (a, v) ∂ν - ∫ v, good.indicator p (a, v) ∂ν ≤ removed ν good a := by
  have bd : ∀ {Z : V → ℝ}, Measurable Z → (∀ v, 0 ≤ Z v) → (∀ v, Z v ≤ 1) → Integrable Z ν :=
    fun {Z} hZ h0 h1 => Integrable.of_bound hZ.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun v => by
        rw [Real.norm_eq_abs, abs_of_nonneg (h0 v)]; exact h1 v)
  have mpa : Measurable (fun v => p (a, v)) := hp.comp measurable_prodMk_left
  have mga : Measurable (fun v => good.indicator p (a, v)) :=
    (hp.indicator hgood).comp measurable_prodMk_left
  have g0 : ∀ v, 0 ≤ good.indicator p (a, v) := fun v => Set.indicator_nonneg (fun x _ => hp0 x) _
  have gle : ∀ v, good.indicator p (a, v) ≤ p (a, v) := fun v => by
    by_cases h : (a, v) ∈ good
    · rw [Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem h]; exact hp0 _
  have ip := bd mpa (fun v => hp0 _) (fun v => hp1 _)
  have ig := bd mga g0 (fun v => (gle v).trans (hp1 _))
  set Sb : Set V := {v | (a, v) ∉ good} with hSb
  have mSb : MeasurableSet Sb := (hgood.compl).preimage measurable_prodMk_left
  have hβ : removed ν good a = ∫ v, Sb.indicator (1 : V → ℝ) v ∂ν := by
    rw [integral_indicator_one mSb]; rfl
  have iSb : Integrable (Sb.indicator (1 : V → ℝ)) ν := (integrable_const (1 : ℝ)).indicator mSb
  refine ⟨integral_nonneg g0, ?_, ?_, ?_⟩
  · have h1 : ∫ v, good.indicator p (a, v) ∂ν ≤ ∫ v, 1 - Sb.indicator (1 : V → ℝ) v ∂ν := by
      refine integral_mono ig ((integrable_const 1).sub iSb) (fun v => ?_)
      change good.indicator p (a, v) ≤ 1 - Sb.indicator (1 : V → ℝ) v
      by_cases h : (a, v) ∈ good
      · have h' : v ∉ Sb := fun h2 => h2 h
        rw [Set.indicator_of_mem h, Set.indicator_of_notMem h']
        simpa using hp1 (a, v)
      · have h' : v ∈ Sb := h
        rw [Set.indicator_of_notMem h, Set.indicator_of_mem h']
        simp
    rw [integral_sub (integrable_const 1) iSb] at h1
    simpa [hβ] using h1
  · rw [← integral_sub ip ig]
    exact integral_nonneg fun v => sub_nonneg.mpr (gle v)
  · rw [← integral_sub ip ig, hβ]
    refine integral_mono (ip.sub ig) iSb (fun v => ?_)
    change p (a, v) - good.indicator p (a, v) ≤ Sb.indicator (1 : V → ℝ) v
    by_cases h : (a, v) ∈ good
    · have h' : v ∉ Sb := fun h2 => h2 h
      rw [Set.indicator_of_mem h, Set.indicator_of_notMem h']
      simp
    · have h' : v ∈ Sb := h
      rw [Set.indicator_of_notMem h, Set.indicator_of_mem h']
      simpa using hp1 (a, v)

/-- At an index with removed mass `β < 1`: the good-set mean is in `[0, 1]`, and
`(√(∫ p dν) − √(goodMean))² ≤ β`. -/
lemma goodMean_bounds (ν : Measure V) [IsProbabilityMeasure ν] {good : Set (A × V)}
    (hgood : MeasurableSet good) {p : A × V → ℝ} (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∀ x, p x ≤ 1) (a : A) (hβ : removed ν good a < 1) :
    0 ≤ goodMean ν good p a ∧ goodMean ν good p a ≤ 1 ∧
      (√(∫ v, p (a, v) ∂ν) - √(goodMean ν good p a)) ^ 2 ≤ removed ν good a := by
  obtain ⟨h1, h2, h3, h4⟩ := good_parts ν hgood hp hp0 hp1 a
  have hm : 0 < 1 - removed ν good a := by linarith
  have hβ0 := removed_nonneg ν good a
  set g := ∫ v, good.indicator p (a, v) ∂ν with hg
  set β := removed ν good a with hβd
  have e : goodMean ν good p a = g / (1 - β) := rfl
  have hgm0 : 0 ≤ g / (1 - β) := div_nonneg h1 hm.le
  have hgm1 : g / (1 - β) ≤ 1 := (div_le_one hm).mpr h2
  have hX0 : 0 ≤ ∫ v, p (a, v) ∂ν := integral_nonneg fun v => hp0 _
  rw [e]
  refine ⟨hgm0, hgm1, (sqrt_sub_sq_le_abs hX0 hgm0).trans ?_⟩
  have e2 : g = (1 - β) * (g / (1 - β)) := by field_simp
  rw [abs_le]
  constructor <;> nlinarith

/-- `√(x + y) ≤ √x + √y`. -/
lemma sqrt_add_le' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : √(x + y) ≤ √x + √y := by
  rw [Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

/-- **The replacement split (Lemma `t7:p07:split`) for one event and abstract kernels.**
`(a, v)` has the product distribution `μ ⊗ ν`. `p (a, v)`, `q0 a`, `qb a`, `qt a` are
probabilities of one event (values in `[0, 1]`, measurable). `B ≥ E β`, `m_tail ≥ μ(Iᶜ)`,
`0 < η < 1`. On each kept index `a` (in `I`, with `β(a) ≤ η`):
`(√(P_a^g) − √(q0 a))² ≤ K_χ(a)`, `(√(q0 a) − √(qb a))² ≤ K_D(a)`,
`(√(qb a) − √(qt a))² ≤ K_B(a)`. THEN
`|√(E p) − √(E qt)| ≤ √(2(1 + 1/η)B) + √(E[1_kept K_χ]) + √(E[1_kept K_D]) + √(E[1_kept K_B]) +
√(2 m_tail)`. -/
theorem root_split (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure V)
    [IsProbabilityMeasure ν] {p : A × V → ℝ} (hp : Measurable p) (hp0 : ∀ x, 0 ≤ p x)
    (hp1 : ∀ x, p x ≤ 1) {good : Set (A × V)} (hgood : MeasurableSet good) {I : Set A}
    (hI : MeasurableSet I) {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) {q0 qb qt : A → ℝ}
    (mq0 : Measurable q0) (mqb : Measurable qb) (mqt : Measurable qt)
    (hq0 : ∀ a, 0 ≤ q0 a ∧ q0 a ≤ 1) (hqb : ∀ a, 0 ≤ qb a ∧ qb a ≤ 1)
    (hqt : ∀ a, 0 ≤ qt a ∧ qt a ≤ 1) {Kχ KD KB : A → ℝ}
    (iχ : IntegrableOn Kχ (keptSet ν good I η) μ) (iD : IntegrableOn KD (keptSet ν good I η) μ)
    (iB : IntegrableOn KB (keptSet ν good I η) μ) {B mtail : ℝ}
    (hB : ∫ a, removed ν good a ∂μ ≤ B) (htail : μ.real Iᶜ ≤ mtail)
    (hχ : ∀ a ∈ keptSet ν good I η, (√(goodMean ν good p a) - √(q0 a)) ^ 2 ≤ Kχ a)
    (hD : ∀ a ∈ keptSet ν good I η, (√(q0 a) - √(qb a)) ^ 2 ≤ KD a)
    (hBi : ∀ a ∈ keptSet ν good I η, (√(qb a) - √(qt a)) ^ 2 ≤ KB a) :
    |√(∫ a, ∫ v, p (a, v) ∂ν ∂μ) - √(∫ a, qt a ∂μ)| ≤
      √(2 * (1 + η⁻¹) * B) + √(∫ a in keptSet ν good I η, Kχ a ∂μ) +
        √(∫ a in keptSet ν good I η, KD a ∂μ) + √(∫ a in keptSet ν good I η, KB a ∂μ) +
        √(2 * mtail) := by
  classical
  set K := keptSet ν good I η with hK
  have mK : MeasurableSet K := measurableSet_keptSet ν hgood hI η
  set β : A → ℝ := removed ν good with hβ
  have mβ : Measurable β := measurable_removed ν hgood
  have β0 : ∀ a, 0 ≤ β a := removed_nonneg ν good
  have β1 : ∀ a, β a ≤ 1 := removed_le_one ν good
  have iβ : Integrable β μ := Integrable.of_bound mβ.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun a => by
      rw [Real.norm_eq_abs, abs_of_nonneg (β0 a)]; exact β1 a)
  have hKβ : ∀ a ∈ K, β a < 1 := fun a ha => lt_of_le_of_lt ha.2 hη1
  -- the five families
  set X0 : A → ℝ := fun a => ∫ v, p (a, v) ∂ν with hX0
  set X1 : A → ℝ := K.piecewise (goodMean ν good p) qt with hX1
  set X2 : A → ℝ := K.piecewise q0 qt with hX2
  set X3 : A → ℝ := K.piecewise qb qt with hX3
  have mX0 : Measurable X0 := hp.stronglyMeasurable.integral_prod_right'.measurable
  have mX1 : Measurable X1 := (measurable_goodMean ν hgood hp).piecewise mK mqt
  have mX2 : Measurable X2 := mq0.piecewise mK mqt
  have mX3 : Measurable X3 := mqb.piecewise mK mqt
  have bX0 : ∀ a, 0 ≤ X0 a ∧ X0 a ≤ 1 := fun a =>
    ⟨integral_nonneg fun v => hp0 _, by
      have h := integral_mono_of_nonneg (μ := ν) (f := fun v => p (a, v)) (g := fun _ => (1 : ℝ))
        (Filter.Eventually.of_forall fun v => hp0 _) (integrable_const 1)
        (Filter.Eventually.of_forall fun v => hp1 _)
      simpa using h⟩
  have bX1 : ∀ a, 0 ≤ X1 a ∧ X1 a ≤ 1 := fun a => by
    by_cases h : a ∈ K
    · simp only [hX1, Set.piecewise_eq_of_mem _ _ _ h]
      obtain ⟨h1, h2, _⟩ := goodMean_bounds ν hgood hp hp0 hp1 a (hKβ a h)
      exact ⟨h1, h2⟩
    · simp only [hX1, Set.piecewise_eq_of_notMem _ _ _ h]; exact hqt a
  have bX2 : ∀ a, 0 ≤ X2 a ∧ X2 a ≤ 1 := fun a => by
    by_cases h : a ∈ K
    · simp only [hX2, Set.piecewise_eq_of_mem _ _ _ h]; exact hq0 a
    · simp only [hX2, Set.piecewise_eq_of_notMem _ _ _ h]; exact hqt a
  have bX3 : ∀ a, 0 ≤ X3 a ∧ X3 a ≤ 1 := fun a => by
    by_cases h : a ∈ K
    · simp only [hX3, Set.piecewise_eq_of_mem _ _ _ h]; exact hqb a
    · simp only [hX3, Set.piecewise_eq_of_notMem _ _ _ h]; exact hqt a
  -- step 0 → 1: the removed mass and the discarded indices
  set K01 : A → ℝ := fun a => 2 * β a + 2 * Kᶜ.indicator (1 : A → ℝ) a with hK01
  have iKc : Integrable (Kᶜ.indicator (1 : A → ℝ)) μ := (integrable_const (1 : ℝ)).indicator mK.compl
  have iK01 : Integrable K01 μ := (iβ.const_mul 2).add (iKc.const_mul 2)
  have p01 : ∀ a, (√(X0 a) - √(X1 a)) ^ 2 ≤ K01 a := fun a => by
    by_cases h : a ∈ K
    · have h' : a ∉ Kᶜ := fun h2 => h2 h
      simp only [hX1, hK01, Set.piecewise_eq_of_mem _ _ _ h, Set.indicator_of_notMem h']
      obtain ⟨_, _, h3⟩ := goodMean_bounds ν hgood hp hp0 hp1 a (hKβ a h)
      have := β0 a
      linarith
    · have h' : a ∈ Kᶜ := h
      simp only [hK01, Set.indicator_of_mem h', Pi.one_apply]
      have := sqrt_sub_sq_le_one (bX0 a).1 (bX0 a).2 (bX1 a).1 (bX1 a).2
      have := β0 a
      linarith
  have d01 := root_mix_abs μ mX0 mX1 (fun a => (bX0 a).1) (fun a => (bX0 a).2)
    (fun a => (bX1 a).1) (fun a => (bX1 a).2) iK01 p01
  have hB0 : 0 ≤ B := (integral_nonneg β0).trans hB
  have hm0 : 0 ≤ mtail := measureReal_nonneg.trans htail
  have hmarkov : μ.real {a | η < β a} ≤ B / η := by
    have h1 := mul_meas_ge_le_integral_of_nonneg (μ := μ) (Filter.Eventually.of_forall β0) iβ η
    have h2 : μ.real {a | η < β a} ≤ μ.real {a | η ≤ β a} :=
      measureReal_mono (fun a (ha : η < β a) => ha.le)
    rw [le_div_iff₀ hη0]
    nlinarith
  have hKc : μ.real Kᶜ ≤ mtail + B / η := by
    have hsub : Kᶜ ⊆ Iᶜ ∪ {a | η < β a} := by
      intro a ha
      by_cases hIa : a ∈ I
      · right
        by_contra hcon
        exact ha ⟨hIa, not_lt.mp hcon⟩
      · left; exact hIa
    calc μ.real Kᶜ ≤ μ.real (Iᶜ ∪ {a | η < β a}) := measureReal_mono hsub
      _ ≤ μ.real Iᶜ + μ.real {a | η < β a} := measureReal_union_le _ _
      _ ≤ mtail + B / η := add_le_add htail hmarkov
  have eK01 : ∫ a, K01 a ∂μ ≤ 2 * (1 + η⁻¹) * B + 2 * mtail := by
    have e : ∫ a, K01 a ∂μ = 2 * ∫ a, β a ∂μ + 2 * μ.real Kᶜ := by
      simp only [hK01]
      rw [integral_add (iβ.const_mul 2) (iKc.const_mul 2), integral_const_mul,
        integral_const_mul, integral_indicator_one mK.compl]
    rw [e]
    have : B / η = η⁻¹ * B := by rw [div_eq_mul_inv, mul_comm]
    nlinarith
  have d01' : |√(∫ a, X0 a ∂μ) - √(∫ a, X1 a ∂μ)| ≤ √(2 * (1 + η⁻¹) * B) + √(2 * mtail) := by
    refine d01.trans ((Real.sqrt_le_sqrt eK01).trans (sqrt_add_le' ?_ ?_))
    · have : 0 < η⁻¹ := inv_pos.mpr hη0
      positivity
    · positivity
  -- steps on the kept indices
  have stepK : ∀ {Y Z Kf : A → ℝ}, Measurable Y → Measurable Z → (∀ a, 0 ≤ Y a ∧ Y a ≤ 1) →
      (∀ a, 0 ≤ Z a ∧ Z a ≤ 1) → IntegrableOn Kf K μ →
      (∀ a ∈ K, (√(Y a) - √(Z a)) ^ 2 ≤ Kf a) → (∀ a, a ∉ K → Y a = Z a) →
      |√(∫ a, Y a ∂μ) - √(∫ a, Z a ∂μ)| ≤ √(∫ a in K, Kf a ∂μ) := by
    intro Y Z Kf mY mZ bY bZ iKf hle heq
    have h := root_mix_abs μ mY mZ (fun a => (bY a).1) (fun a => (bY a).2)
      (fun a => (bZ a).1) (fun a => (bZ a).2) (K := K.indicator Kf)
      ((integrable_indicator_iff mK).mpr iKf) (fun a => by
        by_cases h : a ∈ K
        · rw [Set.indicator_of_mem h]; exact hle a h
        · rw [Set.indicator_of_notMem h, heq a h]; simp)
    rwa [integral_indicator mK] at h
  have d12 := stepK mX1 mX2 bX1 bX2 iχ
    (fun a h => by simpa only [hX1, hX2, Set.piecewise_eq_of_mem _ _ _ h] using hχ a h)
    (fun a h => by simp only [hX1, hX2, Set.piecewise_eq_of_notMem _ _ _ h])
  have d23 := stepK mX2 mX3 bX2 bX3 iD
    (fun a h => by simpa only [hX2, hX3, Set.piecewise_eq_of_mem _ _ _ h] using hD a h)
    (fun a h => by simp only [hX2, hX3, Set.piecewise_eq_of_notMem _ _ _ h])
  have d34 := stepK mX3 mqt bX3 hqt iB
    (fun a h => by simpa only [hX3, Set.piecewise_eq_of_mem _ _ _ h] using hBi a h)
    (fun a h => by simp only [hX3, Set.piecewise_eq_of_notMem _ _ _ h])
  -- the triangle inequality
  have t1 := abs_sub_le (√(∫ a, X0 a ∂μ)) (√(∫ a, X1 a ∂μ)) (√(∫ a, qt a ∂μ))
  have t2 := abs_sub_le (√(∫ a, X1 a ∂μ)) (√(∫ a, X2 a ∂μ)) (√(∫ a, qt a ∂μ))
  have t3 := abs_sub_le (√(∫ a, X2 a ∂μ)) (√(∫ a, X3 a ∂μ)) (√(∫ a, qt a ∂μ))
  linarith

end BstLean.Part161

open BstLean.Part161 in
#print axioms root_split
