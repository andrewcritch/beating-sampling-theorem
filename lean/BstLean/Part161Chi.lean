import BstLean.Part161Red

/-!
# Part 161, item 1(c): the chi-square of a location-scale Gaussian mixture against one Gaussian

Role: `delegations/statements/p161-spec.md`, item 1(c). Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, Lemma `t7:p07:chi-identity` (the
two-copy identity) and the first step of Corollary `t7:p07:chi-bounds` (a uniform window gives a
finite bound).

Setting: `π` is a probability measure on `V`; `P = E_π N(l(v) c, S(v) I)`, `Q = N(l₀ c, S₀ I)`.
Put `δ = l − l₀`, `ε = S/S₀ − 1`, `a² = |c|²/S₀`.

* `kTwo n a² δ ε δ' ε' = (1 − εε')^{−n/2}·exp(a²(2δδ' + δ²ε' + δ'²ε)/(2(1 − εε')))`: the paper's
  `e^T`, `T = −(n/2) log(1 − εε') + a²(2δδ' + δ²ε' + δ'²ε)/(2(1 − εε'))`.
* `twocopy_kTwo`: `∫ gdN μ gdN μ' dγ = kTwo …` for the normalized components.
* `kTwo_le`: the bound of `kTwo` in the window `|ε| ≤ ε₀ < 1`, `|δ| ≤ δ₀`.
* `chi_identity`: `∫ (R − 1)² dγ = E_{π⊗π} kTwo − 1` (`R` the density of `P` after the
  normalization of `Q` to the standard Gaussian distribution): the two-copy identity
  `1 + χ²(P ‖ Q) = E e^T`.
* **`mix_root_chi`**: for every measurable event `B`:
  `(√P(B) − √Q(B))² ≤ E_{π⊗π} kTwo − 1 = χ²(P ‖ Q)`.
-/

namespace BstLean.Part161

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)

/-- **The two-copy kernel** `e^T = (1 − εε')^{−n/2}·exp(a²(2δδ' + δ²ε' + δ'²ε)/(2(1 − εε')))`. -/
noncomputable def kTwo (n : ℕ) (a2 δ ε δ' ε' : ℝ) : ℝ :=
  (√(1 - ε * ε'))⁻¹ ^ n * exp (a2 * (2 * δ * δ' + δ ^ 2 * ε' + δ' ^ 2 * ε) / (2 * (1 - ε * ε')))

lemma kTwo_nonneg (n : ℕ) (a2 δ ε δ' ε' : ℝ) : 0 ≤ kTwo n a2 δ ε δ' ε' :=
  mul_nonneg (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _) (exp_pos _).le

lemma measurable_kTwo (n : ℕ) :
    Measurable (fun p : ℝ × (ℝ × ℝ) × (ℝ × ℝ) => kTwo n p.1 p.2.1.1 p.2.1.2 p.2.2.1 p.2.2.2) := by
  unfold kTwo
  fun_prop

/-- **The bound of the two-copy kernel in a uniform window**: `|ε|, |ε'| ≤ ε₀ < 1`,
`|δ|, |δ'| ≤ δ₀`, `a² ≥ 0`:
`kTwo ≤ (1 − ε₀²)^{−n/2}·exp((1 + ε₀) a² δ₀²/(1 − ε₀²))`. -/
theorem kTwo_le (n : ℕ) {a2 δ ε δ' ε' ε₀ δ₀ : ℝ} (ha : 0 ≤ a2) (hε₀ : ε₀ < 1)
    (hε : |ε| ≤ ε₀) (hε' : |ε'| ≤ ε₀) (hδ : |δ| ≤ δ₀) (hδ' : |δ'| ≤ δ₀) :
    kTwo n a2 δ ε δ' ε' ≤
      (√(1 - ε₀ ^ 2))⁻¹ ^ n * exp ((1 + ε₀) * a2 * δ₀ ^ 2 / (1 - ε₀ ^ 2)) := by
  have hε0 : 0 ≤ ε₀ := (abs_nonneg _).trans hε
  have hδ0 : 0 ≤ δ₀ := (abs_nonneg _).trans hδ
  have hee : |ε * ε'| ≤ ε₀ ^ 2 := by
    rw [abs_mul, sq]; exact mul_le_mul hε hε' (abs_nonneg _) hε0
  have hd0 : 0 < 1 - ε₀ ^ 2 := by nlinarith
  have hD : 1 - ε₀ ^ 2 ≤ 1 - ε * ε' := by
    have := (abs_le.mp hee).2; linarith
  have hDp : 0 < 1 - ε * ε' := lt_of_lt_of_le hd0 hD
  unfold kTwo
  refine mul_le_mul ?_ ?_ (exp_pos _).le (pow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
  · refine pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) ?_ n
    exact inv_anti₀ (Real.sqrt_pos.mpr hd0) (Real.sqrt_le_sqrt hD)
  · refine exp_le_exp.mpr ?_
    have hδ2 : δ ^ 2 ≤ δ₀ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hδ 2
    have hδ'2 : δ' ^ 2 ≤ δ₀ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hδ' 2
    have h1 : 2 * δ * δ' ≤ δ ^ 2 + δ' ^ 2 := by nlinarith [sq_nonneg (δ - δ')]
    have h2 : δ ^ 2 * ε' ≤ δ₀ ^ 2 * ε₀ :=
      calc δ ^ 2 * ε' ≤ δ ^ 2 * |ε'| := mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)
        _ ≤ δ₀ ^ 2 * ε₀ := mul_le_mul hδ2 hε' (abs_nonneg _) (sq_nonneg _)
    have h3 : δ' ^ 2 * ε ≤ δ₀ ^ 2 * ε₀ :=
      calc δ' ^ 2 * ε ≤ δ' ^ 2 * |ε| := mul_le_mul_of_nonneg_left (le_abs_self _) (sq_nonneg _)
        _ ≤ δ₀ ^ 2 * ε₀ := mul_le_mul hδ'2 hε (abs_nonneg _) (sq_nonneg _)
    have hN : a2 * (2 * δ * δ' + δ ^ 2 * ε' + δ' ^ 2 * ε) ≤ 2 * ((1 + ε₀) * a2 * δ₀ ^ 2) := by
      have : 2 * δ * δ' + δ ^ 2 * ε' + δ' ^ 2 * ε ≤ 2 * (1 + ε₀) * δ₀ ^ 2 := by nlinarith
      nlinarith
    have hX : 0 ≤ (1 + ε₀) * a2 * δ₀ ^ 2 := by positivity
    calc a2 * (2 * δ * δ' + δ ^ 2 * ε' + δ' ^ 2 * ε) / (2 * (1 - ε * ε'))
        ≤ 2 * ((1 + ε₀) * a2 * δ₀ ^ 2) / (2 * (1 - ε * ε')) :=
          div_le_div_of_nonneg_right hN (by positivity)
      _ = (1 + ε₀) * a2 * δ₀ ^ 2 / (1 - ε * ε') := by field_simp
      _ ≤ (1 + ε₀) * a2 * δ₀ ^ 2 / (1 - ε₀ ^ 2) := div_le_div_of_nonneg_left hX hd0 hD

variable {n : ℕ}

/-- The normalized location of a component: `μ = S₀^{−1/2}·(l − l₀)·c`. -/
noncomputable def muN (c : Fin n → ℝ) (l0 S0 l : ℝ) : Fin n → ℝ := (√S0)⁻¹ • ((l - l0) • c)

lemma normSq_muN (c : Fin n → ℝ) (l0 l : ℝ) {S0 : ℝ} (hS0 : 0 < S0) :
    normSq (muN c l0 S0 l) = normSq c / S0 * (l - l0) ^ 2 := by
  unfold muN
  rw [BstLean.Part130.normSq_smul, BstLean.Part130.normSq_smul, inv_pow, Real.sq_sqrt hS0.le]
  field_simp

lemma dot_muN (c : Fin n → ℝ) (l0 l l' : ℝ) {S0 : ℝ} (hS0 : 0 < S0) :
    ∑ i, muN c l0 S0 l i * muN c l0 S0 l' i = normSq c / S0 * ((l - l0) * (l' - l0)) := by
  unfold muN normSq
  rw [Finset.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  have h := Real.sq_sqrt hS0.le
  have h0 : √S0 ≠ 0 := (Real.sqrt_pos.mpr hS0).ne'
  field_simp
  rw [h]
  ring

/-- **The two-copy integral in the variables of the paper.** -/
theorem twocopy_kTwo (c : Fin n → ℝ) {l0 S0 : ℝ} (hS0 : 0 < S0) (l l' S S' : ℝ) (hS : 0 < S)
    (hS' : 0 < S') (hD : 0 < 1 - (S / S0 - 1) * (S' / S0 - 1)) :
    Integrable (fun z => gdN (muN c l0 S0 l) (S / S0) z * gdN (muN c l0 S0 l') (S' / S0) z)
        (stdGauss (Fin n)) ∧
      ∫ z, gdN (muN c l0 S0 l) (S / S0) z * gdN (muN c l0 S0 l') (S' / S0) z ∂stdGauss (Fin n) =
        kTwo n (normSq c / S0) (l - l0) (S / S0 - 1) (l' - l0) (S' / S0 - 1) := by
  have e : S / S0 + S' / S0 - S / S0 * (S' / S0) = 1 - (S / S0 - 1) * (S' / S0 - 1) := by ring
  have hD' : 0 < S / S0 + S' / S0 - S / S0 * (S' / S0) := by rw [e]; exact hD
  obtain ⟨h1, h2⟩ := twocopy_gdN (ι := Fin n) (muN c l0 S0 l) (muN c l0 S0 l')
    (div_pos hS hS0) (div_pos hS' hS0) hD'
  refine ⟨h1, ?_⟩
  rw [h2, e, Fintype.card_fin, dot_muN c l0 l l' hS0, normSq_muN c l0 l hS0,
    normSq_muN c l0 l' hS0]
  unfold kTwo
  congr 2
  ring

/-- The probability of `B` under `N(l c, S I)` as an integral of the normalized density, with
`B' = {z | l₀ c + √S₀ z ∈ B}`. -/
lemma gP_eq_dens (c : Fin n → ℝ) {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) {l0 S0 : ℝ}
    (hS0 : 0 < S0) (l S : ℝ) (hS : 0 < S) :
    gP B (l • c) S = ∫ z, {z | l0 • c + √S0 • z ∈ B}.indicator 1 z *
      gdN (muN c l0 S0 l) (S / S0) z ∂stdGauss (Fin n) := by
  have hs2 : 0 < √S0 := Real.sqrt_pos.mpr hS0
  set B' : Set (Fin n → ℝ) := {z | l0 • c + √S0 • z ∈ B} with hB'
  have mB' : MeasurableSet B' := ((measurable_const_smul (√S0)).const_add (l0 • c)) hB
  have e1 : {η : Fin n → ℝ | l • c + √S • η ∈ B} =
      {η | muN c l0 S0 l + √(S / S0) • η ∈ B'} := by
    ext η
    change l • c + √S • η ∈ B ↔ l0 • c + √S0 • (muN c l0 S0 l + √(S / S0) • η) ∈ B
    have : l0 • c + √S0 • (muN c l0 S0 l + √(S / S0) • η) = l • c + √S • η := by
      unfold muN
      rw [smul_add, smul_smul, mul_inv_cancel₀ hs2.ne', one_smul, smul_smul,
        ← Real.sqrt_mul hS0.le, mul_div_cancel₀ _ hS0.ne', sub_smul]
      abel
    rw [this]
  unfold gP
  rw [e1, gauss_event_density _ (div_pos hS hS0) mB']

section mixture

variable {V : Type*} [MeasurableSpace V]

/-- **The two-copy identity and the root comparison for a location-scale Gaussian mixture
(Lemma `t7:p07:chi-identity` with the window of Corollary `t7:p07:chi-bounds`).** `pm` is a
probability measure on `V`; `l`, `S` are measurable; `S₀ > 0`; the window `|S(v)/S₀ − 1| ≤ ε₀ < 1`
and `|l(v) − l₀| ≤ δ₀` holds for every `v`. Then for every measurable event `B`:
`(√(E_pm N(l c, S I)(B)) − √(N(l₀ c, S₀ I)(B)))² ≤ E_{pm⊗pm} kTwo − 1`, and the right side is
`χ²(P ‖ Q)` (`chi_identity` in the proof). -/
theorem mix_root_chi (pm : Measure V) [IsProbabilityMeasure pm] (c : Fin n → ℝ)
    {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) {l0 S0 : ℝ} (hS0 : 0 < S0) {l S : V → ℝ}
    (hl : Measurable l) (hS : Measurable S) {ε₀ δ₀ : ℝ} (hε₀ : ε₀ < 1)
    (hwS : ∀ v, |S v / S0 - 1| ≤ ε₀) (hwl : ∀ v, |l v - l0| ≤ δ₀) :
    (√(∫ v, gP B (l v • c) (S v) ∂pm) - √(gP B (l0 • c) S0)) ^ 2 ≤
      ∫ w, kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1) (l w.2 - l0) (S w.2 / S0 - 1)
        ∂(pm.prod pm) - 1 := by
  set γ := stdGauss (Fin n)
  have : Nonempty V := nonempty_of_isProbabilityMeasure pm
  have hε0 : 0 ≤ ε₀ := (abs_nonneg _).trans (hwS (Classical.arbitrary V))
  have hr : ∀ v, 0 < S v / S0 := fun v => by
    have := (abs_le.mp (hwS v)).1; linarith
  have hSp : ∀ v, 0 < S v := fun v => by
    have := hr v; rwa [div_pos_iff_of_pos_right hS0] at this
  set mu : V → Fin n → ℝ := fun v => muN c l0 S0 (l v) with hmu
  set r : V → ℝ := fun v => S v / S0 with hrd
  have mmu : Measurable mu := by
    simp only [hmu, muN]
    exact (measurable_const (a := (√S0)⁻¹)).smul ((hl.sub_const l0).smul_const c)
  have mr : Measurable r := hS.div_const S0
  set g : V → (Fin n → ℝ) → ℝ := fun v z => gdN (mu v) (r v) z with hg
  have mg : Measurable (Function.uncurry g) :=
    measurable_gdN_joint.comp (((mmu.comp measurable_fst).prodMk (mr.comp measurable_fst)).prodMk
      measurable_snd)
  have g0 : ∀ v z, 0 ≤ g v z := fun v z => gdN_nonneg _ _ _
  have ig : ∀ v, Integrable (g v) γ := fun v => integrable_gdN _ (hr v)
  have ig1 : ∀ v, ∫ z, g v z ∂γ = 1 := fun v => integral_gdN _ (hr v)
  -- the single product
  have iG : Integrable (Function.uncurry g) (pm.prod γ) := by
    refine (integrable_prod_iff mg.aestronglyMeasurable).mpr ⟨Filter.Eventually.of_forall ig, ?_⟩
    have e : (fun v => ∫ z, ‖Function.uncurry g (v, z)‖ ∂γ) = fun _ => (1 : ℝ) := by
      funext v
      simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_of_nonneg (g0 v _)]
      exact ig1 v
    rw [e]; exact integrable_const _
  set R : (Fin n → ℝ) → ℝ := fun z => ∫ v, g v z ∂pm with hR
  have mR : Measurable R := mg.stronglyMeasurable.integral_prod_left.measurable
  have R0 : ∀ z, 0 ≤ R z := fun z => integral_nonneg fun v => g0 v z
  have iR : Integrable R γ := iG.integral_prod_right
  have intR : ∫ z, R z ∂γ = 1 := by
    simp only [hR]
    rw [← integral_integral_swap iG]
    simp [ig1]
  -- the event
  set B' : Set (Fin n → ℝ) := {z | l0 • c + √S0 • z ∈ B} with hB'
  have mB' : MeasurableSet B' := ((measurable_const_smul (√S0)).const_add (l0 • c)) hB
  have hP : ∫ v, gP B (l v • c) (S v) ∂pm = ∫ z, B'.indicator 1 z * R z ∂γ := by
    have e1 : ∀ v, gP B (l v • c) (S v) = ∫ z, B'.indicator 1 z * g v z ∂γ := fun v =>
      gP_eq_dens c hB hS0 (l v) (S v) (hSp v)
    simp_rw [e1]
    have iH : Integrable (Function.uncurry fun v z => B'.indicator (1 : (Fin n → ℝ) → ℝ) z * g v z)
        (pm.prod γ) := by
      refine iG.mono' ((measurable_one.indicator mB').comp measurable_snd |>.mul mg).aestronglyMeasurable
        (Filter.Eventually.of_forall fun p => ?_)
      change ‖B'.indicator (1 : (Fin n → ℝ) → ℝ) p.2 * g p.1 p.2‖ ≤ g p.1 p.2
      rw [Real.norm_eq_abs]
      by_cases h : p.2 ∈ B'
      · simp [h, abs_of_nonneg (g0 p.1 p.2)]
      · simp [h, g0 p.1 p.2]
    rw [integral_integral_swap iH]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hR]
    rw [integral_const_mul]
  have hQ : gP B (l0 • c) S0 = ∫ z, B'.indicator 1 z * (fun _ => (1 : ℝ)) z ∂γ := by
    simp only [mul_one]
    rw [integral_indicator_one mB']
    rfl
  have hroot := root_dens_le γ (p := R) (q := fun _ => (1 : ℝ)) mR measurable_const R0
    (fun _ => zero_le_one) iR (integrable_const 1) mB'
  rw [← hP, ← hQ] at hroot
  -- the two-copy product
  set F : (V × V) × (Fin n → ℝ) → ℝ := fun p => g p.1.1 p.2 * g p.1.2 p.2 with hF
  have mF : Measurable F :=
    (mg.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)).mul
      (mg.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  have hDw : ∀ w : V × V, 0 < 1 - (S w.1 / S0 - 1) * (S w.2 / S0 - 1) := fun w => by
    have h1 := hwS w.1
    have h2 := hwS w.2
    have : |(S w.1 / S0 - 1) * (S w.2 / S0 - 1)| ≤ ε₀ ^ 2 := by
      rw [abs_mul, sq]; exact mul_le_mul h1 h2 (abs_nonneg _) hε0
    have := (abs_le.mp this).2
    nlinarith
  have tw : ∀ w : V × V, Integrable (fun z => F (w, z)) γ ∧ ∫ z, F (w, z) ∂γ =
      kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1) (l w.2 - l0) (S w.2 / S0 - 1) :=
    fun w => twocopy_kTwo c hS0 (l w.1) (l w.2) (S w.1) (S w.2) (hSp _) (hSp _) (hDw w)
  set M := (√(1 - ε₀ ^ 2))⁻¹ ^ n * exp ((1 + ε₀) * (normSq c / S0) * δ₀ ^ 2 / (1 - ε₀ ^ 2))
  have hK : ∀ w : V × V, kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1) (l w.2 - l0)
      (S w.2 / S0 - 1) ≤ M := fun w =>
    kTwo_le n (div_nonneg (normSq_nonneg c) hS0.le) hε₀ (hwS _) (hwS _) (hwl _) (hwl _)
  have mK : Measurable (fun w : V × V => kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1)
      (l w.2 - l0) (S w.2 / S0 - 1)) := by
    refine (measurable_kTwo n).comp (measurable_const.prodMk
      (((hl.comp measurable_fst).sub_const l0).prodMk ((hS.comp measurable_fst).div_const S0 |>.sub_const 1)
        |>.prodMk (((hl.comp measurable_snd).sub_const l0).prodMk
          ((hS.comp measurable_snd).div_const S0 |>.sub_const 1))))
  have iK : Integrable (fun w : V × V => kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1)
      (l w.2 - l0) (S w.2 / S0 - 1)) (pm.prod pm) :=
    Integrable.of_bound mK.aestronglyMeasurable M (Filter.Eventually.of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (kTwo_nonneg _ _ _ _ _ _)]; exact hK w)
  have F0 : ∀ p, 0 ≤ F p := fun p => mul_nonneg (g0 _ _) (g0 _ _)
  have iF : Integrable F ((pm.prod pm).prod γ) := by
    refine (integrable_prod_iff mF.aestronglyMeasurable).mpr
      ⟨Filter.Eventually.of_forall fun w => (tw w).1, ?_⟩
    have e : (fun w => ∫ z, ‖F (w, z)‖ ∂γ) = fun w =>
        kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1) (l w.2 - l0) (S w.2 / S0 - 1) := by
      funext w
      simp only [Real.norm_eq_abs, abs_of_nonneg (F0 _)]
      exact (tw w).2
    rw [e]; exact iK
  have hR2 : ∀ z, R z ^ 2 = ∫ w, F (w, z) ∂(pm.prod pm) := fun z => by
    simp only [hF, hR]
    rw [integral_prod_mul (fun v => g v z) (fun v => g v z)]
    ring
  have iR2 : Integrable (fun z => R z ^ 2) γ := by
    simp_rw [hR2]; exact iF.integral_prod_right
  have intR2 : ∫ z, R z ^ 2 ∂γ = ∫ w, kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1)
      (l w.2 - l0) (S w.2 / S0 - 1) ∂(pm.prod pm) := by
    simp_rw [hR2]
    rw [← integral_integral_swap (f := fun w z => F (w, z)) iF]
    exact integral_congr_ae (Filter.Eventually.of_forall fun w => (tw w).2)
  have i2 : Integrable (fun z => (R z - 1) ^ 2) γ := by
    have e : (fun z => (R z - 1) ^ 2) = fun z => R z ^ 2 - 2 * R z + 1 := by funext z; ring
    rw [e]; exact (iR2.sub (iR.const_mul 2)).add (integrable_const 1)
  have chi_identity : ∫ z, (R z - 1) ^ 2 ∂γ = ∫ w, kTwo n (normSq c / S0) (l w.1 - l0)
      (S w.1 / S0 - 1) (l w.2 - l0) (S w.2 / S0 - 1) ∂(pm.prod pm) - 1 := by
    have e : (fun z => (R z - 1) ^ 2) = fun z => R z ^ 2 - 2 * R z + 1 := by funext z; ring
    rw [e, integral_add (f := fun z => R z ^ 2 - 2 * R z) (g := fun _ => (1 : ℝ))
      (iR2.sub (iR.const_mul 2)) (integrable_const 1),
      integral_sub (f := fun z => R z ^ 2) (g := fun z => 2 * R z) iR2 (iR.const_mul 2),
      integral_const_mul, intR, intR2]
    simp
    ring
  have hchi := hellSq_le_chi γ mR R0 iR i2
  rw [chi_identity] at hchi
  exact hroot.trans hchi

end mixture

end BstLean.Part161

open BstLean.Part161 in
#print axioms twocopy_kTwo
open BstLean.Part161 in
#print axioms kTwo_le
open BstLean.Part161 in
#print axioms mix_root_chi
