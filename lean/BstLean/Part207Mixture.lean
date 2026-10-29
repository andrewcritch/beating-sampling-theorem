import BstLean.Part207Density
import BstLean.Part207Price
import BstLean.Part207Coefficients

/-! HQ for location-scale Gaussian mixtures, with the paper's price.
The density, two-copy product and event transfer reuse Part180's construction.
The new second/fourth moment estimate replaces Part180's split cubic price. -/
namespace BstLean.Part207
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part161
open BstLean.Part180

variable {V : Type*} [MeasurableSpace V]

theorem mix_hq_cubic {n : ℕ} (pm : Measure V) [IsProbabilityMeasure pm] (c : Fin n → ℝ)
    {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) {l0 S0 : ℝ} (hS0 : 0 < S0) {l S : V → ℝ}
    (hl : Measurable l) (hS : Measurable S) {ε₀ δ₀ : ℝ} (hε₀ : ε₀ < 1)
    (hwS : ∀ v, |S v / S0 - 1| ≤ ε₀) (hwl : ∀ v, |l v - l0| ≤ δ₀)
    (hml : ∫ v, (l v - l0) ∂pm = 0) (hmS : ∫ v, (S v / S0 - 1) ∂pm = 0)
    :
    BstLean.Part138.hellSq (stdGauss (Fin n))
      (fun z => ∫ v, gdN (muN c l0 S0 (l v)) (S v / S0) z ∂pm) (fun _ => 1) ≤
      (∫ w, kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1)
        (l w.2 - l0) (S w.2 / S0 - 1) ∂(pm.prod pm) - 1) / 4 +
      3 * hqL n ε₀ (∫ v, (S v / S0 - 1) ^ 2 ∂pm)
        (∫ v, normSq c / S0 * (l v - l0) ^ 2 ∂pm) ^ 3 ∧
    (√(∫ v, gP B (l v • c) (S v) ∂pm) - √(gP B (l0 • c) S0)) ^ 2 ≤
      (∫ w, kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1)
        (l w.2 - l0) (S w.2 / S0 - 1) ∂(pm.prod pm) - 1) / 4 +
      3 * hqL n ε₀ (∫ v, (S v / S0 - 1) ^ 2 ∂pm)
        (∫ v, normSq c / S0 * (l v - l0) ^ 2 ∂pm) ^ 3 := by

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
      refine iG.mono'
        ((measurable_one.indicator mB').comp measurable_snd |>.mul mg).aestronglyMeasurable
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
      (((hl.comp measurable_fst).sub_const l0).prodMk
          ((hS.comp measurable_fst).div_const S0 |>.sub_const 1)
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
  -- Lemma HQ
  obtain ⟨hK, hb, hc⟩ := mix_coef_bounds_sharp pm c hS0 hl hS hε₀ hwS hwl hml hmS
  set u : Fin n → ℝ := fun i => (√S0)⁻¹ * c i with hu
  have hu2 : ∑ i, u i ^ 2 = normSq c / S0 := by
    simp only [hu]
    unfold normSq
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, inv_pow, Real.sq_sqrt hS0.le]; ring
  have hJ : ∀ z, exp ((∫ v, (-(n / 2) * log (S v / S0) + n / 2 * (1 - 1 / (S v / S0)) -
        (l v - l0) ^ 2 * (normSq c / S0) / (2 * (S v / S0))) ∂pm) +
      (1 / 2 * (∫ v, (1 - 1 / (S v / S0)) ∂pm) * (∑ i, z i ^ 2 - n) +
        (∫ v, (l v - l0) / (S v / S0) ∂pm) * ∑ i, u i * z i)) ≤ R z := fun z => by
    have h := jensen_mix pm c hS0 hl hS hε₀ hwS hwl z
    simp only [hu, ← add_assoc]
    exact h
  let K := ∫ v, (-(n / 2) * log (S v / S0) + n / 2 * (1 - 1 / (S v / S0)) -
    (l v - l0) ^ 2 * (normSq c / S0) / (2 * (S v / S0))) ∂pm
  let bb := ∫ v, (1 - 1 / (S v / S0)) ∂pm
  let cc := ∫ v, (l v - l0) / (S v / S0) ∂pm
  let uc : Fin n → ℝ := fun i => cc * u i
  have hJ' : ∀ z, exp (K + (bb / 2) * (normSq z - n) + ∑ i, uc i * z i) ≤ R z := by
    intro z
    have hsum : ∑ i, uc i * z i = cc * ∑ i, u i * z i := by
      simp only [uc, Finset.mul_sum, mul_assoc]
    rw [hsum]
    convert hJ z using 1
    congr 1
    dsimp [K, bb, cc, normSq]
    ring
  have hH := hell_quadratic mR R0 iR i2 K (bb / 2) uc hJ'
  have huc : ∑ i, uc i ^ 2 = (normSq c / S0) * cc ^ 2 := by
    dsimp [uc]
    simp only [mul_pow, ← Finset.mul_sum]
    rw [hu2]
    ring
  rw [chi_identity, huc] at hH
  have htri := triangle_le_hqL hε₀
    (integral_nonneg fun v => sq_nonneg (S v / S0 - 1))
    (integral_nonneg fun v => mul_nonneg
      (div_nonneg (normSq_nonneg c) hS0.le) (sq_nonneg (l v - l0)))
    (div_nonneg (normSq_nonneg c) hS0.le) hK hb hc
  have hbound : BstLean.Part138.hellSq γ R (fun _ => 1) ≤
      (∫ w, kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1)
        (l w.2 - l0) (S w.2 / S0 - 1) ∂(pm.prod pm) - 1) / 4 +
      3 * hqL n ε₀ (∫ v, (S v / S0 - 1) ^ 2 ∂pm)
        (∫ v, normSq c / S0 * (l v - l0) ^ 2 ∂pm) ^ 3 := by
    refine hH.trans ?_
    gcongr <;> exact htri
  exact ⟨hbound, hroot.trans hbound⟩

theorem mix_root_hq_cubic {n : ℕ} (pm : Measure V) [IsProbabilityMeasure pm] (c : Fin n → ℝ)
    {B : Set (Fin n → ℝ)} (hB : MeasurableSet B) {l0 S0 : ℝ} (hS0 : 0 < S0) {l S : V → ℝ}
    (hl : Measurable l) (hS : Measurable S) {ε₀ δ₀ : ℝ} (hε₀ : ε₀ < 1)
    (hwS : ∀ v, |S v / S0 - 1| ≤ ε₀) (hwl : ∀ v, |l v - l0| ≤ δ₀)
    (hml : ∫ v, (l v - l0) ∂pm = 0) (hmS : ∫ v, (S v / S0 - 1) ∂pm = 0)
    :
    (√(∫ v, gP B (l v • c) (S v) ∂pm) - √(gP B (l0 • c) S0)) ^ 2 ≤
      (∫ w, kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1)
        (l w.2 - l0) (S w.2 / S0 - 1) ∂(pm.prod pm) - 1) / 4 +
      3 * hqL n ε₀ (∫ v, (S v / S0 - 1) ^ 2 ∂pm)
        (∫ v, normSq c / S0 * (l v - l0) ^ 2 ∂pm) ^ 3 := by
  exact (mix_hq_cubic pm c hB hS0 hl hS hε₀ hwS hwl hml hmS).2

theorem mix_density_hq_cubic {n : ℕ} (pm : Measure V) [IsProbabilityMeasure pm] (c : Fin n → ℝ)
    {l0 S0 : ℝ} (hS0 : 0 < S0) {l S : V → ℝ}
    (hl : Measurable l) (hS : Measurable S) {ε₀ δ₀ : ℝ} (hε₀ : ε₀ < 1)
    (hwS : ∀ v, |S v / S0 - 1| ≤ ε₀) (hwl : ∀ v, |l v - l0| ≤ δ₀)
    (hml : ∫ v, (l v - l0) ∂pm = 0) (hmS : ∫ v, (S v / S0 - 1) ∂pm = 0)
    :
    BstLean.Part138.hellSq (stdGauss (Fin n))
      (fun z => ∫ v, gdN (muN c l0 S0 (l v)) (S v / S0) z ∂pm) (fun _ => 1) ≤
      (∫ w, kTwo n (normSq c / S0) (l w.1 - l0) (S w.1 / S0 - 1)
        (l w.2 - l0) (S w.2 / S0 - 1) ∂(pm.prod pm) - 1) / 4 +
      3 * hqL n ε₀ (∫ v, (S v / S0 - 1) ^ 2 ∂pm)
        (∫ v, normSq c / S0 * (l v - l0) ^ 2 ∂pm) ^ 3 := by
  exact (mix_hq_cubic pm c MeasurableSet.empty hS0 hl hS hε₀ hwS hwl hml hmS).1

end BstLean.Part207
