import BstLean.Part154Rad

namespace BstLean.Part219
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152 BstLean.Part153

private lemma cs_Rad {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable (fun x => f x ^ 2) μ) (hg : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have key : ∀ s : ℝ, 0 ≤ (∫ x, f x ^ 2 ∂μ) * (s * s) + 2 * (∫ x, f x * g x ∂μ) * s +
      ∫ x, g x ^ 2 ∂μ := by
    intro s
    have h0 : 0 ≤ ∫ x, (s * f x + g x) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
    have e : (fun x => (s * f x + g x) ^ 2) =
        fun x => s * s * f x ^ 2 + 2 * s * (f x * g x) + g x ^ 2 := by
      funext x; ring
    rw [e, integral_add (show Integrable (fun x => s * s * f x ^ 2 + 2 * s * (f x * g x)) μ from
        (hf.const_mul _).add (hfg.const_mul _)) hg,
      integral_add (hf.const_mul _) (hfg.const_mul _), integral_const_mul,
      integral_const_mul] at h0
    linarith
  have h := discrim_le_zero key
  unfold discrim at h
  nlinarith

private lemma abs_cs_Rad {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable (fun x => f x ^ 2) μ) (hg : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    |∫ x, f x * g x ∂μ| ≤ √(∫ x, f x ^ 2 ∂μ) * √(∫ x, g x ^ 2 ∂μ) := by
  rw [← Real.sqrt_mul (integral_nonneg fun x => sq_nonneg _)]
  exact Real.abs_le_sqrt (cs_Rad hf hg hfg)

private lemma int_mul_bdd_Rad {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    {C : ℝ} (hf : Integrable f μ) (hg : Measurable g) (hb : ∀ x, |g x| ≤ C) :
    Integrable (fun x => f x * g x) μ := by
  refine (hf.norm.mul_const C).mono' (hf.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hb x) (abs_nonneg _)

/-- The radius `|y|`, `y = c + τξ`: mean `M` with `ρ − τ²/ρ ≤ M ≤ ρ` and variance `≤ τ²`. -/
theorem radius_stats {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun ξ : Fin n → ℝ => nrm (c + τ • ξ)) (stdGauss (Fin n)) ∧
    Integrable (fun ξ : Fin n → ℝ => (nrm (c + τ • ξ) -
      ∫ ξ', nrm (c + τ • ξ') ∂stdGauss (Fin n)) ^ 2) (stdGauss (Fin n)) ∧
    ∫ ξ : Fin n → ℝ, (nrm (c + τ • ξ) -
      ∫ ξ', nrm (c + τ • ξ') ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤ τ ^ 2 ∧
    rhoC c τ - τ ^ 2 / rhoC c τ ≤ ∫ ξ, nrm (c + τ • ξ) ∂stdGauss (Fin n) ∧
    ∫ ξ, nrm (c + τ • ξ) ∂stdGauss (Fin n) ≤ rhoC c τ := by
  have hlip : BstLean.Part148.EuLip (fun ξ : Fin n → ℝ => nrm (c + τ • ξ)) τ := by
    intro x y
    have h := BstLean.Part153.abs_nrm_sub_le (c + τ • x) (c + τ • y)
    have e : c + τ • x - (c + τ • y) = τ • (x - y) := by
      funext i; simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [e, BstLean.Part153.nrm_smul, abs_of_pos hτ] at h
    exact h
  obtain ⟨hvi, hv⟩ := gaussVar_le_sharp hτ.le hlip
  obtain ⟨hsqi, hsq⟩ := BstLean.Part153.int_normSq_shift c τ
  have hmeas : Measurable (fun ξ : Fin n → ℝ => nrm (c + τ • ξ)) := by
    unfold nrm
    exact (continuous_normSq.measurable.comp
      (measurable_const.add (measurable_const_smul τ))).sqrt
  have hRi : Integrable (fun ξ : Fin n → ℝ => nrm (c + τ • ξ)) (stdGauss (Fin n)) := by
    refine ((integrable_const (1 : ℝ)).add hsqi).mono' hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    have h0 := BstLean.Part153.nrm_nonneg (c + τ • ξ)
    have h2 := BstLean.Part153.nrm_sq (c + τ • ξ)
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (nrm (c + τ • ξ) - 1)]
  set M := ∫ ξ', nrm (c + τ • ξ') ∂stdGauss (Fin n) with hM
  have hρ2 : rhoC c τ ^ 2 = normSq c + (n : ℝ) * τ ^ 2 := by
    unfold rhoC
    exact Real.sq_sqrt (add_nonneg (normSq_nonneg c) (by positivity))
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hτρ : τ ^ 2 ≤ rhoC c τ ^ 2 := by
    rw [hρ2]; nlinarith [normSq_nonneg c, sq_nonneg τ]
  have hρ0 : 0 < rhoC c τ := by
    unfold rhoC
    exact Real.sqrt_pos.mpr (by nlinarith [normSq_nonneg c, sq_pos_of_pos hτ])
  have evar : ∫ ξ : Fin n → ℝ, (nrm (c + τ • ξ) - M) ^ 2 ∂stdGauss (Fin n) =
      rhoC c τ ^ 2 - M ^ 2 := by
    have e : (fun ξ : Fin n → ℝ => (nrm (c + τ • ξ) - M) ^ 2) =
        fun ξ => normSq (c + τ • ξ) - 2 * M * nrm (c + τ • ξ) + M ^ 2 := by
      funext ξ
      rw [← BstLean.Part153.nrm_sq (c + τ • ξ)]; ring
    rw [e, integral_add (show Integrable (fun ξ : Fin n → ℝ =>
        normSq (c + τ • ξ) - 2 * M * nrm (c + τ • ξ)) (stdGauss (Fin n)) from
        hsqi.sub (hRi.const_mul _)) (integrable_const _),
      integral_sub hsqi (hRi.const_mul _), integral_const_mul, hsq, integral_const,
      probReal_univ, one_smul, ← hM, hρ2]
    ring
  have hM0 : 0 ≤ M := integral_nonneg fun ξ => BstLean.Part153.nrm_nonneg _
  have hvar0 : 0 ≤ ∫ ξ : Fin n → ℝ, (nrm (c + τ • ξ) - M) ^ 2 ∂stdGauss (Fin n) :=
    integral_nonneg fun ξ => sq_nonneg _
  refine ⟨hRi, hvi, hv, ?_, ?_⟩
  · have hd : 0 ≤ rhoC c τ - τ ^ 2 / rhoC c τ := by
      rw [sub_nonneg, div_le_iff₀ hρ0]; nlinarith
    have hsq' : (rhoC c τ - τ ^ 2 / rhoC c τ) ^ 2 ≤ M ^ 2 := by
      have e : (rhoC c τ - τ ^ 2 / rhoC c τ) ^ 2 =
          rhoC c τ ^ 2 - 2 * τ ^ 2 + τ ^ 2 * (τ ^ 2 / rhoC c τ ^ 2) := by
        field_simp
        ring
      have h1 : τ ^ 2 / rhoC c τ ^ 2 ≤ 1 := (div_le_one (by positivity)).mpr hτρ
      have h2 : τ ^ 2 * (τ ^ 2 / rhoC c τ ^ 2) ≤ τ ^ 2 := by nlinarith [sq_nonneg τ]
      rw [e]; linarith
    exact le_of_pow_le_pow_left₀ two_ne_zero hM0 hsq'
  · have : M ^ 2 ≤ rhoC c τ ^ 2 := by linarith
    exact le_of_pow_le_pow_left₀ two_ne_zero hρ0.le this

private lemma sq_int_le_Rad {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Integrable f μ)
    (hf2 : Integrable (fun x => f x ^ 2) μ) : (∫ x, f x ∂μ) ^ 2 ≤ ∫ x, f x ^ 2 ∂μ := by
  have h0 : 0 ≤ ∫ x, (f x - ∫ y, f y ∂μ) ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have e : (fun x => (f x - ∫ y, f y ∂μ) ^ 2) =
      fun x => f x ^ 2 - (2 * (∫ y, f y ∂μ) * f x - (∫ y, f y ∂μ) ^ 2) := by
    funext x; ring
  have hB : Integrable (fun x => 2 * (∫ y, f y ∂μ) * f x - (∫ y, f y ∂μ) ^ 2) μ :=
    (hf.const_mul _).sub (integrable_const _)
  rw [e, integral_sub hf2 hB, integral_sub (hf.const_mul _) (integrable_const _),
    integral_const_mul, integral_const, probReal_univ, one_smul] at h0
  nlinarith

/-- `|E[R g] − E R·E g| ≤ sd(R)·sd(g)` for a bounded `g`. -/
theorem radius_covariance {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsProbabilityMeasure μ] {R g : α → ℝ} {C : ℝ} (hR : Integrable R μ)
    (hRv : Integrable (fun x => (R x - ∫ y, R y ∂μ) ^ 2) μ)
    (hgm : Measurable g) (hgb : ∀ x, |g x| ≤ C) :
    |(∫ x, R x * g x ∂μ) - (∫ x, R x ∂μ) * ∫ x, g x ∂μ| ≤
      √(∫ x, (R x - ∫ y, R y ∂μ) ^ 2 ∂μ) * √(∫ x, (g x - ∫ y, g y ∂μ) ^ 2 ∂μ) := by
  have hgi : Integrable g μ :=
    Integrable.of_bound hgm.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hgb x)
  set M := ∫ y, R y ∂μ with hM
  set gb := ∫ y, g y ∂μ with hgb'
  have hRg : Integrable (fun x => R x * g x) μ := int_mul_bdd_Rad hR hgm hgb
  have hgcm : Measurable (fun x => g x - gb) := hgm.sub_const _
  have hgcb : ∀ x, |g x - gb| ≤ C + |gb| := fun x =>
    (abs_sub _ _).trans (add_le_add (hgb x) le_rfl)
  have hgci : Integrable (fun x => g x - gb) μ := hgi.sub (integrable_const _)
  have hRc : Integrable (fun x => R x - M) μ := hR.sub (integrable_const _)
  have hprod : Integrable (fun x => (R x - M) * (g x - gb)) μ :=
    int_mul_bdd_Rad hRc hgcm hgcb
  have hg2 : Integrable (fun x => (g x - gb) ^ 2) μ := by
    have h := int_mul_bdd_Rad hgci hgcm hgcb
    have e : (fun x => (g x - gb) ^ 2) = fun x => (g x - gb) * (g x - gb) := by
      funext x; ring
    rw [e]; exact h
  have I1 : ∫ x, (R x - M) * (g x - gb) ∂μ = (∫ x, R x * g x ∂μ) - M * gb := by
    have e : (fun x => (R x - M) * (g x - gb)) =
        fun x => (R x * g x - gb * R x) - (M * g x - M * gb) := by
      funext x; ring
    have hA : Integrable (fun x => R x * g x - gb * R x) μ := hRg.sub (hR.const_mul gb)
    have hB : Integrable (fun x => M * g x - M * gb) μ :=
      (hgi.const_mul M).sub (integrable_const _)
    rw [e, integral_sub hA hB, integral_sub hRg (hR.const_mul gb),
      integral_sub (hgi.const_mul M) (integrable_const _), integral_const_mul,
      integral_const_mul, integral_const, probReal_univ, one_smul, ← hM, ← hgb']
    ring
  rw [← I1]
  exact abs_cs_Rad hRv hg2 hprod

#print axioms radius_stats
#print axioms radius_covariance
end BstLean.Part219
