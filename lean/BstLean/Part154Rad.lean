import BstLean.Part154App

/-!
# Part 154: Lemma MA (iii): the radius correction
Statement fixed by the lead agent. Auxiliary lemmas are private (suffix `_Rad`).
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm GamS wn Eop Pb XiS N2 hid2Mean_cr)

noncomputable section

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

/-- `h₂(y) = |y|·h₂(y/|y|)` for every `y`. -/
private lemma hid2_eq_Rad {n m : ℕ} (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (y : Fin n → ℝ) : hid2 A₁ A₂ y = nrm y • hid2 A₁ A₂ (sphPt y) := by
  by_cases hy : normSq y = 0
  · have h0 : y = 0 := normSq_eq_zero hy
    have : nrm y = 0 := by unfold nrm; rw [hy, Real.sqrt_zero]
    rw [this, zero_smul, h0]
    exact BstLean.Part153.hid2_zero_cr A₁ A₂
  · have hpos : 0 < nrm y :=
      Real.sqrt_pos.mpr (lt_of_le_of_ne (normSq_nonneg y) (Ne.symm hy))
    rw [← BstLean.Part153.hid2_smul A₁ A₂ hpos.le, BstLean.Part153.sphPt_eq' hy, smul_smul]
    have : nrm y * (1 / √(normSq y)) = 1 := by
      unfold nrm; unfold nrm at hpos; field_simp
    rw [this, one_smul]

/-- The radius `|y|`, `y = c + τξ`: mean `M` with `ρ − τ²/ρ ≤ M ≤ ρ` and variance `≤ τ²`. -/
private lemma radius_stats_Rad {n : ℕ} (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
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
private lemma cov_split_Rad {α : Type*} [MeasurableSpace α] {μ : Measure α}
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

end

/-- **Lemma MA (iii)**: for every `(A₁, A₂)`:
`√t·|ā₂ − h̄₂/ρ| ≤ √γ_A·(1 + N₂₂)·θ/n + (Ξ·θ/n)^{1/2}`. -/
theorem radius_le {n : ℕ} (hn : 6 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    √(2 / ((mA n : ℕ) : ℝ)) *
        nrm (hid2Mean_cr A₁ A₂ c τ - (rhoC c τ)⁻¹ • hbar2 A₁ A₂ c τ) ≤
      √(2 / (n : ℝ)) * (1 + N2 2 A₁ A₂ c τ) * (thetaC c τ / n) +
        √(XiS A₁ A₂ c τ * (thetaC c τ / n)) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  obtain ⟨hRi, hRvi, hRv, hMlo, hMhi⟩ := radius_stats_Rad hn1 c hτ
  have hρ0 : 0 < rhoC c τ := by
    unfold rhoC
    exact Real.sqrt_pos.mpr (by nlinarith [normSq_nonneg c, sq_pos_of_pos hτ])
  set ρ := rhoC c τ with hρ
  set M := ∫ ξ', nrm (c + τ • ξ') ∂stdGauss (Fin n) with hM
  set v := hid2Mean_cr A₁ A₂ c τ - ρ⁻¹ • hbar2 A₁ A₂ c τ with hv
  set s := √(2 / ((mA n : ℕ) : ℝ)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hs2 : s ^ 2 = 2 / ((mA n : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  -- coordinates of `a₂(x)`
  have hmj : ∀ j, Measurable (fun ξ : Fin n → ℝ => hid2 A₁ A₂ (sphPt (c + τ • ξ)) j) :=
    fun j => (measurable_pi_apply j).comp (BstLean.Part153.measurable_hid2_sph_cr A₁ A₂ c τ)
  have hbj : ∀ j (ξ : Fin n → ℝ), |hid2 A₁ A₂ (sphPt (c + τ • ξ)) j| ≤ opN A₂ * opN A₁ := by
    intro j ξ
    have h1 := BstLean.Part153.nrm_hid2_sph_le_cr hn1 A₁ A₂ (c + τ • ξ)
    refine le_trans ?_ h1
    unfold nrm
    refine Real.abs_le_sqrt ?_
    unfold normSq
    exact Finset.single_le_sum (f := fun i => hid2 A₁ A₂ (sphPt (c + τ • ξ)) i ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  have haj := fun j => BstLean.Part153.integrable_hid2_coord_cr hn1 A₁ A₂ c τ j
  have hRaj : ∀ j, Integrable (fun ξ : Fin n → ℝ =>
      nrm (c + τ • ξ) * hid2 A₁ A₂ (sphPt (c + τ • ξ)) j) (stdGauss (Fin n)) :=
    fun j => int_mul_bdd_Rad hRi (hmj j) (hbj j)
  have hvj : ∀ j, v j = (∫ ξ, hid2 A₁ A₂ (sphPt (c + τ • ξ)) j ∂stdGauss (Fin n)) -
      ρ⁻¹ * ∫ ξ, nrm (c + τ • ξ) * hid2 A₁ A₂ (sphPt (c + τ • ξ)) j ∂stdGauss (Fin n) := by
    intro j
    have e : hbar2 A₁ A₂ c τ j =
        ∫ ξ, nrm (c + τ • ξ) * hid2 A₁ A₂ (sphPt (c + τ • ξ)) j ∂stdGauss (Fin n) := by
      unfold hbar2
      refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
      exact congrFun (hid2_eq_Rad A₁ A₂ (c + τ • ξ)) j
    rw [← e]; rfl
  -- the linear form `g = ⟨v, a₂(x)⟩`
  obtain ⟨hgm, hgb⟩ := BstLean.Part153.dot_hid2_bdd_cr hn1 A₁ A₂ c τ v
  have hgbar := BstLean.Part153.integral_dot_hid2_cr hn1 A₁ A₂ c τ v
  have hsplit := cov_split_Rad hRi hRvi hgm hgb
  rw [← hM] at hsplit
  have hRgsum : ∫ ξ, nrm (c + τ • ξ) * (v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)))
        ∂stdGauss (Fin n) =
      ∑ j, v j * ∫ ξ, nrm (c + τ • ξ) * hid2 A₁ A₂ (sphPt (c + τ • ξ)) j ∂stdGauss (Fin n) := by
    have e : (fun ξ : Fin n → ℝ => nrm (c + τ • ξ) * (v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)))) =
        fun ξ => ∑ j, v j * (nrm (c + τ • ξ) * hid2 A₁ A₂ (sphPt (c + τ • ξ)) j) := by
      funext ξ
      unfold dotProduct
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e, integral_finsetSum _ fun j _ => (hRaj j).const_mul (v j)]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  set gb := ∫ ξ, v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) ∂stdGauss (Fin n) with hgbdef
  set Rg := ∫ ξ, nrm (c + τ • ξ) * (v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ))) ∂stdGauss (Fin n)
    with hRgdef
  set V := ∫ ξ, (v ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) - gb) ^ 2 ∂stdGauss (Fin n) with hVdef
  have hV0 : 0 ≤ V := integral_nonneg fun ξ => sq_nonneg _
  have hNv : normSq v = gb - ρ⁻¹ * Rg := by
    rw [hRgsum, hgbar, Finset.mul_sum]
    unfold normSq dotProduct
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h1 : hid2Mean_cr A₁ A₂ c τ j =
        ∫ ξ, hid2 A₁ A₂ (sphPt (c + τ • ξ)) j ∂stdGauss (Fin n) := rfl
    rw [h1]
    linear_combination (v j) * hvj j
  -- the three bounds
  have hq : thetaC c τ / n = (τ * ρ⁻¹) ^ 2 := by
    unfold thetaC
    rw [← hρ]
    field_simp
  have hD : |Rg - M * gb| ≤ τ * √V := by
    refine hsplit.trans (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    calc √(∫ ξ : Fin n → ℝ, (nrm (c + τ • ξ) - M) ^ 2 ∂stdGauss (Fin n)) ≤ √(τ ^ 2) :=
          Real.sqrt_le_sqrt hRv
      _ = τ := Real.sqrt_sq hτ.le
  have hu0 : 0 ≤ 1 - M * ρ⁻¹ := by
    have : M * ρ⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one hρ0]; exact hMhi
    linarith
  have hu1 : 1 - M * ρ⁻¹ ≤ (τ * ρ⁻¹) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hMlo (inv_nonneg.mpr hρ0.le)
    have e : (ρ - τ ^ 2 / ρ) * ρ⁻¹ = 1 - (τ * ρ⁻¹) ^ 2 := by
      field_simp
    rw [e] at h
    linarith
  have hρi0 : 0 < ρ⁻¹ := inv_pos.mpr hρ0
  have H1 : nrm v ^ 2 ≤ |gb| * (τ * ρ⁻¹) ^ 2 + ρ⁻¹ * τ * √V := by
    rw [BstLean.Part153.nrm_sq, hNv]
    have e : gb - ρ⁻¹ * Rg = gb * (1 - M * ρ⁻¹) - ρ⁻¹ * (Rg - M * gb) := by ring
    rw [e]
    have h1 : gb * (1 - M * ρ⁻¹) ≤ |gb| * (τ * ρ⁻¹) ^ 2 :=
      (mul_le_mul_of_nonneg_right (le_abs_self gb) hu0).trans
        (mul_le_mul_of_nonneg_left hu1 (abs_nonneg _))
    have h2 : -(ρ⁻¹ * (Rg - M * gb)) ≤ ρ⁻¹ * (τ * √V) := by
      rw [← mul_neg]
      exact mul_le_mul_of_nonneg_left ((neg_le_abs _).trans hD) hρi0.le
    linarith
  have H2 : |gb| ≤ nrm v * nrm (hid2Mean_cr A₁ A₂ c τ) := by
    rw [hgbar]; exact BstLean.Part153.abs_dot_le_nrm _ _
  have H3 : s * nrm (hid2Mean_cr A₁ A₂ c τ) ≤ √(2 / (n : ℝ)) * (1 + N2 2 A₁ A₂ c τ) := by
    have hN0 := BstLean.Part153.N2_nonneg 2 A₁ A₂ c τ
    have hsum : normSq (hid2Mean_cr A₁ A₂ c τ) ≤ n * (1 + N2 2 A₁ A₂ c τ) ^ 2 := by
      have haj2 : ∀ j, Integrable (fun ξ : Fin n → ℝ =>
          hid2 A₁ A₂ (sphPt (c + τ • ξ)) j ^ 2) (stdGauss (Fin n)) := by
        intro j
        have h := int_mul_bdd_Rad (haj j) (hmj j) (hbj j)
        have e : (fun ξ : Fin n → ℝ => hid2 A₁ A₂ (sphPt (c + τ • ξ)) j ^ 2) =
            fun ξ => hid2 A₁ A₂ (sphPt (c + τ • ξ)) j * hid2 A₁ A₂ (sphPt (c + τ • ξ)) j := by
          funext ξ; ring
        rw [e]; exact h
      have h1 : normSq (hid2Mean_cr A₁ A₂ c τ) ≤
          ∑ j, ∫ ξ, hid2 A₁ A₂ (sphPt (c + τ • ξ)) j ^ 2 ∂stdGauss (Fin n) := by
        unfold normSq
        exact Finset.sum_le_sum fun j _ => sq_int_le_Rad (haj j) (haj2 j)
      have h2 : ∑ j, ∫ ξ, hid2 A₁ A₂ (sphPt (c + τ • ξ)) j ^ 2 ∂stdGauss (Fin n) =
          n * ∫ ξ, BstLean.Part153.sq2 A₁ A₂ c τ ξ ^ 2 ∂stdGauss (Fin n) := by
        rw [← integral_finsetSum _ fun j _ => haj2 j, ← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
        show normSq (hid2 A₁ A₂ (sphPt (c + τ • ξ))) =
          (n : ℝ) * BstLean.Part153.sq2 A₁ A₂ c τ ξ ^ 2
        rw [BstLean.Part153.sq2_eq_hid2, div_pow, Real.sq_sqrt hnR.le, BstLean.Part153.nrm_sq]
        field_simp
      have h3 := BstLean.Part153.int_sq2_sq_le hn1 A₁ A₂ c τ
      rw [h2] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left h3 hnR.le)
    have hsq : (s * nrm (hid2Mean_cr A₁ A₂ c τ)) ^ 2 ≤
        (√(2 / (n : ℝ)) * (1 + N2 2 A₁ A₂ c τ)) ^ 2 := by
      rw [mul_pow, mul_pow, hs2, BstLean.Part153.nrm_sq, Real.sq_sqrt (by positivity), hmA]
      have h := mul_le_mul_of_nonneg_left hsum (show (0 : ℝ) ≤ 2 / (n : ℝ) ^ 2 by positivity)
      have e : 2 / (n : ℝ) ^ 2 * (n * (1 + N2 2 A₁ A₂ c τ) ^ 2) =
          2 / (n : ℝ) * (1 + N2 2 A₁ A₂ c τ) ^ 2 := by
        field_simp
      rw [e] at h
      exact h
    exact le_of_pow_le_pow_left₀ two_ne_zero (by positivity) hsq
  have hΞ0 := BstLean.Part153.XiS_nonneg_cr A₁ A₂ c τ
  have H4 : s * √V ≤ √(XiS A₁ A₂ c τ) * nrm v := by
    have h := BstLean.Part153.cov_hid2_le hn A₁ A₂ c hτ v
    rw [← hgbdef, ← hVdef, ← hs2, ← BstLean.Part153.nrm_sq] at h
    have e1 : s * √V = √(s ^ 2 * V) := by
      rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs0]
    have e2 : √(XiS A₁ A₂ c τ) * nrm v = √(XiS A₁ A₂ c τ * nrm v ^ 2) := by
      rw [Real.sqrt_mul hΞ0, Real.sqrt_sq (BstLean.Part153.nrm_nonneg v)]
    rw [e1, e2]
    exact Real.sqrt_le_sqrt h
  -- the conclusion
  have hroot : √(XiS A₁ A₂ c τ * (thetaC c τ / n)) = √(XiS A₁ A₂ c τ) * (τ * ρ⁻¹) := by
    rw [hq, Real.sqrt_mul hΞ0, Real.sqrt_sq (by positivity)]
  rw [hroot, hq]
  set G := √(2 / (n : ℝ)) * (1 + N2 2 A₁ A₂ c τ) with hG
  set P := nrm (hid2Mean_cr A₁ A₂ c τ) with hP
  have hNv0 := BstLean.Part153.nrm_nonneg v
  have hG0 : 0 ≤ G := by
    have := BstLean.Part153.N2_nonneg 2 A₁ A₂ c τ
    positivity
  have hB0 : 0 ≤ G * (τ * ρ⁻¹) ^ 2 + √(XiS A₁ A₂ c τ) * (τ * ρ⁻¹) := by positivity
  have hX0 : 0 ≤ s * nrm v := mul_nonneg hs0 hNv0
  have h5 : s * |gb| * s ≤ s * nrm v * G := by
    calc s * |gb| * s ≤ s * (nrm v * P) * s := by gcongr
      _ = s * nrm v * (s * P) := by ring
      _ ≤ s * nrm v * G := mul_le_mul_of_nonneg_left H3 hX0
  have hX : (s * nrm v) ^ 2 ≤
      s * nrm v * (G * (τ * ρ⁻¹) ^ 2 + √(XiS A₁ A₂ c τ) * (τ * ρ⁻¹)) := by
    calc (s * nrm v) ^ 2 = s ^ 2 * nrm v ^ 2 := by ring
      _ ≤ s ^ 2 * (|gb| * (τ * ρ⁻¹) ^ 2 + ρ⁻¹ * τ * √V) :=
          mul_le_mul_of_nonneg_left H1 (sq_nonneg s)
      _ = s * |gb| * s * (τ * ρ⁻¹) ^ 2 + s * ρ⁻¹ * τ * (s * √V) := by ring
      _ ≤ s * nrm v * G * (τ * ρ⁻¹) ^ 2 + s * ρ⁻¹ * τ * (√(XiS A₁ A₂ c τ) * nrm v) :=
          add_le_add (mul_le_mul_of_nonneg_right h5 (sq_nonneg _))
            (mul_le_mul_of_nonneg_left H4 (by positivity))
      _ = s * nrm v * (G * (τ * ρ⁻¹) ^ 2 + √(XiS A₁ A₂ c τ) * (τ * ρ⁻¹)) := by ring
  by_contra hcon
  rw [not_le] at hcon
  nlinarith

end BstLean.Part154
