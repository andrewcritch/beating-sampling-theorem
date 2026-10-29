import BstLean.Part107P1a

/-!
# Part 107, (P1): `E[a² | r] ≤ r² + 3/n`
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part105
open BstLean.Part78 (lin)

variable {n : ℕ}

/-- The algebra of the pointwise bound. -/
lemma pt_alg (N X H r s ρ : ℝ) (hN : 0 < N) (hXH : X ^ 2 ≤ H) :
    (r * ρ + s * X) ^ 2 / (r ^ 2 * ρ ^ 2 + 2 * r * s * ρ * X + s ^ 2 * H) ≤
      1 - s ^ 2 * (H - X ^ 2) *
        (2 / N - (r ^ 2 * ρ ^ 2 + 2 * r * s * ρ * X + s ^ 2 * H) / N ^ 2) := by
  set B := r ^ 2 * ρ ^ 2 + 2 * r * s * ρ * X + s ^ 2 * H with hB
  set Z := s ^ 2 * (H - X ^ 2) with hZ
  have hZ0 : 0 ≤ Z := mul_nonneg (sq_nonneg s) (by linarith)
  have hc : (r * ρ + s * X) ^ 2 = B - Z := by rw [hB, hZ]; ring
  have hB0 : 0 ≤ B := by nlinarith [sq_nonneg (r * ρ + s * X)]
  rcases hB0.eq_or_lt with h0 | hpos
  · rw [← h0]
    have : Z = 0 := by nlinarith [sq_nonneg (r * ρ + s * X)]
    rw [this]
    simp
  · rw [hc]
    have h1 : (B - Z) / B = 1 - Z * (1 / B) := by field_simp
    rw [h1]
    have h2 : 2 / N - B / N ^ 2 ≤ 1 / B := by
      rw [← sub_nonneg]
      have : 1 / B - (2 / N - B / N ^ 2) = (N - B) ^ 2 / (B * N ^ 2) := by
        field_simp
        ring
      rw [this]
      positivity
    nlinarith [mul_le_mul_of_nonneg_left h2 hZ0]

lemma p1_sphProj_apply (g : Fin n → ℝ) (i : Fin n) :
    sphProj g i = 1 / Real.sqrt (∑ j, g j ^ 2) * g i := by
  simp [sphProj]

lemma p1_sphProj_sq_le (g : Fin n → ℝ) : ∑ i, sphProj g i ^ 2 ≤ 1 := by
  simp_rw [p1_sphProj_apply, mul_pow]
  rw [← Finset.mul_sum, one_div, inv_pow,
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (g i))]
  exact inv_mul_le_one

lemma p1_abs_cosA_le (g g' : Fin n → ℝ) : |cosA g g'| ≤ 1 := by
  rw [← sq_le_one_iff_abs_le_one]
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (sphProj g) (sphProj g')
  have h1 := p1_sphProj_sq_le g
  have h2 := p1_sphProj_sq_le g'
  have h3 : 0 ≤ ∑ i, sphProj g' i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  unfold cosA dot
  nlinarith

/-- The pointwise bound: `a² ≤ lowF` when `g ≠ 0`. -/
lemma aR_sq_le (hn : 1 ≤ n) (r : ℝ) (g h : Fin n → ℝ) (hg : g ≠ 0) :
    aR r (g, h) ^ 2 ≤ lowF n (sphProj g) r (sC r) (Real.sqrt (∑ i, g i ^ 2)) h := by
  set ρ := Real.sqrt (∑ i, g i ^ 2) with hρ
  set x := sphProj g with hx
  set s := sC r
  have hS : 0 < ∑ i, g i ^ 2 := by
    rcases (Finset.sum_nonneg fun i (_ : i ∈ Finset.univ) => sq_nonneg (g i)).eq_or_lt with h0 | h0
    · exfalso
      apply hg
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (g i)).mp h0.symm i
        (Finset.mem_univ i)
      simpa using this
    · exact h0
  have hρ0 : 0 < ρ := Real.sqrt_pos.mpr hS
  have hρ2 : ρ ^ 2 = ∑ i, g i ^ 2 := Real.sq_sqrt hS.le
  have hgx : ∀ i, g i = ρ * x i := by
    intro i
    rw [hx, p1_sphProj_apply, ← hρ]
    field_simp
  have hx1 : ∑ i, x i ^ 2 = 1 := by
    have : ∑ i, g i ^ 2 = ρ ^ 2 * ∑ i, x i ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [hgx i]; ring
    rw [← hρ2] at this
    have h2 : ρ ^ 2 ≠ 0 := by positivity
    field_simp at this
    linarith
  set X := lin x h with hX
  set H := Hs h with hH
  have hXH : X ^ 2 ≤ H := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x h
    rw [hx1, one_mul] at this
    exact this
  -- `g′`
  set g' : Fin n → ℝ := r • g + s • h with hg'
  have hg'i : ∀ i, g' i = r * ρ * x i + s * h i := by
    intro i
    simp only [hg', Pi.add_apply, Pi.smul_apply, smul_eq_mul, hgx i]
    ring
  have hB : ∑ i, g' i ^ 2 = r ^ 2 * ρ ^ 2 + 2 * r * s * ρ * X + s ^ 2 * H := by
    have : ∀ i, g' i ^ 2 = r ^ 2 * ρ ^ 2 * x i ^ 2 + 2 * r * s * ρ * (x i * h i) +
        s ^ 2 * h i ^ 2 := fun i => by rw [hg'i]; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum, hx1]
    simp only [hX, hH, lin, Hs]
    ring
  have hc : ∑ i, x i * g' i = r * ρ + s * X := by
    have : ∀ i, x i * g' i = r * ρ * x i ^ 2 + s * (x i * h i) := fun i => by rw [hg'i]; ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hx1]
    simp only [hX, lin]
    ring
  have ha : aR r (g, h) ^ 2 = (r * ρ + s * X) ^ 2 /
      (r ^ 2 * ρ ^ 2 + 2 * r * s * ρ * X + s ^ 2 * H) := by
    have : aR r (g, h) = 1 / Real.sqrt (∑ i, g' i ^ 2) * ∑ i, x i * g' i := by
      change ∑ i, x i * sphProj g' i = _
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [p1_sphProj_apply g' i]
      ring
    rw [this, mul_pow, one_div, inv_pow,
      Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (g' i)), hB, hc]
    ring
  rw [ha]
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  exact pt_alg n X H r s ρ hN hXH

lemma p1_measurable_aR (r : ℝ) : Measurable (aR (n := n) r) := by
  have h1 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => sphProj p.1) :=
    measurable_sphProj.comp measurable_fst
  have h0 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => r • p.1 + sC r • p.2) :=
    Measurable.add (f := fun p : (Fin n → ℝ) × (Fin n → ℝ) => r • p.1)
      (g := fun p : (Fin n → ℝ) × (Fin n → ℝ) => sC r • p.2)
      (measurable_fst.const_smul r) (measurable_snd.const_smul (sC r))
  have h2 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => sphProj (r • p.1 + sC r • p.2)) :=
    measurable_sphProj.comp h0
  exact measurable_dot2.comp (h1.prodMk h2)

theorem p1_107 (hZ : NonZero107) : P1_107 := by
  intro n r hn hr
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := sC_sq hr
  set s := sC r
  have hInt : Integrable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => aR r p ^ 2) (gg n) := by
    refine Integrable.of_bound ((p1_measurable_aR r).pow_const 2).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_pow, aR]
    exact pow_le_one₀ (abs_nonneg _) (p1_abs_cosA_le _ _)
  have hF : ∫ p, aR r p ^ 2 ∂gg n =
      ∫ g, ∫ h, aR r (g, h) ^ 2 ∂stdGauss (Fin n) ∂stdGauss (Fin n) := integral_prod _ hInt
  rw [hF]
  have hGi : Integrable (fun g : Fin n → ℝ => 1 - 2 * s ^ 2 * ((n : ℝ) - 1) / n +
      s ^ 2 / (n : ℝ) ^ 2 * ((n : ℝ) - 1) * (r ^ 2 * Hs g + s ^ 2 * ((n : ℝ) + 2)))
      (stdGauss (Fin n)) :=
    (integrable_const _).add (((iH.const_mul _).add (integrable_const _)).const_mul _)
  have hle : ∫ g, ∫ h, aR r (g, h) ^ 2 ∂stdGauss (Fin n) ∂stdGauss (Fin n) ≤
      ∫ g : Fin n → ℝ, (1 - 2 * s ^ 2 * ((n : ℝ) - 1) / n +
        s ^ 2 / (n : ℝ) ^ 2 * ((n : ℝ) - 1) * (r ^ 2 * Hs g + s ^ 2 * ((n : ℝ) + 2)))
        ∂stdGauss (Fin n) := by
    refine integral_mono_ae hInt.integral_prod_left hGi ?_
    filter_upwards [hZ n hn] with g hg
    have hS : 0 ≤ ∑ i, g i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (g i)
    have hx1 : ∑ i, sphProj g i ^ 2 = 1 := by
      simp_rw [p1_sphProj_apply, mul_pow]
      rw [← Finset.mul_sum, one_div, inv_pow, Real.sq_sqrt hS]
      refine inv_mul_cancel₀ fun h0 => hg ?_
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => sq_nonneg (g i)).mp h0 i
        (Finset.mem_univ i)
      simpa using this
    have hpt : ∀ h : Fin n → ℝ,
        aR r (g, h) ^ 2 ≤ lowF n (sphProj g) r s (Real.sqrt (∑ i, g i ^ 2)) h :=
      fun h => aR_sq_le hn r g h hg
    have h1 : ∫ h, aR r (g, h) ^ 2 ∂stdGauss (Fin n) ≤
        ∫ h, lowF n (sphProj g) r s (Real.sqrt (∑ i, g i ^ 2)) h ∂stdGauss (Fin n) := by
      refine integral_mono_of_nonneg ?_ (lowF_integrable _ _ _ _) ?_
      · exact Filter.Eventually.of_forall fun h => sq_nonneg (aR r (g, h))
      · exact Filter.Eventually.of_forall hpt
    have h2 := lowF_integral (sphProj g) hx1 r s (Real.sqrt (∑ i, g i ^ 2))
    rw [Real.sq_sqrt hS] at h2
    rw [h2] at h1
    exact h1
  refine hle.trans ?_
  have e1 := integral_add (integrable_const (μ := stdGauss (Fin n))
      (1 - 2 * s ^ 2 * ((n : ℝ) - 1) / n))
    (((iH (n := n)).const_mul (r ^ 2)).add (integrable_const (s ^ 2 * ((n : ℝ) + 2)))
      |>.const_mul (s ^ 2 / (n : ℝ) ^ 2 * ((n : ℝ) - 1)))
  simp only [Pi.add_apply] at e1
  rw [e1, integral_const_mul]
  have e2 := integral_add ((iH (n := n)).const_mul (r ^ 2))
    (integrable_const (μ := stdGauss (Fin n)) (s ^ 2 * ((n : ℝ) + 2)))
  rw [e2, integral_const_mul, mH]
  simp only [integral_const, probReal_univ, one_smul]
  -- the final inequality
  have hq0 : 0 ≤ s ^ 2 := sq_nonneg s
  have hq1 : s ^ 2 ≤ 1 := by rw [hs]; nlinarith [sq_nonneg r]
  have hr2 : r ^ 2 = 1 - s ^ 2 := by linarith
  rw [hr2]
  generalize s ^ 2 = q at *
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  rw [show 1 - 2 * q * ((n : ℝ) - 1) / n + q / (n : ℝ) ^ 2 * ((n : ℝ) - 1) *
      ((1 - q) * n + q * ((n : ℝ) + 2)) =
      1 - q + q * (2 * q * n - 2 * q + n) / (n : ℝ) ^ 2 by field_simp; ring]
  have : q * (2 * q * n - 2 * q + n) / (n : ℝ) ^ 2 ≤ 3 / n := by
    rw [div_le_div_iff₀ (by positivity) hN]
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1), mul_nonneg hq0 hN.le]
  linarith

#print axioms p1_107

end BstLean.Part107
