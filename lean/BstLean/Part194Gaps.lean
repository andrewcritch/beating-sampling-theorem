import BstLean.Part152GC

/-! Positive-gap concentration for nonnegative Gaussian functions. -/
namespace BstLean.Part194
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part148 (EuLip)

noncomputable def gap (a r k : ℝ) : ℝ := √(1 - a * r) - 1 / √k
noncomputable def tail (a r k : ℝ) : ℝ := exp (-(gap a r k) ^ 2 / (2 * r))

/-- Increasing the variance ratio increases the tail bound on the positive-gap domain. -/
theorem tail_mono {a r R k : ℝ} (ha : 0 ≤ a) (hr : 0 < r) (hrR : r ≤ R)
    (hgap : 0 < gap a R k) : tail a r k ≤ tail a R k := by
  have hR : 0 < R := hr.trans_le hrR
  have hg : gap a R k ≤ gap a r k := by
    unfold gap
    exact sub_le_sub_right (sqrt_le_sqrt (by nlinarith)) _
  have hsq : (gap a R k) ^ 2 ≤ (gap a r k) ^ 2 :=
    pow_le_pow_left₀ hgap.le hg 2
  have hdiv : (gap a R k) ^ 2 / (2 * R) ≤ (gap a r k) ^ 2 / (2 * r) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * R) (by positivity : 0 < 2 * r)).mpr
    have h1 := mul_le_mul_of_nonneg_right hsq hr.le
    have h2 := mul_le_mul_of_nonneg_left hrR (sq_nonneg (gap a r k))
    nlinarith
  unfold tail
  apply exp_le_exp.mpr
  simpa only [neg_div] using neg_le_neg hdiv

/-- A positive mean reserve supplies the paper's variable-ratio concentration formula.
The mean reserve is a hypothesis; this theorem does not assume independent input indices. -/
theorem gaussian_lower_tail {ι : Type} [Fintype ι] {f : (ι → ℝ) → ℝ}
    {L D a r k : ℝ} (hL : 0 < L) (hD : 0 < D) (hr : 0 < r) (hk : 0 < k)
    (hLip : EuLip f L) (hRatio : L ^ 2 / D ≤ r)
    (hMean : √D * √(1 - a * r) ≤ ∫ x, f x ∂stdGauss ι)
    (hgap : 0 < gap a r k) :
    (stdGauss ι).real {x | f x < √D / √k} ≤ tail a r k := by
  classical
  have hsd : 0 < √D := sqrt_pos.mpr hD
  have hd : 0 < √D * gap a r k := mul_pos hsd hgap
  have hsub : {x | f x < √D / √k} ⊆
      {x | f x ≤ (∫ y, f y ∂stdGauss ι) - √D * gap a r k} := by
    intro x hx
    simp only [mem_setOf_eq] at hx ⊢
    unfold gap
    have he : √D * (√(1 - a * r) - 1 / √k) =
        √D * √(1 - a * r) - √D / √k := by ring
    rw [he]
    linarith
  have hc := BstLean.Part152.gaussConc_lower_sharp hL.le hLip hd.le
  refine (measureReal_mono hsub).trans (hc.trans ?_)
  unfold tail
  apply exp_le_exp.mpr
  have hratio : L ^ 2 ≤ D * r := by
    simpa only [mul_comm] using (div_le_iff₀ hD).mp hRatio
  have hs : (√D * gap a r k) ^ 2 = D * (gap a r k) ^ 2 := by
    rw [mul_pow, sq_sqrt hD.le]
  rw [hs]
  have he : (gap a r k) ^ 2 / (2 * r) ≤ D * (gap a r k) ^ 2 / (2 * L ^ 2) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * r) (by positivity : 0 < 2 * L ^ 2)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hratio (sq_nonneg (gap a r k))]
  simpa only [neg_div] using neg_le_neg he

/-- Poincare and a second-moment reserve imply a lower bound for the mean. -/
theorem gaussian_mean_reserve {ι : Type} [Fintype ι] {f : (ι → ℝ) → ℝ}
    {L D b r : ℝ} (hL : 0 ≤ L) (hD : 0 < D) (hb : 0 ≤ b)
    (hLip : EuLip f L) (hf : Integrable f (stdGauss ι))
    (hf2 : Integrable (fun x => f x ^ 2) (stdGauss ι)) (hf0 : ∀ x, 0 ≤ f x)
    (hSecond : D - b * L ^ 2 ≤ ∫ x, f x ^ 2 ∂stdGauss ι)
    (hRatio : L ^ 2 / D ≤ r) (hRad : 0 ≤ 1 - (b + 1) * r) :
    √D * √(1 - (b + 1) * r) ≤ ∫ x, f x ∂stdGauss ι := by
  classical
  set e := ∫ x, f x ∂stdGauss ι with he
  have he0 : 0 ≤ e := integral_nonneg hf0
  have hVar := (BstLean.Part152.gaussVar_le_sharp hL hLip).2
  have hEq : ∫ x, (f x - e) ^ 2 ∂stdGauss ι =
      (∫ x, f x ^ 2 ∂stdGauss ι) - e ^ 2 := by
    have hFun : (fun x => (f x - e) ^ 2) =
        fun x => f x ^ 2 - 2 * e * f x + e ^ 2 := by funext x; ring
    rw [hFun,
      integral_add (f := fun x => f x ^ 2 - 2 * e * f x)
        (g := fun _ => e ^ 2) (hf2.sub (hf.const_mul (2 * e))) (integrable_const _),
      integral_sub (f := fun x => f x ^ 2) (g := fun x => 2 * e * f x)
        hf2 (hf.const_mul (2 * e)), integral_const_mul, integral_const]
    simp only [probReal_univ, one_smul, ← he]
    ring
  change ∫ x, (f x - e) ^ 2 ∂stdGauss ι ≤ L ^ 2 at hVar
  rw [hEq] at hVar
  have hR : L ^ 2 ≤ r * D := by
    have := (div_le_iff₀ hD).mp hRatio
    simpa only [mul_comm] using this
  have hMul := mul_le_mul_of_nonneg_left hR (by linarith : 0 ≤ b + 1)
  have hsq : (√D * √(1 - (b + 1) * r)) ^ 2 ≤ e ^ 2 := by
    rw [mul_pow, sq_sqrt hD.le, sq_sqrt hRad]
    nlinarith
  have h0 : 0 ≤ √D * √(1 - (b + 1) * r) := by positivity
  nlinarith [sq_nonneg (e - √D * √(1 - (b + 1) * r))]

/-- Concentration with a second-moment reserve and explicit positive gap. -/
theorem gaussian_tail_of_second_moment {ι : Type} [Fintype ι]
    {f : (ι → ℝ) → ℝ} {L D b r k : ℝ} (hL : 0 < L) (hD : 0 < D)
    (hb : 0 ≤ b) (hr : 0 < r) (hk : 0 < k) (hLip : EuLip f L)
    (hf : Integrable f (stdGauss ι))
    (hf2 : Integrable (fun x => f x ^ 2) (stdGauss ι)) (hf0 : ∀ x, 0 ≤ f x)
    (hSecond : D - b * L ^ 2 ≤ ∫ x, f x ^ 2 ∂stdGauss ι)
    (hRatio : L ^ 2 / D ≤ r) (hRad : 0 ≤ 1 - (b + 1) * r)
    (hgap : 0 < gap (b + 1) r k) :
    (stdGauss ι).real {x | f x < √D / √k} ≤ tail (b + 1) r k :=
  gaussian_lower_tail hL hD hr hk hLip hRatio
    (gaussian_mean_reserve hL.le hD hb hLip hf hf2 hf0 hSecond hRatio hRad) hgap

#print axioms gaussian_mean_reserve
#print axioms gaussian_tail_of_second_moment
#print axioms tail_mono
#print axioms gaussian_lower_tail
end BstLean.Part194
