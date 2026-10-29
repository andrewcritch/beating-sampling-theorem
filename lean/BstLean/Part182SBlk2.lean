import BstLean.Part182SBlk

/-!
# Part 182 (file `SBlk2`): the conditional mean and the scalar bound of Lemma TI

No proof is left open; no `native_decide` or `axiom` is used.

Paper source: `proofs/option-n/theorem7-04-frame-numerator.tex`, proof of Lemma `t7:p04:ti`, from
"The exact conditional mean retains radial terms" to "This proves the scalar bound".

* **`s2_polar_bil`**: the polar matrix `H` as a bilinear form (polarization of `sb_polar_quad`),
  with integrability.
* **`s2_mean_s`**, **`s2_cond_mean`**: for fixed `a, a' ≠ 0, p, p'` (functions of `A₁`) and
  `A₂ ~ gaussMat m k t`, the mean of `s = Σᵢ mask((A₂a)ᵢ)mask((A₂a')ᵢ)(A₂p)ᵢ(A₂p')ᵢ`; with `mt = 2`
  it is the paper's formula (t7:p04:cm).
* `s2_map_unit`, **`s2_dev`**: the row-sum inequality (`bn_rowsum`) for a general row summand with
  envelope `b(((r·u)/√v)² + ((r·u')/√v)²)/2`, `u, u'` unit.
* **`s2_scalar_dev`**: `Pr(|s − E[s|A₁]| > r_s) ≤ 2e^{−τ}`, `r_s = 2·t p₊²(√(2mτ) + τ)`.
* **`s2_scalar_det`**: the deterministic scalar bound `𝖫 ≤ s ≤ 𝖴` of the paper.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open Matrix

/-- `(w·z)²` is integrable under the standard Gaussian. -/
lemma s2_int_dot_sq {k : ℕ} (z : Fin k → ℝ) :
    Integrable (fun w : Fin k → ℝ => (w ⬝ᵥ z) ^ 2) (stdGauss (Fin k)) := by
  have hs : Integrable (fun w : Fin k → ℝ => ∑ i, w i ^ 2) (stdGauss (Fin k)) :=
    integrable_finsetSum _ fun i _ => (BstLean.Part112.memLp_coord i).integrable_sq
  refine Integrable.mono' (hs.const_mul (∑ i, z i ^ 2)) ?_ (Filter.Eventually.of_forall fun w => ?_)
  · exact (by simp only [dotProduct]; fun_prop : Measurable fun w : Fin k → ℝ => (w ⬝ᵥ z) ^ 2).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w z
    simp only [dotProduct]
    nlinarith [h]

lemma s2_measurable_posI : Measurable posI := by
  unfold posI
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const
    measurable_const

/-- The cone-weighted square is integrable. -/
lemma s2_int_cone {k : ℕ} (v v' z : Fin k → ℝ) :
    Integrable (fun w : Fin k → ℝ => posI (w ⬝ᵥ v) * posI (w ⬝ᵥ v') * (w ⬝ᵥ z) ^ 2)
      (stdGauss (Fin k)) := by
  refine Integrable.mono' (s2_int_dot_sq z) ?_ (Filter.Eventually.of_forall fun w => ?_)
  · have h1 : Measurable fun w : Fin k → ℝ => w ⬝ᵥ v := by simp only [dotProduct]; fun_prop
    have h2 : Measurable fun w : Fin k → ℝ => w ⬝ᵥ v' := by simp only [dotProduct]; fun_prop
    have h3 : Measurable fun w : Fin k → ℝ => (w ⬝ᵥ z) ^ 2 := by simp only [dotProduct]; fun_prop
    exact (((s2_measurable_posI.comp h1).mul (s2_measurable_posI.comp h2)).mul h3).aestronglyMeasurable
  · obtain ⟨a0, a1⟩ := sb_posI_le (w ⬝ᵥ v)
    obtain ⟨b0, b1⟩ := sb_posI_le (w ⬝ᵥ v')
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hp : posI (w ⬝ᵥ v) * posI (w ⬝ᵥ v') ≤ 1 := by nlinarith
    nlinarith [sq_nonneg (w ⬝ᵥ z)]

lemma s2_normSq_dot {k : ℕ} (z : Fin k → ℝ) : normSq z = z ⬝ᵥ z := by
  simp [normSq, dotProduct, sq]

/-- **The polar matrix `H` as a bilinear form** (polarization of `sb_polar_quad`): for unit `v, v'`
with `q = v·v'`, `q² < 1`, and any `u, u'`:
`E[1(w·v > 0)1(w·v' > 0)(w·u)(w·u')] = (κ̇(q)/2)(u·u') +
(αβ' + α'β − q(αα' + ββ'))/(2π√(1 − q²))`, `α = u·v`, `β = u·v'`, `α' = u'·v`, `β' = u'·v'`. -/
theorem s2_polar_bil {k : ℕ} {v v' : Fin k → ℝ} (hv : normSq v = 1) (hv' : normSq v' = 1)
    (hq : (v ⬝ᵥ v') ^ 2 < 1) (u u' : Fin k → ℝ) :
    Integrable (fun w : Fin k → ℝ => posI (w ⬝ᵥ v) * posI (w ⬝ᵥ v') * ((w ⬝ᵥ u) * (w ⬝ᵥ u')))
      (stdGauss (Fin k)) ∧
    ∫ w, posI (w ⬝ᵥ v) * posI (w ⬝ᵥ v') * ((w ⬝ᵥ u) * (w ⬝ᵥ u')) ∂stdGauss (Fin k) =
      kdot (v ⬝ᵥ v') / 2 * (u ⬝ᵥ u') +
        ((u ⬝ᵥ v) * (u' ⬝ᵥ v') + (u' ⬝ᵥ v) * (u ⬝ᵥ v') -
          (v ⬝ᵥ v') * ((u ⬝ᵥ v) * (u' ⬝ᵥ v) + (u ⬝ᵥ v') * (u' ⬝ᵥ v'))) /
          (2 * π * √(1 - (v ⬝ᵥ v') ^ 2)) := by
  have hP := s2_int_cone v v' (u + u')
  have hM := s2_int_cone v v' (u - u')
  have heq : (fun w : Fin k → ℝ => posI (w ⬝ᵥ v) * posI (w ⬝ᵥ v') * ((w ⬝ᵥ u) * (w ⬝ᵥ u'))) =
      fun w => (1 / 4 : ℝ) * (posI (w ⬝ᵥ v) * posI (w ⬝ᵥ v') * (w ⬝ᵥ (u + u')) ^ 2 -
        posI (w ⬝ᵥ v) * posI (w ⬝ᵥ v') * (w ⬝ᵥ (u - u')) ^ 2) := by
    funext w
    rw [dotProduct_add, dotProduct_sub]
    ring
  have hint : Integrable (fun w : Fin k → ℝ =>
      posI (w ⬝ᵥ v) * posI (w ⬝ᵥ v') * ((w ⬝ᵥ u) * (w ⬝ᵥ u'))) (stdGauss (Fin k)) := by
    rw [heq]; exact (hP.sub hM).const_mul _
  refine ⟨hint, ?_⟩
  rw [heq, integral_const_mul, integral_sub hP hM, sb_polar_quad hv hv' hq,
    sb_polar_quad hv hv' hq]
  have hσ : 0 < √(1 - (v ⬝ᵥ v') ^ 2) := Real.sqrt_pos.2 (by linarith)
  have hp := pi_pos
  rw [s2_normSq_dot, s2_normSq_dot]
  simp only [add_dotProduct, sub_dotProduct, dotProduct_add, dotProduct_sub]
  rw [dotProduct_comm u' u]
  field_simp
  ring

/-- The unit vector `a/|a|`. -/
noncomputable def s2_unit {k : ℕ} (a : Fin k → ℝ) : Fin k → ℝ := (√(normSq a))⁻¹ • a

lemma s2_normSq_pos {k : ℕ} {a : Fin k → ℝ} (ha : a ≠ 0) : 0 < normSq a := by
  rcases (Finset.sum_nonneg fun i _ => sq_nonneg (a i) : 0 ≤ normSq a).lt_or_eq with h | h
  · exact h
  · exfalso; apply ha; funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (a i))).1 h.symm i
      (Finset.mem_univ _)
    simpa using this

lemma s2_unit_norm {k : ℕ} {a : Fin k → ℝ} (ha : a ≠ 0) : normSq (s2_unit a) = 1 := by
  have h := s2_normSq_pos ha
  have hs : 0 < √(normSq a) := Real.sqrt_pos.2 h
  rw [s2_normSq_dot, s2_unit, smul_dotProduct, dotProduct_smul, ← s2_normSq_dot]
  simp only [smul_eq_mul]
  rw [← mul_assoc, ← sq, inv_pow, Real.sq_sqrt h.le, inv_mul_cancel₀ h.ne']

lemma s2_dot_unit {k : ℕ} {a : Fin k → ℝ} (ha : a ≠ 0) (w : Fin k → ℝ) :
    w ⬝ᵥ a = √(normSq a) * (w ⬝ᵥ s2_unit a) := by
  have hs : 0 < √(normSq a) := Real.sqrt_pos.2 (s2_normSq_pos ha)
  rw [s2_unit, dotProduct_smul, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]

lemma s2_posI_unit {k : ℕ} {a : Fin k → ℝ} (ha : a ≠ 0) (w : Fin k → ℝ) :
    posI (w ⬝ᵥ a) = posI (w ⬝ᵥ s2_unit a) := by
  rw [s2_dot_unit ha, posI_mul_of_pos (Real.sqrt_pos.2 (s2_normSq_pos ha))]

/-- The one-row summand of `s = ⟨J e, J' e'⟩` given `A₁`. -/
noncomputable def s2_Phi {k : ℕ} (a a' p p' : Fin k → ℝ) (r : Fin k → ℝ) : ℝ :=
  posI (r ⬝ᵥ a) * posI (r ⬝ᵥ a') * ((r ⬝ᵥ p) * (r ⬝ᵥ p'))

lemma s2_measurable_Phi {k : ℕ} (a a' p p' : Fin k → ℝ) : Measurable (s2_Phi a a' p p') := by
  unfold s2_Phi
  have h : ∀ z : Fin k → ℝ, Measurable fun r : Fin k → ℝ => r ⬝ᵥ z := fun z => by
    simp only [dotProduct]; fun_prop
  exact ((s2_measurable_posI.comp (h a)).mul (s2_measurable_posI.comp (h a'))).mul
    ((h p).mul (h p'))

/-- **The conditional mean of the scalar row sum** (paper: the mean of `s = ⟨J_x e, J_{x'} e'⟩`
given `A₁`): for FIXED `a, a' ≠ 0, p, p'` (functions of `A₁`), `v = a/|a|`, `v' = a'/|a'|`,
`q = v·v'`, `q² < 1`, and `A₂ ~ gaussMat m k t` (`t > 0`):
`E Σᵢ mask((A₂a)ᵢ) mask((A₂a')ᵢ) (A₂p)ᵢ (A₂p')ᵢ = m t [(κ̇(q)/2)⟨p,p'⟩ +
(εβ' + α'β − q(εα' + ββ'))/(2π√(1−q²))]`, `ε = p·v`, `β = p·v'`, `α' = p'·v`, `β' = ε' = p'·v'`. -/
theorem s2_mean_s {m k : ℕ} {t : ℝ} (ht : 0 < t) {a a' p p' : Fin k → ℝ} (ha : a ≠ 0)
    (ha' : a' ≠ 0) (hq : (s2_unit a ⬝ᵥ s2_unit a') ^ 2 < 1) :
    ∫ A, ∑ i, BstLean.Part151.mask ((A *ᵥ a) i) * BstLean.Part151.mask ((A *ᵥ a') i) *
        ((A *ᵥ p) i * (A *ᵥ p') i) ∂gaussMat m k t =
      m * t * (kdot (s2_unit a ⬝ᵥ s2_unit a') / 2 * (p ⬝ᵥ p') +
        ((p ⬝ᵥ s2_unit a) * (p' ⬝ᵥ s2_unit a') + (p' ⬝ᵥ s2_unit a) * (p ⬝ᵥ s2_unit a') -
          (s2_unit a ⬝ᵥ s2_unit a') * ((p ⬝ᵥ s2_unit a) * (p' ⬝ᵥ s2_unit a) +
            (p ⬝ᵥ s2_unit a') * (p' ⬝ᵥ s2_unit a'))) /
          (2 * π * √(1 - (s2_unit a ⬝ᵥ s2_unit a') ^ 2))) := by
  set Φ := s2_Phi a a' p p' with hΦd
  have hΦm : Measurable Φ := s2_measurable_Phi a a' p p'
  obtain ⟨hbi, hbv⟩ := s2_polar_bil (s2_unit_norm ha) (s2_unit_norm ha') hq p p'
  have hsc : ∀ ξ : Fin k → ℝ, Φ (√t • ξ) = t * (posI (ξ ⬝ᵥ s2_unit a) *
      posI (ξ ⬝ᵥ s2_unit a') * ((ξ ⬝ᵥ p) * (ξ ⬝ᵥ p'))) := by
    intro ξ
    have hst : 0 < √t := Real.sqrt_pos.2 ht
    simp only [hΦd, s2_Phi, smul_dotProduct, smul_eq_mul]
    rw [posI_mul_of_pos hst, posI_mul_of_pos hst, s2_posI_unit ha, s2_posI_unit ha']
    have : √t * (ξ ⬝ᵥ p) * (√t * (ξ ⬝ᵥ p')) = t * ((ξ ⬝ᵥ p) * (ξ ⬝ᵥ p')) := by
      rw [show √t * (ξ ⬝ᵥ p) * (√t * (ξ ⬝ᵥ p')) = (√t * √t) * ((ξ ⬝ᵥ p) * (ξ ⬝ᵥ p')) by ring,
        Real.mul_self_sqrt ht.le]
    rw [this]; ring
  have hint_k : Integrable (fun ξ => Φ (√t • ξ)) (stdGauss (Fin k)) := by
    simp_rw [hsc]; exact hbi.const_mul t
  have hrow : ∀ i : Fin m, (fun A : Matrix (Fin m) (Fin k) ℝ =>
      BstLean.Part151.mask ((A *ᵥ a) i) * BstLean.Part151.mask ((A *ᵥ a') i) *
        ((A *ᵥ p) i * (A *ᵥ p') i)) = fun A => Φ (rowOf i A) := by
    intro i; funext A; rfl
  have hint_i : ∀ i : Fin m, Integrable (fun A : Matrix (Fin m) (Fin k) ℝ =>
      BstLean.Part151.mask ((A *ᵥ a) i) * BstLean.Part151.mask ((A *ᵥ a') i) *
        ((A *ᵥ p) i * (A *ᵥ p') i)) (gaussMat m k t) := by
    intro i
    rw [hrow]
    refine (integrable_map_measure hΦm.aestronglyMeasurable (measurable_rowOf i).aemeasurable).1 ?_
    rw [gaussMat_row]
    exact (integrable_map_measure hΦm.aestronglyMeasurable
      (measurable_const_smul _).aemeasurable).2 hint_k
  rw [integral_finset_sum _ fun i _ => hint_i i]
  have hval : ∀ i : Fin m, ∫ A, BstLean.Part151.mask ((A *ᵥ a) i) *
      BstLean.Part151.mask ((A *ᵥ a') i) * ((A *ᵥ p) i * (A *ᵥ p') i) ∂gaussMat m k t =
      t * ∫ ξ, posI (ξ ⬝ᵥ s2_unit a) * posI (ξ ⬝ᵥ s2_unit a') * ((ξ ⬝ᵥ p) * (ξ ⬝ᵥ p'))
        ∂stdGauss (Fin k) := by
    intro i
    rw [hrow, ← integral_map (measurable_rowOf i).aemeasurable hΦm.aestronglyMeasurable,
      gaussMat_row, integral_map (measurable_const_smul _).aemeasurable hΦm.aestronglyMeasurable]
    simp_rw [hsc]
    rw [integral_const_mul]
  simp_rw [hval]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hbv]
  ring

/-- **The conditional mean formula** `(t7:p04:cm)`: with `m t = 2`,
`E[s | A₁] = κ̇(q)⟨p,p'⟩ + κ''(q)(⟨p,v'⟩ − qε)(⟨p',v⟩ − qε') + (√(1−q²)/π)εε'`,
`κ''(q) = 1/(π√(1 − q²))`, `ε = p·v`, `ε' = p'·v'`. -/
theorem s2_cond_mean {m k : ℕ} {t : ℝ} (ht : 0 < t) (hmt : (m : ℝ) * t = 2)
    {a a' p p' : Fin k → ℝ} (ha : a ≠ 0) (ha' : a' ≠ 0)
    (hq : (s2_unit a ⬝ᵥ s2_unit a') ^ 2 < 1) :
    ∫ A, ∑ i, BstLean.Part151.mask ((A *ᵥ a) i) * BstLean.Part151.mask ((A *ᵥ a') i) *
        ((A *ᵥ p) i * (A *ᵥ p') i) ∂gaussMat m k t =
      kdot (s2_unit a ⬝ᵥ s2_unit a') * (p ⬝ᵥ p') +
        1 / (π * √(1 - (s2_unit a ⬝ᵥ s2_unit a') ^ 2)) *
          ((p ⬝ᵥ s2_unit a') - (s2_unit a ⬝ᵥ s2_unit a') * (p ⬝ᵥ s2_unit a)) *
          ((p' ⬝ᵥ s2_unit a) - (s2_unit a ⬝ᵥ s2_unit a') * (p' ⬝ᵥ s2_unit a')) +
        √(1 - (s2_unit a ⬝ᵥ s2_unit a') ^ 2) / π * (p ⬝ᵥ s2_unit a) * (p' ⬝ᵥ s2_unit a') := by
  rw [s2_mean_s ht ha ha' hq, hmt]
  set q := s2_unit a ⬝ᵥ s2_unit a'
  have hσ2 : 0 < 1 - q ^ 2 := by linarith
  have hσ : 0 < √(1 - q ^ 2) := Real.sqrt_pos.2 hσ2
  have hσsq : √(1 - q ^ 2) ^ 2 = 1 - q ^ 2 := Real.sq_sqrt hσ2.le
  have hp := pi_pos
  field_simp
  rw [hσsq]
  ring

/-- The law of `ξ ↦ ξ·u` for a unit `u`. -/
lemma s2_map_unit {k : ℕ} {u : Fin k → ℝ} (hu : normSq u = 1) :
    (stdGauss (Fin k)).map (fun ξ => ξ ⬝ᵥ u) = gaussianReal 0 1 := by
  have hAB : Matrix.of ![u] * (Matrix.of ![u]).transpose =
      (1 : Matrix (Fin 1) (Fin 1) ℝ) * (1 : Matrix (Fin 1) (Fin 1) ℝ).transpose := by
    have h1 : ∑ j, u j * u j = 1 := by rw [← hu]; simp [normSq, sq]
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, h1]
  have h := BstLean.Part105.gaussLin105 (Fin k) (Fin 1) (Fin 1) _ _ hAB
  simp only [Matrix.one_mulVec, Measure.map_id'] at h
  have hA : Measurable (fun ξ : Fin k → ℝ => (Matrix.of ![u]).mulVec ξ) := measurable_mulVec_left _
  have e1 : (fun ξ : Fin k → ℝ => ξ ⬝ᵥ u) = Function.eval 0 ∘ (fun ξ => (Matrix.of ![u]).mulVec ξ) := by
    funext ξ
    simp [dotProduct_comm]
  rw [e1, ← Measure.map_map (measurable_pi_apply 0) hA, h]
  exact (measurePreserving_eval (μ := fun _ : Fin 1 => gaussianReal 0 1) 0).map_eq

/-- **The row-sum deviation for a general summand** (paper: the row-sum inequality, used for the
conditional scalar sum): rows of `A ~ gaussMat m k v` (`v > 0`), a measurable `Φ`, unit `u, u'`,
and the envelope `|Φ r| ≤ b(((r·u)/√v)² + ((r·u')/√v)²)/2` (`b > 0`):
`Pr(|Σᵢ Φ(rowᵢ A) − m·E Φ(√v ξ)| > 2b(√(2mτ) + τ)) ≤ 2e^{−τ}`. -/
theorem s2_dev {m k : ℕ} {v : ℝ} (hv : 0 < v) {Φ : (Fin k → ℝ) → ℝ} (hΦm : Measurable Φ)
    {u u' : Fin k → ℝ} (hu : normSq u = 1) (hu' : normSq u' = 1) {b τ : ℝ} (hb : 0 < b)
    (hdom : ∀ r, |Φ r| ≤ b * (((r ⬝ᵥ u) / √v) ^ 2 + ((r ⬝ᵥ u') / √v) ^ 2) / 2)
    (hm : 0 < m) (hτ : 0 ≤ τ) :
    (gaussMat m k v).real {A | 2 * b * (√(2 * m * τ) + τ) <
      |∑ i, Φ (rowOf i A) - m * ∫ ξ, Φ (√v • ξ) ∂stdGauss (Fin k)|} ≤ 2 * exp (-τ) := by
  have hsv : 0 < √v := Real.sqrt_pos.mpr hv
  set ρ : Measure (Fin k → ℝ) := (stdGauss (Fin k)).map (fun ξ => √v • ξ) with hρ
  have hρp : IsProbabilityMeasure ρ := by
    rw [hρ]; exact (Measure.isProbabilityMeasure_map_iff (measurable_const_smul _).aemeasurable).2
      inferInstance
  set P : Measure (Fin m → Fin k → ℝ) := Measure.pi fun _ : Fin m => ρ with hP
  have hPp : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hrows : Measurable (fun G : Matrix (Fin m) (Fin k) ℝ => fun i => rowOf i G) :=
    measurable_pi_iff.mpr fun i => measurable_rowOf i
  have hmap : (gaussMat m k v).map (fun G i => rowOf i G) = P := by
    rw [hP, hρ]; exact BstLean.Part148.gaussMat_rows_map m k v
  have hmean : ∫ r, Φ r ∂ρ = ∫ ξ, Φ (√v • ξ) ∂stdGauss (Fin k) := by
    rw [hρ, integral_map (measurable_const_smul _).aemeasurable hΦm.aestronglyMeasurable]
  have hS : MeasurableSet {ω : Fin m → Fin k → ℝ | 2 * b * (√(2 * m * τ) + τ) <
      |∑ i, Φ (ω i) - m * ∫ ξ, Φ (√v • ξ) ∂stdGauss (Fin k)|} :=
    measurableSet_lt measurable_const
      (((Finset.measurable_sum _ fun i _ => hΦm.comp (measurable_pi_apply i)).sub_const _).abs)
  have e1 : {A : Matrix (Fin m) (Fin k) ℝ | 2 * b * (√(2 * m * τ) + τ) <
      |∑ i, Φ (rowOf i A) - m * ∫ ξ, Φ (√v • ξ) ∂stdGauss (Fin k)|} =
      (fun G i => rowOf i G) ⁻¹' {ω | 2 * b * (√(2 * m * τ) + τ) <
        |∑ i, Φ (ω i) - m * ∫ ξ, Φ (√v • ξ) ∂stdGauss (Fin k)|} := rfl
  rw [e1, ← map_measureReal_apply hrows hS, hmap]
  set X : Fin m → (Fin m → Fin k → ℝ) → ℝ := fun j ω => Φ (ω j) with hX
  set U : Fin m → (Fin m → Fin k → ℝ) → ℝ := fun j ω => (ω j ⬝ᵥ u) / √v with hU
  set V : Fin m → (Fin m → Fin k → ℝ) → ℝ := fun j ω => (ω j ⬝ᵥ u') / √v with hV
  have hind : iIndepFun X P := by
    rw [hP]
    exact iIndepFun_pi (μ := fun _ : Fin m => ρ) (X := fun _ r => Φ r)
      (fun _ => hΦm.aemeasurable)
  have hXm : ∀ j, Measurable (X j) := fun j => hΦm.comp (measurable_pi_apply j)
  have hdotm : ∀ (w : Fin k → ℝ) (j : Fin m), Measurable
      (fun ω : Fin m → Fin k → ℝ => (ω j ⬝ᵥ w) / √v) := by
    intro w j
    refine Measurable.div_const ?_ _
    simp only [dotProduct]
    exact Finset.measurable_sum _ fun l _ =>
      ((measurable_pi_apply l).comp (measurable_pi_apply j)).mul_const _
  have hmapU : ∀ (w : Fin k → ℝ), normSq w = 1 → ∀ j : Fin m,
      P.map (fun ω => (ω j ⬝ᵥ w) / √v) = gaussianReal 0 1 := by
    intro w hw j
    have hev : P.map (Function.eval j) = ρ := by
      rw [hP]; exact (measurePreserving_eval (μ := fun _ : Fin m => ρ) j).map_eq
    have hg : Measurable (fun r : Fin k → ℝ => (r ⬝ᵥ w) / √v) := by
      refine Measurable.div_const ?_ _
      simp only [dotProduct]; fun_prop
    have e2 : (fun ω : Fin m → Fin k → ℝ => (ω j ⬝ᵥ w) / √v) =
        (fun r : Fin k → ℝ => (r ⬝ᵥ w) / √v) ∘ Function.eval j := rfl
    rw [e2, ← Measure.map_map hg (measurable_pi_apply j), hev, hρ,
      Measure.map_map hg (measurable_const_smul _)]
    have e3 : ((fun r : Fin k → ℝ => (r ⬝ᵥ w) / √v) ∘ fun ξ => √v • ξ) = fun ξ => ξ ⬝ᵥ w := by
      funext ξ
      simp only [Function.comp, smul_dotProduct, smul_eq_mul]
      field_simp
    rw [e3, s2_map_unit hw]
  have hdom' : ∀ j ω, |X j ω| ≤ b * (U j ω ^ 2 + V j ω ^ 2) / 2 := fun j ω => hdom (ω j)
  have hbr := bn_rowsum hind hXm (fun j => hdotm u j) (fun j => hdotm u' j) (hmapU u hu)
    (hmapU u' hu') hb hdom' hm hτ
  have hEX : ∀ j, ∫ ω, X j ω ∂P = ∫ ξ, Φ (√v • ξ) ∂stdGauss (Fin k) := by
    intro j
    rw [hP, integral_comp_eval (μ := fun _ : Fin m => ρ) (i := j) hΦm.aestronglyMeasurable, hmean]
  refine le_trans (measureReal_mono (fun ω hω => ?_)) hbr
  simp only [Set.mem_setOf_eq] at hω ⊢
  simp_rw [hEX]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact hω

lemma s2_Phi_scale {k : ℕ} {t : ℝ} (ht : 0 < t) {a a' p p' : Fin k → ℝ} (ha : a ≠ 0)
    (ha' : a' ≠ 0) (ξ : Fin k → ℝ) :
    s2_Phi a a' p p' (√t • ξ) = t * (posI (ξ ⬝ᵥ s2_unit a) *
      posI (ξ ⬝ᵥ s2_unit a') * ((ξ ⬝ᵥ p) * (ξ ⬝ᵥ p'))) := by
  have hst : 0 < √t := Real.sqrt_pos.2 ht
  simp only [s2_Phi, smul_dotProduct, smul_eq_mul]
  rw [posI_mul_of_pos hst, posI_mul_of_pos hst, s2_posI_unit ha, s2_posI_unit ha']
  have : √t * (ξ ⬝ᵥ p) * (√t * (ξ ⬝ᵥ p')) = t * ((ξ ⬝ᵥ p) * (ξ ⬝ᵥ p')) := by
    rw [show √t * (ξ ⬝ᵥ p) * (√t * (ξ ⬝ᵥ p')) = (√t * √t) * ((ξ ⬝ᵥ p) * (ξ ⬝ᵥ p')) by ring,
      Real.mul_self_sqrt ht.le]
  rw [this]; ring

/-- **The conditional scalar-sum deviation** (Lemma TI, "the conditional scalar summands have
envelope `t_A p₊²(U² + V²)/2`, so the row-sum bound gives `|s − E[s|A₁]| ≤ r_s`"): for FIXED
`a, a' ≠ 0`, `p, p' ≠ 0` with `|p|, |p'| ≤ p₊`, under `A₂ ~ gaussMat m k t` (`t > 0`, `m > 0`):
`Pr(|s − E[s]| > r_s) ≤ 2e^{−τ}`, `r_s = 2·t p₊²(√(2mτ) + τ)`, where
`s = Σᵢ mask((A₂a)ᵢ)mask((A₂a')ᵢ)(A₂p)ᵢ(A₂p')ᵢ` and `E[s]` is the closed form of `s2_mean_s`. -/
theorem s2_scalar_dev {m k : ℕ} {t : ℝ} (ht : 0 < t) {a a' p p' : Fin k → ℝ} (ha : a ≠ 0)
    (ha' : a' ≠ 0) (hq : (s2_unit a ⬝ᵥ s2_unit a') ^ 2 < 1) (hp : p ≠ 0) (hp' : p' ≠ 0)
    {pp τ : ℝ} (hpp : √(normSq p) ≤ pp) (hpp' : √(normSq p') ≤ pp) (hm : 0 < m) (hτ : 0 ≤ τ) :
    (gaussMat m k t).real {A | 2 * (t * pp ^ 2) * (√(2 * m * τ) + τ) <
      |∑ i, BstLean.Part151.mask ((A *ᵥ a) i) * BstLean.Part151.mask ((A *ᵥ a') i) *
          ((A *ᵥ p) i * (A *ᵥ p') i) -
        m * t * (kdot (s2_unit a ⬝ᵥ s2_unit a') / 2 * (p ⬝ᵥ p') +
          ((p ⬝ᵥ s2_unit a) * (p' ⬝ᵥ s2_unit a') + (p' ⬝ᵥ s2_unit a) * (p ⬝ᵥ s2_unit a') -
            (s2_unit a ⬝ᵥ s2_unit a') * ((p ⬝ᵥ s2_unit a) * (p' ⬝ᵥ s2_unit a) +
              (p ⬝ᵥ s2_unit a') * (p' ⬝ᵥ s2_unit a'))) /
            (2 * π * √(1 - (s2_unit a ⬝ᵥ s2_unit a') ^ 2)))|} ≤ 2 * exp (-τ) := by
  have hsp : 0 < √(normSq p) := Real.sqrt_pos.2 (s2_normSq_pos hp)
  have hsp' : 0 < √(normSq p') := Real.sqrt_pos.2 (s2_normSq_pos hp')
  have hpp0 : 0 < pp := lt_of_lt_of_le hsp hpp
  have hst : 0 < √t := Real.sqrt_pos.2 ht
  have hb : 0 < t * pp ^ 2 := by positivity
  have hdom : ∀ r : Fin k → ℝ, |s2_Phi a a' p p' r| ≤ t * pp ^ 2 *
      (((r ⬝ᵥ s2_unit p) / √t) ^ 2 + ((r ⬝ᵥ s2_unit p') / √t) ^ 2) / 2 := by
    intro r
    set X := r ⬝ᵥ s2_unit p
    set Y := r ⬝ᵥ s2_unit p'
    have e : t * pp ^ 2 * ((X / √t) ^ 2 + (Y / √t) ^ 2) / 2 = pp ^ 2 * (X ^ 2 + Y ^ 2) / 2 := by
      rw [div_pow, div_pow, Real.sq_sqrt ht.le]; field_simp
    rw [e]
    obtain ⟨a0, a1⟩ := sb_posI_le (r ⬝ᵥ a)
    obtain ⟨b0, b1⟩ := sb_posI_le (r ⬝ᵥ a')
    have hpq : posI (r ⬝ᵥ a) * posI (r ⬝ᵥ a') ≤ 1 := by nlinarith
    have h1 : |s2_Phi a a' p p' r| ≤ |r ⬝ᵥ p| * |r ⬝ᵥ p'| := by
      simp only [s2_Phi]
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg a0, abs_of_nonneg b0]
      have hz := mul_nonneg (abs_nonneg (r ⬝ᵥ p)) (abs_nonneg (r ⬝ᵥ p'))
      nlinarith
    have h2 : |r ⬝ᵥ p| * |r ⬝ᵥ p'| ≤ pp ^ 2 * (|X| * |Y|) := by
      rw [s2_dot_unit hp r, s2_dot_unit hp' r, abs_mul, abs_mul, abs_of_pos hsp, abs_of_pos hsp']
      have hX := abs_nonneg X; have hY := abs_nonneg Y
      calc √(normSq p) * |X| * (√(normSq p') * |Y|) = (√(normSq p) * √(normSq p')) * (|X| * |Y|) := by ring
        _ ≤ pp ^ 2 * (|X| * |Y|) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            rw [sq]; exact mul_le_mul hpp hpp' hsp'.le hpp0.le
    have h3 : |X| * |Y| ≤ (X ^ 2 + Y ^ 2) / 2 := by
      nlinarith [sq_nonneg (|X| - |Y|), sq_abs X, sq_abs Y]
    calc |s2_Phi a a' p p' r| ≤ pp ^ 2 * (|X| * |Y|) := h1.trans h2
      _ ≤ pp ^ 2 * ((X ^ 2 + Y ^ 2) / 2) := mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = pp ^ 2 * (X ^ 2 + Y ^ 2) / 2 := by ring
  have hd := s2_dev (m := m) ht (s2_measurable_Phi a a' p p') (s2_unit_norm hp) (s2_unit_norm hp')
    hb hdom hm hτ
  obtain ⟨-, hbv⟩ := s2_polar_bil (s2_unit_norm ha) (s2_unit_norm ha') hq p p'
  have hI : ∫ ξ, s2_Phi a a' p p' (√t • ξ) ∂stdGauss (Fin k) = t * (kdot (s2_unit a ⬝ᵥ s2_unit a') / 2 * (p ⬝ᵥ p') +
          ((p ⬝ᵥ s2_unit a) * (p' ⬝ᵥ s2_unit a') + (p' ⬝ᵥ s2_unit a) * (p ⬝ᵥ s2_unit a') -
            (s2_unit a ⬝ᵥ s2_unit a') * ((p ⬝ᵥ s2_unit a) * (p' ⬝ᵥ s2_unit a) +
              (p ⬝ᵥ s2_unit a') * (p' ⬝ᵥ s2_unit a'))) /
            (2 * π * √(1 - (s2_unit a ⬝ᵥ s2_unit a') ^ 2))) := by
    simp_rw [s2_Phi_scale ht ha ha']
    rw [integral_const_mul, hbv]
  rw [hI] at hd
  refine le_trans (le_of_eq ?_) hd
  congr 1
  ext A
  simp only [Set.mem_setOf_eq]
  rw [mul_assoc (m : ℝ) t]
  rfl

/-- **The scalar bound of Lemma TI** (deterministic; paper: "The stated positive-factor condition
makes both factors in the second term of (cm) positive. Each factor is at most `Λ`. Since
`1/2 ≤ κ̇(q) ≤ κ̇(c₁⁺)`, the sign rule for `U` is valid. Dropping the positive product gives `L`").
If `0 ≤ q ≤ c₁⁺ < 1`, `pp_L ≤ ⟨p,p'⟩ ≤ pp_U`, both factors `⟨p,v'⟩ − qε`, `⟨p',v⟩ − qε'` lie in
`[0, Λ]`, `|ε||ε'| ≤ R_ε`, and `s` is within `r_s` of the conditional mean (t7:p04:cm), then
`s ≤ 𝖴 = (κ̇(c₁⁺)pp_U if pp_U ≥ 0, else pp_U/2) + Λ²/(π√(1 − c₁⁺²)) + R_ε + r_s` and
`s ≥ 𝖫 = κ̇(c₁⁺)·min(pp_L, 0) − R_ε − r_s`. -/
theorem s2_scalar_det {s q PP ε ε' β α' c1 ppL ppU Λ Rε rs : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ c1)
    (hc1 : c1 < 1) (hL : ppL ≤ PP) (hU : PP ≤ ppU) (hF1 : 0 ≤ β - q * ε) (hF1' : β - q * ε ≤ Λ)
    (hF2 : 0 ≤ α' - q * ε') (hF2' : α' - q * ε' ≤ Λ) (hR : |ε| * |ε'| ≤ Rε)
    (hs : |s - (kdot q * PP + 1 / (π * √(1 - q ^ 2)) * (β - q * ε) * (α' - q * ε') +
      √(1 - q ^ 2) / π * ε * ε')| ≤ rs) :
    s ≤ (if 0 ≤ ppU then kdot c1 * ppU else ppU / 2) + Λ ^ 2 / (π * √(1 - c1 ^ 2)) + Rε + rs ∧
      kdot c1 * min ppL 0 - Rε - rs ≤ s := by
  have hp := pi_pos
  have hc0 : 0 ≤ c1 := hq0.trans hq1
  have hq2 : q ^ 2 ≤ c1 ^ 2 := pow_le_pow_left₀ hq0 hq1 2
  have hc2 : c1 ^ 2 < 1 := by nlinarith
  have hσq : 0 < √(1 - q ^ 2) := Real.sqrt_pos.2 (by linarith)
  have hσc : 0 < √(1 - c1 ^ 2) := Real.sqrt_pos.2 (by linarith)
  have hσle : √(1 - c1 ^ 2) ≤ √(1 - q ^ 2) := Real.sqrt_le_sqrt (by linarith)
  have hσ1 : √(1 - q ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]; nlinarith [sq_nonneg q]
  have hK0 : 1 / 2 ≤ kdot q := half_le_kdot hq0
  have hKc : kdot q ≤ kdot c1 := kdot_monotoneOn ⟨by linarith, by linarith⟩
    ⟨by linarith, hc1.le⟩ hq1
  -- the second term
  have hk2 : 1 / (π * √(1 - q ^ 2)) ≤ 1 / (π * √(1 - c1 ^ 2)) :=
    one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_left hσle hp.le)
  have hFF : (β - q * ε) * (α' - q * ε') ≤ Λ ^ 2 := by
    rw [sq]; exact mul_le_mul hF1' hF2' hF2 (hF1.trans hF1')
  have hT2 : 1 / (π * √(1 - q ^ 2)) * (β - q * ε) * (α' - q * ε') ≤ Λ ^ 2 / (π * √(1 - c1 ^ 2)) := by
    rw [mul_assoc, div_eq_mul_one_div (Λ ^ 2), mul_comm (Λ ^ 2)]
    exact mul_le_mul hk2 hFF (mul_nonneg hF1 hF2) (by positivity)
  have hT2' : 0 ≤ 1 / (π * √(1 - q ^ 2)) * (β - q * ε) * (α' - q * ε') := by
    have := mul_nonneg hF1 hF2
    have : 0 ≤ 1 / (π * √(1 - q ^ 2)) := by positivity
    rw [mul_assoc]; positivity
  -- the third term
  have hT3 : |√(1 - q ^ 2) / π * ε * ε'| ≤ Rε := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ √(1 - q ^ 2) / π)]
    have h1 : √(1 - q ^ 2) / π ≤ 1 := by
      rw [div_le_one hp]; linarith [Real.pi_gt_three]
    have hee := mul_nonneg (abs_nonneg ε) (abs_nonneg ε')
    calc √(1 - q ^ 2) / π * |ε| * |ε'| = √(1 - q ^ 2) / π * (|ε| * |ε'|) := by ring
      _ ≤ 1 * (|ε| * |ε'|) := mul_le_mul_of_nonneg_right h1 hee
      _ ≤ Rε := by linarith
  have hs' := abs_le.1 hs
  have hT3' := abs_le.1 hT3
  constructor
  · have hKPP : kdot q * PP ≤ (if 0 ≤ ppU then kdot c1 * ppU else ppU / 2) := by
      split_ifs with h
      · rcases le_or_gt 0 PP with hP | hP
        · exact (mul_le_mul_of_nonneg_right hKc hP).trans
            (mul_le_mul_of_nonneg_left hU (by linarith))
        · have : kdot q * PP ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by linarith) hP.le
          have : 0 ≤ kdot c1 * ppU := mul_nonneg (by linarith) h
          linarith
      · have hP : PP < 0 := lt_of_le_of_lt hU (not_le.mp h)
        nlinarith
    linarith
  · have hKPP : kdot c1 * min ppL 0 ≤ kdot q * PP := by
      rcases le_or_gt 0 PP with hP | hP
      · have : kdot c1 * min ppL 0 ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) (min_le_right _ _)
        have : 0 ≤ kdot q * PP := mul_nonneg (by linarith) hP
        linarith
      · have hm : min ppL 0 = ppL := min_eq_left (hL.trans hP.le)
        rw [hm]
        nlinarith
    linarith

end BstLean.Part182

open BstLean.Part182 in
#print axioms s2_polar_bil
open BstLean.Part182 in
#print axioms s2_mean_s
open BstLean.Part182 in
#print axioms s2_cond_mean
open BstLean.Part182 in
#print axioms s2_dev
open BstLean.Part182 in
#print axioms s2_scalar_dev
open BstLean.Part182 in
#print axioms s2_scalar_det
