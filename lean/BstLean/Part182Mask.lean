import BstLean.Part182Kap
import BstLean.Part153Bin
import BstLean.Part148Tools

/-!
# Part 182 (file `Mask`): the mask-count tails of Lemma TI (both layers)

No proof is left open; no `native_decide` or `axiom` is used.

Paper source: `proofs/option-n/theorem7-04-frame-numerator.tex`, Lemma `t7:p04:ti`, rows
"First marginal masks and first intersection count" and "Second marginal masks; second
intersection count" of the tail table: "The first two mask counts are binomial `(m, 1/2)`, their
intersection count is binomial `(m, κ̇(c)/2)`, and the second intersection count, given `A₁` with
`a, a' ≠ 0`, is binomial `(m, κ̇(q)/2)`. Lemma `t7:p04:hoeffding` with `η` gives the thresholds."

* `mk_rows_hoeff`: Hoeffding for `Σ_i f(row_i G)`, `f ∈ [0, 1]`, `G ~ gaussMat M k v` (rows
  independent by Part 148 `gaussMat_rows_map`).
* `mk_ov_mean`: `E[mask(√v ξ·u)·mask(√v ξ·u')] = κ̇(q)/2` (Sheppard, Part 182 `orthant_prob`).
* **`overlap_tail`**, `overlap_tail_le` (with `q ≤ q₊ ≤ 1`), **`single_tail`** (mean `1/2`).
* **`mask_first`**: `Pr_{A₁}(tr D₁D₁' > m(κ̇(c₊)/2 + η)) ≤ exp(−2η²m)` for unit `x, x'`, `x·x' ≤ c₊`.
* **`mask_second`**: the same for `A₂ ~ gaussMat m m (2/m)` and FIXED nonzero `a, a'` with cosine
  `≤ q₊` (to be applied conditionally on `A₁`, with `a = ReLU(A₁x)`, `a' = ReLU(A₁x')`).
The paper's `η = √(τ/(2m))` gives the charge `e^{−τ}` per count.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part151 (mask measurable_mask mask_nonneg)

/-- **Hoeffding for a `[0,1]`-valued function of the rows of a Gaussian matrix**:
`Pr(Σ_i f(row_i G) > M(p + η)) ≤ exp(−2η²M)`, `p = E f(√v ξ)`. -/
theorem mk_rows_hoeff {M k : ℕ} (v : ℝ) {f : (Fin k → ℝ) → ℝ} (hf : Measurable f)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) {η : ℝ} (hη : 0 ≤ η) :
    (gaussMat M k v).real
      {G | (M : ℝ) * ((∫ ξ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k)) + η) < ∑ i, f (rowOf i G)} ≤
      exp (-2 * η ^ 2 * M) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  set ρ : Measure (Fin k → ℝ) := (stdGauss (Fin k)).map (fun ξ => Real.sqrt v • ξ) with hρ
  have hρp : IsProbabilityMeasure ρ := by
    rw [hρ]; exact (Measure.isProbabilityMeasure_map_iff (measurable_const_smul _).aemeasurable).2 inferInstance
  set p := ∫ ξ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k) with hp
  have hpρ : ∫ x, f x ∂ρ = p := by
    rw [hρ, integral_map (measurable_const_smul _).aemeasurable hf.aestronglyMeasurable]
  set P : Measure (Fin M → Fin k → ℝ) := Measure.pi fun _ : Fin M => ρ with hP
  have hPp : IsProbabilityMeasure P := by rw [hP]; infer_instance
  have hrows : Measurable (fun G : Matrix (Fin M) (Fin k) ℝ => fun i => rowOf i G) :=
    measurable_pi_iff.mpr fun i => measurable_rowOf i
  have hmap : (gaussMat M k v).map (fun G i => rowOf i G) = P := by
    rw [hP, hρ]; exact BstLean.Part148.gaussMat_rows_map M k v
  have hS : MeasurableSet {ω : Fin M → Fin k → ℝ | (M : ℝ) * (p + η) < ∑ i, f (ω i)} :=
    measurableSet_lt measurable_const
      (Finset.measurable_sum _ fun i _ => hf.comp (measurable_pi_apply i))
  have e : {G : Matrix (Fin M) (Fin k) ℝ | (M : ℝ) * (p + η) < ∑ i, f (rowOf i G)} =
      (fun G i => rowOf i G) ⁻¹' {ω | (M : ℝ) * (p + η) < ∑ i, f (ω i)} := rfl
  rw [e, ← map_measureReal_apply hrows hS, hmap]
  -- Hoeffding under the product measure
  have hind : iIndepFun (fun (i : Fin M) (ω : Fin M → Fin k → ℝ) => f (ω i) - p) P := by
    rw [hP]
    exact iIndepFun_pi (μ := fun _ : Fin M => ρ) (X := fun _ x => f x - p)
      (fun _ => (hf.sub_const _).aemeasurable)
  have hsub : ∀ i : Fin M, HasSubgaussianMGF (fun ω : Fin M → Fin k → ℝ => f (ω i) - p)
      ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) P := by
    intro i
    have h := hasSubgaussianMGF_of_mem_Icc (μ := P)
      (X := fun ω : Fin M → Fin k → ℝ => f (ω i)) (a := 0) (b := 1)
      (hf.comp (measurable_pi_apply i)).aemeasurable
      (ae_of_all _ fun ω => ⟨h0 _, h1 _⟩)
    have hm : ∫ ω, f (ω i) ∂P = p := by
      rw [hP, integral_comp_eval (μ := fun _ : Fin M => ρ) (i := i) hf.aestronglyMeasurable, hpρ]
    rw [hm] at h
    exact h
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind (s := Finset.univ)
    (c := fun _ => (‖(1 : ℝ) - 0‖₊ / 2) ^ 2) (fun i _ => hsub i) (ε := η * M) (by positivity)
  rw [BstLean.Part153.hoeff_exponent hM η] at h
  refine le_trans (measureReal_mono (fun ω hω => ?_)) h
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linarith


/-- The overlap indicator of one row: `mask(w·u)·mask(w·u')`. -/
noncomputable def mk_ov {k : ℕ} (u u' : Fin k → ℝ) (w : Fin k → ℝ) : ℝ :=
  mask (∑ j, w j * u j) * mask (∑ j, w j * u' j)

lemma mk_measurable_ov {k : ℕ} (u u' : Fin k → ℝ) : Measurable (mk_ov u u') :=
  (measurable_mask.comp (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).mul_const _)).mul
    (measurable_mask.comp (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).mul_const _))

lemma mk_mask_le_one (t : ℝ) : mask t ≤ 1 := by
  unfold mask; split_ifs <;> norm_num

lemma mk_ov_nonneg {k : ℕ} (u u' w : Fin k → ℝ) : 0 ≤ mk_ov u u' w :=
  mul_nonneg (mask_nonneg _) (mask_nonneg _)

lemma mk_ov_le_one {k : ℕ} (u u' w : Fin k → ℝ) : mk_ov u u' w ≤ 1 :=
  mul_le_one₀ (mk_mask_le_one _) (mask_nonneg _) (mk_mask_le_one _)

lemma mk_mask_mul_pos {s : ℝ} (hs : 0 < s) (t : ℝ) : mask (s * t) = mask t := by
  unfold mask
  by_cases ht : 0 < t
  · simp [ht, mul_pos hs ht]
  · have : ¬ 0 < s * t := fun h => ht (pos_of_mul_pos_right h hs.le)
    simp [ht, this]

/-- The unit vector `u/|u|`. -/
noncomputable def mk_unit {k : ℕ} (u : Fin k → ℝ) : Fin k → ℝ := (√(normSq u))⁻¹ • u

lemma mk_normSq_pos {k : ℕ} {u : Fin k → ℝ} (hu : u ≠ 0) : 0 < normSq u := by
  rcases (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (u i))).lt_or_eq with h | h
  · exact h
  · exfalso; apply hu; funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (u i))).1 h.symm i (Finset.mem_univ _)
    simpa using this

lemma mk_normSq_unit {k : ℕ} {u : Fin k → ℝ} (hu : u ≠ 0) : normSq (mk_unit u) = 1 := by
  have h0 : 0 < ∑ i, u i ^ 2 := mk_normSq_pos hu
  unfold mk_unit normSq
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [← Finset.mul_sum, inv_pow, Real.sq_sqrt h0.le]
  exact inv_mul_cancel₀ h0.ne'

/-- **The mean of the overlap indicator** (Sheppard): for `v > 0` and nonzero `u, u'`,
`E mk_ov u u' (√v ξ) = κ̇(q)/2`, `q = u·u'/(|u||u'|)`. -/
theorem mk_ov_mean {k : ℕ} {v : ℝ} (hv : 0 < v) {u u' : Fin k → ℝ} (hu : u ≠ 0) (hu' : u' ≠ 0) :
    ∫ ξ, mk_ov u u' (Real.sqrt v • ξ) ∂stdGauss (Fin k) =
      kdot ((∑ j, u j * u' j) / (√(normSq u) * √(normSq u'))) / 2 := by
  have hP : IsProbabilityMeasure (stdGauss (Fin k)) := by unfold stdGauss; infer_instance
  have hn := mk_normSq_pos hu
  have hn' := mk_normSq_pos hu'
  have hs : 0 < √v := Real.sqrt_pos.2 hv
  have hr : 0 < √(normSq u) := Real.sqrt_pos.2 hn
  have hr' : 0 < √(normSq u') := Real.sqrt_pos.2 hn'
  have e1 : ∀ ξ : Fin k → ℝ, mk_ov u u' (Real.sqrt v • ξ) =
      mask (∑ j, ξ j * mk_unit u j) * mask (∑ j, ξ j * mk_unit u' j) := by
    intro ξ
    unfold mk_ov mk_unit
    have ea : ∑ j, (Real.sqrt v • ξ) j * u j =
        (√v * √(normSq u)) * ∑ j, ξ j * ((√(normSq u))⁻¹ • u) j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]; field_simp
    have eb : ∑ j, (Real.sqrt v • ξ) j * u' j =
        (√v * √(normSq u')) * ∑ j, ξ j * ((√(normSq u'))⁻¹ • u') j := by
      rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Pi.smul_apply, smul_eq_mul]; field_simp
    rw [ea, eb, mk_mask_mul_pos (mul_pos hs hr), mk_mask_mul_pos (mul_pos hs hr')]
  simp_rw [e1]
  have hma : Measurable (fun w : Fin k → ℝ => ∑ j, w j * mk_unit u j) :=
    Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).mul_const _
  have hmb : Measurable (fun w : Fin k → ℝ => ∑ j, w j * mk_unit u' j) :=
    Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).mul_const _
  have hS : MeasurableSet {w : Fin k → ℝ | 0 < ∑ j, w j * mk_unit u j ∧
      0 < ∑ j, w j * mk_unit u' j} :=
    (measurableSet_lt measurable_const hma).inter (measurableSet_lt measurable_const hmb)
  have e2 : (fun w : Fin k → ℝ => mask (∑ j, w j * mk_unit u j) * mask (∑ j, w j * mk_unit u' j)) =
      {w : Fin k → ℝ | 0 < ∑ j, w j * mk_unit u j ∧ 0 < ∑ j, w j * mk_unit u' j}.indicator 1 := by
    funext w
    by_cases h1 : 0 < ∑ j, w j * mk_unit u j <;> by_cases h2 : 0 < ∑ j, w j * mk_unit u' j <;>
      simp [Set.indicator, mask, h1, h2]
  rw [e2, integral_indicator_one hS, orthant_prob (mk_normSq_unit hu) (mk_normSq_unit hu')]
  congr 2
  unfold mk_unit
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp


/-- The cosine `u·u'/(|u||u'|)` lies in `[−1, 1]`. -/
lemma mk_cos_mem {k : ℕ} {u u' : Fin k → ℝ} (hu : u ≠ 0) (hu' : u' ≠ 0) :
    -1 ≤ (∑ j, u j * u' j) / (√(normSq u) * √(normSq u')) ∧
      (∑ j, u j * u' j) / (√(normSq u) * √(normSq u')) ≤ 1 := by
  have e : (∑ j, u j * u' j) / (√(normSq u) * √(normSq u')) =
      ∑ j, mk_unit u j * mk_unit u' j := by
    unfold mk_unit
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := Real.sqrt_pos.2 (mk_normSq_pos hu)
    have := Real.sqrt_pos.2 (mk_normSq_pos hu')
    field_simp
  rw [e]
  have h1 := mk_normSq_unit hu
  have h2 := mk_normSq_unit hu'
  unfold normSq at h1 h2
  have hp : 0 ≤ ∑ j, (mk_unit u j + mk_unit u' j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hm : 0 ≤ ∑ j, (mk_unit u j - mk_unit u' j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have ep : ∑ j, (mk_unit u j + mk_unit u' j) ^ 2 = ∑ j, mk_unit u j ^ 2 +
      ∑ j, mk_unit u' j ^ 2 + 2 * ∑ j, mk_unit u j * mk_unit u' j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have em : ∑ j, (mk_unit u j - mk_unit u' j) ^ 2 = ∑ j, mk_unit u j ^ 2 +
      ∑ j, mk_unit u' j ^ 2 - 2 * ∑ j, mk_unit u j * mk_unit u' j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  constructor <;> nlinarith

/-- **The overlap-count tail** (Hoeffding with Sheppard's mean): for a Gaussian matrix
`G ~ gaussMat M k v` (`v > 0`) and fixed nonzero `u, u'` with cosine `q`,
`Pr(#{i : (Gu)_i > 0, (Gu')_i > 0} > M(κ̇(q)/2 + η)) ≤ exp(−2η²M)`. -/
theorem overlap_tail {M k : ℕ} {v : ℝ} (hv : 0 < v) {u u' : Fin k → ℝ} (hu : u ≠ 0)
    (hu' : u' ≠ 0) {η : ℝ} (hη : 0 ≤ η) :
    (gaussMat M k v).real {G | (M : ℝ) * (kdot ((∑ j, u j * u' j) /
        (√(normSq u) * √(normSq u'))) / 2 + η) <
      ∑ i, mask ((G *ᵥ u) i) * mask ((G *ᵥ u') i)} ≤ exp (-2 * η ^ 2 * M) := by
  have h := mk_rows_hoeff (M := M) v (mk_measurable_ov u u') (mk_ov_nonneg u u')
    (mk_ov_le_one u u') hη
  rw [mk_ov_mean hv hu hu'] at h
  exact h

/-- The same with an upper bound `q ≤ q₊ ≤ 1` of the cosine (`κ̇` is monotone). -/
theorem overlap_tail_le {M k : ℕ} {v : ℝ} (hv : 0 < v) {u u' : Fin k → ℝ} (hu : u ≠ 0)
    (hu' : u' ≠ 0) {qp η : ℝ} (hq : (∑ j, u j * u' j) / (√(normSq u) * √(normSq u')) ≤ qp)
    (hqp : qp ≤ 1) (hη : 0 ≤ η) :
    (gaussMat M k v).real {G | (M : ℝ) * (kdot qp / 2 + η) <
      ∑ i, mask ((G *ᵥ u) i) * mask ((G *ᵥ u') i)} ≤ exp (-2 * η ^ 2 * M) := by
  obtain ⟨hlo, hhi⟩ := mk_cos_mem hu hu'
  have hk : kdot ((∑ j, u j * u' j) / (√(normSq u) * √(normSq u'))) ≤ kdot qp :=
    kdot_monotoneOn ⟨hlo, hhi⟩ ⟨by linarith, hqp⟩ hq
  refine le_trans (measureReal_mono (fun G hG => ?_) (measure_ne_top _ _)) (overlap_tail hv hu hu' hη)
  simp only [Set.mem_setOf_eq] at hG ⊢
  have hM : (0 : ℝ) ≤ M := Nat.cast_nonneg _
  nlinarith

/-- **The single-mask count tail** (`u' = u`, `κ̇(1) = 1`): `Pr(#{i : (Gu)_i > 0} > M(1/2 + η))
≤ exp(−2η²M)`. -/
theorem single_tail {M k : ℕ} {v : ℝ} (hv : 0 < v) {u : Fin k → ℝ} (hu : u ≠ 0) {η : ℝ}
    (hη : 0 ≤ η) :
    (gaussMat M k v).real {G | (M : ℝ) * (1 / 2 + η) < ∑ i, mask ((G *ᵥ u) i)} ≤
      exp (-2 * η ^ 2 * M) := by
  have h := overlap_tail (M := M) hv hu hu hη
  have hq : (∑ j, u j * u j) / (√(normSq u) * √(normSq u)) = 1 := by
    have h0 := mk_normSq_pos hu
    rw [Real.mul_self_sqrt h0.le]
    have : ∑ j, u j * u j = normSq u := by
      unfold normSq; exact Finset.sum_congr rfl fun j _ => by ring
    rw [this, div_self h0.ne']
  have hk : kdot 1 = 1 := by simp [kdot]
  rw [hq, hk] at h
  have e : ∀ G : Matrix (Fin M) (Fin k) ℝ, ∑ i, mask ((G *ᵥ u) i) * mask ((G *ᵥ u) i) =
      ∑ i, mask ((G *ᵥ u) i) := fun G => Finset.sum_congr rfl fun i _ => by
    rw [← sq, BstLean.Part151.mask_sq]
  simp_rw [e] at h
  exact h

variable {n : ℕ}

/-- **First layer of Lemma TI**: for unit inputs `x, x'` with `x·x' ≤ c₊ ≤ 1` and
`A₁ ~ gaussMat m n (2/n)` (`m = n²`): `Pr(tr D₁D₁' > m(κ̇(c₊)/2 + η)) ≤ exp(−2η²m)`. -/
theorem mask_first {x x' : Fin n → ℝ} (hx : normSq x = 1) (hx' : normSq x' = 1) {cp η : ℝ}
    (hc : ∑ j, x j * x' j ≤ cp) (hcp : cp ≤ 1) (hη : 0 ≤ η) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real {A | ((mA n : ℕ) : ℝ) * (kdot cp / 2 + η) <
      ∑ i, mask ((A *ᵥ x) i) * mask ((A *ᵥ x') i)} ≤ exp (-2 * η ^ 2 * (mA n : ℕ)) := by
  have hne : ∀ y : Fin n → ℝ, normSq y = 1 → y ≠ 0 := by
    intro y hy h0; rw [h0] at hy; simp [normSq] at hy
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp [normSq] at hx
    · exact h
  have hv : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  refine overlap_tail_le hv (hne x hx) (hne x' hx') ?_ hcp hη
  rw [hx, hx', Real.sqrt_one, mul_one, div_one]
  exact hc

/-- **Second layer of Lemma TI** (conditional form): for FIXED nonzero `a, a' ∈ ℝ^m` (in TI:
`a = ReLU(A₁x)`, `a' = ReLU(A₁x')`) with cosine `q ≤ q₊ ≤ 1` and `A₂ ~ gaussMat m m (2/m)`:
`Pr(tr D₂D₂' > m(κ̇(q₊)/2 + η)) ≤ exp(−2η²m)`. -/
theorem mask_second {m : ℕ} {a a' : Fin m → ℝ} (ha : a ≠ 0) (ha' : a' ≠ 0) {qp η : ℝ}
    (hq : (∑ j, a j * a' j) / (√(normSq a) * √(normSq a')) ≤ qp) (hqp : qp ≤ 1) (hη : 0 ≤ η) :
    (gaussMat m m (2 / (m : ℝ))).real {A | (m : ℝ) * (kdot qp / 2 + η) <
      ∑ i, mask ((A *ᵥ a) i) * mask ((A *ᵥ a') i)} ≤ exp (-2 * η ^ 2 * m) := by
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; exact absurd (funext fun i => Fin.elim0 i) ha
    · exact h
  have hv : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  exact overlap_tail_le hv ha ha' hq hqp hη

end BstLean.Part182

open BstLean.Part182 in
#print axioms mk_rows_hoeff
open BstLean.Part182 in
#print axioms overlap_tail_le
open BstLean.Part182 in
#print axioms single_tail
open BstLean.Part182 in
#print axioms mask_first
open BstLean.Part182 in
#print axioms mask_second
