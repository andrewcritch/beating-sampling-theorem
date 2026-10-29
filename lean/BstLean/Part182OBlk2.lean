import BstLean.Part182OBlk
import BstLean.Part182EBlk
import BstLean.Part182Norm

/-!
# Part 182 (file `OBlk2`): the remaining O-block pieces of Lemma TI

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `proofs/option-n/theorem7-04-frame-numerator.tex`, proof of Lemma `t7:p04:ti` (O block):
"Fix `A₁` and `A₂|U₃` with `U₃ = span(a, a', p')`. Then `z` is fixed. The restriction term in `y₁`
has norm at most `√t_A(n + √3 + υ)|z|`; the remaining Gaussian masked term has norm at most
`√t_A(√K₁⁺ + υ)|z|`", and the tail row "two masked tangent lengths" in joint form.

* `o2_dot_sq`: `E(ξ·c)² = c·c` for the standard Gaussian.
* `o2_g d Q z A = |d ⊙ (Q Aᵀ z)|`; `o2_g_lip` (Frobenius-Lipschitz with constant `|z|`),
  `o2_g_sq` (`E o2_g² ≤ t|z|²∑d`), **`o2_mask_tail`** (`Pr(√t(√K + √(2τ))|z| < o2_g) ≤ e^{−τ}`).
* **`o2_y1_tail`**: under `μ₁ ⊗ gaussMat m m t`, with `z = Zf(a, A₂ P a)` (`P a` the projection on
  `U₃`, rank `≤ 3`) and the mask `d a`: `Pr(∑d ≤ K ∧ √t((√m + √3 + υ) + (√K + υ))|z| < |D₁A₂ᵀz|)
  ≤ 2e^{−τ}`, `υ = √(2τ)`. Route: `A₂ᵀz = P(A₂UUᵀ)ᵀz + (A₂Q)ᵀz`; Gordon (`eb_cond_gordon`, `m × 3`)
  for the first term; column-block independence (`eb_colsplit`) and `o2_mask_tail` for the second.
* **`o2_mtan_joint`**: the joint form of `ob_mtan_fixed` (`u`, `r` measurable functions of `A₁`).
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (mask measurable_mask)
open BstLean.Part153 (nrm nrm_nonneg nrm_sq abs_nrm_sub_le nrm_add_le nrm_mulVec_le)

lemma o2_dot_sq {ι : Type} [Fintype ι] (c : ι → ℝ) :
    Integrable (fun ξ : ι → ℝ => (ξ ⬝ᵥ c) ^ 2) (stdGauss ι) ∧
      ∫ ξ, (ξ ⬝ᵥ c) ^ 2 ∂stdGauss ι = c ⬝ᵥ c := by
  have hD : 0 ≤ c ⬝ᵥ c := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hm : Measurable (fun ξ : ι → ℝ => ξ ⬝ᵥ c) := by unfold dotProduct; fun_prop
  have hmap := BstLean.Part131.stdGauss_dot c
  have hsq : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 (c ⬝ᵥ c).toNNReal) :=
    (memLp_id_gaussianReal (μ := 0) (v := (c ⬝ᵥ c).toNNReal) 2).integrable_sq
  have hint : Integrable (fun ξ : ι → ℝ => (ξ ⬝ᵥ c) ^ 2) (stdGauss ι) := by
    rw [← hmap] at hsq
    exact (integrable_map_measure (μ := stdGauss ι) (f := fun ξ : ι → ℝ => ξ ⬝ᵥ c)
      (by fun_prop) hm.aemeasurable).1 hsq
  refine ⟨hint, ?_⟩
  have h := integral_map (μ := stdGauss ι) hm.aemeasurable
    (f := fun x : ℝ => x ^ 2) (by fun_prop)
  rw [hmap] at h
  rw [← h]
  have hv := variance_id_gaussianReal (μ := (0 : ℝ)) (v := (c ⬝ᵥ c).toNNReal)
  rw [variance_eq_integral measurable_id.aemeasurable] at hv
  simp only [id] at hv
  rw [integral_id_gaussianReal] at hv
  simp only [sub_zero] at hv
  rw [hv, Real.coe_toNNReal _ hD]


variable {m : ℕ}

/-- The masked projected length `|d ⊙ (Q Aᵀ z)|`. -/
noncomputable def o2_g (d : Fin m → ℝ) (Q : Matrix (Fin m) (Fin m) ℝ) (z : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ) : ℝ :=
  nrm (fun k => d k * (Q *ᵥ (Aᵀ *ᵥ z)) k)

lemma o2_nrm_mask_le {d : Fin m → ℝ} (hd : ∀ i, d i = 0 ∨ d i = 1) (w : Fin m → ℝ) :
    nrm (fun k => d k * w k) ≤ nrm w := by
  unfold nrm normSq
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ => ?_)
  rcases hd k with h | h <;> simp [h, sq_nonneg]

lemma o2_proj_nrm {Q : Matrix (Fin m) (Fin m) ℝ} (hQs : Qᵀ = Q) (hQi : Q * Q = Q)
    (w : Fin m → ℝ) : nrm (Q *ᵥ w) ≤ nrm w := by
  have h1 : nrm (Q *ᵥ w) ^ 2 = w ⬝ᵥ (Q *ᵥ w) := by
    rw [nrm_sq]
    have : normSq (Q *ᵥ w) = (Q *ᵥ w) ⬝ᵥ (Q *ᵥ w) := by
      simp [normSq, dotProduct, sq]
    rw [this, dotProduct_mulVec, ← Matrix.mulVec_transpose, hQs, Matrix.mulVec_mulVec, hQi,
      dotProduct_comm]
  have h2 := BstLean.Part153.abs_dot_le_nrm w (Q *ᵥ w)
  have h0 := nrm_nonneg (Q *ᵥ w)
  have hw0 := nrm_nonneg w
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]; exact hw0
  · have : nrm (Q *ᵥ w) ^ 2 ≤ nrm w * nrm (Q *ᵥ w) := by
      rw [h1]; exact (le_abs_self _).trans h2
    nlinarith

lemma o2_nrm_transpose_le (B : Matrix (Fin m) (Fin m) ℝ) (z : Fin m → ℝ) :
    nrm (Bᵀ *ᵥ z) ≤ nrm z * √(∑ i, ∑ j, B i j ^ 2) := by
  refine (nrm_mulVec_le Bᵀ z).trans ?_
  rw [mul_comm]
  refine mul_le_mul_of_nonneg_left ?_ (nrm_nonneg z)
  refine (opN_le_frob Bᵀ).trans (le_of_eq ?_)
  congr 1
  simp only [Matrix.transpose_apply]
  exact Finset.sum_comm

lemma o2_g_lip {d : Fin m → ℝ} (hd : ∀ i, d i = 0 ∨ d i = 1) {Q : Matrix (Fin m) (Fin m) ℝ}
    (hQs : Qᵀ = Q) (hQi : Q * Q = Q) (z : Fin m → ℝ) (A A' : Matrix (Fin m) (Fin m) ℝ) :
    |o2_g d Q z A - o2_g d Q z A'| ≤ nrm z * √(∑ i, ∑ j, (A i j - A' i j) ^ 2) := by
  unfold o2_g
  refine (abs_nrm_sub_le _ _).trans ?_
  have e : ((fun k => d k * (Q *ᵥ (Aᵀ *ᵥ z)) k) - fun k => d k * (Q *ᵥ (A'ᵀ *ᵥ z)) k) =
      fun k => d k * (Q *ᵥ ((A - A')ᵀ *ᵥ z)) k := by
    funext k
    simp only [Pi.sub_apply, Matrix.transpose_sub, Matrix.sub_mulVec, Matrix.mulVec_sub]
    ring
  rw [e]
  refine (o2_nrm_mask_le hd _).trans ((o2_proj_nrm hQs hQi _).trans ?_)
  refine (o2_nrm_transpose_le (A - A') z).trans (le_of_eq ?_)
  simp only [Matrix.sub_apply]

lemma o2_expand (Q : Matrix (Fin m) (Fin m) ℝ) (z : Fin m → ℝ) (t : ℝ) (ξ : Fin m × Fin m → ℝ)
    (k : Fin m) :
    (Q *ᵥ ((Matrix.of fun i j => √t * ξ (i, j) : Matrix (Fin m) (Fin m) ℝ)ᵀ *ᵥ z)) k =
      √t * (ξ ⬝ᵥ fun p => Q k p.2 * z p.1) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.of_apply,
    Fintype.sum_prod_type, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

lemma o2_row_le {Q : Matrix (Fin m) (Fin m) ℝ} (hQs : Qᵀ = Q) (hQi : Q * Q = Q) (k : Fin m) :
    ∑ j, Q k j ^ 2 ≤ 1 := by
  have e : ∑ j, Q k j ^ 2 = Q k k := by
    have h := congrFun (congrFun hQi k) k
    rw [Matrix.mul_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    have : Q j k = Q k j := by
      have := congrFun (congrFun hQs j) k
      simpa [Matrix.transpose_apply] using this.symm
    rw [this, sq]
  have h2 : Q k k ^ 2 ≤ ∑ j, Q k j ^ 2 :=
    Finset.single_le_sum (f := fun j => Q k j ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)
  rw [e] at h2 ⊢
  nlinarith

lemma o2_dsum {d : Fin m → ℝ} (hd : ∀ i, d i = 0 ∨ d i = 1) (k : Fin m) : d k ^ 2 = d k := by
  rcases hd k with h | h <;> simp [h]

/-- **The second moment of the masked projected length**: `E|d ⊙ (Q Aᵀz)|² ≤ t|z|²·∑d`. -/
theorem o2_g_sq {d : Fin m → ℝ} (hd : ∀ i, d i = 0 ∨ d i = 1) {Q : Matrix (Fin m) (Fin m) ℝ}
    (hQs : Qᵀ = Q) (hQi : Q * Q = Q) (z : Fin m → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun A => o2_g d Q z A ^ 2) (gaussMat m m t) ∧
      ∫ A, o2_g d Q z A ^ 2 ∂gaussMat m m t ≤ t * normSq z * ∑ i, d i := by
  set c : Fin m → Fin m × Fin m → ℝ := fun k p => Q k p.2 * z p.1 with hc
  have hpt : ∀ ξ : Fin m × Fin m → ℝ,
      o2_g d Q z (Matrix.of fun i j => √t * ξ (i, j)) ^ 2 =
        ∑ k, d k * t * (ξ ⬝ᵥ c k) ^ 2 := by
    intro ξ
    unfold o2_g
    rw [nrm_sq]
    unfold normSq
    refine Finset.sum_congr rfl fun k _ => ?_
    show (d k * (Q *ᵥ ((Matrix.of fun i j => √t * ξ (i, j) : Matrix (Fin m) (Fin m) ℝ)ᵀ *ᵥ z)) k) ^ 2 = _
    rw [o2_expand Q z t ξ k, mul_pow, mul_pow, Real.sq_sqrt ht, o2_dsum hd k]
    ring
  have hmeasF := measurable_ofFlat (m := m) (k := m) √t
  have hgm : Measurable (fun A : Matrix (Fin m) (Fin m) ℝ => o2_g d Q z A ^ 2) := by
    unfold o2_g nrm normSq
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
    fun_prop
  have hI : Integrable (fun ξ : Fin m × Fin m → ℝ => ∑ k, d k * t * (ξ ⬝ᵥ c k) ^ 2)
      (stdGauss (Fin m × Fin m)) :=
    integrable_finsetSum _ fun k _ => (o2_dot_sq (c k)).1.const_mul _
  have hI' : Integrable (fun ξ : Fin m × Fin m → ℝ =>
      o2_g d Q z (Matrix.of fun i j => √t * ξ (i, j)) ^ 2) (stdGauss (Fin m × Fin m)) := by
    simp_rw [hpt]; exact hI
  refine ⟨?_, ?_⟩
  · unfold gaussMat
    exact (integrable_map_measure hgm.aestronglyMeasurable hmeasF.aemeasurable).2 hI'
  · unfold gaussMat
    rw [integral_map hmeasF.aemeasurable hgm.aestronglyMeasurable]
    simp_rw [hpt]
    rw [integral_finsetSum _ fun k _ => (o2_dot_sq (c k)).1.const_mul _]
    simp_rw [integral_const_mul, (o2_dot_sq _).2]
    have hck : ∀ k, c k ⬝ᵥ c k ≤ normSq z := by
      intro k
      have e : c k ⬝ᵥ c k = (∑ j, Q k j ^ 2) * normSq z := by
        simp only [hc, dotProduct, Fintype.sum_prod_type, normSq, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        ring
      rw [e]
      have := o2_row_le hQs hQi k
      have h0 : 0 ≤ normSq z := Finset.sum_nonneg fun i _ => sq_nonneg _
      nlinarith
    calc ∑ k, d k * t * (c k ⬝ᵥ c k) ≤ ∑ k, d k * t * normSq z :=
          Finset.sum_le_sum fun k _ => by
            have : 0 ≤ d k * t := mul_nonneg (by rcases hd k with h | h <;> simp [h]) ht
            exact mul_le_mul_of_nonneg_left (hck k) this
      _ = t * normSq z * ∑ i, d i := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring

lemma o2_g_nonneg (d : Fin m → ℝ) (Q : Matrix (Fin m) (Fin m) ℝ) (z : Fin m → ℝ)
    (A : Matrix (Fin m) (Fin m) ℝ) : 0 ≤ o2_g d Q z A := nrm_nonneg _

lemma measurable_o2_g (d : Fin m → ℝ) (Q : Matrix (Fin m) (Fin m) ℝ) (z : Fin m → ℝ) :
    Measurable (o2_g d Q z) := by
  unfold o2_g nrm normSq
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  fun_prop

/-- **The masked projected Gaussian length for a fixed `z`**: for a 0/1 vector `d` with
`∑ d ≤ K`, a symmetric idempotent `Q` and `A ∼ gaussMat m m t`,
`Pr(√t(√K + √(2τ))|z| < |d ⊙ (Q Aᵀ z)|) ≤ e^{−τ}`. -/
theorem o2_mask_tail {d : Fin m → ℝ} (hd : ∀ i, d i = 0 ∨ d i = 1) {K : ℝ} (hK : ∑ i, d i ≤ K)
    {Q : Matrix (Fin m) (Fin m) ℝ} (hQs : Qᵀ = Q) (hQi : Q * Q = Q) (z : Fin m → ℝ) {t τ : ℝ}
    (ht : 0 < t) (hτ : 0 ≤ τ) :
    (gaussMat m m t) {A | √t * (√K + √(2 * τ)) * nrm z < o2_g d Q z A} ≤
      ENNReal.ofReal (exp (-τ)) := by
  have hP : IsProbabilityMeasure (gaussMat m m t) := by unfold gaussMat; infer_instance
  by_cases hz : nrm z = 0
  · have e : {A : Matrix (Fin m) (Fin m) ℝ | √t * (√K + √(2 * τ)) * nrm z < o2_g d Q z A} = ∅ := by
      ext A
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt, hz, mul_zero]
      unfold o2_g
      have h1 := (o2_nrm_mask_le hd (Q *ᵥ (Aᵀ *ᵥ z))).trans
        ((o2_proj_nrm hQs hQi _).trans (nrm_mulVec_le Aᵀ z))
      rw [hz, mul_zero] at h1
      exact h1
    rw [e, measure_empty]; exact bot_le
  have hzp : 0 < nrm z := lt_of_le_of_ne (nrm_nonneg z) (Ne.symm hz)
  obtain ⟨hSi, hSle⟩ := o2_g_sq hd hQs hQi z ht.le
  have hm := (nm_mean (L := nrm z) (S := ∫ A, o2_g d Q z A ^ 2 ∂gaussMat m m t) (nrm_nonneg z)
    (o2_g_lip hd hQs hQi z) ht.le (o2_g_nonneg d Q z) hSi rfl).1
  have hK0 : 0 ≤ K := le_trans (Finset.sum_nonneg fun i _ => by
    rcases hd i with h | h <;> simp [h]) hK
  have hmean : ∫ A, o2_g d Q z A ∂gaussMat m m t ≤ √t * √K * nrm z := by
    refine hm.trans ?_
    have h1 : ∫ A, o2_g d Q z A ^ 2 ∂gaussMat m m t ≤ t * normSq z * K := by
      refine hSle.trans ?_
      have : 0 ≤ t * normSq z := mul_nonneg ht.le (Finset.sum_nonneg fun i _ => sq_nonneg _)
      exact mul_le_mul_of_nonneg_left hK this
    refine (Real.sqrt_le_sqrt h1).trans (le_of_eq ?_)
    have hz0 : 0 ≤ normSq z := Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [Real.sqrt_mul (mul_nonneg ht.le hz0), Real.sqrt_mul ht.le]
    have : √(normSq z) = nrm z := rfl
    rw [this]; ring
  set s := √t * √(2 * τ) * nrm z with hs
  have hs0 : 0 ≤ s := by positivity
  have hc := BstLean.Part152.gaussConc_mat_upper_sharp (g := o2_g d Q z) (nrm_nonneg z)
    (o2_g_lip hd hQs hQi z) ht.le hs0
  have hexp : -s ^ 2 / (2 * (t * nrm z ^ 2)) = -τ := by
    rw [hs, mul_pow, mul_pow, Real.sq_sqrt ht.le, Real.sq_sqrt (by linarith)]
    field_simp
  rw [hexp] at hc
  have hsub : {A : Matrix (Fin m) (Fin m) ℝ | √t * (√K + √(2 * τ)) * nrm z < o2_g d Q z A} ⊆
      {M | ∫ M, o2_g d Q z M ∂gaussMat m m t + s ≤ o2_g d Q z M} := by
    intro A hA
    simp only [mem_setOf_eq] at hA ⊢
    have : √t * (√K + √(2 * τ)) * nrm z = √t * √K * nrm z + s := by rw [hs]; ring
    linarith
  refine (measure_mono hsub).trans ?_
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hc

lemma o2_nrm_tmul_le (M : Matrix (Fin m) (Fin m) ℝ) (z : Fin m → ℝ) :
    nrm (Mᵀ *ᵥ z) ≤ opN M * nrm z := by
  have h1 : nrm (Mᵀ *ᵥ z) ^ 2 = z ⬝ᵥ (M *ᵥ (Mᵀ *ᵥ z)) := by
    rw [nrm_sq]
    have : normSq (Mᵀ *ᵥ z) = (Mᵀ *ᵥ z) ⬝ᵥ (Mᵀ *ᵥ z) := by simp [normSq, dotProduct, sq]
    rw [this, ← Matrix.vecMul_transpose, Matrix.transpose_transpose, Matrix.dotProduct_mulVec]
  have h2 := (le_abs_self _).trans (BstLean.Part153.abs_dot_le_nrm z (M *ᵥ (Mᵀ *ᵥ z)))
  have h3 := nrm_mulVec_le M (Mᵀ *ᵥ z)
  have h0 := nrm_nonneg (Mᵀ *ᵥ z)
  have hz := nrm_nonneg z
  have hM := opN_nonneg M
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h]; positivity
  · have : nrm (Mᵀ *ᵥ z) ^ 2 ≤ nrm z * (opN M * nrm (Mᵀ *ᵥ z)) := by
      rw [h1]; exact h2.trans (mul_le_mul_of_nonneg_left h3 hz)
    nlinarith

lemma o2_mask_add (d u v : Fin m → ℝ) :
    (fun k => d k * (u + v) k) = (fun k => d k * u k) + fun k => d k * v k := by
  funext k; simp [mul_add]

/-- **The bound on `|y₁|` of the O block of Lemma TI** (paper: "Fix `A₁` and `A₂|U₃`. Then `z` is
fixed. The restriction term in `y₁` has norm at most `√t(n + √3 + υ)|z|`; the remaining Gaussian
masked term has norm at most `√t(√K₁⁺ + υ)|z|`"). Setting: `μ₁` is the distribution of the first
factor `a` (e.g. `A₁`); `P a` is the orthogonal projection on `U₃` (rank `≤ 3`, expressed by
`P a = U Uᵀ P a` for some `U` with `UᵀU = 1`); `d a` is the 0/1 first-layer mask; `z` depends on
`A₂` only through `A₂ P a` (`z = Zf (a, A₂ P a)`). Then, with `A₂ ∼ gaussMat m m t` (`n = √m`),
`Pr(∑d ≤ K ∧ √t((√m + √3 + υ) + (√K + υ))|z| < |D₁ A₂ᵀ z|) ≤ 2e^{−τ}`, `υ = √(2τ)`. -/
theorem o2_y1_tail {α : Type*} [MeasurableSpace α] (μ₁ : Measure α) [IsProbabilityMeasure μ₁]
    {t τ K : ℝ} (ht : 0 < t) (hτ : 0 ≤ τ)
    (P : α → Matrix (Fin m) (Fin m) ℝ) (hPm : Measurable P) (hPs : ∀ a, (P a)ᵀ = P a)
    (hPi : ∀ a, P a * P a = P a)
    (hP3 : ∀ a, ∃ U : Matrix (Fin m) (Fin 3) ℝ, Uᵀ * U = 1 ∧ P a = U * Uᵀ * P a)
    (d : α → Fin m → ℝ) (hdm : Measurable d) (hd : ∀ a i, d a i = 0 ∨ d a i = 1)
    (Zf : α × Matrix (Fin m) (Fin m) ℝ → Fin m → ℝ) (hZ : Measurable Zf) :
    (μ₁.prod (gaussMat m m t)) {q | ∑ i, d q.1 i ≤ K ∧
      √t * ((√(m : ℝ) + √3 + √(2 * τ)) + (√K + √(2 * τ))) * nrm (Zf (q.1, q.2 * P q.1)) <
        nrm (fun k => d q.1 k * (q.2ᵀ *ᵥ Zf (q.1, q.2 * P q.1)) k)} ≤
      ENNReal.ofReal (2 * exp (-τ)) := by
  have hP2 : IsProbabilityMeasure (gaussMat m m t) := by unfold gaussMat; infer_instance
  -- measurability
  have hmul : Measurable (fun q : α × Matrix (Fin m) (Fin m) ℝ => q.2 * P q.1) :=
    (continuous_fst.matrix_mul continuous_snd).measurable.comp
      (measurable_snd.prodMk (hPm.comp measurable_fst))
  have hz : Measurable (fun q : α × Matrix (Fin m) (Fin m) ℝ => Zf (q.1, q.2 * P q.1)) :=
    hZ.comp (measurable_fst.prodMk hmul)
  have hy : Measurable (fun q : α × Matrix (Fin m) (Fin m) ℝ =>
      fun k => d q.1 k * (q.2ᵀ *ᵥ Zf (q.1, q.2 * P q.1)) k) := by
    have hc : Continuous (fun w : Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) => w.1ᵀ *ᵥ w.2) :=
      continuous_fst.matrix_transpose.matrix_mulVec continuous_snd
    have h1 := hc.measurable.comp (measurable_snd.prodMk hz)
    refine measurable_pi_iff.mpr fun k => ?_
    exact ((measurable_pi_apply k).comp (hdm.comp measurable_fst)).mul
      ((measurable_pi_apply k).comp h1)
  have hSm : MeasurableSet {q : α × Matrix (Fin m) (Fin m) ℝ | ∑ i, d q.1 i ≤ K ∧
      √t * ((√(m : ℝ) + √3 + √(2 * τ)) + (√K + √(2 * τ))) * nrm (Zf (q.1, q.2 * P q.1)) <
        nrm (fun k => d q.1 k * (q.2ᵀ *ᵥ Zf (q.1, q.2 * P q.1)) k)} := by
    have hsum : Measurable (fun q : α × Matrix (Fin m) (Fin m) ℝ => ∑ i, d q.1 i) :=
      Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).comp (hdm.comp measurable_fst)
    exact (measurableSet_le hsum measurable_const).inter
      (measurableSet_lt ((ob_meas_nrm hz).const_mul _) (ob_meas_nrm hy))
  rw [Measure.prod_apply hSm]
  have hinner : ∀ a : α, (gaussMat m m t) (Prod.mk a ⁻¹' {q : α × Matrix (Fin m) (Fin m) ℝ |
      ∑ i, d q.1 i ≤ K ∧
      √t * ((√(m : ℝ) + √3 + √(2 * τ)) + (√K + √(2 * τ))) * nrm (Zf (q.1, q.2 * P q.1)) <
        nrm (fun k => d q.1 k * (q.2ᵀ *ᵥ Zf (q.1, q.2 * P q.1)) k)}) ≤
      ENNReal.ofReal (2 * exp (-τ)) := by
    intro a
    by_cases hKa : ∑ i, d a i ≤ K
    swap
    · have e : Prod.mk a ⁻¹' {q : α × Matrix (Fin m) (Fin m) ℝ | ∑ i, d q.1 i ≤ K ∧
          √t * ((√(m : ℝ) + √3 + √(2 * τ)) + (√K + √(2 * τ))) * nrm (Zf (q.1, q.2 * P q.1)) <
            nrm (fun k => d q.1 k * (q.2ᵀ *ᵥ Zf (q.1, q.2 * P q.1)) k)} = ∅ := by
        ext A; simp only [mem_preimage, mem_setOf_eq, mem_empty_iff_false, iff_false, not_and]
        intro h; exact absurd h hKa
      rw [e, measure_empty]; exact bot_le
    obtain ⟨U, hU, hPU⟩ := hP3 a
    set Pa := P a with hPa
    set Q : Matrix (Fin m) (Fin m) ℝ := 1 - Pa with hQ
    have hQs : Qᵀ = Q := by rw [hQ, Matrix.transpose_sub, Matrix.transpose_one, hPs a]
    have hQi : Q * Q = Q := by
      rw [hQ, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, hPi a]; abel
    have hPU' : Pa = Pa * (U * Uᵀ) := by
      have h := congrArg Matrix.transpose hPU
      rw [hPs a, Matrix.transpose_mul, hPs a, Matrix.transpose_mul, Matrix.transpose_transpose] at h
      rw [← hPa] at h
      exact h
    set c1 := √t * (√(m : ℝ) + √3 + √(2 * τ)) with hc1
    set c2 := √t * (√K + √(2 * τ)) with hc2
    set E1 := {A : Matrix (Fin m) (Fin m) ℝ | √t * (√((m : ℕ) : ℝ) + √((3 : ℕ) : ℝ) + √(2 * τ)) ≤
      opN (((1 : Matrix (Fin m) (Fin m) ℝ) * (1 : Matrix (Fin m) (Fin m) ℝ)ᵀ) * A * (U * Uᵀ))}
      with hE1
    set T := {X : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin m) ℝ |
      c2 * nrm (Zf (a, X.1)) < nrm (fun k => d a k * (X.2ᵀ *ᵥ Zf (a, X.1)) k)} with hT
    set f : Matrix (Fin m) (Fin m) ℝ → Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin m) ℝ :=
      fun A => (A * Pa, A * Q) with hf
    have hfm : Measurable f := by
      refine Measurable.prodMk ?_ ?_ <;>
      exact (continuous_id.matrix_mul continuous_const).measurable
    have hZa : Measurable (fun X : Matrix (Fin m) (Fin m) ℝ => Zf (a, X)) :=
      hZ.comp measurable_prodMk_left
    have hTm : MeasurableSet T := by
      have hza : Measurable (fun X : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin m) ℝ =>
          Zf (a, X.1)) := hZa.comp measurable_fst
      have hc : Continuous (fun w : Matrix (Fin m) (Fin m) ℝ × (Fin m → ℝ) => w.1ᵀ *ᵥ w.2) :=
        continuous_fst.matrix_transpose.matrix_mulVec continuous_snd
      have hyy : Measurable (fun X : Matrix (Fin m) (Fin m) ℝ × Matrix (Fin m) (Fin m) ℝ =>
          fun k => d a k * (X.2ᵀ *ᵥ Zf (a, X.1)) k) := by
        have h1 := hc.measurable.comp (measurable_snd.prodMk hza)
        exact measurable_pi_iff.mpr fun k => measurable_const.mul ((measurable_pi_apply k).comp h1)
      exact measurableSet_lt ((ob_meas_nrm hza).const_mul _) (ob_meas_nrm hyy)
    have hsub : Prod.mk a ⁻¹' {q : α × Matrix (Fin m) (Fin m) ℝ | ∑ i, d q.1 i ≤ K ∧
        √t * ((√(m : ℝ) + √3 + √(2 * τ)) + (√K + √(2 * τ))) * nrm (Zf (q.1, q.2 * P q.1)) <
          nrm (fun k => d q.1 k * (q.2ᵀ *ᵥ Zf (q.1, q.2 * P q.1)) k)} ⊆ E1 ∪ f ⁻¹' T := by
      intro A hA
      simp only [mem_preimage, mem_setOf_eq] at hA
      obtain ⟨-, hA⟩ := hA
      by_contra hc
      simp only [mem_union, not_or] at hc
      obtain ⟨h1, h2⟩ := hc
      simp only [hE1, mem_setOf_eq, not_le, Matrix.transpose_one, Matrix.one_mul,
        Nat.cast_ofNat] at h1
      simp only [mem_preimage, hT, hf, mem_setOf_eq, not_lt] at h2
      set z := Zf (a, A * Pa) with hzd
      -- the split `Aᵀz = P(Aᵀz) + Q(Aᵀz)`
      have hsplit : Aᵀ *ᵥ z = Pa *ᵥ ((A * (U * Uᵀ))ᵀ *ᵥ z) + (A * Q)ᵀ *ᵥ z := by
        have eA : (A * (U * Uᵀ))ᵀ = (U * Uᵀ) * Aᵀ := by
          rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose]
        have eQ : (A * Q)ᵀ = Q * Aᵀ := by rw [Matrix.transpose_mul, hQs]
        rw [eA, eQ, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← hPU',
          ← Matrix.add_mulVec, hQ, Matrix.sub_mul, Matrix.one_mul]
        congr 1; abel
      have hb1 : nrm (fun k => d a k * (Pa *ᵥ ((A * (U * Uᵀ))ᵀ *ᵥ z)) k) ≤ c1 * nrm z := by
        refine (o2_nrm_mask_le (hd a) _).trans ((o2_proj_nrm (hPs a) (hPi a) _).trans ?_)
        refine (o2_nrm_tmul_le _ z).trans ?_
        rw [hc1]
        exact mul_le_mul_of_nonneg_right h1.le (nrm_nonneg z)
      have hlt := hA
      rw [hsplit, o2_mask_add] at hlt
      have htri := nrm_add_le (fun k => d a k * (Pa *ᵥ ((A * (U * Uᵀ))ᵀ *ᵥ z)) k)
        (fun k => d a k * ((A * Q)ᵀ *ᵥ z) k)
      have : √t * ((√(m : ℝ) + √3 + √(2 * τ)) + (√K + √(2 * τ))) * nrm z = c1 * nrm z + c2 * nrm z := by
        rw [hc1, hc2]; ring
      linarith
    -- the two probabilities
    have hE1b : (gaussMat m m t) E1 ≤ ENNReal.ofReal (exp (-τ)) := by
      have h := eb_cond_gordon (M := m) (k := m) (K := m) (d := 3) ht
        (1 : Matrix (Fin m) (Fin m) ℝ) U (by simp) hU (υ := √(2 * τ)) (Real.sqrt_nonneg _)
      rw [Real.sq_sqrt (by linarith)] at h
      have e : -(2 * τ) / 2 = -τ := by ring
      rw [e] at h
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal h
    have hE2b : (gaussMat m m t) (f ⁻¹' T) ≤ ENNReal.ofReal (exp (-τ)) := by
      rw [← Measure.map_apply hfm hTm]
      have hcs := eb_colsplit (M := m) t Pa (hPs a) (hPi a)
      rw [← hQ] at hcs
      rw [show (gaussMat m m t).map f = _ from hcs, Measure.prod_apply hTm]
      have hν1 : IsProbabilityMeasure ((gaussMat m m t).map (fun A => A * Pa)) := inferInstance
      calc ∫⁻ X₁, ((gaussMat m m t).map (fun A => A * Q)) (Prod.mk X₁ ⁻¹' T)
            ∂(gaussMat m m t).map (fun A => A * Pa)
          ≤ ∫⁻ _X₁, ENNReal.ofReal (exp (-τ)) ∂(gaussMat m m t).map (fun A => A * Pa) := by
            refine lintegral_mono fun X₁ => ?_
            have hgm : Measurable (fun A : Matrix (Fin m) (Fin m) ℝ => A * Q) :=
              (continuous_id.matrix_mul continuous_const).measurable
            rw [Measure.map_apply hgm (measurable_prodMk_left hTm)]
            refine le_trans (measure_mono ?_) (o2_mask_tail (hd a) hKa hQs hQi (Zf (a, X₁)) ht hτ)
            intro A hA
            simp only [mem_preimage, hT, mem_setOf_eq] at hA ⊢
            unfold o2_g
            have e : (A * Q)ᵀ *ᵥ Zf (a, X₁) = Q *ᵥ (Aᵀ *ᵥ Zf (a, X₁)) := by
              rw [Matrix.transpose_mul, hQs, Matrix.mulVec_mulVec]
            rw [← e, ← hc2]; exact hA
        _ = ENNReal.ofReal (exp (-τ)) := by rw [lintegral_const, measure_univ, mul_one]
    calc (gaussMat m m t) _ ≤ (gaussMat m m t) (E1 ∪ f ⁻¹' T) := measure_mono hsub
      _ ≤ (gaussMat m m t) E1 + (gaussMat m m t) (f ⁻¹' T) := measure_union_le _ _
      _ ≤ ENNReal.ofReal (exp (-τ)) + ENNReal.ofReal (exp (-τ)) := add_le_add hE1b hE2b
      _ = ENNReal.ofReal (2 * exp (-τ)) := by
          rw [← ENNReal.ofReal_add (exp_pos _).le (exp_pos _).le]; ring_nf
  calc ∫⁻ a, (gaussMat m m t) (Prod.mk a ⁻¹' _) ∂μ₁
      ≤ ∫⁻ _a, ENNReal.ofReal (2 * exp (-τ)) ∂μ₁ := lintegral_mono hinner
    _ = ENNReal.ofReal (2 * exp (-τ)) := by rw [lintegral_const, measure_univ, mul_one]

/-- **The masked tangent length on the joint weights** (joint form of `ob_mtan_fixed`): for a unit
`u = U(a)` and `r = R(a) ⊥ u`, measurable functions of the first factor,
`Pr(tr diag(mask(A₂u)) ≤ K ∧ √w(√K + √(2τ))|r| < |diag(mask(A₂u)) A₂ r|) ≤ e^{−τ}`. -/
theorem o2_mtan_joint {α : Type*} [MeasurableSpace α] (μ₁ : Measure α) [IsProbabilityMeasure μ₁]
    {M k : ℕ} {w : ℝ} (hw : 0 < w) (Uf Rf : α → Fin k → ℝ) (hUm : Measurable Uf)
    (hRm : Measurable Rf) (hU : ∀ a, normSq (Uf a) = 1) (hUR : ∀ a, Uf a ⬝ᵥ Rf a = 0)
    {K τ : ℝ} (hτ : 0 ≤ τ) :
    (μ₁.prod (gaussMat M k w)) {q | ∑ i, mask ((q.2 *ᵥ Uf q.1) i) ≤ K ∧
      √w * (√K + √(2 * τ)) * nrm (Rf q.1) < nrm (obD (q.2 *ᵥ Uf q.1) *ᵥ (q.2 *ᵥ Rf q.1))} ≤
      ENNReal.ofReal (exp (-τ)) := by
  have hP2 : IsProbabilityMeasure (gaussMat M k w) := by unfold gaussMat; infer_instance
  have hc : Continuous (fun z : Matrix (Fin M) (Fin k) ℝ × (Fin k → ℝ) => z.1 *ᵥ z.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have hAu : Measurable (fun q : α × Matrix (Fin M) (Fin k) ℝ => q.2 *ᵥ Uf q.1) :=
    hc.measurable.comp (measurable_snd.prodMk (hUm.comp measurable_fst))
  have hAr : Measurable (fun q : α × Matrix (Fin M) (Fin k) ℝ => q.2 *ᵥ Rf q.1) :=
    hc.measurable.comp (measurable_snd.prodMk (hRm.comp measurable_fst))
  have hsum : Measurable (fun q : α × Matrix (Fin M) (Fin k) ℝ => ∑ i, mask ((q.2 *ᵥ Uf q.1) i)) :=
    Finset.measurable_sum _ fun i _ => measurable_mask.comp ((measurable_pi_apply i).comp hAu)
  have hv : Measurable (fun q : α × Matrix (Fin M) (Fin k) ℝ =>
      obD (q.2 *ᵥ Uf q.1) *ᵥ (q.2 *ᵥ Rf q.1)) := by
    simp_rw [ob_obD_mulVec]
    exact measurable_pi_iff.mpr fun i =>
      (measurable_mask.comp ((measurable_pi_apply i).comp hAu)).mul ((measurable_pi_apply i).comp hAr)
  have hSm : MeasurableSet {q : α × Matrix (Fin M) (Fin k) ℝ | ∑ i, mask ((q.2 *ᵥ Uf q.1) i) ≤ K ∧
      √w * (√K + √(2 * τ)) * nrm (Rf q.1) < nrm (obD (q.2 *ᵥ Uf q.1) *ᵥ (q.2 *ᵥ Rf q.1))} :=
    (measurableSet_le hsum measurable_const).inter
      (measurableSet_lt ((ob_meas_nrm (hRm.comp measurable_fst)).const_mul _) (ob_meas_nrm hv))
  rw [Measure.prod_apply hSm]
  calc ∫⁻ a, (gaussMat M k w) (Prod.mk a ⁻¹' {q : α × Matrix (Fin M) (Fin k) ℝ |
        ∑ i, mask ((q.2 *ᵥ Uf q.1) i) ≤ K ∧ √w * (√K + √(2 * τ)) * nrm (Rf q.1) <
          nrm (obD (q.2 *ᵥ Uf q.1) *ᵥ (q.2 *ᵥ Rf q.1))}) ∂μ₁
      ≤ ∫⁻ _a, ENNReal.ofReal (exp (-τ)) ∂μ₁ :=
        lintegral_mono fun a => ob_mtan_fixed hw (hU a) (hUR a) hτ
    _ = ENNReal.ofReal (exp (-τ)) := by rw [lintegral_const, measure_univ, mul_one]

end BstLean.Part182

open BstLean.Part182 in
#print axioms o2_mask_tail
open BstLean.Part182 in
#print axioms o2_y1_tail
open BstLean.Part182 in
#print axioms o2_mtan_joint
