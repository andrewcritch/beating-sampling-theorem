import BstLean.Part182Blk
import BstLean.Part182Geo

/-!
# Part 182 (file `OBlk`): the O block of Lemma TI — deterministic assembly and tails

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `proofs/option-n/theorem7-04-frame-numerator.tex`, proof of Lemma `t7:p04:ti`, paragraph
"Decompose `p = εv + Π_v p` … This proves the O block", and the tail-table rows "`|p|, |p'| ≤ p₊`",
"`|v·p|, |v'·p'| ≤ υ√γ_A`", "two lengths `|A₂v|, |A₂v'|`", "two masked tangent lengths".
Notation: `J(y) = D₂A₂D₁A₁` (`ob_jac_eq`), `obD u = diag(mask u)`.

Deterministic:
* `ob_identity`: `P (J(x)ᵀJ(x')) w = (A₁P)ᵀ(D₁A₂ᵀ(D₂(J(x')w)))` for symmetric `P`.
* **`ob_assembly`**: `|J(x')w| ≤ j_z`, `|y₁| ≤ Y|z|`, `|(A₁P)ᵀy₁| ≤ B|y₁|` ⇒
  `|P(J(x)ᵀJ(x'))w| ≤ B·Y·j_z` (with `P = P_E`, `w = e'` this is the paper's `n k_o`).
* **`ob_jz`**: `|J(x)e| ≤ ε₀ a_v + C p₊` from `p = εv + r` (the paper's `j_z`).
Probabilistic (each one tail with its charge):
* `ob_chi_tail`: `Pr(√K + υ ≤ |d ⊙ ξ|) ≤ e^{−υ²/2}` (`d ∈ {0,1}`, `∑d ≤ K`).
* **`ob_p_tail`**: `Pr(tr D₁ ≤ K ∧ √v(√K + √(2τ)) ≤ |D₁A₁e|) ≤ e^{−τ}` (`p₊`).
* **`ob_eps_tail`**: `Pr(√v√(2τ) < |v·p|) ≤ 2e^{−τ}`, `v = a/|a|`.
* `ob_len_fixed`, **`ob_len_cond`**, **`ob_len_joint`**: `Pr(√v(√n + √(2τ))|y| < |(A₁P)ᵀy|) ≤ e^{−τ}`
  for `y` fixed, `y = Y(A₁x, A₁e)`, and `y = Y(A₂, A₁x, A₁e)` (the paper's conditional length of
  `B₁ᵀy₁`).
* `ob_Av_fixed`, **`ob_Av_joint`**: `Pr(√t(√m + √(2τ)) < |A₂v|) ≤ e^{−τ}`, `|v| ≤ 1`, `v = V(A₁)`.
* **`ob_mtan_fixed`**: `Pr(tr D₂ ≤ K ∧ √t(√K + √(2τ))|r| < |D₂A₂r|) ≤ e^{−τ}`, `D₂ = diag(mask(A₂u))`,
  `r ⊥ u`, `u` unit (fixed; the joint form follows as in `ob_Av_joint`).
Not done here: the restriction/projection split of `A₂` on `U₃ = span(a, a', p')` that gives
`|y₁| ≤ √t((n + √3 + υ) + (√K₁⁺ + υ))|z|` (needs the column-block independence of `A₂` given `A₁` and
`A₂|U₃`), and the union of the O-block tails.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (mask measurable_mask jac mask_nonneg)
open BstLean.Part153 (projT nrm gaussMat_decomp mask_mul_pos)

variable {m m₂ n : ℕ}

/-! ## Deterministic part -/

/-- The mask diagonal of a vector. -/
noncomputable def obD {k : ℕ} (u : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.diagonal (fun i => mask (u i))

lemma ob_mask_le_one (t : ℝ) : mask t ≤ 1 := by unfold mask; split_ifs <;> norm_num

/-- `J(y) = D₂ A₂ D₁ A₁` with the strict masks. -/
lemma ob_jac_eq (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m₂) (Fin m) ℝ)
    (y : Fin n → ℝ) :
    jac A₁ A₂ y = obD (A₂ *ᵥ reluV (A₁ *ᵥ y)) * A₂ * obD (A₁ *ᵥ y) * A₁ := by
  ext j l
  simp only [jac, obD, Matrix.of_apply]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- A mask diagonal does not increase lengths. -/
lemma ob_nrm_obD_le {k : ℕ} (u w : Fin k → ℝ) : nrm (obD u *ᵥ w) ≤ nrm w := by
  unfold nrm normSq
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  simp only [obD, Matrix.mulVec_diagonal]
  have h0 := mask_nonneg (u i)
  have h1 := ob_mask_le_one (u i)
  rw [mul_pow]
  have : mask (u i) ^ 2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg (w i)]

lemma ob_obD_transpose {k : ℕ} (u : Fin k → ℝ) : (obD u)ᵀ = obD u := by
  unfold obD; exact Matrix.diagonal_transpose _

/-- **The O-block identity**: for any symmetric `P` (e.g. `P_E`),
`P (J(x)ᵀ J(x')) w = (A₁ P)ᵀ (D₁ A₂ᵀ (D₂ (J(x') w)))`. -/
lemma ob_identity (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m₂) (Fin m) ℝ)
    (x x' : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (w : Fin n → ℝ) :
    P *ᵥ (((jac A₁ A₂ x)ᵀ * jac A₁ A₂ x') *ᵥ w) =
      (A₁ * P)ᵀ *ᵥ (obD (A₁ *ᵥ x) *ᵥ (A₂ᵀ *ᵥ (obD (A₂ *ᵥ reluV (A₁ *ᵥ x)) *ᵥ
        (jac A₁ A₂ x' *ᵥ w)))) := by
  rw [ob_jac_eq A₁ A₂ x]
  simp only [Matrix.transpose_mul, hP, ob_obD_transpose, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- **The O-block assembly** (deterministic): with `z = D₂ (J(x') w)` and `y₁ = D₁ A₂ᵀ z`, if
`|J(x') w| ≤ j_z`, `|y₁| ≤ Y |z|` and `|(A₁ P)ᵀ y₁| ≤ B |y₁|`, then
`|P (J(x)ᵀ J(x')) w| ≤ B·Y·j_z`. With `P = P_E`, `w = e'`, `B = √γ(√n + υ)`,
`Y = √t((n + √3 + υ) + (√K₁⁺ + υ))` this is the paper's `n k_o`. -/
theorem ob_assembly (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m₂) (Fin m) ℝ)
    (x x' : Fin n → ℝ) (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (w : Fin n → ℝ)
    {jz Y B : ℝ} (hY : 0 ≤ Y) (hB : 0 ≤ B)
    (hz : nrm (jac A₁ A₂ x' *ᵥ w) ≤ jz)
    (hy : nrm (obD (A₁ *ᵥ x) *ᵥ (A₂ᵀ *ᵥ (obD (A₂ *ᵥ reluV (A₁ *ᵥ x)) *ᵥ (jac A₁ A₂ x' *ᵥ w)))) ≤
      Y * nrm (obD (A₂ *ᵥ reluV (A₁ *ᵥ x)) *ᵥ (jac A₁ A₂ x' *ᵥ w)))
    (hb : nrm ((A₁ * P)ᵀ *ᵥ (obD (A₁ *ᵥ x) *ᵥ (A₂ᵀ *ᵥ (obD (A₂ *ᵥ reluV (A₁ *ᵥ x)) *ᵥ
        (jac A₁ A₂ x' *ᵥ w))))) ≤
      B * nrm (obD (A₁ *ᵥ x) *ᵥ (A₂ᵀ *ᵥ (obD (A₂ *ᵥ reluV (A₁ *ᵥ x)) *ᵥ (jac A₁ A₂ x' *ᵥ w))))) :
    nrm (P *ᵥ (((jac A₁ A₂ x)ᵀ * jac A₁ A₂ x') *ᵥ w)) ≤ B * Y * jz := by
  rw [ob_identity A₁ A₂ x x' P hP w]
  have hz' := (ob_nrm_obD_le (A₂ *ᵥ reluV (A₁ *ᵥ x)) (jac A₁ A₂ x' *ᵥ w)).trans hz
  calc _ ≤ B * nrm (obD (A₁ *ᵥ x) *ᵥ (A₂ᵀ *ᵥ (obD (A₂ *ᵥ reluV (A₁ *ᵥ x)) *ᵥ
        (jac A₁ A₂ x' *ᵥ w)))) := hb
    _ ≤ B * (Y * jz) := mul_le_mul_of_nonneg_left (hy.trans (mul_le_mul_of_nonneg_left hz' hY)) hB
    _ = B * Y * jz := by ring

/-- **The tangent length `j_z`** (deterministic): `J(x) e = D₂ A₂ p` with `p = D₁ A₁ e`; if
`p = ε v + r`, `|A₂ v| ≤ a_v`, `|ε| ≤ ε₀`, `|D₂ A₂ r| ≤ C |r|`, `|r| ≤ p₊`, then
`|J(x) e| ≤ ε₀ a_v + C p₊` (paper: `j_z = √t(n + υ)υ√γ + √t(√K₁⁺ + υ)p₊`). -/
theorem ob_jz (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m₂) (Fin m) ℝ)
    (x e : Fin n → ℝ) (v r : Fin m → ℝ) (ε : ℝ)
    (hp : obD (A₁ *ᵥ x) *ᵥ (A₁ *ᵥ e) = ε • v + r) {av ε₀ C pp : ℝ} (hC : 0 ≤ C)
    (hv : nrm (A₂ *ᵥ v) ≤ av) (hε : |ε| ≤ ε₀)
    (hr : nrm (obD (A₂ *ᵥ reluV (A₁ *ᵥ x)) *ᵥ (A₂ *ᵥ r)) ≤ C * nrm r) (hr' : nrm r ≤ pp) :
    nrm (jac A₁ A₂ x *ᵥ e) ≤ ε₀ * av + C * pp := by
  have e1 : jac A₁ A₂ x *ᵥ e = ε • (obD (A₂ *ᵥ reluV (A₁ *ᵥ x)) *ᵥ (A₂ *ᵥ v)) +
      obD (A₂ *ᵥ reluV (A₁ *ᵥ x)) *ᵥ (A₂ *ᵥ r) := by
    rw [ob_jac_eq]
    simp only [← Matrix.mulVec_mulVec]
    rw [hp, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  rw [e1]
  have hav : 0 ≤ av := (BstLean.Part153.nrm_nonneg _).trans hv
  have t1 : nrm (ε • (obD (A₂ *ᵥ reluV (A₁ *ᵥ x)) *ᵥ (A₂ *ᵥ v))) ≤ ε₀ * av := by
    rw [BstLean.Part153.nrm_smul]
    exact mul_le_mul hε ((ob_nrm_obD_le _ _).trans hv) (BstLean.Part153.nrm_nonneg _) ((abs_nonneg ε).trans hε)
  have t2 : nrm (obD (A₂ *ᵥ reluV (A₁ *ᵥ x)) *ᵥ (A₂ *ᵥ r)) ≤ C * pp :=
    hr.trans (mul_le_mul_of_nonneg_left hr' hC)
  exact (BstLean.Part153.nrm_add_le _ _).trans (add_le_add t1 t2)

/-! ## Probabilistic part -/

lemma ob_coord_sq {k : ℕ} (i : Fin k) : ∫ ξ : Fin k → ℝ, ξ i ^ 2 ∂stdGauss (Fin k) = 1 := by
  unfold stdGauss
  rw [integral_comp_eval (μ := fun _ : Fin k => gaussianReal 0 1) (i := i) (f := fun x => x ^ 2)
    (integrable_pow_gauss 2).aestronglyMeasurable, BstLean.Part29.gaussMom_eq]
  norm_num [BstLean.Part29.gaussMom]

lemma ob_coord_int {k : ℕ} (i : Fin k) :
    Integrable (fun ξ : Fin k → ℝ => ξ i ^ 2) (stdGauss (Fin k)) := by
  unfold stdGauss
  exact integrable_comp_eval (μ := fun _ : Fin k => gaussianReal 0 1) (i := i)
    (f := fun x => x ^ 2) (integrable_pow_gauss 2)

/-- **Chi tail with selected coordinates**: for `d ∈ {0,1}^k` with `∑ d ≤ K` and `υ ≥ 0`,
`Pr(√K + υ ≤ |d ⊙ ξ|) ≤ e^{−υ²/2}` under the standard Gaussian. -/
theorem ob_chi_tail {k : ℕ} (d : Fin k → ℝ) (hd : ∀ i, d i = 0 ∨ d i = 1) {K υ : ℝ}
    (hK : ∑ i, d i ≤ K) (hυ : 0 ≤ υ) :
    (stdGauss (Fin k)).real {ξ | √K + υ ≤ nrm (fun i => d i * ξ i)} ≤ exp (-υ ^ 2 / 2) := by
  set f : (Fin k → ℝ) → ℝ := fun ξ => nrm (fun i => d i * ξ i) with hf
  have hd2 : ∀ i, d i ^ 2 = d i := fun i => by rcases hd i with h | h <;> rw [h] <;> norm_num
  have hdabs : ∀ i, |d i| ≤ 1 := fun i => by rcases hd i with h | h <;> rw [h] <;> norm_num
  have hLip : BstLean.Part148.EuLip f 1 := by
    intro a b
    refine (BstLean.Part153.abs_nrm_sub_le _ _).trans ?_
    rw [one_mul]
    unfold nrm normSq
    refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
    simp only [Pi.sub_apply]
    rw [← mul_sub, mul_pow, hd2]
    rcases hd i with h | h <;> rw [h] <;> nlinarith [sq_nonneg (a i - b i)]
  have hsq : ∀ ξ, f ξ ^ 2 = ∑ i, d i * ξ i ^ 2 := by
    intro ξ
    simp only [hf, nrm, normSq]
    rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_pow, hd2]
  have hf2i : Integrable (fun ξ => f ξ ^ 2) (stdGauss (Fin k)) := by
    simp_rw [hsq]
    exact integrable_finsetSum _ fun i _ => (ob_coord_int i).const_mul _
  have hfm : Measurable f := by
    simp only [hf, nrm, normSq]; fun_prop
  have hfi : Integrable f (stdGauss (Fin k)) := by
    refine (hf2i.add (integrable_const (1 : ℝ))).mono' hfm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ξ => ?_)
    have h0 : 0 ≤ f ξ := Real.sqrt_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    show f ξ ≤ f ξ ^ 2 + 1
    nlinarith [sq_nonneg (f ξ - 1)]
  have hE2 : ∫ ξ, f ξ ^ 2 ∂stdGauss (Fin k) = ∑ i, d i := by
    simp_rw [hsq]
    rw [integral_finsetSum _ fun i _ => (ob_coord_int i).const_mul _]
    exact Finset.sum_congr rfl fun i _ => by rw [integral_const_mul, ob_coord_sq, mul_one]
  have hmean : ∫ ξ, f ξ ∂stdGauss (Fin k) ≤ √K := by
    have h1 := BstLean.Part153.sq_integral_le hfi hf2i
    rw [hE2] at h1
    have h0 : 0 ≤ ∫ ξ, f ξ ∂stdGauss (Fin k) := integral_nonneg fun ξ => Real.sqrt_nonneg _
    calc ∫ ξ, f ξ ∂stdGauss (Fin k) = √((∫ ξ, f ξ ∂stdGauss (Fin k)) ^ 2) := (Real.sqrt_sq h0).symm
      _ ≤ √K := Real.sqrt_le_sqrt (h1.trans hK)
  have h := BstLean.Part152.gaussConc_upper_sharp zero_le_one hLip hυ
  rw [one_pow, mul_one] at h
  refine le_trans (measureReal_mono (fun ξ hξ => ?_) (measure_ne_top _ _)) h
  simp only [Set.mem_setOf_eq] at hξ ⊢
  linarith

lemma ob_obD_mulVec {k : ℕ} (g u : Fin k → ℝ) : obD g *ᵥ u = fun i => mask (g i) * u i := by
  funext i; simp [obD, Matrix.mulVec_diagonal]

lemma ob_obD_smul_pos {k : ℕ} {a : ℝ} (ha : 0 < a) (g : Fin k → ℝ) : obD (a • g) = obD g := by
  unfold obD
  congr 1
  funext i
  rw [Pi.smul_apply, smul_eq_mul, mask_mul_pos ha]

lemma ob_nrm_obD_smul {k : ℕ} (g ξ : Fin k → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    nrm (obD g *ᵥ (a • ξ)) = a * nrm (fun i => mask (g i) * ξ i) := by
  rw [Matrix.mulVec_smul, BstLean.Part153.nrm_smul, abs_of_nonneg ha]
  congr 2
  funext i
  simp [obD, Matrix.mulVec_diagonal]

/-- **The tangent length `|p| ≤ p₊`** (paper: `|p|, |p'| ≤ p₊ = √γ(√K₁⁺ + υ)`): for a unit `x` and
a unit `e ⊥ x`, a Gaussian `m × n` matrix `A` (variance `v`) and `D = diag(mask(A x))`:
`Pr(tr D ≤ K ∧ √v(√K + √(2τ)) ≤ |D A e|) ≤ e^{−τ}`. -/
theorem ob_p_tail {v : ℝ} (hv : 0 < v) {x e : Fin n → ℝ} (hx : normSq x = 1)
    (he : normSq e = 1) (hxe : x ⬝ᵥ e = 0) {K τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat m n v) {A | ∑ i, mask ((A *ᵥ x) i) ≤ K ∧
      √v * (√K + √(2 * τ)) ≤ nrm (obD (A *ᵥ x) *ᵥ (A *ᵥ e))} ≤ ENNReal.ofReal (exp (-τ)) := by
  set b := √v * (√K + √(2 * τ)) with hb
  have hsv : 0 < √v := Real.sqrt_pos.2 hv
  set S2 := {q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ |
      ∑ i, mask (q.1 i) ≤ K ∧ b ≤ nrm (obD q.1 *ᵥ (q.2 *ᵥ e))} with hS2
  have hS2m : MeasurableSet S2 := by
    have h1 : Measurable (fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ => ∑ i, mask (q.1 i)) :=
      Finset.measurable_sum _ fun i _ =>
        measurable_mask.comp ((measurable_pi_apply i).comp measurable_fst)
    have h2 : Measurable (fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ =>
        nrm (obD q.1 *ᵥ (q.2 *ᵥ e))) := by
      simp only [ob_obD_mulVec, nrm, normSq]
      refine Measurable.sqrt (Finset.measurable_sum _ fun i _ => ?_)
      have hc : Measurable (fun q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ => (q.2 *ᵥ e) i) :=
        (measurable_pi_apply i).comp
          ((continuous_id.matrix_mulVec continuous_const).measurable.comp measurable_snd)
      exact ((measurable_mask.comp ((measurable_pi_apply i).comp measurable_fst)).mul hc).pow_const 2
    exact (measurableSet_le h1 measurable_const).inter (measurableSet_le measurable_const h2)
  have hf : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => (A *ᵥ x, A * projT x)) :=
    (continuous_id.matrix_mulVec continuous_const).measurable.prodMk
      (BstLean.Part153.measurable_mul_const _)
  have hset : {A : Matrix (Fin m) (Fin n) ℝ | ∑ i, mask ((A *ᵥ x) i) ≤ K ∧
      b ≤ nrm (obD (A *ᵥ x) *ᵥ (A *ᵥ e))} =
      (fun A : Matrix (Fin m) (Fin n) ℝ => (A *ᵥ x, A * projT x)) ⁻¹' S2 := by
    ext A
    simp only [mem_setOf_eq, mem_preimage, hS2, bk_mul_projT_mulVec hxe]
  rw [hset, ← bk_lint_ind _ hS2m hf,
    gaussMat_decomp hx hv.le ((measurable_one.indicator hS2m))]
  have inner : ∀ g : Fin m → ℝ, ∫⁻ M, S2.indicator 1 (√v • g, M * projT x) ∂gaussMat m n v ≤
      ENNReal.ofReal (exp (-τ)) := by
    intro g
    have hm : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => (√v • g, M * projT x)) :=
      measurable_const.prodMk (BstLean.Part153.measurable_mul_const _)
    rw [bk_lint_ind _ hS2m hm]
    have hmk : ∀ i, mask ((√v • g) i) = mask (g i) := fun i => by
      rw [Pi.smul_apply, smul_eq_mul, mask_mul_pos hsv]
    by_cases hK : ∑ i, mask (g i) ≤ K
    · -- the preimage is the set of `M` with `b ≤ |D (M e)|`
      have hT : MeasurableSet {u : Fin m → ℝ | b ≤ nrm (obD g *ᵥ u)} := by
        refine measurableSet_le measurable_const ?_
        simp only [ob_obD_mulVec, nrm, normSq]
        fun_prop
      have hpre : (fun M : Matrix (Fin m) (Fin n) ℝ => (√v • g, M * projT x)) ⁻¹' S2 ⊆
          (fun M : Matrix (Fin m) (Fin n) ℝ => M *ᵥ e) ⁻¹' {u | b ≤ nrm (obD g *ᵥ u)} := by
        intro M hM
        simp only [mem_preimage, hS2, mem_setOf_eq, bk_mul_projT_mulVec hxe,
          ob_obD_smul_pos hsv] at hM ⊢
        exact hM.2
      refine (measure_mono hpre).trans ?_
      have hmv : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => M *ᵥ e) :=
        (continuous_id.matrix_mulVec continuous_const).measurable
      rw [← Measure.map_apply hmv hT, gaussMat_mulVec, he, Real.sqrt_one, mul_one,
        Measure.map_apply (measurable_const_smul _) hT]
      have hset2 : (fun ξ : Fin m → ℝ => √v • ξ) ⁻¹' {u | b ≤ nrm (obD g *ᵥ u)} =
          {ξ | √K + √(2 * τ) ≤ nrm (fun i => mask (g i) * ξ i)} := by
        ext ξ
        simp only [mem_preimage, mem_setOf_eq, ob_nrm_obD_smul g ξ hsv.le, hb]
        exact mul_le_mul_iff_of_pos_left hsv
      rw [hset2]
      have hc := ob_chi_tail (fun i => mask (g i)) (fun i => bk_mask01 _) hK
        (Real.sqrt_nonneg (2 * τ))
      rw [Real.sq_sqrt (by linarith)] at hc
      have e2 : -(2 * τ) / 2 = -τ := by ring
      rw [e2] at hc
      rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal hc
    · have e0 : (fun M : Matrix (Fin m) (Fin n) ℝ => (√v • g, M * projT x)) ⁻¹' S2 = ∅ := by
        ext M
        simp only [mem_preimage, hS2, mem_setOf_eq, hmk, mem_empty_iff_false, iff_false, not_and]
        intro h; exact absurd h hK
      rw [e0, measure_empty]; exact bot_le
  have hP1 : IsProbabilityMeasure (stdGauss (Fin m)) := by unfold stdGauss; infer_instance
  calc ∫⁻ g, ∫⁻ M, S2.indicator 1 (√v • g, M * projT x) ∂gaussMat m n v ∂stdGauss (Fin m)
      ≤ ∫⁻ _g, ENNReal.ofReal (exp (-τ)) ∂stdGauss (Fin m) := lintegral_mono inner
    _ = ENNReal.ofReal (exp (-τ)) := by rw [lintegral_const, measure_univ, mul_one]

lemma ob_dot_obD {k : ℕ} (g w y : Fin k → ℝ) : w ⬝ᵥ (obD g *ᵥ y) = (obD g *ᵥ w) ⬝ᵥ y := by
  simp only [ob_obD_mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma ob_nrm_unit_le {k : ℕ} (a : Fin k → ℝ) : nrm ((nrm a)⁻¹ • a) ≤ 1 := by
  rw [BstLean.Part153.nrm_smul, abs_inv, abs_of_nonneg (BstLean.Part153.nrm_nonneg a)]
  by_cases h : nrm a = 0
  · rw [h]; simp
  · rw [inv_mul_cancel₀ h]

/-- **The tangent component `ε = v·p`** (paper: "`|v·p|, |v'·p'| ≤ υ√γ_A`", `v = a/|a|`,
`a = ReLU(A x)`, `p = D A e`): for a unit `x`, a unit `e ⊥ x` and a Gaussian `A` (variance `v`),
`Pr(√v·√(2τ) < |v·p|) ≤ 2e^{−τ}` (`v = 0` when `a = 0`). -/
theorem ob_eps_tail {v : ℝ} (hv : 0 < v) {x e : Fin n → ℝ} (hx : normSq x = 1)
    (he : normSq e = 1) (hxe : x ⬝ᵥ e = 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat m n v) {A | √v * √(2 * τ) < |((nrm (reluV (A *ᵥ x)))⁻¹ • reluV (A *ᵥ x)) ⬝ᵥ
      (obD (A *ᵥ x) *ᵥ (A *ᵥ e))|} ≤ ENNReal.ofReal (2 * exp (-τ)) := by
  set t := √v * √(2 * τ) with ht
  have hsv : 0 < √v := Real.sqrt_pos.2 hv
  set S2 := {q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ |
      t < |((nrm (reluV q.1))⁻¹ • reluV q.1) ⬝ᵥ (obD q.1 *ᵥ (q.2 *ᵥ e))|} with hS2
  have hS2m : MeasurableSet S2 := by
    refine measurableSet_lt measurable_const ?_
    have hmask := measurable_mask
    simp only [ob_obD_mulVec]
    simp only [dotProduct, nrm, normSq, reluV, relu, Pi.smul_apply, smul_eq_mul, Matrix.mulVec]
    fun_prop
  have hf : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => (A *ᵥ x, A * projT x)) :=
    (continuous_id.matrix_mulVec continuous_const).measurable.prodMk
      (BstLean.Part153.measurable_mul_const _)
  have hset : {A : Matrix (Fin m) (Fin n) ℝ | t < |((nrm (reluV (A *ᵥ x)))⁻¹ • reluV (A *ᵥ x)) ⬝ᵥ
      (obD (A *ᵥ x) *ᵥ (A *ᵥ e))|} =
      (fun A : Matrix (Fin m) (Fin n) ℝ => (A *ᵥ x, A * projT x)) ⁻¹' S2 := by
    ext A
    simp only [mem_setOf_eq, mem_preimage, hS2, bk_mul_projT_mulVec hxe]
  rw [hset, ← bk_lint_ind _ hS2m hf,
    gaussMat_decomp hx hv.le ((measurable_one.indicator hS2m))]
  have inner : ∀ g : Fin m → ℝ, ∫⁻ M, S2.indicator 1 (√v • g, M * projT x) ∂gaussMat m n v ≤
      ENNReal.ofReal (2 * exp (-τ)) := by
    intro g
    have hm : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => (√v • g, M * projT x)) :=
      measurable_const.prodMk (BstLean.Part153.measurable_mul_const _)
    rw [bk_lint_ind _ hS2m hm]
    set u := obD (√v • g) *ᵥ ((nrm (reluV (√v • g)))⁻¹ • reluV (√v • g)) with hu
    have hun : nrm u ≤ 1 := (ob_nrm_obD_le _ _).trans (ob_nrm_unit_le _)
    have hT : MeasurableSet {y : Fin m → ℝ | t < |u ⬝ᵥ y|} := by
      refine measurableSet_lt measurable_const ?_
      simp only [dotProduct]; fun_prop
    have hpre : (fun M : Matrix (Fin m) (Fin n) ℝ => (√v • g, M * projT x)) ⁻¹' S2 ⊆
        (fun M : Matrix (Fin m) (Fin n) ℝ => M *ᵥ e) ⁻¹' {y | t < |u ⬝ᵥ y|} := by
      intro M hM
      simp only [mem_preimage, hS2, mem_setOf_eq, bk_mul_projT_mulVec hxe, ob_dot_obD] at hM ⊢
      exact hM
    refine (measure_mono hpre).trans ?_
    have hmv : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => M *ᵥ e) :=
      (continuous_id.matrix_mulVec continuous_const).measurable
    rw [← Measure.map_apply hmv hT, gaussMat_mulVec, he, Real.sqrt_one, mul_one,
      Measure.map_apply (measurable_const_smul _) hT]
    have hset2 : (fun ξ : Fin m → ℝ => √v • ξ) ⁻¹' {y | t < |u ⬝ᵥ y|} =
        {ξ | √(2 * τ) < |u ⬝ᵥ ξ|} := by
      ext ξ
      simp only [mem_preimage, mem_setOf_eq, dotProduct_smul, smul_eq_mul, abs_mul,
        abs_of_pos hsv, ht]
      exact mul_lt_mul_iff_of_pos_left hsv
    rw [hset2]
    have hc := lin_tail u (L := 1) one_pos hun (Real.sqrt_nonneg (2 * τ))
    rw [Real.sq_sqrt (by linarith), one_pow, mul_one] at hc
    have e2 : -(2 * τ) / 2 = -τ := by ring
    rw [e2] at hc
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    exact ENNReal.ofReal_le_ofReal hc
  have hP1 : IsProbabilityMeasure (stdGauss (Fin m)) := by unfold stdGauss; infer_instance
  calc ∫⁻ g, ∫⁻ M, S2.indicator 1 (√v • g, M * projT x) ∂gaussMat m n v ∂stdGauss (Fin m)
      ≤ ∫⁻ _g, ENNReal.ofReal (2 * exp (-τ)) ∂stdGauss (Fin m) := lintegral_mono inner
    _ = ENNReal.ofReal (2 * exp (-τ)) := by rw [lintegral_const, measure_univ, mul_one]

/-- **The length of `(A P)ᵀ y` for a FIXED `y`** (paper: "`B₁ᵀ y₁` has conditional length at most
`√γ_A(√n + υ)|y₁|`"): for a Gaussian `A` (variance `v`) and `‖P‖ ≤ 1`,
`Pr(√v(√n + √(2τ))·|y| < |(A P)ᵀ y|) ≤ e^{−τ}`. -/
theorem ob_len_fixed {v : ℝ} (hv : 0 < v) (P : Matrix (Fin n) (Fin n) ℝ) (hP : opN P ≤ 1)
    (y : Fin m → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat m n v) {A | √v * (√(n : ℝ) + √(2 * τ)) * nrm y < nrm ((A * P)ᵀ *ᵥ y)} ≤
      ENNReal.ofReal (exp (-τ)) := by
  have hsv : 0 < √v := Real.sqrt_pos.2 hv
  set c := √v * (√(n : ℝ) + √(2 * τ)) with hc
  -- reduce to `Aᵀ y`
  have hsub : {A : Matrix (Fin m) (Fin n) ℝ | c * nrm y < nrm ((A * P)ᵀ *ᵥ y)} ⊆
      (fun A : Matrix (Fin m) (Fin n) ℝ => Aᵀ *ᵥ y) ⁻¹' {u | c * nrm y < nrm u} := by
    intro A hA
    simp only [mem_setOf_eq, mem_preimage] at hA ⊢
    have h1 : nrm ((A * P)ᵀ *ᵥ y) ≤ nrm (Aᵀ *ᵥ y) := by
      rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
      refine (BstLean.Part153.nrm_mulVec_le _ _).trans ?_
      rw [BstLean.Part153.opN_transpose]
      calc opN P * nrm (Aᵀ *ᵥ y) ≤ 1 * nrm (Aᵀ *ᵥ y) :=
            mul_le_mul_of_nonneg_right hP (BstLean.Part153.nrm_nonneg _)
        _ = nrm (Aᵀ *ᵥ y) := one_mul _
    linarith
  refine (measure_mono hsub).trans ?_
  have hT : MeasurableSet {u : Fin n → ℝ | c * nrm y < nrm u} := by
    refine measurableSet_lt measurable_const ?_
    show Measurable (fun u : Fin n → ℝ => √(∑ i, u i ^ 2))
    fun_prop
  have hmt : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => Aᵀ *ᵥ y) :=
    (continuous_id.matrix_transpose.matrix_mulVec continuous_const).measurable
  have hmv : Measurable (fun B : Matrix (Fin n) (Fin m) ℝ => B *ᵥ y) :=
    (continuous_id.matrix_mulVec continuous_const).measurable
  have e1 : (fun A : Matrix (Fin m) (Fin n) ℝ => Aᵀ *ᵥ y) =
      (fun B : Matrix (Fin n) (Fin m) ℝ => B *ᵥ y) ∘ Matrix.transpose := rfl
  rw [← Measure.map_apply hmt hT, e1, ← Measure.map_map hmv (BstLean.Part153.measurable_transposeM),
    BstLean.Part153.gaussMat_transpose, gaussMat_mulVec,
    Measure.map_apply (measurable_const_smul _) hT]
  by_cases hy : nrm y = 0
  · have e0 : (fun ξ : Fin n → ℝ => (√v * √(normSq y)) • ξ) ⁻¹' {u | c * nrm y < nrm u} = ∅ := by
      have hy' : √(normSq y) = 0 := hy
      ext ξ
      simp only [mem_preimage, mem_setOf_eq, hy, hy', mul_zero, zero_smul, mem_empty_iff_false,
        iff_false, not_lt]
      simp [nrm, normSq]
    rw [e0, measure_empty]; exact bot_le
  have hyp : 0 < nrm y := lt_of_le_of_ne (BstLean.Part153.nrm_nonneg y) (Ne.symm hy)
  have hset2 : (fun ξ : Fin n → ℝ => (√v * √(normSq y)) • ξ) ⁻¹' {u | c * nrm y < nrm u} ⊆
      {ξ | √(n : ℝ) + √(2 * τ) ≤ nrm (fun i => (fun _ : Fin n => (1 : ℝ)) i * ξ i)} := by
    intro ξ hξ
    have e3 : √(normSq y) = nrm y := rfl
    simp only [mem_preimage, mem_setOf_eq, BstLean.Part153.nrm_smul, e3, hc] at hξ ⊢
    simp only [one_mul]
    rw [abs_of_nonneg (by positivity)] at hξ
    have : √v * nrm y * (√(n : ℝ) + √(2 * τ)) < √v * nrm y * nrm ξ := by linarith
    exact (lt_of_mul_lt_mul_left this (by positivity)).le
  refine (measure_mono hset2).trans ?_
  have hc1 := ob_chi_tail (k := n) (fun _ => (1 : ℝ)) (fun _ => Or.inr rfl) (K := (n : ℝ))
    (by simp) (Real.sqrt_nonneg (2 * τ))
  rw [Real.sq_sqrt (by linarith)] at hc1
  have e2 : -(2 * τ) / 2 = -τ := by ring
  rw [e2] at hc1
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hc1

lemma ob_meas_nrm {α : Type*} [MeasurableSpace α] {k : ℕ} {f : α → Fin k → ℝ}
    (hf : Measurable f) : Measurable (fun a => nrm (f a)) := by
  have h : Measurable (fun u : Fin k → ℝ => √(∑ i, u i ^ 2)) := by fun_prop
  exact h.comp hf

lemma ob_meas_len {α : Type*} [MeasurableSpace α] (P : Matrix (Fin n) (Fin n) ℝ)
    {M : α → Matrix (Fin m) (Fin n) ℝ} {y : α → Fin m → ℝ} (hM : Measurable M) (hy : Measurable y)
    (c : ℝ) : MeasurableSet {a | c * nrm (y a) < nrm ((M a * P)ᵀ *ᵥ y a)} := by
  have hc : Continuous (fun z : Matrix (Fin m) (Fin n) ℝ × (Fin m → ℝ) => (z.1 * P)ᵀ *ᵥ z.2) :=
    ((continuous_fst.matrix_mul continuous_const).matrix_transpose).matrix_mulVec continuous_snd
  have h1 : Measurable (fun a => c * nrm (y a)) := (ob_meas_nrm hy).const_mul c
  have h2' : Measurable (fun a => (M a * P)ᵀ *ᵥ y a) := by
    have := hc.measurable.comp (hM.prodMk hy)
    exact this
  have h2 : Measurable (fun a => nrm ((M a * P)ᵀ *ᵥ y a)) := ob_meas_nrm h2'
  exact measurableSet_lt h1 h2

/-- **The conditional length of `B₁ᵀ y₁`** (paper: "`y₁` depends only on `(g, ĝ, A₂)`, not on `B₁`.
Thus `B₁ᵀ y₁` has conditional length at most `√γ_A(√n + υ)|y₁|`"): for orthonormal `x`, `e`, a
matrix `P` with `Π_x P = P`, `Π_e P = P`, `‖P‖ ≤ 1` (e.g. `P_E`) and ANY measurable
`Y(A x, A e)`: `Pr(√v(√n + √(2τ))|Y| < |(A P)ᵀ Y|) ≤ e^{−τ}`. (The dependence on `A₂` is
handled by applying this for each fixed `A₂`, see `ob_len_joint`.) -/
theorem ob_len_cond {v : ℝ} (hv : 0 < v) {x e : Fin n → ℝ} (hx : normSq x = 1)
    (he : normSq e = 1) (hxe : x ⬝ᵥ e = 0) (P : Matrix (Fin n) (Fin n) ℝ)
    (hPx : projT x * P = P) (hPe : projT e * P = P) (hP : opN P ≤ 1)
    (Y : (Fin m → ℝ) × (Fin m → ℝ) → Fin m → ℝ) (hY : Measurable Y) {τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat m n v) {A | √v * (√(n : ℝ) + √(2 * τ)) * nrm (Y (A *ᵥ x, A *ᵥ e)) <
      nrm ((A * P)ᵀ *ᵥ Y (A *ᵥ x, A *ᵥ e))} ≤ ENNReal.ofReal (exp (-τ)) := by
  set c := √v * (√(n : ℝ) + √(2 * τ)) with hc
  have hmv : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => M *ᵥ e) :=
    (continuous_id.matrix_mulVec continuous_const).measurable
  set S2 := {q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ |
      c * nrm (Y (q.1, q.2 *ᵥ e)) < nrm ((q.2 * P)ᵀ *ᵥ Y (q.1, q.2 *ᵥ e))} with hS2
  have hS2m : MeasurableSet S2 :=
    ob_meas_len P measurable_snd (hY.comp (measurable_fst.prodMk (hmv.comp measurable_snd))) c
  have hf : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => (A *ᵥ x, A * projT x)) :=
    (continuous_id.matrix_mulVec continuous_const).measurable.prodMk
      (BstLean.Part153.measurable_mul_const _)
  have hset : {A : Matrix (Fin m) (Fin n) ℝ | c * nrm (Y (A *ᵥ x, A *ᵥ e)) <
      nrm ((A * P)ᵀ *ᵥ Y (A *ᵥ x, A *ᵥ e))} =
      (fun A : Matrix (Fin m) (Fin n) ℝ => (A *ᵥ x, A * projT x)) ⁻¹' S2 := by
    ext A
    simp only [mem_setOf_eq, mem_preimage, hS2, bk_mul_projT_mulVec hxe, Matrix.mul_assoc, hPx]
  rw [hset, ← bk_lint_ind _ hS2m hf, gaussMat_decomp hx hv.le (measurable_one.indicator hS2m)]
  have inner : ∀ g : Fin m → ℝ, ∫⁻ M, S2.indicator 1 (√v • g, M * projT x) ∂gaussMat m n v ≤
      ENNReal.ofReal (exp (-τ)) := by
    intro g
    set a := √v • g with ha
    have hm : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => (a, M * projT x)) :=
      measurable_const.prodMk (BstLean.Part153.measurable_mul_const _)
    rw [bk_lint_ind _ hS2m hm]
    set T := {q : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ |
        c * nrm (Y (a, q.1)) < nrm ((q.2 * P)ᵀ *ᵥ Y (a, q.1))} with hT
    have hTm : MeasurableSet T :=
      ob_meas_len P measurable_snd (hY.comp (measurable_const.prodMk measurable_fst)) c
    have hf₂ : Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => (M *ᵥ e, M * projT e)) :=
      hmv.prodMk (BstLean.Part153.measurable_mul_const _)
    have hset2 : (fun M : Matrix (Fin m) (Fin n) ℝ => (a, M * projT x)) ⁻¹' S2 =
        (fun M : Matrix (Fin m) (Fin n) ℝ => (M *ᵥ e, M * projT e)) ⁻¹' T := by
      ext M
      simp only [mem_preimage, hS2, hT, mem_setOf_eq, bk_mul_projT_mulVec hxe, Matrix.mul_assoc,
        hPx, hPe]
    rw [hset2, ← bk_lint_ind _ hTm hf₂, gaussMat_decomp he hv.le (measurable_one.indicator hTm)]
    have inner2 : ∀ h : Fin m → ℝ, ∫⁻ M', T.indicator 1 (√v • h, M' * projT e)
        ∂gaussMat m n v ≤ ENNReal.ofReal (exp (-τ)) := by
      intro h
      have hm' : Measurable (fun M' : Matrix (Fin m) (Fin n) ℝ => (√v • h, M' * projT e)) :=
        measurable_const.prodMk (BstLean.Part153.measurable_mul_const _)
      rw [bk_lint_ind _ hTm hm']
      refine (measure_mono ?_).trans (ob_len_fixed hv P hP (Y (a, √v • h)) hτ)
      intro M' hM'
      simp only [mem_preimage, hT, mem_setOf_eq, Matrix.mul_assoc, hPe] at hM'
      exact hM'
    have hP1 : IsProbabilityMeasure (stdGauss (Fin m)) := by unfold stdGauss; infer_instance
    calc ∫⁻ h, ∫⁻ M', T.indicator 1 (√v • h, M' * projT e) ∂gaussMat m n v ∂stdGauss (Fin m)
        ≤ ∫⁻ _h, ENNReal.ofReal (exp (-τ)) ∂stdGauss (Fin m) := lintegral_mono inner2
      _ = ENNReal.ofReal (exp (-τ)) := by rw [lintegral_const, measure_univ, mul_one]
  have hP1 : IsProbabilityMeasure (stdGauss (Fin m)) := by unfold stdGauss; infer_instance
  calc ∫⁻ g, ∫⁻ M, S2.indicator 1 (√v • g, M * projT x) ∂gaussMat m n v ∂stdGauss (Fin m)
      ≤ ∫⁻ _g, ENNReal.ofReal (exp (-τ)) ∂stdGauss (Fin m) := lintegral_mono inner
    _ = ENNReal.ofReal (exp (-τ)) := by rw [lintegral_const, measure_univ, mul_one]

/-- **The conditional length of `B₁ᵀ y₁` on the joint weights**: `y₁ = Y(A₂, A₁x, A₁e)` for any
jointly measurable `Y` and any probability distribution `μ₂` of the second factor (e.g. the law of
`A₂`): `Pr(√v(√n + √(2τ))|y₁| < |(A₁ P)ᵀ y₁|) ≤ e^{−τ}`. -/
theorem ob_len_joint {β : Type*} [MeasurableSpace β] (μ₂ : Measure β) [IsProbabilityMeasure μ₂]
    {v : ℝ} (hv : 0 < v) {x e : Fin n → ℝ} (hx : normSq x = 1)
    (he : normSq e = 1) (hxe : x ⬝ᵥ e = 0) (P : Matrix (Fin n) (Fin n) ℝ)
    (hPx : projT x * P = P) (hPe : projT e * P = P) (hP : opN P ≤ 1)
    (Y : β → (Fin m → ℝ) × (Fin m → ℝ) → Fin m → ℝ) (hY : Measurable (Function.uncurry Y))
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ((gaussMat m n v).prod μ₂) {q | √v * (√(n : ℝ) + √(2 * τ)) *
      nrm (Y q.2 (q.1 *ᵥ x, q.1 *ᵥ e)) < nrm ((q.1 * P)ᵀ *ᵥ Y q.2 (q.1 *ᵥ x, q.1 *ᵥ e))} ≤
      ENNReal.ofReal (exp (-τ)) := by
  have hP1 : IsProbabilityMeasure (gaussMat m n v) := by unfold gaussMat; infer_instance
  set c := √v * (√(n : ℝ) + √(2 * τ)) with hc
  have hmv : ∀ w : Fin n → ℝ, Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => M *ᵥ w) :=
    fun w => (continuous_id.matrix_mulVec continuous_const).measurable
  have hyq : Measurable (fun q : Matrix (Fin m) (Fin n) ℝ × β => Y q.2 (q.1 *ᵥ x, q.1 *ᵥ e)) := by
    have : (fun q : Matrix (Fin m) (Fin n) ℝ × β => Y q.2 (q.1 *ᵥ x, q.1 *ᵥ e)) =
        Function.uncurry Y ∘ (fun q => (q.2, (q.1 *ᵥ x, q.1 *ᵥ e))) := rfl
    rw [this]
    exact hY.comp (measurable_snd.prodMk (((hmv x).comp measurable_fst).prodMk
      ((hmv e).comp measurable_fst)))
  have hSm := ob_meas_len P measurable_fst hyq c
  rw [Measure.prod_apply_symm hSm]
  calc ∫⁻ b, (gaussMat m n v) ((fun A => (A, b)) ⁻¹' {q : Matrix (Fin m) (Fin n) ℝ × β |
        c * nrm (Y q.2 (q.1 *ᵥ x, q.1 *ᵥ e)) < nrm ((q.1 * P)ᵀ *ᵥ Y q.2 (q.1 *ᵥ x, q.1 *ᵥ e))}) ∂μ₂
      ≤ ∫⁻ _b, ENNReal.ofReal (exp (-τ)) ∂μ₂ := by
        refine lintegral_mono fun b => ?_
        have hYb : Measurable (Y b) := by
          have : Y b = Function.uncurry Y ∘ (fun z => (b, z)) := rfl
          rw [this]; exact hY.comp (measurable_const.prodMk measurable_id)
        exact ob_len_cond hv hx he hxe P hPx hPe hP (Y b) hYb hτ
    _ = ENNReal.ofReal (exp (-τ)) := by rw [lintegral_const, measure_univ, mul_one]

/-- **The length `|A₂ v|` for a FIXED `v` with `|v| ≤ 1`** (paper: "two lengths `|A₂v|, |A₂v'|`",
bound `√t_A(n + υ)` with `√m = n`): `Pr(√w(√M + √(2τ)) < |A v|) ≤ e^{−τ}` for a Gaussian
`M × k` matrix `A` (variance `w`). -/
theorem ob_Av_fixed {M k : ℕ} {w : ℝ} (hw : 0 < w) (u : Fin k → ℝ) (hu : nrm u ≤ 1) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    (gaussMat M k w) {A | √w * (√(M : ℝ) + √(2 * τ)) < nrm (A *ᵥ u)} ≤
      ENNReal.ofReal (exp (-τ)) := by
  have hsw : 0 < √w := Real.sqrt_pos.2 hw
  have hT : MeasurableSet {y : Fin M → ℝ | √w * (√(M : ℝ) + √(2 * τ)) < nrm y} :=
    measurableSet_lt measurable_const (ob_meas_nrm measurable_id)
  have hmv : Measurable (fun A : Matrix (Fin M) (Fin k) ℝ => A *ᵥ u) :=
    (continuous_id.matrix_mulVec continuous_const).measurable
  have e1 : {A : Matrix (Fin M) (Fin k) ℝ | √w * (√(M : ℝ) + √(2 * τ)) < nrm (A *ᵥ u)} =
      (fun A : Matrix (Fin M) (Fin k) ℝ => A *ᵥ u) ⁻¹'
        {y | √w * (√(M : ℝ) + √(2 * τ)) < nrm y} := rfl
  rw [e1, ← Measure.map_apply hmv hT, gaussMat_mulVec,
    Measure.map_apply (measurable_const_smul _) hT]
  have hu' : √(normSq u) ≤ 1 := hu
  have hsub : (fun ξ : Fin M → ℝ => (√w * √(normSq u)) • ξ) ⁻¹'
      {y | √w * (√(M : ℝ) + √(2 * τ)) < nrm y} ⊆
      {ξ | √(M : ℝ) + √(2 * τ) ≤ nrm (fun i => (fun _ : Fin M => (1 : ℝ)) i * ξ i)} := by
    intro ξ hξ
    simp only [mem_preimage, mem_setOf_eq, BstLean.Part153.nrm_smul] at hξ ⊢
    simp only [one_mul]
    rw [abs_of_nonneg (by positivity)] at hξ
    have h0 : 0 ≤ √(normSq u) := Real.sqrt_nonneg _
    have hξ0 := BstLean.Part153.nrm_nonneg ξ
    have : √w * (√(M : ℝ) + √(2 * τ)) < √w * nrm ξ := by
      calc √w * (√(M : ℝ) + √(2 * τ)) < √w * √(normSq u) * nrm ξ := hξ
        _ ≤ √w * 1 * nrm ξ := by gcongr
        _ = √w * nrm ξ := by ring
    exact (lt_of_mul_lt_mul_left this hsw.le).le
  refine (measure_mono hsub).trans ?_
  have hc1 := ob_chi_tail (k := M) (fun _ => (1 : ℝ)) (fun _ => Or.inr rfl) (K := (M : ℝ))
    (by simp) (Real.sqrt_nonneg (2 * τ))
  rw [Real.sq_sqrt (by linarith)] at hc1
  have e2 : -(2 * τ) / 2 = -τ := by ring
  rw [e2] at hc1
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hc1

/-- **`|A₂ v| ≤ √t(√m + υ)` on the joint weights**, for `v = V(A₁)` any measurable function of the
first factor with `|V| ≤ 1` (e.g. `v = a/|a|`): `Pr ≤ e^{−τ}`. -/
theorem ob_Av_joint {α : Type*} [MeasurableSpace α] (μ₁ : Measure α) [IsProbabilityMeasure μ₁]
    {M k : ℕ} {w : ℝ} (hw : 0 < w) (V : α → Fin k → ℝ) (hV : Measurable V) (hV1 : ∀ a, nrm (V a) ≤ 1)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (μ₁.prod (gaussMat M k w)) {q | √w * (√(M : ℝ) + √(2 * τ)) < nrm (q.2 *ᵥ V q.1)} ≤
      ENNReal.ofReal (exp (-τ)) := by
  have hP2 : IsProbabilityMeasure (gaussMat M k w) := by unfold gaussMat; infer_instance
  have hc : Continuous (fun z : Matrix (Fin M) (Fin k) ℝ × (Fin k → ℝ) => z.1 *ᵥ z.2) :=
    continuous_fst.matrix_mulVec continuous_snd
  have h2 : Measurable (fun q : α × Matrix (Fin M) (Fin k) ℝ => q.2 *ᵥ V q.1) := by
    have := hc.measurable.comp (measurable_snd.prodMk (hV.comp measurable_fst))
    exact this
  have hSm : MeasurableSet {q : α × Matrix (Fin M) (Fin k) ℝ |
      √w * (√(M : ℝ) + √(2 * τ)) < nrm (q.2 *ᵥ V q.1)} :=
    measurableSet_lt measurable_const (ob_meas_nrm h2)
  rw [Measure.prod_apply hSm]
  calc ∫⁻ a, (gaussMat M k w) (Prod.mk a ⁻¹' {q : α × Matrix (Fin M) (Fin k) ℝ |
        √w * (√(M : ℝ) + √(2 * τ)) < nrm (q.2 *ᵥ V q.1)}) ∂μ₁
      ≤ ∫⁻ _a, ENNReal.ofReal (exp (-τ)) ∂μ₁ :=
        lintegral_mono fun a => ob_Av_fixed hw (V a) (hV1 a) hτ
    _ = ENNReal.ofReal (exp (-τ)) := by rw [lintegral_const, measure_univ, mul_one]

/-- **The masked tangent length for a FIXED pair** (paper: "two masked tangent lengths"
`|D₂A₂Π_v p| ≤ √t_A(√K₂ + υ)|Π_v p|`): for a unit `u` and `r ⊥ u`, a Gaussian `A` (variance `w`),
`Pr(tr diag(mask(Au)) ≤ K ∧ √w(√K + √(2τ))|r| < |diag(mask(Au)) A r|) ≤ e^{−τ}`. -/
theorem ob_mtan_fixed {M k : ℕ} {w : ℝ} (hw : 0 < w) {u r : Fin k → ℝ} (hu : normSq u = 1)
    (hur : u ⬝ᵥ r = 0) {K τ : ℝ} (hτ : 0 ≤ τ) :
    (gaussMat M k w) {A | ∑ i, mask ((A *ᵥ u) i) ≤ K ∧
      √w * (√K + √(2 * τ)) * nrm r < nrm (obD (A *ᵥ u) *ᵥ (A *ᵥ r))} ≤
      ENNReal.ofReal (exp (-τ)) := by
  by_cases hr : nrm r = 0
  · have e0 : {A : Matrix (Fin M) (Fin k) ℝ | ∑ i, mask ((A *ᵥ u) i) ≤ K ∧
        √w * (√K + √(2 * τ)) * nrm r < nrm (obD (A *ᵥ u) *ᵥ (A *ᵥ r))} = ∅ := by
      ext A
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
      intro _
      have h := (ob_nrm_obD_le (A *ᵥ u) (A *ᵥ r)).trans (BstLean.Part153.nrm_mulVec_le A r)
      rw [hr, mul_zero] at h ⊢
      exact h
    rw [e0, measure_empty]; exact bot_le
  have hrp : 0 < nrm r := lt_of_le_of_ne (BstLean.Part153.nrm_nonneg r) (Ne.symm hr)
  set e := (nrm r)⁻¹ • r with he
  have hen : normSq e = 1 := by
    have h1 : nrm e = 1 := by
      rw [he, BstLean.Part153.nrm_smul, abs_inv, abs_of_pos hrp, inv_mul_cancel₀ hr]
    have : normSq e = nrm e ^ 2 := by
      rw [show nrm e = √(normSq e) from rfl]
      exact (Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)).symm
    rw [this, h1, one_pow]
  have hue : u ⬝ᵥ e = 0 := by rw [he, dotProduct_smul, hur, smul_zero]
  have hre : r = nrm r • e := by rw [he, smul_smul, mul_inv_cancel₀ hr, one_smul]
  refine (measure_mono ?_).trans (ob_p_tail (m := M) hw hu hen hue (K := K) hτ)
  intro A hA
  simp only [mem_setOf_eq] at hA ⊢
  refine ⟨hA.1, ?_⟩
  have hAr : A *ᵥ r = nrm r • (A *ᵥ e) := by
    conv_lhs => rw [hre]
    rw [Matrix.mulVec_smul]
  have h2 := hA.2
  rw [hAr, Matrix.mulVec_smul, BstLean.Part153.nrm_smul, abs_of_pos hrp] at h2
  have : √w * (√K + √(2 * τ)) * nrm r < nrm (obD (A *ᵥ u) *ᵥ (A *ᵥ e)) * nrm r := by
    linarith [mul_comm (nrm r) (nrm (obD (A *ᵥ u) *ᵥ (A *ᵥ e)))]
  exact (lt_of_mul_lt_mul_right this hrp.le).le

end BstLean.Part182

open BstLean.Part182 in
#print axioms ob_assembly
open BstLean.Part182 in
#print axioms ob_jz
open BstLean.Part182 in
#print axioms ob_chi_tail
open BstLean.Part182 in
#print axioms ob_p_tail
open BstLean.Part182 in
#print axioms ob_eps_tail
open BstLean.Part182 in
#print axioms ob_len_cond
open BstLean.Part182 in
#print axioms ob_len_joint
open BstLean.Part182 in
#print axioms ob_Av_joint
open BstLean.Part182 in
#print axioms ob_mtan_fixed
