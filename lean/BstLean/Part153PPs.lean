import BstLean.Part153PP
import BstLean.Part153Dec
import BstLean.Part153Bin
import BstLean.Part153SJ

/-!
# Part 153, Lemma PP (i) with the sharp constant: row selection and the conditional step (A)

Paper source: `proofs/option-n/theorem5-05-covariance.tex`, Lemma PP (i). The route here does not
use the Beta distribution or the Haar measure: the two masks are handled by the decomposition of a
Gaussian matrix along a unit vector (`gaussMat_decomp'`), by the selection of rows of a Gaussian
matrix, and by Hoeffding's inequality for the count of active rows.

* §1 `opN_add_le'`, `opN_vecMulVec_le`, `opN_diag_le_submatrix`: algebra.
* §2 `gaussMat_submatrix_rows`; **`opN_rowsel_moment`** (step (R)).
* §3 `cnt_moment`: the `N`-th moment of `√v·(√K + c)`, `K` the count of positive coordinates.
* §4 **`opN_jacT_le_split`** (the deterministic inequality of step (A)).
* §5 **`stepA`**, `stepA_hat` (step (A)).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped ENNReal NNReal MatrixOrder
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part151 (jac mask measurable_mask mask_nonneg)

/-! ## §1 Algebra -/

section alg2

variable {p q r : ℕ}

lemma opN_add_le' (M M' : Matrix (Fin p) (Fin q) ℝ) : opN (M + M') ≤ opN M + opN M' := by
  refine opN_le_of_forall _ (add_nonneg (opN_nonneg M) (opN_nonneg M')) fun v => ?_
  rw [Matrix.add_mulVec, add_mul]
  exact (nrm_add_le _ _).trans (add_le_add (nrm_mulVec_le M v) (nrm_mulVec_le M' v))

lemma vecMulVec_mulVec' (u : Fin p → ℝ) (w v : Fin q → ℝ) :
    Matrix.vecMulVec u w *ᵥ v = (w ⬝ᵥ v) • u := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `opN (u wᵀ) ≤ |u|·|w|`. -/
lemma opN_vecMulVec_le (u : Fin p → ℝ) (w : Fin q → ℝ) :
    opN (Matrix.vecMulVec u w) ≤ nrm u * nrm w := by
  refine opN_le_of_forall _ (mul_nonneg (nrm_nonneg u) (nrm_nonneg w)) fun v => ?_
  rw [vecMulVec_mulVec', nrm_smul]
  calc |w ⬝ᵥ v| * nrm u ≤ (nrm w * nrm v) * nrm u :=
        mul_le_mul_of_nonneg_right (abs_dot_le_nrm w v) (nrm_nonneg u)
    _ = nrm u * nrm w * nrm v := by ring

lemma normSq_diag_sel {K : ℕ} (d : Fin p → ℝ) (S : Finset (Fin p))
    (hd : ∀ i, d i = if i ∈ S then 1 else 0) (hK : S.card = K) (w : Fin p → ℝ) :
    normSq (Matrix.diagonal d *ᵥ w) = normSq (fun a : Fin K => w (S.orderEmbOfFin hK a)) := by
  unfold normSq
  simp only [Matrix.mulVec_diagonal]
  have h1 : ∀ i, (d i * w i) ^ 2 = if i ∈ S then w i ^ 2 else 0 := by
    intro i
    rw [hd i]
    split_ifs <;> ring
  simp only [h1]
  rw [Finset.sum_ite_mem, Finset.univ_inter]
  have h2 := Finset.sum_map Finset.univ (S.orderEmbOfFin hK).toEmbedding (fun i => w i ^ 2)
  rw [Finset.map_orderEmbOfFin_univ] at h2
  rw [h2]
  rfl

/-- A diagonal matrix with entries in `{0, 1}` on the left selects rows. -/
lemma opN_diag_le_submatrix {K : ℕ} (d : Fin p → ℝ) (S : Finset (Fin p))
    (hd : ∀ i, d i = if i ∈ S then 1 else 0) (hK : S.card = K) (X : Matrix (Fin p) (Fin q) ℝ) :
    opN (Matrix.diagonal d * X) ≤ opN (X.submatrix (S.orderEmbOfFin hK) id) := by
  refine opN_le_of_forall _ (opN_nonneg _) fun v => ?_
  rw [← Matrix.mulVec_mulVec]
  have e : nrm (Matrix.diagonal d *ᵥ (X *ᵥ v)) =
      nrm (X.submatrix (S.orderEmbOfFin hK) id *ᵥ v) := by
    unfold nrm
    rw [normSq_diag_sel d S hd hK]
    rfl
  rw [e]
  exact nrm_mulVec_le _ v

end alg2

/-! ## §2 Selection of rows of a Gaussian matrix (step (R)) -/

section rowsel

variable {p m n : ℕ}

lemma measurable_submatrix_rows {K : ℕ} (e : Fin K → Fin p) :
    Measurable (fun A : Matrix (Fin p) (Fin m) ℝ => A.submatrix e id) :=
  measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun i =>
    (measurable_pi_apply i).comp (measurable_pi_apply (e a))

/-- **Rows of a Gaussian matrix**: the rows with distinct indices `e 0, …, e (K−1)` form a
Gaussian `K × m` matrix. -/
theorem gaussMat_submatrix_rows {K : ℕ} (v : ℝ) (e : Fin K → Fin p)
    (he : Function.Injective e) :
    (gaussMat p m v).map (fun A : Matrix (Fin p) (Fin m) ℝ => A.submatrix e id) =
      gaussMat K m v := by
  classical
  have hfam := gaussMat_family (m := m) (k := p) (k' := K) v
    (fun a => Pi.single (e a) (1 : ℝ)) (fun a => Pi.single a (1 : ℝ)) (by
      intro a b
      simp [Pi.single_apply, he.eq_iff])
  have h1 : (fun (N : Matrix (Fin m) (Fin p) ℝ) (a : Fin K) => N *ᵥ Pi.single (e a) (1 : ℝ)) =
      (fun A : Matrix (Fin p) (Fin m) ℝ => A.submatrix e id) ∘ Matrix.transpose := by
    funext N a i
    simp
  have h2 : (fun (N : Matrix (Fin m) (Fin K) ℝ) (a : Fin K) => N *ᵥ Pi.single a (1 : ℝ)) =
      Matrix.transpose := by
    funext N a i
    simp
  rw [← gaussMat_transpose m p v, Measure.map_map (measurable_submatrix_rows e)
    measurable_transposeM, ← gaussMat_transpose m K v, ← h1, ← h2]
  exact hfam

/-- **Step (R): the fact (G2) for selected rows.** For a fixed `d` with values in `{0, 1}`, a
fixed `m × n` matrix `B` and a `p × m` Gaussian matrix `A` with variance `v`:
`E opN(diag(d)·A·B)^{2P} ≤ (opN(B)·√v·(√K + √n + 𝔪_P))^{2P}`, `K = ∑ i, d i`. -/
theorem opN_rowsel_moment (d : Fin p → ℝ) (hd : ∀ i, d i = 0 ∨ d i = 1)
    (B : Matrix (Fin m) (Fin n) ℝ) {v : ℝ} (hv : 0 ≤ v) {P : ℕ} (hP : 1 ≤ P) :
    ∫⁻ A : Matrix (Fin p) (Fin m) ℝ,
        ENNReal.ofReal (opN (Matrix.diagonal d * (A * B)) ^ (2 * P)) ∂gaussMat p m v ≤
      ENNReal.ofReal ((opN B * (√v * (√(∑ i, d i) + √(n : ℝ) + gaussMomConst P))) ^ (2 * P)) := by
  classical
  obtain ⟨S, hS⟩ : ∃ S : Finset (Fin p), ∀ i, i ∈ S ↔ d i = 1 :=
    ⟨Finset.univ.filter fun i => d i = 1, by simp⟩
  have hd' : ∀ i, d i = if i ∈ S then 1 else 0 := by
    intro i
    rcases hd i with h | h
    · have : i ∉ S := by rw [hS, h]; norm_num
      simp [this, h]
    · simp [(hS i).2 h, h]
  have hsum : ∑ i, d i = (S.card : ℝ) := by
    simp only [hd']
    rw [Finset.sum_ite_mem, Finset.univ_inter]
    simp
  obtain ⟨K, hK⟩ : ∃ K, S.card = K := ⟨_, rfl⟩
  rw [hsum, hK]
  obtain ⟨hI, hB⟩ := opN_mul_moment (p := K) B hv hP
  have hφ : Measurable fun A' : Matrix (Fin K) (Fin m) ℝ =>
      ENNReal.ofReal (opN (A' * B) ^ (2 * P)) :=
    ((opN_continuous.comp (continuous_id.matrix_mul continuous_const)).measurable.pow_const
      _).ennreal_ofReal
  calc ∫⁻ A : Matrix (Fin p) (Fin m) ℝ,
        ENNReal.ofReal (opN (Matrix.diagonal d * (A * B)) ^ (2 * P)) ∂gaussMat p m v
      ≤ ∫⁻ A : Matrix (Fin p) (Fin m) ℝ,
        ENNReal.ofReal (opN (A.submatrix (S.orderEmbOfFin hK) id * B) ^ (2 * P))
          ∂gaussMat p m v := by
        refine lintegral_mono fun A => ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (opN_nonneg _) ?_ _)
        have h := opN_diag_le_submatrix d S hd' hK (A * B)
        have e2 : (A * B).submatrix (S.orderEmbOfFin hK) id =
            A.submatrix (S.orderEmbOfFin hK) id * B := by
          ext i j
          simp [Matrix.mul_apply, Matrix.submatrix_apply]
        rwa [e2] at h
    _ = ∫⁻ A' : Matrix (Fin K) (Fin m) ℝ, ENNReal.ofReal (opN (A' * B) ^ (2 * P))
          ∂gaussMat K m v := by
        rw [← gaussMat_submatrix_rows v _ (S.orderEmbOfFin hK).injective,
          lintegral_map hφ (measurable_submatrix_rows _)]
    _ = ENNReal.ofReal (∫ A' : Matrix (Fin K) (Fin m) ℝ, opN (A' * B) ^ (2 * P)
          ∂gaussMat K m v) :=
        (ofReal_integral_eq_lintegral_ofReal hI
          (ae_of_all _ fun _ => pow_nonneg (opN_nonneg _) _)).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by rw [mul_pow]; exact hB)

end rowsel

/-! ## §3 The moment of the count of positive coordinates -/

/-- The constant of the split on the event `{K > (1/2 + η)·p}`:
`√v·(√((1/2+η)p) + c) + exp(−2η²p)^{1/N}·√v·(√p + c)`. -/
noncomputable def splitC (v : ℝ) (p : ℕ) (c η : ℝ) (N : ℕ) : ℝ :=
  √v * (√((1 / 2 + η) * p) + c) +
    Real.exp (-2 * η ^ 2 * p) ^ ((1 : ℝ) / N) * (√v * (√(p : ℝ) + c))

lemma splitC_nonneg (v : ℝ) (p : ℕ) {c : ℝ} (hc : 0 ≤ c) (η : ℝ) (N : ℕ) :
    0 ≤ splitC v p c η N := by
  unfold splitC
  have := Real.rpow_nonneg (Real.exp_pos (-2 * η ^ 2 * p)).le ((1 : ℝ) / N)
  positivity

lemma measurable_cnt (p : ℕ) : Measurable fun g : Fin p → ℝ => ∑ i, mask (g i) :=
  Finset.measurable_sum _ fun i _ => measurable_mask.comp (measurable_pi_apply i)

/-- The `N`-th moment of `√v·(√K + c)`, `K = ∑ i, mask (g i)` the count of positive coordinates
of a standard Gaussian vector of `ℝ^p`. -/
theorem cnt_moment {p : ℕ} (v : ℝ) {c η : ℝ} (hc : 0 ≤ c) (hη : 0 ≤ η) {N : ℕ} (hN : 1 ≤ N) :
    ∫⁻ g : Fin p → ℝ, ENNReal.ofReal (√v * (√(∑ i, mask (g i)) + c)) ^ N ∂stdGauss (Fin p) ≤
      ENNReal.ofReal (splitC v p c η N ^ N) := by
  have hS : MeasurableSet {g : Fin p → ℝ | (1 / 2 + η) * p < ∑ i, mask (g i)} :=
    measurableSet_lt measurable_const (measurable_cnt p)
  have hq : stdGauss (Fin p) {g : Fin p → ℝ | (1 / 2 + η) * p < ∑ i, mask (g i)} ≤
      ENNReal.ofReal (Real.exp (-2 * η ^ 2 * p)) := by
    have h := cnt_tail (m := p) hη
    rw [measureReal_def] at h
    exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (Real.exp_pos _).le).2 h
  have hK0 : ∀ g : Fin p → ℝ, 0 ≤ ∑ i, mask (g i) := fun g =>
    Finset.sum_nonneg fun i _ => mask_nonneg _
  have hKp : ∀ g : Fin p → ℝ, ∑ i, mask (g i) ≤ (p : ℝ) := by
    intro g
    calc ∑ i, mask (g i) ≤ ∑ _i : Fin p, (1 : ℝ) := Finset.sum_le_sum fun i _ => mask_le_one _
      _ = p := by simp
  unfold splitC
  refine lintegral_pow_split_le' hS (Real.exp_pos _).le hq (by positivity) (by positivity)
    (fun g hg => ENNReal.ofReal_le_ofReal ?_) (fun g => ENNReal.ofReal_le_ofReal ?_) hN
  · have hg' : ∑ i, mask (g i) ≤ (1 / 2 + η) * p := not_lt.mp hg
    exact mul_le_mul_of_nonneg_left (add_le_add (Real.sqrt_le_sqrt hg') le_rfl)
      (Real.sqrt_nonneg _)
  · exact mul_le_mul_of_nonneg_left (add_le_add (Real.sqrt_le_sqrt (hKp g)) le_rfl)
      (Real.sqrt_nonneg _)

/-! ## §4 The deterministic inequality of step (A) -/

section detA

variable {n m p : ℕ}

lemma mask_mul_self (t : ℝ) : mask t * t = relu t := by
  by_cases ht : 0 < t
  · rw [BstLean.Part151.mask_of_pos ht, relu_of_nonneg ht.le, one_mul]
  · rw [BstLean.Part151.mask_of_nonpos (not_lt.mp ht), relu_of_nonpos (not_lt.mp ht), zero_mul]

/-- **The deterministic inequality of step (A).** If `ReLU(A₁x) = s·â` with `s > 0`, then with
`T = tanB A₁ x`, `g₂ = A₂â`, `B₂ = A₂Π_â`:
`opN(𝒥(x)Π_x) ≤ |ReLU(g₂)|·|Tᵀâ| + opN(diag(mask g₂)·B₂·T)`. -/
theorem opN_jacT_le_split (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin p) (Fin m) ℝ)
    (x : Fin n → ℝ) {s : ℝ} (hs : 0 < s) (â : Fin m → ℝ) (ha : reluV (A₁ *ᵥ x) = s • â) :
    opN (jacT A₁ A₂ x) ≤ nrm (reluV (A₂ *ᵥ â)) * nrm ((tanB A₁ x)ᵀ *ᵥ â) +
      opN (Matrix.diagonal (fun j => mask ((A₂ *ᵥ â) j)) * ((A₂ * projT â) * tanB A₁ x)) := by
  have hmask : (fun j => mask ((A₂ *ᵥ reluV (A₁ *ᵥ x)) j)) = fun j => mask ((A₂ *ᵥ â) j) := by
    funext j
    rw [ha, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul, mask_mul_pos hs]
  rw [jacT_eq, hmask]
  have h0 := eq_vecMulVec_add_mul_projT A₂ â
  have e1 : A₂ * tanB A₁ x = Matrix.vecMulVec (A₂ *ᵥ â) ((tanB A₁ x)ᵀ *ᵥ â) +
      (A₂ * projT â) * tanB A₁ x := by
    calc A₂ * tanB A₁ x = (Matrix.vecMulVec (A₂ *ᵥ â) â + A₂ * projT â) * tanB A₁ x :=
          congrArg (fun Z => Z * tanB A₁ x) h0
      _ = _ := by rw [Matrix.add_mul, Matrix.vecMulVec_mul, Matrix.mulVec_transpose]
  have e2 : Matrix.diagonal (fun j => mask ((A₂ *ᵥ â) j)) * (A₂ * tanB A₁ x) =
      Matrix.vecMulVec (reluV (A₂ *ᵥ â)) ((tanB A₁ x)ᵀ *ᵥ â) +
        Matrix.diagonal (fun j => mask ((A₂ *ᵥ â) j)) * ((A₂ * projT â) * tanB A₁ x) := by
    rw [e1, Matrix.mul_add]
    congr 1
    ext i j
    simp only [Matrix.diagonal_mul, Matrix.vecMulVec_apply, reluV]
    rw [← mul_assoc, mask_mul_self]
  rw [e2]
  exact (opN_add_le' _ _).trans (add_le_add (opN_vecMulVec_le _ _) le_rfl)

end detA

/-! ## §5 Step (A): the integral over `A₂` -/

section stepA

variable {n m p : ℕ}

lemma measurable_nrm_reluV (p : ℕ) : Measurable fun g : Fin p → ℝ => nrm (reluV g) :=
  (BstLean.Part130.measurable_normSq.comp measurable_reluV).sqrt

lemma measurable_diag_mask_mul (T : Matrix (Fin m) (Fin n) ℝ) :
    Measurable fun q : (Fin p → ℝ) × Matrix (Fin p) (Fin m) ℝ =>
      Matrix.diagonal (fun j => mask (q.1 j)) * (q.2 * T) := by
  refine measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun l => ?_
  have e : (fun q : (Fin p → ℝ) × Matrix (Fin p) (Fin m) ℝ =>
      (Matrix.diagonal (fun j => mask (q.1 j)) * (q.2 * T)) j l) =
      fun q => mask (q.1 j) * ∑ k, q.2 j k * T k l := by
    funext q
    rw [Matrix.diagonal_mul, Matrix.mul_apply]
  show Measurable (fun q : (Fin p → ℝ) × Matrix (Fin p) (Fin m) ℝ =>
      (Matrix.diagonal (fun j => mask (q.1 j)) * (q.2 * T)) j l)
  rw [e]
  exact (measurable_mask.comp ((measurable_pi_apply j).comp measurable_fst)).mul
    (Finset.measurable_sum _ fun k _ =>
      ((measurable_pi_apply k).comp ((measurable_pi_apply j).comp measurable_snd)).mul_const _)

lemma opN_zero' (p q : ℕ) : opN (0 : Matrix (Fin p) (Fin q) ℝ) = 0 := by
  refine le_antisymm (opN_le_of_forall _ le_rfl fun v => ?_) (opN_nonneg _)
  rw [Matrix.zero_mulVec, zero_mul]
  unfold nrm normSq
  simp

/-- **Step (A).** For a fixed `A₁` with `ReLU(A₁x) = s·â`, `s > 0`, `|â| = 1`, and a Gaussian
`p × m` matrix `A₂` with variance `t > 0`, with `T = tanB A₁ x`:
`‖opN(𝒥(x)Π_x)‖_{L^{2P}} ≤ √t(√(p/2) + 𝔪_P)·|Tᵀâ| + splitC·opN(T)`. -/
theorem stepA (A₁ : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) {s : ℝ} (hs : 0 < s)
    {â : Fin m → ℝ} (hâ : normSq â = 1) (ha : reluV (A₁ *ᵥ x) = s • â) {t : ℝ} (ht : 0 < t)
    {P : ℕ} (hP : 1 ≤ P) {η : ℝ} (hη : 0 ≤ η) :
    ∫⁻ A₂ : Matrix (Fin p) (Fin m) ℝ, ENNReal.ofReal (opN (jacT A₁ A₂ x) ^ (2 * P))
        ∂gaussMat p m t ≤
      ENNReal.ofReal ((√t * (√((p : ℝ) / 2) + gaussMomConst P) * nrm ((tanB A₁ x)ᵀ *ᵥ â) +
        splitC t p (√(n : ℝ) + gaussMomConst P) η (2 * P) * opN (tanB A₁ x)) ^ (2 * P)) := by
  have hN : 1 ≤ 2 * P := by omega
  have hst : 0 < √t := Real.sqrt_pos.2 ht
  have h𝔪 := gaussMomConst_nonneg P
  obtain ⟨T, hT⟩ : ∃ T, T = tanB A₁ x := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁, c₁ = nrm (Tᵀ *ᵥ â) := ⟨_, rfl⟩
  have hc₁0 : 0 ≤ c₁ := hc₁ ▸ nrm_nonneg _
  have hA : 0 ≤ √t * c₁ := mul_nonneg hst.le hc₁0
  have h𝔫 : 0 ≤ √(n : ℝ) + gaussMomConst P := add_nonneg (Real.sqrt_nonneg _) h𝔪
  have hB : ∀ K : ℝ, 0 ≤ √t * (√K + (√(n : ℝ) + gaussMomConst P)) := fun K =>
    mul_nonneg hst.le (add_nonneg (Real.sqrt_nonneg _) h𝔫)
  have hB' : ∀ K : ℝ, 0 ≤ √t * (√K + √(n : ℝ) + gaussMomConst P) := fun K =>
    mul_nonneg hst.le (add_nonneg (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) h𝔪)
  have hrc : 0 ≤ √((p : ℝ) / 2) + gaussMomConst P := add_nonneg (Real.sqrt_nonneg _) h𝔪
  rw [← hT, ← hc₁]
  let Φ : (Fin p → ℝ) → Matrix (Fin p) (Fin m) ℝ → ℝ≥0∞ := fun g B =>
    ENNReal.ofReal ((nrm (reluV g) * c₁ +
      opN (Matrix.diagonal (fun j => mask (g j)) * (B * T))) ^ (2 * P))
  have hΦ : Measurable (Function.uncurry Φ) := by
    have h1 : Measurable fun q : (Fin p → ℝ) × Matrix (Fin p) (Fin m) ℝ => nrm (reluV q.1) :=
      (measurable_nrm_reluV p).comp measurable_fst
    have h2 := opN_continuous.measurable.comp (measurable_diag_mask_mul (p := p) T)
    exact (((h1.mul_const c₁).add h2).pow_const _).ennreal_ofReal
  have step1 : ∫⁻ A₂ : Matrix (Fin p) (Fin m) ℝ, ENNReal.ofReal (opN (jacT A₁ A₂ x) ^ (2 * P))
      ∂gaussMat p m t ≤ ∫⁻ A₂ : Matrix (Fin p) (Fin m) ℝ, Φ (A₂ *ᵥ â) (A₂ * projT â)
        ∂gaussMat p m t := by
    refine lintegral_mono fun A₂ => ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (opN_nonneg _) ?_ _)
    have h := opN_jacT_le_split A₁ A₂ x hs â ha
    rw [← hT, ← hc₁] at h
    exact h
  refine step1.trans ?_
  rw [gaussMat_decomp' hâ ht.le hΦ]
  -- the integral over `M`, for a fixed `g`
  have inner : ∀ g : Fin p → ℝ, ∫⁻ M : Matrix (Fin p) (Fin m) ℝ, Φ (√t • g) (M * projT â)
      ∂gaussMat p m t ≤ ENNReal.ofReal ((√t * c₁ * nrm (reluV g) +
        opN T * (√t * (√(∑ i, mask (g i)) + (√(n : ℝ) + gaussMomConst P)))) ^ (2 * P)) := by
    intro g
    have e : ∀ M : Matrix (Fin p) (Fin m) ℝ, Φ (√t • g) (M * projT â) =
        (ENNReal.ofReal (√t * c₁ * nrm (reluV g)) +
          ENNReal.ofReal (opN (Matrix.diagonal (fun j => mask (g j)) *
            (M * (projT â * T))))) ^ (2 * P) := by
      intro M
      have hm : (fun j => mask ((√t • g) j)) = fun j => mask (g j) := by
        funext j
        rw [Pi.smul_apply, smul_eq_mul, mask_mul_pos hst]
      simp only [Φ]
      rw [hm, reluV_smul_of_nonneg hst.le, nrm_smul, abs_of_pos hst, Matrix.mul_assoc,
        show √t * nrm (reluV g) * c₁ = √t * c₁ * nrm (reluV g) by ring,
        ENNReal.ofReal_pow (add_nonneg (mul_nonneg hA (nrm_nonneg _)) (opN_nonneg _)),
        ENNReal.ofReal_add (mul_nonneg hA (nrm_nonneg _)) (opN_nonneg _)]
    simp only [e]
    have hY : Measurable fun M : Matrix (Fin p) (Fin m) ℝ =>
        ENNReal.ofReal (opN (Matrix.diagonal (fun j => mask (g j)) * (M * (projT â * T)))) :=
      (opN_continuous.comp (continuous_const.matrix_mul
        (continuous_id.matrix_mul continuous_const))).measurable.ennreal_ofReal
    refine lintegral_pow_add_le aemeasurable_const hY.aemeasurable (mul_nonneg hA (nrm_nonneg _))
      (mul_nonneg (opN_nonneg T) (hB _)) hN ?_ ?_
    · rw [lintegral_const, measure_univ, mul_one,
        ENNReal.ofReal_pow (mul_nonneg hA (nrm_nonneg _))]
    · have hR := opN_rowsel_moment (p := p) (fun j => mask (g j))
        (fun j => by unfold mask; split_ifs <;> simp) (projT â * T) ht.le hP
      have e3 : ∀ M : Matrix (Fin p) (Fin m) ℝ,
          ENNReal.ofReal (opN (Matrix.diagonal (fun j => mask (g j)) *
            (M * (projT â * T)))) ^ (2 * P) =
          ENNReal.ofReal (opN (Matrix.diagonal (fun j => mask (g j)) *
            (M * (projT â * T))) ^ (2 * P)) := fun M => (ENNReal.ofReal_pow (opN_nonneg _) _).symm
      simp only [e3]
      refine hR.trans (ENNReal.ofReal_le_ofReal (pow_le_pow_left₀
        (mul_nonneg (opN_nonneg _) (hB' _)) ?_ _))
      have hpT : opN (projT â * T) ≤ opN T := by
        have h := (opN_mul_le (projT â) T).trans
          (mul_le_mul_of_nonneg_right (opN_projT_le hâ) (opN_nonneg T))
        rwa [one_mul] at h
      have e4 : √(∑ i, mask (g i)) + √(n : ℝ) + gaussMomConst P =
          √(∑ i, mask (g i)) + (√(n : ℝ) + gaussMomConst P) := by ring
      rw [e4]
      exact mul_le_mul_of_nonneg_right hpT (hB _)
  refine (lintegral_mono inner).trans ?_
  -- the integral over `g`
  have e5 : ∀ g : Fin p → ℝ, ENNReal.ofReal ((√t * c₁ * nrm (reluV g) +
        opN T * (√t * (√(∑ i, mask (g i)) + (√(n : ℝ) + gaussMomConst P)))) ^ (2 * P)) =
      (ENNReal.ofReal (√t * c₁) * ENNReal.ofReal (nrm (reluV g)) +
        ENNReal.ofReal (opN T) * ENNReal.ofReal
          (√t * (√(∑ i, mask (g i)) + (√(n : ℝ) + gaussMomConst P)))) ^ (2 * P) := by
    intro g
    rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul (opN_nonneg _),
      ← ENNReal.ofReal_add (mul_nonneg hA (nrm_nonneg _))
        (mul_nonneg (opN_nonneg _) (hB _)),
      ENNReal.ofReal_pow (add_nonneg (mul_nonneg hA (nrm_nonneg _))
        (mul_nonneg (opN_nonneg _) (hB _)))]
  simp only [e5]
  have hX : Measurable fun g : Fin p → ℝ =>
      ENNReal.ofReal (√t * c₁) * ENNReal.ofReal (nrm (reluV g)) :=
    measurable_const.mul (measurable_nrm_reluV p).ennreal_ofReal
  have hY : Measurable fun g : Fin p → ℝ => ENNReal.ofReal (opN T) * ENNReal.ofReal
      (√t * (√(∑ i, mask (g i)) + (√(n : ℝ) + gaussMomConst P))) :=
    measurable_const.mul
      ((((measurable_cnt p).sqrt.add_const _).const_mul _).ennreal_ofReal)
  have m1 : ∫⁻ g : Fin p → ℝ, ENNReal.ofReal (nrm (reluV g)) ^ (2 * P) ∂stdGauss (Fin p) ≤
      ENNReal.ofReal ((√((p : ℝ) / 2) + gaussMomConst P) ^ (2 * P)) := by
    have h := nrm_reluV_moment_lintegral p hP
    have e6 : ∀ g : Fin p → ℝ, ENNReal.ofReal (nrm (reluV g)) ^ (2 * P) =
        ENNReal.ofReal (nrm (reluV g) ^ (2 * P)) :=
      fun g => (ENNReal.ofReal_pow (nrm_nonneg _) _).symm
    simpa only [e6] using h
  have m2 := cnt_moment (p := p) t (c := √(n : ℝ) + gaussMomConst P) h𝔫 hη hN
  have hfin := lintegral_pow_add_le hX.aemeasurable hY.aemeasurable
    (a := √t * c₁ * (√((p : ℝ) / 2) + gaussMomConst P))
    (b := opN T * splitC t p (√(n : ℝ) + gaussMomConst P) η (2 * P)) (mul_nonneg hA hrc)
    (mul_nonneg (opN_nonneg _) (splitC_nonneg _ _ h𝔫 _ _)) hN
    (lintegral_pow_const_mul_le hA m1)
    (lintegral_pow_const_mul_le (opN_nonneg _) m2)
  refine hfin.trans (le_of_eq ?_)
  congr 2
  ring

/-- The unit vector in the direction of `a` (it is `0` if `a = 0`). -/
noncomputable def hatV {ι : Type*} [Fintype ι] (a : ι → ℝ) : ι → ℝ := (nrm a)⁻¹ • a

lemma nrm_eq_zero' {ι : Type*} [Fintype ι] {a : ι → ℝ} (h : nrm a = 0) : a = 0 := by
  unfold nrm at h
  have h2 : normSq a = 0 := (Real.sqrt_eq_zero (normSq_nonneg a)).1 h
  unfold normSq at h2
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (a i))).1 h2 i (Finset.mem_univ i)
  simpa using this

lemma normSq_hatV {ι : Type*} [Fintype ι] {a : ι → ℝ} (h : a ≠ 0) : normSq (hatV a) = 1 := by
  have h0 : nrm a ≠ 0 := fun h' => h (nrm_eq_zero' h')
  unfold hatV
  rw [normSq_smul, ← nrm_sq a, ← mul_pow, inv_mul_cancel₀ h0, one_pow]

lemma normSq_hatV_le {ι : Type*} [Fintype ι] (a : ι → ℝ) : normSq (hatV a) ≤ 1 := by
  by_cases h : a = 0
  · subst h
    unfold hatV normSq
    simp
  · exact (normSq_hatV h).le

/-- **Step (A), for every `A₁`**, with `â = hatV (ReLU(A₁x))`. -/
theorem stepA_hat (A₁ : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) {t : ℝ} (ht : 0 < t)
    {P : ℕ} (hP : 1 ≤ P) {η : ℝ} (hη : 0 ≤ η) :
    ∫⁻ A₂ : Matrix (Fin p) (Fin m) ℝ, ENNReal.ofReal (opN (jacT A₁ A₂ x) ^ (2 * P))
        ∂gaussMat p m t ≤
      ENNReal.ofReal ((√t * (√((p : ℝ) / 2) + gaussMomConst P) *
          nrm ((tanB A₁ x)ᵀ *ᵥ hatV (reluV (A₁ *ᵥ x))) +
        splitC t p (√(n : ℝ) + gaussMomConst P) η (2 * P) * opN (tanB A₁ x)) ^ (2 * P)) := by
  by_cases h : reluV (A₁ *ᵥ x) = 0
  · have hz : ∀ A₂ : Matrix (Fin p) (Fin m) ℝ, jacT A₁ A₂ x = 0 := by
      intro A₂
      rw [jacT_eq, h, Matrix.mulVec_zero]
      have : (fun j : Fin p => mask ((0 : Fin p → ℝ) j)) = 0 := by
        funext j
        simp [BstLean.Part151.mask_of_nonpos]
      rw [this, show Matrix.diagonal (0 : Fin p → ℝ) = 0 from Matrix.diagonal_zero,
        Matrix.zero_mul]
    simp only [hz, opN_zero']
    rw [zero_pow (by omega), ENNReal.ofReal_zero, lintegral_zero]
    exact zero_le
  · have h0 : nrm (reluV (A₁ *ᵥ x)) ≠ 0 := fun h' => h (nrm_eq_zero' h')
    have hs : 0 < nrm (reluV (A₁ *ᵥ x)) := lt_of_le_of_ne (nrm_nonneg _) (Ne.symm h0)
    refine stepA A₁ x hs (normSq_hatV h) ?_ ht hP hη
    unfold hatV
    rw [smul_smul, mul_inv_cancel₀ h0, one_smul]

end stepA

end BstLean.Part153

open BstLean.Part153 in
#print axioms opN_rowsel_moment
open BstLean.Part153 in
#print axioms opN_jacT_le_split
open BstLean.Part153 in
#print axioms stepA
open BstLean.Part153 in
#print axioms stepA_hat
