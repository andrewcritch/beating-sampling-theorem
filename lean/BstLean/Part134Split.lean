import BstLean.Part130Sym
import BstLean.Part130Mean
import BstLean.Part105GebeleinL2

/-!
# Part 134, item 1: the split of the last matrix of the World network (`s1_split`)

Role: `delegations/statements/p134-spec.md`, item 1 (paper Theorem S1, part (a)).
Do not use `sorry`, `native_decide` or `axiom`.

`M` is an `n × m` Gaussian matrix with entry variance `v` (`gaussMat n m v`; `v = 2/m` for the
last matrix `M₃` of the World network). `b ∈ ℝ^m` is a fixed vector.

* `lam b h = ⟨h, b⟩/|b|²`; `res b h = h − lam b h • b` (the part of `h` orthogonal to `b`);
  `sig v b h = √v·|res b h|`; `projPerp b = 1 − b bᵀ/|b|²` (the matrix `P_{b^⊥}`);
  `glue b c R = c bᵀ/|b|² + R`.
* `split_eq`: `M = glue b (M b) (M P)`.
* `stdGauss_indep_of_orth`: two uncorrelated linear images of a standard Gaussian vector are
  independent.
* `s1_split`: for `b ≠ 0`, the pair `(M b, M P)` has the product distribution: `c = M b` and
  the residual matrix `M P` are independent.
* `s1_disint`: the distribution of `(M b, M)` is the distribution of `(c, glue b c (M' P))`,
  `c` with the distribution of `M b` and `M'` an independent Gaussian matrix.
-/

namespace BstLean.Part134

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105 (gaussLin105)
open BstLean.Part130

/-- **Two uncorrelated linear images of a standard Gaussian vector are independent.** -/
theorem stdGauss_indep_of_orth {ι κ₁ κ₂ : Type} [Fintype ι] [Fintype κ₁] [Fintype κ₂]
    (A : Matrix κ₁ ι ℝ) (B : Matrix κ₂ ι ℝ) (h : A * B.transpose = 0) :
    (stdGauss ι).map (fun ξ => (A.mulVec ξ, B.mulVec ξ)) =
      ((stdGauss ι).map (fun ξ => A.mulVec ξ)).prod ((stdGauss ι).map (fun ξ => B.mulVec ξ)) := by
  classical
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : κ₁ ⊕ κ₂ => ℝ)
  let e' := MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ ι => ℝ)
  let C : Matrix (κ₁ ⊕ κ₂) ι ℝ := Matrix.fromRows A B
  let D : Matrix (κ₁ ⊕ κ₂) (ι ⊕ ι) ℝ := Matrix.fromBlocks A 0 0 B
  have hB : B * A.transpose = 0 := by
    have := congrArg Matrix.transpose h
    simpa [Matrix.transpose_mul] using this
  have hCD : C * C.transpose = D * D.transpose := by
    simp only [C, D, Matrix.transpose_fromRows, Matrix.fromRows_mul_fromCols,
      Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, h, hB]
    simp
  have mA : Measurable (fun ξ : ι → ℝ => A.mulVec ξ) := measurable_mulVec_left A
  have mB : Measurable (fun ξ : ι → ℝ => B.mulVec ξ) := measurable_mulVec_left B
  have hL : (fun ξ : ι → ℝ => (A.mulVec ξ, B.mulVec ξ)) = e ∘ (fun ξ => C.mulVec ξ) := by
    funext ξ
    refine Prod.ext ?_ ?_ <;> funext a <;>
      simp [e, C, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, Matrix.fromRows_mulVec]
  have hR : (Prod.map (fun ξ : ι → ℝ => A.mulVec ξ) (fun ξ : ι → ℝ => B.mulVec ξ)) ∘ e' =
      e ∘ (fun ξ => D.mulVec ξ) := by
    funext ξ
    refine Prod.ext ?_ ?_ <;> funext a <;>
      simp [e, e', D, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, Matrix.mulVec,
        dotProduct, Fintype.sum_sum_type]
  have hprod : (stdGauss ι).prod (stdGauss ι) = (stdGauss (ι ⊕ ι)).map e' :=
    ((measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ ι => gaussianReal 0 1)).map_eq).symm
  have mC : Measurable (fun ξ : ι → ℝ => C.mulVec ξ) := measurable_mulVec_left C
  have mD : Measurable (fun ξ : ι ⊕ ι → ℝ => D.mulVec ξ) := measurable_mulVec_left D
  have : IsProbabilityMeasure (stdGauss ι) := inferInstance
  rw [Measure.map_prod_map _ _ mA mB, hprod, Measure.map_map (mA.prodMap mB) e'.measurable, hR,
    hL, ← Measure.map_map e.measurable mC, ← Measure.map_map e.measurable mD,
    gaussLin105 _ _ _ C D hCD]

/-! ## The quantities of Theorem S1 -/

variable {n m : ℕ}

/-- `λ = ⟨h, b⟩/|b|²`: the coefficient of `h` along `b`. -/
noncomputable def lam (b h : Fin m → ℝ) : ℝ := (∑ j, h j * b j) / normSq b

/-- `r = h − λ·b`: the part of `h` orthogonal to `b`. -/
noncomputable def res (b h : Fin m → ℝ) : Fin m → ℝ := h - lam b h • b

/-- `σ = √v·|r|`: the residual standard deviation (`v = 2/m` for the World network). -/
noncomputable def sig (v : ℝ) (b h : Fin m → ℝ) : ℝ := Real.sqrt v * Real.sqrt (normSq (res b h))

/-- `P_{b^⊥} = 1 − b bᵀ/|b|²`. -/
noncomputable def projPerp (b : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  1 - (normSq b)⁻¹ • Matrix.vecMulVec b b

/-- `c bᵀ/|b|² + R`: the matrix with image `c` on `b` and residual part `R`. -/
noncomputable def glue (b : Fin m → ℝ) (c : Fin n → ℝ) (R : Matrix (Fin n) (Fin m) ℝ) :
    Matrix (Fin n) (Fin m) ℝ :=
  (normSq b)⁻¹ • Matrix.vecMulVec c b + R

lemma normSq_ne_zero {b : Fin m → ℝ} (hb : b ≠ 0) : normSq b ≠ 0 := by
  intro h
  apply hb
  funext j
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (b i))).mp h j (Finset.mem_univ j)
  simpa using this

lemma projPerp_mulVec (b h : Fin m → ℝ) : (projPerp b).mulVec h = res b h := by
  rw [projPerp, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  funext i
  simp only [res, lam, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct,
    Matrix.vecMulVec_apply]
  have : ∑ j, b i * b j * h j = b i * ∑ j, h j * b j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]; ring

lemma res_self {b : Fin m → ℝ} (hb : b ≠ 0) : res b b = 0 := by
  have h0 := normSq_ne_zero hb
  have : lam b b = 1 := by
    unfold lam
    have : ∑ j, b j * b j = normSq b := Finset.sum_congr rfl fun j _ => (sq _).symm
    rw [this, div_self h0]
  simp [res, this]

/-- The residual is orthogonal to `b`. -/
lemma res_orth {b : Fin m → ℝ} (hb : b ≠ 0) (h : Fin m → ℝ) : ∑ j, res b h j * b j = 0 := by
  have h0 := normSq_ne_zero hb
  simp only [res, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_sub_distrib]
  have : ∑ j, lam b h * b j * b j = lam b h * normSq b := by
    unfold normSq; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this, lam, div_mul_cancel₀ _ h0, sub_self]

lemma mul_projPerp_mulVec (M : Matrix (Fin n) (Fin m) ℝ) (b h : Fin m → ℝ) :
    (M * projPerp b).mulVec h = M.mulVec (res b h) := by
  rw [← Matrix.mulVec_mulVec, projPerp_mulVec]

/-- **The decomposition of the matrix**: `M = (M b) bᵀ/|b|² + M P_{b^⊥}`. -/
theorem split_eq (b : Fin m → ℝ) (M : Matrix (Fin n) (Fin m) ℝ) :
    M = glue b (M.mulVec b) (M * projPerp b) := by
  ext i j
  simp only [glue, projPerp, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, Matrix.add_apply,
    Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul, Matrix.vecMulVec_apply, Matrix.mul_apply,
    Matrix.mulVec, dotProduct]
  have : ∑ l, M i l * (b l * b j) = (∑ l, M i l * b l) * b j := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun l _ => by ring
  rw [this]; ring

lemma glue_mulVec (b : Fin m → ℝ) (c : Fin n → ℝ) (R : Matrix (Fin n) (Fin m) ℝ)
    (h : Fin m → ℝ) : (glue b c R).mulVec h = lam b h • c + R.mulVec h := by
  funext i
  simp only [glue, Matrix.add_mulVec, Matrix.smul_mulVec, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, lam]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply]
  have : ∑ j, c i * b j * h j = c i * ∑ j, h j * b j := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]; ring

/-- **The decomposition of the output** (Theorem S1 (a), first assertion):
`M h = λ·(M b) + (M P) h`, and `(M P) h = M r`. -/
theorem s1_decomp (b h : Fin m → ℝ) (M : Matrix (Fin n) (Fin m) ℝ) :
    M.mulVec h = lam b h • M.mulVec b + M.mulVec (res b h) := by
  conv_lhs => rw [split_eq b M]
  rw [glue_mulVec, mul_projPerp_mulVec]

/-! ## Independence -/

lemma measurable_mul_right (P : Matrix (Fin m) (Fin m) ℝ) :
    Measurable (fun M : Matrix (Fin n) (Fin m) ℝ => M * P) :=
  (Continuous.matrix_mul continuous_id continuous_const).measurable

lemma measurable_glue (b : Fin m → ℝ) :
    Measurable (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ => glue b p.1 p.2) := by
  unfold glue
  have hc : Continuous (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      Matrix.vecMulVec p.1 b) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    simp only [Matrix.vecMulVec_apply]
    exact ((continuous_apply i).comp continuous_fst).mul continuous_const
  exact ((hc.const_smul ((normSq b)⁻¹)).add continuous_snd).measurable

/-- Two uncorrelated linear images of a Gaussian matrix are independent. -/
theorem gaussMat_indep {κ₁ κ₂ : Type} [Fintype κ₁] [Fintype κ₂] (v : ℝ)
    (A : Matrix κ₁ (Fin n × Fin m) ℝ) (B : Matrix κ₂ (Fin n × Fin m) ℝ)
    (h : A * B.transpose = 0) :
    (gaussMat n m v).map (fun M => (A.mulVec (flat M), B.mulVec (flat M))) =
      ((gaussMat n m v).map (fun M => A.mulVec (flat M))).prod
        ((gaussMat n m v).map (fun M => B.mulVec (flat M))) := by
  unfold gaussMat
  have h1 : ∀ {κ : Type} [Fintype κ] (A : Matrix κ (Fin n × Fin m) ℝ),
      ((fun M : Matrix (Fin n) (Fin m) ℝ => A.mulVec (flat M)) ∘
        fun ξ : Fin n × Fin m → ℝ => Matrix.of fun i j => Real.sqrt v * ξ (i, j)) =
      fun ξ => (Real.sqrt v • A).mulVec ξ := by
    intro κ _ A
    funext ξ a
    simp only [Function.comp, Matrix.mulVec, dotProduct, flat, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  have h2 : ((fun M : Matrix (Fin n) (Fin m) ℝ => (A.mulVec (flat M), B.mulVec (flat M))) ∘
        fun ξ : Fin n × Fin m → ℝ => Matrix.of fun i j => Real.sqrt v * ξ (i, j)) =
      fun ξ => ((Real.sqrt v • A).mulVec ξ, (Real.sqrt v • B).mulVec ξ) := by
    funext ξ
    exact Prod.ext (congrFun (h1 A) ξ) (congrFun (h1 B) ξ)
  rw [Measure.map_map ((measurable_mulVec_flat A).prodMk (measurable_mulVec_flat B))
      (measurable_ofFlat _),
    Measure.map_map (measurable_mulVec_flat A) (measurable_ofFlat _),
    Measure.map_map (measurable_mulVec_flat B) (measurable_ofFlat _), h1 A, h1 B, h2]
  apply stdGauss_indep_of_orth
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, h, smul_zero]

/-- The matrix of `flat M ↦ flat (M P)`. -/
def mulMat (n : ℕ) (P : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin n × Fin m) (Fin n × Fin m) ℝ :=
  Matrix.of fun a q => rowMat n (fun l => P l a.2) a.1 q

lemma mulMat_mulVec (P : Matrix (Fin m) (Fin m) ℝ) (M : Matrix (Fin n) (Fin m) ℝ) :
    unflat ((mulMat n P).mulVec (flat M)) = M * P := by
  ext i j
  have : ((mulMat n P).mulVec (flat M)) (i, j) = ((rowMat n (fun l => P l j)).mulVec (flat M)) i :=
    rfl
  change (mulMat n P).mulVec (flat M) (i, j) = _
  rw [this, rowMat_mulVec, Matrix.mul_apply]
  rfl

lemma vecMul_projPerp {b : Fin m → ℝ} (hb : b ≠ 0) (j : Fin m) :
    ∑ l, b l * projPerp b l j = 0 := by
  classical
  have h0 := normSq_ne_zero hb
  simp only [projPerp, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.vecMulVec_apply,
    Matrix.one_apply, mul_sub, Finset.sum_sub_distrib]
  have e1 : ∑ l, b l * (if l = j then (1 : ℝ) else 0) = b j := by simp
  have e2 : ∑ l, b l * ((normSq b)⁻¹ * (b l * b j)) = b j := by
    have : ∑ l, b l * ((normSq b)⁻¹ * (b l * b j)) = (normSq b)⁻¹ * b j * normSq b := by
      unfold normSq; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    rw [this]; field_simp
  rw [e1, e2, sub_self]

/-- **Theorem S1 (a), the independence.** `M` an `n × m` Gaussian matrix with entry variance
`v`, `b ≠ 0`. The vector `c = M b` and the residual matrix `M P_{b^⊥}` are independent: the pair
has the product of the two marginal distributions. -/
theorem s1_split (v : ℝ) {b : Fin m → ℝ} (hb : b ≠ 0) :
    (gaussMat n m v).map (fun M => (M.mulVec b, M * projPerp b)) =
      ((gaussMat n m v).map (fun M => M.mulVec b)).prod
        ((gaussMat n m v).map (fun M => M * projPerp b)) := by
  classical
  have horth : rowMat n b * (mulMat n (projPerp b)).transpose = 0 := by
    ext i a
    have e : (rowMat n b * (mulMat n (projPerp b)).transpose) i a =
        (rowMat n b * (rowMat n (fun l => projPerp b l a.2)).transpose) i a.1 := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      rfl
    rw [e, rowMat_mul_transpose, vecMul_projPerp hb]
    simp
  have key := gaussMat_indep (n := n) (m := m) v (rowMat n b) (mulMat n (projPerp b)) horth
  have hmu : Measurable (unflat : (Fin n × Fin m → ℝ) → Matrix (Fin n) (Fin m) ℝ) :=
    measurable_unflat
  have hid : Measurable (id : (Fin n → ℝ) → (Fin n → ℝ)) := measurable_id
  have e1 : (fun M : Matrix (Fin n) (Fin m) ℝ => (M.mulVec b, M * projPerp b)) =
      Prod.map id unflat ∘
        fun M => ((rowMat n b).mulVec (flat M), (mulMat n (projPerp b)).mulVec (flat M)) := by
    funext M
    simp only [Function.comp, Prod.map, id, rowMat_mulVec, mulMat_mulVec]
  have e2 : (fun M : Matrix (Fin n) (Fin m) ℝ => M.mulVec b) =
      id ∘ fun M => (rowMat n b).mulVec (flat M) := by
    funext M; simp only [Function.comp, id, rowMat_mulVec]
  have e3 : (fun M : Matrix (Fin n) (Fin m) ℝ => M * projPerp b) =
      unflat ∘ fun M => (mulMat n (projPerp b)).mulVec (flat M) := by
    funext M; simp only [Function.comp, mulMat_mulVec]
  have : IsProbabilityMeasure ((gaussMat n m v).map
      fun M => (rowMat n b).mulVec (flat M)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_mulVec_flat _).aemeasurable).2 inferInstance
  have : IsProbabilityMeasure ((gaussMat n m v).map
      fun M => (mulMat n (projPerp b)).mulVec (flat M)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_mulVec_flat _).aemeasurable).2 inferInstance
  rw [e1, ← Measure.map_map (hid.prodMap hmu)
      ((measurable_mulVec_flat _).prodMk (measurable_mulVec_flat _)), key,
    ← Measure.map_prod_map _ _ hid hmu,
    Measure.map_map hid (measurable_mulVec_flat _), Measure.map_map hmu (measurable_mulVec_flat _),
    ← e2, ← e3]

/-- The distribution of `c = M b`: `√v·|b|·ξ`, `ξ` standard Gaussian in `ℝⁿ`; that is
`N(0, v|b|²·I_n)`. -/
noncomputable def cDist (n : ℕ) (v : ℝ) (b : Fin m → ℝ) : Measure (Fin n → ℝ) :=
  (stdGauss (Fin n)).map (fun ξ => (Real.sqrt v * Real.sqrt (normSq b)) • ξ)

theorem cDist_eq (v : ℝ) (b : Fin m → ℝ) :
    (gaussMat n m v).map (fun M => M.mulVec b) = cDist n v b := gaussMat_mulVec v b

instance (v : ℝ) (b : Fin m → ℝ) : IsProbabilityMeasure (cDist n v b) := by
  rw [← cDist_eq]
  exact (Measure.isProbabilityMeasure_map_iff (measurable_mulVec_right b).aemeasurable).2
    inferInstance

/-- **Theorem S1 (a), the form for later parts (disintegration).** For `b ≠ 0`, the pair
`(M b, M)` has the distribution of `(c, c bᵀ/|b|² + M' P_{b^⊥})`, where `c ~ N(0, v|b|²·I_n)`
and `M'` is a Gaussian matrix independent of `c`. So, given `c = M b`, the matrix `M` has the
distribution of `glue b c (M' * projPerp b)`. -/
theorem s1_disint (v : ℝ) {b : Fin m → ℝ} (hb : b ≠ 0) :
    (gaussMat n m v).map (fun M => (M.mulVec b, M)) =
      ((cDist n v b).prod (gaussMat n m v)).map
        (fun p => (p.1, glue b p.1 (p.2 * projPerp b))) := by
  have hG : Measurable (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      (p.1, glue b p.1 p.2)) := measurable_fst.prodMk (measurable_glue b)
  have hid : Measurable (id : (Fin n → ℝ) → (Fin n → ℝ)) := measurable_id
  have hP := measurable_mul_right (n := n) (projPerp b)
  have e1 : (fun M : Matrix (Fin n) (Fin m) ℝ => (M.mulVec b, M)) =
      (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ => (p.1, glue b p.1 p.2)) ∘
        fun M => (M.mulVec b, M * projPerp b) := by
    funext M
    simp only [Function.comp]
    rw [← split_eq]
  have e2 : (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      (p.1, glue b p.1 (p.2 * projPerp b))) =
      (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ => (p.1, glue b p.1 p.2)) ∘
        Prod.map id (fun M => M * projPerp b) := rfl
  rw [e1, ← Measure.map_map hG ((measurable_mulVec_right b).prodMk hP), s1_split v hb, e2,
    ← Measure.map_map hG (hid.prodMap hP), ← Measure.map_prod_map _ _ hid hP, Measure.map_id,
    cDist_eq]

/-- The distribution of `M` is the distribution of `glue b c (M' P)`, `c` and `M'` independent. -/
theorem s1_glue (v : ℝ) {b : Fin m → ℝ} (hb : b ≠ 0) :
    gaussMat n m v =
      ((cDist n v b).prod (gaussMat n m v)).map (fun p => glue b p.1 (p.2 * projPerp b)) := by
  have h := congrArg (Measure.map Prod.snd) (s1_disint (n := n) v hb)
  have hm : Measurable (fun p : (Fin n → ℝ) × Matrix (Fin n) (Fin m) ℝ =>
      (p.1, glue b p.1 (p.2 * projPerp b))) :=
    measurable_fst.prodMk ((measurable_glue b).comp
      (measurable_fst.prodMk ((measurable_mul_right _).comp measurable_snd)))
  have hm' : Measurable (fun M : Matrix (Fin n) (Fin m) ℝ => (M.mulVec b, M)) :=
    (measurable_mulVec_right b).prodMk measurable_id
  rw [Measure.map_map measurable_snd hm', Measure.map_map measurable_snd hm] at h
  have e : (Prod.snd ∘ fun M : Matrix (Fin n) (Fin m) ℝ => (M.mulVec b, M)) = id := rfl
  rw [e, Measure.map_id] at h
  exact h

/-- **Theorem S1 (a), the covariance of the residual field**: for the residual matrix `M P`,
`E[((M P) h)_i ((M P) h′)_j] = δ_ij · v · ⟨r, r′⟩`, `r = res b h`, `r′ = res b h′`. -/
theorem s1_resid_cov {v : ℝ} (hv : 0 ≤ v) (b h h' : Fin m → ℝ) (i j : Fin n) :
    ∫ M, ((M * projPerp b).mulVec h) i * ((M * projPerp b).mulVec h') j ∂gaussMat n m v =
      if i = j then v * ∑ l, res b h l * res b h' l else 0 := by
  simp_rw [mul_projPerp_mulVec]
  exact gaussMat_cov hv _ _ i j

/-- The residual field at one input is a Gaussian vector with covariance `σ²·I_n`. -/
theorem s1_resid_gauss (v : ℝ) (b h : Fin m → ℝ) :
    (gaussMat n m v).map (fun M => (M * projPerp b).mulVec h) =
      (stdGauss (Fin n)).map (fun ξ => sig v b h • ξ) := by
  simp_rw [mul_projPerp_mulVec]
  exact gaussMat_mulVec v (res b h)

/-- The covariance of `c = M b` and the residual field is zero (for `b ≠ 0`). -/
theorem s1_cross_cov {v : ℝ} (hv : 0 ≤ v) {b : Fin m → ℝ} (hb : b ≠ 0) (h : Fin m → ℝ)
    (i j : Fin n) :
    ∫ M, (M.mulVec b) i * ((M * projPerp b).mulVec h) j ∂gaussMat n m v = 0 := by
  simp_rw [mul_projPerp_mulVec]
  rw [gaussMat_cov hv]
  have : ∑ l, b l * res b h l = 0 := by
    rw [← res_orth hb h]; exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  simp [this]

end BstLean.Part134

open BstLean.Part134 in
#print axioms stdGauss_indep_of_orth
open BstLean.Part134 in
#print axioms split_eq
open BstLean.Part134 in
#print axioms s1_decomp
open BstLean.Part134 in
#print axioms s1_split
open BstLean.Part134 in
#print axioms s1_disint
open BstLean.Part134 in
#print axioms s1_glue
open BstLean.Part134 in
#print axioms s1_resid_cov
open BstLean.Part134 in
#print axioms s1_resid_gauss
open BstLean.Part134 in
#print axioms s1_cross_cov
