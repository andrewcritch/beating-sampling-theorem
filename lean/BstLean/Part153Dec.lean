import BstLean.Part153JDefs
import BstLean.Part148Tools

/-!
# Part 153, the decomposition of a Gaussian matrix along a unit vector (standard fact (G6))

Paper source: `proofs/option-n/theorem5-03-inputs.tex`, fact (G6), as used in "Step 0: structure"
of the proof of Lemma PP in `theorem5-05-covariance.tex`.

For a Gaussian matrix `A` (independent `N(0, v)` entries) and a unit vector `x`: the vector `A x`
and the matrix `A Π_x` (`Π_x = projT x = I − x xᵀ`) are independent, `A x` has the distribution of
`√v·g` (`g` a standard Gaussian vector), and `A Π_x` has the distribution of `M Π_x` for an
independent copy `M` of `A`.

* `gaussMat_transpose`: the transpose of a Gaussian matrix is a Gaussian matrix.
* `opN_transpose`: `opN Mᵀ = opN M`.
* `gaussMat_cols_map`: the columns of a Gaussian matrix are independent.
* `gaussMat_split`: a Gaussian `m × (n+1)` matrix is a first column and an independent Gaussian
  `m × n` matrix.
* `gaussMat_decomp`, `gaussMat_decomp'`: the decomposition, as an identity of `∫⁻`.
* `eq_vecMulVec_add_mul_projT`: `A = (A x) xᵀ + A Π_x`.
* `gaussMat_vecMul`: `Mᵀ a` has the distribution of `√v·|a|·ζ`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part148 (gaussMat_rows_map)

variable {m n k : ℕ}

/-! ## Transposition -/

/-- The standard Gaussian on `Fin m × Fin n` does not change if the two indices are exchanged. -/
lemma stdGauss_swap (m n : ℕ) :
    (stdGauss (Fin m × Fin n)).map (fun ξ (p : Fin n × Fin m) => ξ p.swap) =
      stdGauss (Fin n × Fin m) := by
  have h1 := measurePreserving_piCongrLeft (fun _ : Fin n × Fin m => gaussianReal 0 1)
    (Equiv.prodComm (Fin m) (Fin n))
  have e : (fun (ξ : Fin m × Fin n → ℝ) (p : Fin n × Fin m) => ξ p.swap) =
      MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin m => ℝ)
        (Equiv.prodComm (Fin m) (Fin n)) := by
    funext ξ p
    obtain ⟨q, rfl⟩ := (Equiv.prodComm (Fin m) (Fin n)).surjective p
    exact (Equiv.piCongrLeft_apply_apply (P := fun _ : Fin n × Fin m => ℝ)
      (Equiv.prodComm (Fin m) (Fin n)) ξ q).symm
  rw [e]
  exact h1.map_eq

lemma measurable_transposeM :
    Measurable (Matrix.transpose : Matrix (Fin m) (Fin n) ℝ → Matrix (Fin n) (Fin m) ℝ) :=
  measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun i =>
    (measurable_pi_apply j).comp (measurable_pi_apply i)

/-- **The transpose of a Gaussian matrix is a Gaussian matrix.** -/
theorem gaussMat_transpose (m n : ℕ) (v : ℝ) :
    (gaussMat m n v).map Matrix.transpose = gaussMat n m v := by
  have hsw : Measurable (fun (ξ : Fin m × Fin n → ℝ) (p : Fin n × Fin m) => ξ p.swap) :=
    measurable_pi_iff.mpr fun p => measurable_pi_apply p.swap
  unfold gaussMat
  rw [Measure.map_map measurable_transposeM (measurable_ofFlat _), ← stdGauss_swap m n,
    Measure.map_map (measurable_ofFlat _) hsw]
  rfl

/-- `‖Mᵀ‖_op = ‖M‖_op`. -/
theorem opN_transpose (M : Matrix (Fin m) (Fin n) ℝ) : opN Mᵀ = opN M := by
  have key : ∀ {p q : ℕ} (N : Matrix (Fin p) (Fin q) ℝ), opSet Nᵀ ⊆ opSet N := by
    intro p q N y hy
    obtain ⟨u, w, hu, hw, rfl⟩ := hy
    refine ⟨w, u, hw, hu, ?_⟩
    rw [Matrix.mulVec_transpose, dotProduct_comm, ← Matrix.dotProduct_mulVec]
  unfold opN
  congr 1
  refine Subset.antisymm (key M) ?_
  have h := key Mᵀ
  rwa [Matrix.transpose_transpose] at h

/-- **The image of a fixed vector under the transposed Gaussian matrix**: `Mᵀ a = a ᵥ* M` has
the distribution of `√v·|a|·ζ`, `ζ` a standard Gaussian vector. -/
theorem gaussMat_vecMul (v : ℝ) (a : Fin m → ℝ) :
    (gaussMat m n v).map (fun M => Matrix.vecMul a M) =
      (stdGauss (Fin n)).map (fun ζ => (√v * √(normSq a)) • ζ) := by
  have h := gaussMat_mulVec (m := n) (k := m) v a
  have hmv : Measurable (fun M : Matrix (Fin n) (Fin m) ℝ => M *ᵥ a) :=
    (Continuous.matrix_mulVec continuous_id continuous_const).measurable
  rw [← gaussMat_transpose m n v, Measure.map_map hmv measurable_transposeM] at h
  rw [← h]
  congr 1
  funext M
  simp [Function.comp, Matrix.mulVec_transpose]

/-- The same statement with `Mᵀ *ᵥ a`. -/
theorem gaussMat_transpose_mulVec (v : ℝ) (a : Fin m → ℝ) :
    (gaussMat m n v).map (fun M => Mᵀ *ᵥ a) =
      (stdGauss (Fin n)).map (fun ζ => (√v * √(normSq a)) • ζ) := by
  rw [← gaussMat_vecMul v a]
  congr 1
  funext M
  rw [Matrix.mulVec_transpose]

/-! ## The columns are independent -/

/-- The distribution of one column of a Gaussian matrix with `m` rows: `√v·g`. -/
noncomputable def gaussCol (m : ℕ) (v : ℝ) : Measure (Fin m → ℝ) :=
  (stdGauss (Fin m)).map (fun ξ => √v • ξ)

instance (m : ℕ) (v : ℝ) : IsProbabilityMeasure (gaussCol m v) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_const_smul _).aemeasurable).2 inferInstance

lemma measurable_colsOf :
    Measurable (fun (M : Matrix (Fin m) (Fin k) ℝ) (j : Fin k) (i : Fin m) => M i j) :=
  measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun i =>
    (measurable_pi_apply j).comp (measurable_pi_apply i)

lemma measurable_ofCols :
    Measurable (fun (c : Fin k → Fin m → ℝ) => (Matrix.of fun i j => c j i :
      Matrix (Fin m) (Fin k) ℝ)) :=
  measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
    (measurable_pi_apply i).comp (measurable_pi_apply j)

/-- **The columns of a Gaussian matrix are independent**, each with the distribution of `√v·g`. -/
theorem gaussMat_cols_map (m k : ℕ) (v : ℝ) :
    (gaussMat m k v).map (fun M j i => M i j) = Measure.pi fun _ : Fin k => gaussCol m v := by
  have h := gaussMat_rows_map k m v
  have hrows : Measurable (fun M : Matrix (Fin k) (Fin m) ℝ => fun i => rowOf i M) :=
    measurable_pi_iff.mpr fun i => measurable_rowOf i
  rw [← gaussMat_transpose m k v, Measure.map_map hrows measurable_transposeM] at h
  exact h

/-- **A Gaussian `m × (n+1)` matrix is a first column and an independent Gaussian `m × n`
matrix.** -/
theorem gaussMat_split (m n : ℕ) (v : ℝ) :
    (gaussMat m (n + 1) v).map (fun M => ((fun i => M i 0),
      (Matrix.of fun i j => M i j.succ : Matrix (Fin m) (Fin n) ℝ))) =
      (gaussCol m v).prod (gaussMat m n v) := by
  have hp := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussCol m v) 0).map_eq
  rw [← gaussMat_cols_map m (n + 1) v, ← gaussMat_cols_map m n v,
    Measure.map_map (MeasurableEquiv.measurable _) measurable_colsOf] at hp
  have : IsProbabilityMeasure ((gaussMat m n v).map (fun M j i => M i j)) :=
    (Measure.isProbabilityMeasure_map_iff measurable_colsOf.aemeasurable).2 inferInstance
  have h2 := congrArg (Measure.map (Prod.map (id : (Fin m → ℝ) → (Fin m → ℝ))
    (fun (c : Fin n → Fin m → ℝ) => (Matrix.of fun i j => c j i :
      Matrix (Fin m) (Fin n) ℝ)))) hp
  rw [← Measure.map_prod_map _ _ measurable_id measurable_ofCols, Measure.map_id,
    Measure.map_map measurable_ofCols measurable_colsOf,
    Measure.map_map (measurable_id.prodMap measurable_ofCols)
      ((MeasurableEquiv.measurable _).comp measurable_colsOf)] at h2
  have e : ((fun (c : Fin n → Fin m → ℝ) => (Matrix.of fun i j => c j i :
      Matrix (Fin m) (Fin n) ℝ)) ∘ fun (M : Matrix (Fin m) (Fin n) ℝ) j i => M i j) = id := rfl
  rw [e, Measure.map_id] at h2
  rw [← h2]
  rfl

/-! ## The decomposition -/

lemma measurable_mul_const (P : Matrix (Fin n) (Fin k) ℝ) :
    Measurable (fun M : Matrix (Fin m) (Fin n) ℝ => M * P) :=
  (Continuous.matrix_mul continuous_id continuous_const).measurable

/-- `A = (A x) xᵀ + A Π_x`: the matrix is a function of the pair `(A x, A Π_x)`. -/
theorem eq_vecMulVec_add_mul_projT (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    A = Matrix.vecMulVec (A *ᵥ x) x + A * projT x := by
  have h : A * Matrix.vecMulVec x x = Matrix.vecMulVec (A *ᵥ x) x := by
    ext i j
    simp [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul,
      mul_assoc]
  rw [projT, Matrix.mul_sub, Matrix.mul_one, h]
  abel

lemma sum_mul_projT {x : Fin n → ℝ} (hx : normSq x = 1) (b : Fin n) :
    ∑ j, x j * projT x j b = 0 := by
  classical
  have h1 : ∀ j, x j * projT x j b = (if j = b then x j else 0) - x j ^ 2 * x b := by
    intro j
    simp only [projT, Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
    split_ifs <;> ring
  simp_rw [h1]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  have h2 : ∑ j, x j ^ 2 = 1 := hx
  rw [h2]
  simp

/-- **The decomposition of a Gaussian matrix along a unit vector** (fact (G6)): the pair
`(A x, A Π_x)` has the distribution of `(√v·g, M Π_x)`, with `g` a standard Gaussian vector and
`M` an independent copy of `A`. -/
theorem gaussMat_decomp {m n : ℕ} {x : Fin n → ℝ} (hx : normSq x = 1) {v : ℝ} (_hv : 0 ≤ v)
    {F : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ A, F (A *ᵥ x, A * projT x) ∂gaussMat m n v =
      ∫⁻ g, ∫⁻ M, F (√v • g, M * projT x) ∂gaussMat m n v ∂stdGauss (Fin m) := by
  classical
  let col : Fin n → Fin n → ℝ := fun a j => projT x j a
  let H : Fin (n + 1) → Fin n → ℝ := Fin.cases x col
  let G : Fin (n + 1) → Fin (n + 1) → ℝ :=
    Fin.cases (Fin.cases 1 fun _ => 0) fun a => Fin.cases 0 (col a)
  let Ψ : (Fin (n + 1) → Fin m → ℝ) → (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ :=
    fun w => (w 0, Matrix.of fun i a => w (Fin.succ a) i)
  have hΨ : Measurable Ψ :=
    (measurable_pi_apply 0).prodMk (measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun a =>
      (measurable_pi_apply i).comp (measurable_pi_apply (Fin.succ a)))
  have hx2 : ∑ j, x j * x j = 1 := by
    have h : ∑ j, x j ^ 2 = 1 := hx
    simpa [sq] using h
  have hGram : ∀ a b, ∑ j, H a j * H b j = ∑ j, G a j * G b j := by
    intro a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b
    · simp [H, G, Fin.sum_univ_succ, hx2]
    · simp [H, G, Fin.sum_univ_succ, col, sum_mul_projT hx b]
    · have h := sum_mul_projT hx a
      simp only [mul_comm (x _)] at h
      simp [H, G, Fin.sum_univ_succ, col, h]
    · simp [H, G, Fin.sum_univ_succ]
  have hfam : ∀ {k p : ℕ} (K : Fin p → Fin k → ℝ),
      Measurable (fun (M : Matrix (Fin m) (Fin k) ℝ) a => M *ᵥ K a) := fun K =>
    measurable_pi_iff.mpr fun a =>
      (Continuous.matrix_mulVec continuous_id continuous_const).measurable
  have hL : ∀ A : Matrix (Fin m) (Fin n) ℝ,
      (A *ᵥ x, A * projT x) = Ψ (fun a => A *ᵥ H a) := by
    intro A
    refine Prod.ext rfl ?_
    ext i a
    simp [Ψ, H, col, Matrix.mul_apply, Matrix.mulVec, dotProduct]
  let split : Matrix (Fin m) (Fin (n + 1)) ℝ → (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ :=
    fun M => ((fun i => M i 0), (Matrix.of fun i j => M i j.succ))
  have hsplit : Measurable split :=
    (measurable_pi_iff.mpr fun i => (measurable_pi_apply 0).comp (measurable_pi_apply i)).prodMk
      (measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j =>
        (measurable_pi_apply j.succ).comp (measurable_pi_apply i))
  have hR : ∀ M : Matrix (Fin m) (Fin (n + 1)) ℝ,
      Ψ (fun a => M *ᵥ G a) = ((split M).1, (split M).2 * projT x) := by
    intro M
    refine Prod.ext ?_ ?_
    · funext i
      simp [Ψ, G, split, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    · ext i a
      simp [Ψ, G, split, col, Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  have hQ : Measurable (fun p : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ =>
      F (p.1, p.2 * projT x)) :=
    hF.comp (measurable_fst.prodMk ((measurable_mul_const (projT x)).comp measurable_snd))
  calc ∫⁻ A, F (A *ᵥ x, A * projT x) ∂gaussMat m n v
      = ∫⁻ A, F (Ψ (fun a => A *ᵥ H a)) ∂gaussMat m n v := by simp_rw [hL]
    _ = ∫⁻ w, F (Ψ w) ∂(gaussMat m n v).map (fun M a => M *ᵥ H a) :=
        (lintegral_map (hF.comp hΨ) (hfam H)).symm
    _ = ∫⁻ w, F (Ψ w) ∂(gaussMat m (n + 1) v).map (fun M a => M *ᵥ G a) := by
        rw [gaussMat_family v H G hGram]
    _ = ∫⁻ M, F (Ψ (fun a => M *ᵥ G a)) ∂gaussMat m (n + 1) v :=
        lintegral_map (hF.comp hΨ) (hfam G)
    _ = ∫⁻ M, F ((split M).1, (split M).2 * projT x) ∂gaussMat m (n + 1) v := by simp_rw [hR]
    _ = ∫⁻ p, F (p.1, p.2 * projT x) ∂(gaussMat m (n + 1) v).map split :=
        (lintegral_map hQ hsplit).symm
    _ = ∫⁻ p, F (p.1, p.2 * projT x) ∂(gaussCol m v).prod (gaussMat m n v) := by
        rw [gaussMat_split m n v]
    _ = ∫⁻ c, ∫⁻ M, F (c, M * projT x) ∂gaussMat m n v ∂gaussCol m v :=
        lintegral_prod _ hQ.aemeasurable
    _ = ∫⁻ g, ∫⁻ M, F (√v • g, M * projT x) ∂gaussMat m n v ∂stdGauss (Fin m) :=
        lintegral_map hQ.lintegral_prod_right' (measurable_const_smul _)

/-- The decomposition for a function of two variables (jointly measurable). -/
theorem gaussMat_decomp' {m n : ℕ} {x : Fin n → ℝ} (hx : normSq x = 1) {v : ℝ} (hv : 0 ≤ v)
    {Φ : (Fin m → ℝ) → Matrix (Fin m) (Fin n) ℝ → ℝ≥0∞} (hΦ : Measurable (Function.uncurry Φ)) :
    ∫⁻ A, Φ (A *ᵥ x) (A * projT x) ∂gaussMat m n v =
      ∫⁻ g, ∫⁻ M, Φ (√v • g) (M * projT x) ∂gaussMat m n v ∂stdGauss (Fin m) :=
  gaussMat_decomp hx hv hΦ

/-- The decomposition for a function of the matrix `A` itself:
`A = (A x) xᵀ + A Π_x ∼ (√v·g) xᵀ + M Π_x`. -/
theorem gaussMat_decomp_self {m n : ℕ} {x : Fin n → ℝ} (hx : normSq x = 1) {v : ℝ} (hv : 0 ≤ v)
    {Φ : Matrix (Fin m) (Fin n) ℝ → ℝ≥0∞} (hΦ : Measurable Φ) :
    ∫⁻ A, Φ A ∂gaussMat m n v =
      ∫⁻ g, ∫⁻ M, Φ (Matrix.vecMulVec (√v • g) x + M * projT x) ∂gaussMat m n v
        ∂stdGauss (Fin m) := by
  have hm : Measurable (fun p : (Fin m → ℝ) × Matrix (Fin m) (Fin n) ℝ =>
      Matrix.vecMulVec p.1 x + p.2) := by
    refine Measurable.add ?_ measurable_snd
    refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
    simp only [Matrix.vecMulVec_apply]
    exact ((measurable_pi_apply i).comp measurable_fst).mul_const _
  have h := gaussMat_decomp hx hv (hΦ.comp hm)
  simp only [Function.comp] at h
  rw [← h]
  refine lintegral_congr fun A => ?_
  rw [← eq_vecMulVec_add_mul_projT]

end BstLean.Part153

open BstLean.Part153 in
#print axioms gaussMat_transpose
open BstLean.Part153 in
#print axioms opN_transpose
open BstLean.Part153 in
#print axioms gaussMat_vecMul
open BstLean.Part153 in
#print axioms gaussMat_transpose_mulVec
open BstLean.Part153 in
#print axioms gaussMat_cols_map
open BstLean.Part153 in
#print axioms gaussMat_split
open BstLean.Part153 in
#print axioms eq_vecMulVec_add_mul_projT
open BstLean.Part153 in
#print axioms gaussMat_decomp
open BstLean.Part153 in
#print axioms gaussMat_decomp'
open BstLean.Part153 in
#print axioms gaussMat_decomp_self
