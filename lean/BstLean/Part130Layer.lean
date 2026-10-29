import BstLean.Part130Defs
import BstLean.Part105Law

/-!
# Part 130, one Gaussian matrix: its distribution under linear maps

* `gaussMat_map_eq`: two linear images of Gaussian matrices with the same covariance have the same
  distribution.
* `gaussMat_mulVec`: `M h` is `√v·|h|·ξ`, `ξ` standard Gaussian in `ℝ^m`: a Gaussian vector with
  covariance `v|h|²·I`.
* `gaussMat_family`: the distribution of the family `(M h_a)_a` depends on the Gram matrix of
  `(h_a)_a` only.
* `gaussMat_mul_orth`, `gaussMat_orth_mul`: invariance under `M ↦ M R` and `M ↦ Q M`, `R`, `Q`
  orthogonal.
-/

namespace BstLean.Part130

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105 (sphProj gaussLin105)
open BstLean.Part73 (IsOrth)

variable {m k m' k' : ℕ}

/-- The entries of a matrix as a vector indexed by pairs. -/
def flat (M : Matrix (Fin m) (Fin k) ℝ) : Fin m × Fin k → ℝ := fun p => M p.1 p.2

lemma measurable_flat : Measurable (flat : Matrix (Fin m) (Fin k) ℝ → _) := by
  unfold flat
  refine measurable_pi_iff.mpr fun p => ?_
  exact (measurable_pi_apply p.2).comp (measurable_pi_apply p.1)

lemma measurable_mulVec_left {ι κ : Type} [Fintype ι] [Fintype κ] (A : Matrix κ ι ℝ) :
    Measurable (fun ξ : ι → ℝ => A.mulVec ξ) :=
  (Continuous.matrix_mulVec continuous_const continuous_id).measurable

lemma measurable_mulVec_flat {κ : Type} [Fintype κ] (A : Matrix κ (Fin m × Fin k) ℝ) :
    Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => A.mulVec (flat M)) :=
  (measurable_mulVec_left A).comp measurable_flat

lemma measurable_ofFlat (c : ℝ) :
    Measurable (fun ξ : Fin m × Fin k → ℝ => (Matrix.of fun i j => c * ξ (i, j) :
      Matrix (Fin m) (Fin k) ℝ)) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  exact measurable_const.mul (measurable_pi_apply (i, j))

instance (v : ℝ) : IsProbabilityMeasure (gaussMat m k v) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_ofFlat _).aemeasurable).2 inferInstance

instance (k m q : ℕ) : IsProbabilityMeasure (mlpGauss k m q) := by
  unfold mlpGauss; infer_instance

/-- **Two linear images with the same covariance have the same distribution.** -/
theorem gaussMat_map_eq {κ : Type} [Fintype κ] (v : ℝ) (A : Matrix κ (Fin m × Fin k) ℝ)
    (B : Matrix κ (Fin m' × Fin k') ℝ) (h : A * A.transpose = B * B.transpose) :
    (gaussMat m k v).map (fun M => A.mulVec (flat M)) =
      (gaussMat m' k' v).map (fun M => B.mulVec (flat M)) := by
  unfold gaussMat
  rw [Measure.map_map (measurable_mulVec_flat A) (measurable_ofFlat _),
    Measure.map_map (measurable_mulVec_flat B) (measurable_ofFlat _)]
  have h1 : ∀ {m k : ℕ} (A : Matrix κ (Fin m × Fin k) ℝ),
      ((fun M : Matrix (Fin m) (Fin k) ℝ => A.mulVec (flat M)) ∘
        fun ξ : Fin m × Fin k → ℝ => Matrix.of fun i j => Real.sqrt v * ξ (i, j)) =
      fun ξ => (Real.sqrt v • A).mulVec ξ := by
    intro m k A
    funext ξ a
    simp only [Function.comp, Matrix.mulVec, dotProduct, flat, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [h1, h1]
  apply gaussLin105
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, h]

/-- The matrix with entries `ξ (i, j)`. -/
def unflat (ξ : Fin m × Fin k → ℝ) : Matrix (Fin m) (Fin k) ℝ := Matrix.of fun i j => ξ (i, j)

lemma measurable_unflat : Measurable (unflat : (Fin m × Fin k → ℝ) → _) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun j => ?_
  exact measurable_pi_apply (i, j)

@[simp] lemma unflat_flat (M : Matrix (Fin m) (Fin k) ℝ) : unflat (flat M) = M := rfl

lemma sum_pair_ite (i i' : Fin m) (f g : Fin k → ℝ) :
    ∑ p : Fin m × Fin k, (if i = p.1 then f p.2 else 0) * (if i' = p.1 then g p.2 else 0) =
      if i = i' then ∑ j, f j * g j else 0 := by
  rw [Fintype.sum_prod_type]
  by_cases h : i = i'
  · subst h
    simp only [ite_true]
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · simp only [h, ite_false]
    apply Finset.sum_eq_zero
    intro b _
    by_cases h1 : i = b
    · have h2 : ¬ i' = b := fun h2 => h (h1.trans h2.symm)
      simp [h2]
    · simp [h1]

lemma sum_pair_ite_single (i : Fin m) (f : Fin k → ℝ) (ξ : Fin m × Fin k → ℝ) :
    ∑ p : Fin m × Fin k, (if i = p.1 then f p.2 else 0) * ξ p = ∑ j, f j * ξ (i, j) := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

/-- The matrix of `ξ ↦ (Σ_j ξ(i, j) h_j)_i`. -/
def rowMat (m : ℕ) (h : Fin k → ℝ) : Matrix (Fin m) (Fin m × Fin k) ℝ :=
  Matrix.of fun i p => if i = p.1 then h p.2 else 0

lemma rowMat_mulVec (h : Fin k → ℝ) (M : Matrix (Fin m) (Fin k) ℝ) :
    (rowMat m h).mulVec (flat M) = M.mulVec h := by
  funext i
  simp only [Matrix.mulVec, dotProduct, rowMat, flat, Matrix.of_apply]
  rw [sum_pair_ite_single i h (fun p => M p.1 p.2)]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

lemma rowMat_mul_transpose (h h' : Fin k → ℝ) (i i' : Fin m) :
    (rowMat m h * (rowMat m h').transpose) i i' = if i = i' then ∑ j, h j * h' j else 0 := by
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, rowMat, Matrix.of_apply]
  exact sum_pair_ite i i' h h'

/-- **Given its input `h`, the output `M h` of a Gaussian matrix is a Gaussian vector with
covariance `v·|h|²·I`**: it has the distribution of `√v·|h|·ξ`, `ξ` standard Gaussian in `ℝ^m`. -/
theorem gaussMat_mulVec (v : ℝ) (h : Fin k → ℝ) :
    (gaussMat m k v).map (fun M => M.mulVec h) =
      (stdGauss (Fin m)).map (fun ξ => (Real.sqrt v * Real.sqrt (normSq h)) • ξ) := by
  classical
  have hA : (fun M : Matrix (Fin m) (Fin k) ℝ => M.mulVec h) =
      fun M => (rowMat m h).mulVec (flat M) := by
    funext M; rw [rowMat_mulVec]
  have hB : (fun ξ : Fin m → ℝ => (Real.sqrt v * Real.sqrt (normSq h)) • ξ) =
      fun ξ => ((Real.sqrt v * Real.sqrt (normSq h)) • (1 : Matrix (Fin m) (Fin m) ℝ)).mulVec ξ := by
    funext ξ; rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hA, hB]
  unfold gaussMat
  rw [Measure.map_map (measurable_mulVec_flat _) (measurable_ofFlat _)]
  have h1 : ((fun M : Matrix (Fin m) (Fin k) ℝ => (rowMat m h).mulVec (flat M)) ∘
        fun ξ : Fin m × Fin k → ℝ => Matrix.of fun i j => Real.sqrt v * ξ (i, j)) =
      fun ξ => (Real.sqrt v • rowMat m h).mulVec ξ := by
    funext ξ a
    simp only [Function.comp, Matrix.mulVec, dotProduct, flat, Matrix.of_apply, Matrix.smul_apply,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [h1]
  apply gaussLin105
  ext i i'
  simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_apply,
    rowMat_mul_transpose, Matrix.transpose_one, Matrix.mul_one, Matrix.one_apply, smul_eq_mul]
  have hn : (0 : ℝ) ≤ normSq h := Finset.sum_nonneg fun j _ => sq_nonneg _
  by_cases hi : i = i'
  · simp only [hi, ite_true]
    by_cases hv : 0 ≤ v
    · have e1 := Real.mul_self_sqrt hv
      have e2 := Real.mul_self_sqrt hn
      have e3 : ∑ j, h j * h j = normSq h := Finset.sum_congr rfl fun j _ => (sq _).symm
      rw [e3]
      calc Real.sqrt v * (Real.sqrt v * normSq h) = (Real.sqrt v * Real.sqrt v) * normSq h := by ring
        _ = (Real.sqrt v * Real.sqrt v) * (Real.sqrt (normSq h) * Real.sqrt (normSq h)) := by rw [e2]
        _ = _ := by ring
    · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hv)]; simp
  · simp [hi]

/-- **The distribution of the family `(M h_a)_a` depends on the Gram matrix of `(h_a)_a` only.**
`M` and `M'` are Gaussian matrices with the same variance `v` and with `k`, `k'` columns. -/
theorem gaussMat_family {p : ℕ} (v : ℝ) (H : Fin p → Fin k → ℝ) (G : Fin p → Fin k' → ℝ)
    (hG : ∀ a b, ∑ j, H a j * H b j = ∑ j, G a j * G b j) :
    (gaussMat m k v).map (fun M a => M.mulVec (H a)) =
      (gaussMat m k' v).map (fun M a => M.mulVec (G a)) := by
  classical
  let A : ∀ {k : ℕ}, (Fin p → Fin k → ℝ) → Matrix (Fin p × Fin m) (Fin m × Fin k) ℝ :=
    fun H => Matrix.of fun a q => rowMat m (H a.1) a.2 q
  let c : (Fin p × Fin m → ℝ) → Fin p → Fin m → ℝ := fun x a i => x (a, i)
  have hc : Measurable c :=
    measurable_pi_iff.mpr fun a => measurable_pi_iff.mpr fun i => measurable_pi_apply (a, i)
  have h1 : ∀ {k : ℕ} (H : Fin p → Fin k → ℝ),
      (fun (M : Matrix (Fin m) (Fin k) ℝ) a => M.mulVec (H a)) =
        c ∘ fun M => (A H).mulVec (flat M) := by
    intro k H
    funext M a i
    simp only [Function.comp, c, A]
    rw [← rowMat_mulVec]
    rfl
  have hAA : A H * (A H).transpose = A G * (A G).transpose := by
    ext a b
    have e : ∀ {k : ℕ} (H : Fin p → Fin k → ℝ),
        (A H * (A H).transpose) a b = (rowMat m (H a.1) * (rowMat m (H b.1)).transpose) a.2 b.2 := by
      intro k H
      rw [Matrix.mul_apply, Matrix.mul_apply]
      rfl
    rw [e, e, rowMat_mul_transpose, rowMat_mul_transpose, hG]
  rw [h1 H, h1 G, ← Measure.map_map hc (measurable_mulVec_flat _),
    ← Measure.map_map hc (measurable_mulVec_flat _), gaussMat_map_eq v (A H) (A G) hAA]

lemma gaussMat_map_one (v : ℝ) :
    (gaussMat m k v).map (fun M => (1 : Matrix (Fin m × Fin k) (Fin m × Fin k) ℝ).mulVec (flat M)) =
      (gaussMat m k v).map flat := by
  congr 1
  funext M
  rw [Matrix.one_mulVec]

lemma gaussMat_map_unflat_flat (v : ℝ) :
    ((gaussMat m k v).map flat).map unflat = gaussMat m k v := by
  rw [Measure.map_map measurable_unflat measurable_flat]
  have : (unflat ∘ flat : Matrix (Fin m) (Fin k) ℝ → _) = id := rfl
  rw [this, Measure.map_id]

/-- A linear map of the entries with `A Aᵀ = 1` keeps the distribution of a Gaussian matrix. -/
theorem gaussMat_map_isom (v : ℝ) (A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℝ)
    (hA : A * A.transpose = 1) :
    (gaussMat m k v).map (fun M => unflat (A.mulVec (flat M))) = gaussMat m k v := by
  have h := gaussMat_map_eq v A (1 : Matrix (Fin m × Fin k) (Fin m × Fin k) ℝ)
    (by rw [hA, Matrix.transpose_one, Matrix.mul_one])
  have h2 : (fun M : Matrix (Fin m) (Fin k) ℝ => unflat (A.mulVec (flat M))) =
      unflat ∘ fun M => A.mulVec (flat M) := rfl
  rw [h2, ← Measure.map_map measurable_unflat (measurable_mulVec_flat A), h, gaussMat_map_one,
    gaussMat_map_unflat_flat]

/-- **Invariance under an orthogonal change of the input**: `M R` has the distribution of `M`. -/
theorem gaussMat_mul_orth (v : ℝ) (R : Matrix (Fin k) (Fin k) ℝ) (hR : IsOrth R) :
    (gaussMat m k v).map (fun M => M * R) = gaussMat m k v := by
  classical
  let A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℝ :=
    Matrix.of fun a q => rowMat m (fun l => R l a.2) a.1 q
  have hA : A * A.transpose = 1 := by
    ext a b
    have e : (A * A.transpose) a b =
        (rowMat m (fun l => R l a.2) * (rowMat m (fun l => R l b.2)).transpose) a.1 b.1 := by
      rw [Matrix.mul_apply, Matrix.mul_apply]
      rfl
    rw [e, rowMat_mul_transpose]
    have hRR : ∑ j, R j a.2 * R j b.2 = (1 : Matrix (Fin k) (Fin k) ℝ) a.2 b.2 := by
      rw [← hR, Matrix.mul_apply]
      rfl
    rw [hRR, Matrix.one_apply, Matrix.one_apply]
    by_cases h1 : a.1 = b.1 <;> by_cases h2 : a.2 = b.2 <;> simp [h1, h2, Prod.ext_iff]
  have hf : (fun M : Matrix (Fin m) (Fin k) ℝ => M * R) = fun M => unflat (A.mulVec (flat M)) := by
    funext M
    ext i j
    have : (A.mulVec (flat M)) (i, j) = ((rowMat m (fun l => R l j)).mulVec (flat M)) i := rfl
    change _ = (A.mulVec (flat M)) (i, j)
    rw [this, rowMat_mulVec, Matrix.mul_apply]
    rfl
  rw [hf, gaussMat_map_isom v A hA]

lemma sum_pair_ite_right (j j' : Fin k) (f g : Fin m → ℝ) :
    ∑ p : Fin m × Fin k, (if j = p.2 then f p.1 else 0) * (if j' = p.2 then g p.1 else 0) =
      if j = j' then ∑ i, f i * g i else 0 := by
  rw [Fintype.sum_prod_type_right]
  by_cases h : j = j'
  · subst h
    simp only [ite_true]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  · simp only [h, ite_false]
    apply Finset.sum_eq_zero
    intro b _
    by_cases h1 : j = b
    · have h2 : ¬ j' = b := fun h2 => h (h1.trans h2.symm)
      simp [h2]
    · simp [h1]

/-- **Invariance under an orthogonal change of the output**: `Q M` has the distribution of `M`. -/
theorem gaussMat_orth_mul (v : ℝ) (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : IsOrth Q) :
    (gaussMat m k v).map (fun M => Q * M) = gaussMat m k v := by
  classical
  let A : Matrix (Fin m × Fin k) (Fin m × Fin k) ℝ :=
    Matrix.of fun a q => if a.2 = q.2 then Q a.1 q.1 else 0
  have hA : A * A.transpose = 1 := by
    ext a b
    rw [Matrix.mul_apply]
    simp only [A, Matrix.transpose_apply, Matrix.of_apply]
    rw [sum_pair_ite_right a.2 b.2 (fun l => Q a.1 l) (fun l => Q b.1 l)]
    have hQQ : ∑ l, Q a.1 l * Q b.1 l = (1 : Matrix (Fin m) (Fin m) ℝ) a.1 b.1 := by
      rw [← hQ.mul_t, Matrix.mul_apply]
      rfl
    rw [hQQ, Matrix.one_apply, Matrix.one_apply]
    by_cases h1 : a.1 = b.1 <;> by_cases h2 : a.2 = b.2 <;> simp [h1, h2, Prod.ext_iff]
  have hf : (fun M : Matrix (Fin m) (Fin k) ℝ => Q * M) = fun M => unflat (A.mulVec (flat M)) := by
    funext M
    ext i j
    change _ = (A.mulVec (flat M)) (i, j)
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, A, Matrix.of_apply, flat]
    rw [Fintype.sum_prod_type_right, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [hf, gaussMat_map_isom v A hA]

/-- The sign change `M ↦ −M` keeps the distribution of a Gaussian matrix. -/
theorem gaussMat_neg (v : ℝ) : (gaussMat m k v).map (fun M => -M) = gaussMat m k v := by
  have hA : (-1 : Matrix (Fin m × Fin k) (Fin m × Fin k) ℝ) * (-1 : Matrix _ _ ℝ).transpose = 1 := by
    simp
  have hf : (fun M : Matrix (Fin m) (Fin k) ℝ => -M) =
      fun M => unflat ((-1 : Matrix (Fin m × Fin k) (Fin m × Fin k) ℝ).mulVec (flat M)) := by
    funext M
    ext i j
    simp [unflat, flat, Matrix.neg_mulVec]
  rw [hf, gaussMat_map_isom v _ hA]

end BstLean.Part130

open BstLean.Part130 in
#print axioms gaussMat_mulVec
open BstLean.Part130 in
#print axioms gaussMat_family
open BstLean.Part130 in
#print axioms gaussMat_mul_orth
open BstLean.Part130 in
#print axioms gaussMat_orth_mul
open BstLean.Part130 in
#print axioms gaussMat_neg
