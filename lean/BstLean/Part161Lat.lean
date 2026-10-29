import BstLean.Part161Defs

/-!
# Part 161: the latitude decomposition of the stand-in input

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, Lemma `t7:p07:latitude`.

* `hh_mulVec`, `hh_dot`, `hh_normSq`, `hh_e0`, `hh_mul_transpose`, `stdGauss_map_hh`: the
  reflection `hhMat u` keeps the scalar product, sends `e0 n` to the unit vector `u`, and keeps
  the standard Gaussian distribution.
* `consV_map`: `(Z, G) ↦ consV Z G` sends the product of two standard Gaussian distributions to
  the standard Gaussian distribution of `ℝⁿ`.
* `sphPt_latitude`: the stand-in input at `ξ = H (Z, G)` is the point of latitude
  `latitude |ĉ| τ (Z, G)` and direction `G/|G|`.
* `xLat_eq`, `dir_orth`, `dir_normSq`: `xLat c s v = s·u + √(1 − s²)·H(0, v)`, with `H(0, v)`
  orthogonal to `u` and of the same length as `v`.
* **`nuStand_latitude`**: the stand-in input distribution is the distribution of
  `xLat c s V`, with the latitude `s` and an INDEPENDENT direction `V = G'/|G'|`.
* `unitF_map_uniformSphere`: `G'/|G'|` has the uniform distribution on the unit sphere.
-/

namespace BstLean.Part161

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part130 BstLean.Part134
open BstLean.Part105 (sphProj)
open BstLean.Part157
open BstLean.Part53 (unitF53 radF53 measurable_unitF measurable_radF gauss_polar_gen)

variable {n : ℕ}

/-! ## The reflection -/

/-- The reflection as a function: `H x = x − κ⟨w, x⟩·w`, `w = e0 − u`, `κ = 2/|w|²`. -/
lemma hh_mulVec (u x : Fin n → ℝ) :
    (hhMat u).mulVec x =
      x - (2 * (normSq (e0 n - u))⁻¹ * ∑ j, (e0 n - u) j * x j) • (e0 n - u) := by
  unfold hhMat
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec]
  congr 1
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

private lemma kap_mul (w : Fin n → ℝ) :
    (2 * (normSq w)⁻¹) * (2 * (normSq w)⁻¹) * normSq w = 2 * (2 * (normSq w)⁻¹) := by
  by_cases h : normSq w = 0
  · simp [h]
  · field_simp

/-- The reflection keeps the scalar product. -/
lemma hh_dot (u x y : Fin n → ℝ) :
    ∑ i, (hhMat u).mulVec x i * (hhMat u).mulVec y i = ∑ i, x i * y i := by
  rw [hh_mulVec, hh_mulVec]
  set w := e0 n - u with hw
  set κ := 2 * (normSq w)⁻¹ with hκ
  set A := ∑ j, w j * x j with hA
  set B := ∑ j, w j * y j with hB
  have e : ∀ i, (x - (κ * A) • w) i * (y - (κ * B) • w) i =
      x i * y i - κ * B * (w i * x i) - κ * A * (w i * y i) + κ * κ * A * B * (w i ^ 2) := by
    intro i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [e]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← hA, ← hB]
  have h2 : κ * κ * A * B * ∑ i, w i ^ 2 = 2 * κ * A * B := by
    have := kap_mul w
    rw [← hκ] at this
    have e2 : ∑ i, w i ^ 2 = normSq w := rfl
    rw [e2]
    calc κ * κ * A * B * normSq w = (κ * κ * normSq w) * A * B := by ring
      _ = 2 * κ * A * B := by rw [this]
  rw [h2]
  ring

/-- The reflection keeps the length. -/
lemma hh_normSq (u x : Fin n → ℝ) : normSq ((hhMat u).mulVec x) = normSq x := by
  have h := hh_dot u x x
  unfold normSq
  simp_rw [sq]
  exact h

lemma e0_apply_sq_sum (hn : 1 ≤ n) : normSq (e0 n) = 1 := by
  unfold normSq e0
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin n)]
  · simp
  · intro i _ hi
    have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    simp [this]
  · simp

lemma e0_dot (hn : 1 ≤ n) (x : Fin n → ℝ) : ∑ i, e0 n i * x i = x ⟨0, by omega⟩ := by
  unfold e0
  rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin n)]
  · simp
  · intro i _ hi
    have : (i : ℕ) ≠ 0 := fun h => hi (Fin.ext h)
    simp [this]
  · simp

/-- The reflection sends `e0 n` to the unit vector `u`. -/
lemma hh_e0 (hn : 1 ≤ n) {u : Fin n → ℝ} (hu : normSq u = 1) : (hhMat u).mulVec (e0 n) = u := by
  rw [hh_mulVec]
  set w := e0 n - u with hw
  have h1 : ∑ j, w j * e0 n j = 1 - u ⟨0, by omega⟩ := by
    have e : ∀ j, w j * e0 n j = e0 n j * e0 n j - e0 n j * u j := by
      intro j; simp only [hw, Pi.sub_apply]; ring
    simp_rw [e]
    rw [Finset.sum_sub_distrib, e0_dot hn u, e0_dot hn (e0 n)]
    simp [e0]
  have h2 : normSq w = 2 * (1 - u ⟨0, by omega⟩) := by
    have e : ∀ j, w j ^ 2 = e0 n j ^ 2 - 2 * (e0 n j * u j) + u j ^ 2 := by
      intro j; simp only [hw, Pi.sub_apply]; ring
    unfold normSq
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, e0_dot hn u]
    have a1 : ∑ j, e0 n j ^ 2 = 1 := e0_apply_sq_sum hn
    have a2 : ∑ j, u j ^ 2 = 1 := hu
    rw [a1, a2]; ring
  by_cases h : normSq w = 0
  · have hw0 : w = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (w i))).1 h i
        (Finset.mem_univ i)
      simpa using this
    have : e0 n = u := sub_eq_zero.mp hw0
    rw [hw0]; simp [this]
  · have h3 : 2 * (normSq w)⁻¹ * ∑ j, w j * e0 n j = 1 := by
      rw [h1]
      have : (1 - u ⟨0, by omega⟩) ≠ 0 := by
        intro h0; apply h; rw [h2, h0]; ring
      rw [h2]; field_simp
    rw [h3, one_smul, hw]; abel

lemma hh_symm (u : Fin n → ℝ) (i j : Fin n) : hhMat u i j = hhMat u j i := by
  unfold hhMat
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul,
    Matrix.one_apply]
  rw [mul_comm ((e0 n - u) i)]
  congr 1
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

/-- The reflection is an orthogonal matrix. -/
lemma hh_mul_transpose (u : Fin n → ℝ) : hhMat u * (hhMat u).transpose = 1 := by
  classical
  ext i j
  have h := hh_dot u (Pi.single i 1) (Pi.single j 1)
  simp only [Matrix.mulVec_single_one, Matrix.col_apply] at h
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  have e : ∀ k, hhMat u i k * hhMat u j k = hhMat u k i * hhMat u k j := fun k => by
    rw [hh_symm u i k, hh_symm u j k]
  simp_rw [e]
  rw [h, Matrix.one_apply]
  simp [Pi.single_apply, eq_comm]

/-- The reflection keeps the standard Gaussian distribution. -/
lemma stdGauss_map_hh (u : Fin n → ℝ) :
    (stdGauss (Fin n)).map (fun ξ => (hhMat u).mulVec ξ) = stdGauss (Fin n) :=
  stdGauss_map_orthonormal (hhMat u) (hh_mul_transpose u)

lemma measurable_hh (u : Fin n → ℝ) : Measurable (fun ξ : Fin n → ℝ => (hhMat u).mulVec ξ) :=
  (Continuous.matrix_mulVec continuous_const continuous_id).measurable

/-! ## The unit vector of the retained World centre value -/

lemma normSq_uHat {c : Ret n} (hc : c.1.2 ≠ 0) : normSq (uHat c) = 1 := by
  have h0 : normSq c.1.2 ≠ 0 := fun h => hc (BstLean.Part130.normSq_eq_zero h)
  have hp : 0 < normSq c.1.2 := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm h0)
  unfold uHat
  rw [normSq_smul, inv_pow, Real.sq_sqrt hp.le, inv_mul_cancel₀ h0]

lemma c_eq_uHat {c : Ret n} (hc : c.1.2 ≠ 0) : c.1.2 = √(normSq c.1.2) • uHat c := by
  have h0 : normSq c.1.2 ≠ 0 := fun h => hc (BstLean.Part130.normSq_eq_zero h)
  have hp : 0 < normSq c.1.2 := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm h0)
  unfold uHat
  rw [smul_smul, mul_inv_cancel₀ (Real.sqrt_pos.mpr hp).ne', one_smul]

/-! ## The vector `consV` -/

lemma consV_zero (hn : 1 ≤ n) (z : ℝ) (g : Fin (n - 1) → ℝ) : consV z g ⟨0, by omega⟩ = z := by
  simp [consV]

lemma consV_smul (a z : ℝ) (g : Fin (n - 1) → ℝ) : consV (a * z) (a • g) = a • consV z g := by
  funext i
  unfold consV
  by_cases h : (i : ℕ) = 0 <;> simp [h]

lemma consV_add (z z' : ℝ) (g g' : Fin (n - 1) → ℝ) :
    consV (z + z') (g + g') = consV z g + consV z' g' := by
  funext i
  unfold consV
  by_cases h : (i : ℕ) = 0 <;> simp [h]

lemma consV_one_zero : consV (n := n) 1 0 = e0 n := by
  funext i
  unfold consV e0
  by_cases h : (i : ℕ) = 0 <;> simp [h]

private lemma consV_eq_cons (k : ℕ) (z : ℝ) (g : Fin k → ℝ) :
    consV (n := k + 1) z g = (Fin.cons z g : Fin (k + 1) → ℝ) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [consV]
  · simp only [consV, Fin.val_succ, Nat.succ_ne_zero, dite_false, Fin.cons_succ,
      Nat.add_sub_cancel]
    rfl

lemma normSq_consV (hn : 1 ≤ n) (z : ℝ) (g : Fin (n - 1) → ℝ) :
    normSq (consV z g) = z ^ 2 + normSq g := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [consV_eq_cons]
  unfold normSq
  rw [Fin.sum_univ_succ]
  simp

/-- `(Z, G) ↦ consV Z G` sends the product of the standard Gaussian distributions of `ℝ` and of
`ℝ^{n−1}` to the standard Gaussian distribution of `ℝⁿ`. -/
theorem consV_map (hn : 1 ≤ n) :
    ((gaussianReal 0 1).prod (stdGauss (Fin (n - 1)))).map (fun p => consV p.1 p.2) =
      stdGauss (Fin n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  change ((gaussianReal 0 1).prod (stdGauss (Fin k))).map
    (fun p : ℝ × (Fin k → ℝ) => consV (n := k + 1) p.1 p.2) = stdGauss (Fin (k + 1))
  have hmp := (measurePreserving_piFinSuccAbove (fun _ : Fin (k + 1) => gaussianReal 0 1) 0).symm
  have e : (fun p : ℝ × (Fin k → ℝ) => consV (n := k + 1) p.1 p.2) =
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (k + 1) => ℝ) 0).symm := by
    funext p
    rw [consV_eq_cons]
    simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero']
  rw [e]
  exact hmp.map_eq

/-! ## The latitude form of the stand-in input -/

lemma hh_smul (u : Fin n → ℝ) (a : ℝ) (x : Fin n → ℝ) :
    (hhMat u).mulVec (a • x) = a • (hhMat u).mulVec x := Matrix.mulVec_smul _ _ _

/-- `xLat c s v = s·u + √(1 − s²)·H(0, v)`. -/
lemma xLat_eq (hn : 1 ≤ n) {c : Ret n} (hc : c.1.2 ≠ 0) (s : ℝ) (v : Fin (n - 1) → ℝ) :
    xLat c s v = s • uHat c + √(1 - s ^ 2) • (hhMat (uHat c)).mulVec (consV 0 v) := by
  unfold xLat
  have e : consV s (√(1 - s ^ 2) • v) = s • e0 n + √(1 - s ^ 2) • consV 0 v := by
    rw [← consV_one_zero, ← consV_smul, ← consV_smul, ← consV_add]
    simp
  rw [e, Matrix.mulVec_add, hh_smul, hh_smul, hh_e0 hn (normSq_uHat hc)]

/-- The direction `H(0, v)` is orthogonal to `u`. -/
lemma dir_orth (hn : 1 ≤ n) {c : Ret n} (hc : c.1.2 ≠ 0) (v : Fin (n - 1) → ℝ) :
    ∑ i, (hhMat (uHat c)).mulVec (consV 0 v) i * uHat c i = 0 := by
  have h := hh_dot (uHat c) (consV 0 v) (e0 n)
  rw [hh_e0 hn (normSq_uHat hc)] at h
  rw [h]
  have e : ∀ i, consV 0 v i * e0 n i = e0 n i * consV 0 v i := fun i => mul_comm _ _
  simp_rw [e]
  rw [e0_dot hn, consV_zero hn]

/-- The direction `H(0, v)` has the length of `v`. -/
lemma dir_normSq (hn : 1 ≤ n) (c : Ret n) (v : Fin (n - 1) → ℝ) :
    normSq ((hhMat (uHat c)).mulVec (consV 0 v)) = normSq v := by
  rw [hh_normSq, normSq_consV hn]; simp

/-- **The latitude form of the stand-in input.** For `ξ = H (Z, G)` with `G ≠ 0` and `τ > 0`:
`sphPt (ĉ + τ ξ)` is the point of latitude `latitude |ĉ| τ (Z, G)` and direction `G/|G|`. -/
theorem sphPt_latitude (hn : 1 ≤ n) {c : Ret n} (hc : c.1.2 ≠ 0) {τ : ℝ} (hτ : 0 < τ) (Z : ℝ)
    {G : Fin (n - 1) → ℝ} (hG : normSq G ≠ 0) :
    sphPt (c.1.2 + τ • (hhMat (uHat c)).mulVec (consV Z G)) =
      xLat c (latitude (√(normSq c.1.2)) τ (Z, G)) (unitF53 G) := by
  set a := √(normSq c.1.2) with ha
  set w : Fin n → ℝ := consV (a + τ * Z) (τ • G) with hw
  have hGp : 0 < normSq G := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hG)
  have e1 : c.1.2 + τ • (hhMat (uHat c)).mulVec (consV Z G) = (hhMat (uHat c)).mulVec w := by
    have e : w = a • e0 n + τ • consV Z G := by
      rw [hw, ← consV_one_zero, ← consV_smul, ← consV_smul, ← consV_add]
      simp
    rw [e, Matrix.mulVec_add, hh_smul, hh_smul, hh_e0 hn (normSq_uHat hc), ← c_eq_uHat hc]
  have hN : normSq w = (a + τ * Z) ^ 2 + τ ^ 2 * normSq G := by
    rw [hw, normSq_consV hn, normSq_smul]
  have hNp : 0 < normSq w := by rw [hN]; positivity
  set N := √(normSq w) with hNd
  have hN0 : 0 < N := Real.sqrt_pos.mpr hNp
  have hs : latitude a τ (Z, G) = (a + τ * Z) / N := by
    unfold latitude; rw [hNd, hN]
  rw [e1]
  unfold sphPt
  rw [hh_normSq]
  simp only [hNp.ne', ↓reduceIte]
  have e2 : sphProj ((hhMat (uHat c)).mulVec w) =
      (1 / N) • (hhMat (uHat c)).mulVec w := by
    have : sphProj ((hhMat (uHat c)).mulVec w) =
      (1 / √(normSq ((hhMat (uHat c)).mulVec w))) • (hhMat (uHat c)).mulVec w := rfl
    rw [this, hh_normSq]
  rw [e2, ← hh_smul]
  unfold xLat
  congr 1
  rw [hs, hw, ← consV_smul]
  have hr : √(normSq G) ≠ 0 := (Real.sqrt_pos.mpr hGp).ne'
  have h1 : 1 - ((a + τ * Z) / N) ^ 2 = (τ * √(normSq G) / N) ^ 2 := by
    have hN2 : N ^ 2 = (a + τ * Z) ^ 2 + τ ^ 2 * normSq G := by
      rw [hNd, Real.sq_sqrt hNp.le, hN]
    have hg2 : √(normSq G) ^ 2 = normSq G := Real.sq_sqrt hGp.le
    field_simp
    rw [hN2, hg2]; ring
  have h2 : √(1 - ((a + τ * Z) / N) ^ 2) = τ * √(normSq G) / N := by
    rw [h1, Real.sqrt_sq (by positivity)]
  rw [h2]
  have e3 : unitF53 G = (1 / √(normSq G)) • G := rfl
  rw [e3, smul_smul, smul_smul]
  congr 1
  · ring
  · congr 1
    field_simp

/-! ## The latitude and an independent direction -/

/-- The set of the vectors of length `0` has probability `0` (dimension at least `1`). -/
lemma stdGauss_normSq_zero {k : ℕ} (hk : 1 ≤ k) :
    stdGauss (Fin k) {G | normSq G = 0} = 0 := by
  have hsub : {G : Fin k → ℝ | normSq G = 0} ⊆
      (fun G : Fin k → ℝ => G ⟨0, by omega⟩) ⁻¹' {0} := by
    intro G hG
    have := BstLean.Part130.normSq_eq_zero hG
    simp [this]
  refine measure_mono_null hsub ?_
  have hmp := measurePreserving_eval (fun _ : Fin k => gaussianReal 0 1) (⟨0, by omega⟩ : Fin k)
  have : stdGauss (Fin k) ((fun G : Fin k → ℝ => G ⟨0, by omega⟩) ⁻¹' {0}) =
      gaussianReal 0 1 {0} := by
    rw [← hmp.map_eq, Measure.map_apply hmp.measurable (measurableSet_singleton 0)]
    rfl
  rw [this]
  have : NullSingletonClass (gaussianReal (0 : ℝ) 1) :=
    nullSingletonClass_gaussianReal one_ne_zero
  exact measure_singleton 0

/-- Step 1: the stand-in input distribution with the Gaussian vector `ξ = H (Z, G)`. -/
lemma nuStand_cons (hn : 1 ≤ n) (D : Design n) (c : Ret n) :
    nuStand D c = ((gaussianReal 0 1).prod (stdGauss (Fin (n - 1)))).map
      (fun p => sphPt (c.1.2 + D.tau0 c • (hhMat (uHat c)).mulVec (consV p.1 p.2))) := by
  have mf : Measurable (fun ξ : Fin n → ℝ => sphPt (c.1.2 + D.tau0 c • ξ)) :=
    measurable_sphPt.comp (measurable_const.add (measurable_const_smul (D.tau0 c)))
  unfold nuStand
  conv_lhs => rw [← stdGauss_map_hh (uHat c), ← consV_map hn]
  rw [Measure.map_map (measurable_hh _) measurable_consV,
    Measure.map_map mf ((measurable_hh _).comp measurable_consV)]
  rfl

lemma measurable_latitude (a τ : ℝ) :
    Measurable (fun p : ℝ × (Fin (n - 1) → ℝ) => latitude a τ p) :=
  measurable_latitude_comp measurable_const measurable_const measurable_id

lemma measurable_xLat_comp {β : Type*} [MeasurableSpace β] (c : Ret n) {f : β → ℝ}
    {g : β → Fin (n - 1) → ℝ} (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => xLat c (f x) (g x)) := by
  unfold xLat
  have h1 : Measurable (fun x => consV (n := n) (f x) (√(1 - f x ^ 2) • g x)) :=
    measurable_consV.comp (hf.prodMk
      (((measurable_const.sub (hf.pow_const 2)).sqrt).smul hg))
  exact (Continuous.matrix_mulVec continuous_const continuous_id).measurable.comp h1

/-- The direction and the radius of a standard Gaussian vector are independent, in the form
`∫ F(|G|, G/|G|) = ∫∫ F(|G|, G'/|G'|)`. -/
lemma polar_indep_lintegral {k : ℕ} (F : ℝ → (Fin k → ℝ) → ℝ≥0∞)
    (hF : Measurable (Function.uncurry F)) :
    ∫⁻ G, F (radF53 G) (unitF53 G) ∂stdGauss (Fin k) =
      ∫⁻ G, ∫⁻ G', F (radF53 G) (unitF53 G') ∂stdGauss (Fin k) ∂stdGauss (Fin k) := by
  have hF' : Measurable (Function.uncurry (fun (v : Fin k → ℝ) (r : ℝ) => F r v)) :=
    hF.comp (measurable_snd.prodMk measurable_fst)
  have hp := gauss_polar_gen (fun (v : Fin k → ℝ) (r : ℝ) => F r v) hF'
  rw [hp]
  exact lintegral_lintegral_swap
    ((hF'.comp ((measurable_unitF.comp measurable_fst).prodMk
      (measurable_radF.comp measurable_snd))).aemeasurable)

/-- The latitude as a function of the radius `r = |G|`. -/
noncomputable def latR (a τ Z r : ℝ) : ℝ := (a + τ * Z) / √((a + τ * Z) ^ 2 + τ ^ 2 * r ^ 2)

lemma latitude_eq_latR (a τ Z : ℝ) (G : Fin (n - 1) → ℝ) :
    latitude a τ (Z, G) = latR a τ Z (radF53 G) := by
  have : radF53 G ^ 2 = normSq G := Real.sq_sqrt (normSq_nonneg G)
  unfold latR
  rw [this]
  rfl

lemma measurable_latR (a τ Z : ℝ) : Measurable (latR a τ Z) := by
  unfold latR
  exact measurable_const.div ((measurable_const.add
    (measurable_const.mul (measurable_id.pow_const 2))).sqrt)

/-- Step 3: the direction of `G` is replaced by the direction of an independent `G'` (the
direction and the radius of a standard Gaussian vector are independent). -/
lemma latitude_indep (c : Ret n) (a τ : ℝ) :
    ((gaussianReal 0 1).prod (stdGauss (Fin (n - 1)))).map
        (fun p : ℝ × (Fin (n - 1) → ℝ) => xLat c (latitude (n := n) a τ p) (unitF53 p.2)) =
      (((gaussianReal 0 1).prod (stdGauss (Fin (n - 1)))).prod (stdGauss (Fin (n - 1)))).map
        (fun p : (ℝ × (Fin (n - 1) → ℝ)) × (Fin (n - 1) → ℝ) =>
          xLat c (latitude (n := n) a τ p.1) (unitF53 p.2)) := by
  have mlat : Measurable (fun p : ℝ × (Fin (n - 1) → ℝ) => latitude (n := n) a τ p) :=
    measurable_latitude (n := n) a τ
  have mu1 : Measurable (fun p : ℝ × (Fin (n - 1) → ℝ) => unitF53 p.2) :=
    measurable_unitF.comp measurable_snd
  have mg1 : Measurable (fun p : ℝ × (Fin (n - 1) → ℝ) =>
      xLat c (latitude (n := n) a τ p) (unitF53 p.2)) := measurable_xLat_comp c mlat mu1
  have mu2 : Measurable (fun p : (ℝ × (Fin (n - 1) → ℝ)) × (Fin (n - 1) → ℝ) => unitF53 p.2) :=
    measurable_unitF.comp measurable_snd
  have mg2 : Measurable (fun p : (ℝ × (Fin (n - 1) → ℝ)) × (Fin (n - 1) → ℝ) =>
      xLat c (latitude (n := n) a τ p.1) (unitF53 p.2)) :=
    measurable_xLat_comp c (mlat.comp measurable_fst) mu2
  refine Measure.ext fun S hS => ?_
  have mφ : Measurable (S.indicator (1 : (Fin n → ℝ) → ℝ≥0∞)) := measurable_one.indicator hS
  rw [← lintegral_indicator_one hS, ← lintegral_indicator_one hS, lintegral_map mφ mg1,
    lintegral_map mφ mg2]
  set φ : (Fin n → ℝ) → ℝ≥0∞ := S.indicator 1 with hφ
  have h1 : Measurable (fun p : ℝ × (Fin (n - 1) → ℝ) =>
      φ (xLat c (latitude (n := n) a τ p) (unitF53 p.2))) := mφ.comp mg1
  have h2 : Measurable (fun p : (ℝ × (Fin (n - 1) → ℝ)) × (Fin (n - 1) → ℝ) =>
      φ (xLat c (latitude (n := n) a τ p.1) (unitF53 p.2))) := mφ.comp mg2
  rw [lintegral_prod _ h1.aemeasurable, lintegral_prod _ h2.aemeasurable]
  have h3 : Measurable (fun x : ℝ × (Fin (n - 1) → ℝ) =>
      ∫⁻ y : Fin (n - 1) → ℝ, φ (xLat c (latitude (n := n) a τ x) (unitF53 y))
        ∂stdGauss (Fin (n - 1))) := h2.lintegral_prod_right'
  rw [lintegral_prod _ h3.aemeasurable]
  refine lintegral_congr fun Z => ?_
  have hFm : Measurable (Function.uncurry (fun (r : ℝ) (v : Fin (n - 1) → ℝ) =>
      φ (xLat c (latR a τ Z r) v))) :=
    mφ.comp (measurable_xLat_comp c ((measurable_latR a τ Z).comp measurable_fst)
      measurable_snd)
  have h := polar_indep_lintegral (k := n - 1) (fun r v => φ (xLat c (latR a τ Z r) v)) hFm
  simp only [latitude_eq_latR]
  exact h

/-- **The latitude decomposition of the stand-in input (Lemma `t7:p07:latitude`).** For
`ĉ ≠ 0` and `τ₀ > 0`, the stand-in input distribution `ν'` (the distribution of
`sphPt (ĉ + τ₀ ξ)`) is the distribution of `xLat c s V = s·u + √(1 − s²)·H(0, V)`, where
`s = latitude |ĉ| τ₀ (Z, G)` is the latitude and `V = G'/|G'|` is a direction; `Z`, `G`, `G'`
are independent standard Gaussian (`G`, `G'` in `ℝ^{n−1}`). So the direction is independent of
the latitude, and it is uniform on the unit sphere (`unitF_map_uniformSphere`). -/
theorem nuStand_latitude (hn : 2 ≤ n) (D : Design n) (c : Ret n) (hc : c.1.2 ≠ 0)
    (hτ : 0 < D.tau0 c) :
    nuStand D c =
      (((gaussianReal 0 1).prod (stdGauss (Fin (n - 1)))).prod (stdGauss (Fin (n - 1)))).map
        (fun p => xLat c (latitude (√(normSq c.1.2)) (D.tau0 c) p.1) (unitF53 p.2)) := by
  have hn1 : 1 ≤ n := by omega
  rw [nuStand_cons hn1, ← latitude_indep]
  have hnull : ((gaussianReal 0 1).prod (stdGauss (Fin (n - 1))))
      {p : ℝ × (Fin (n - 1) → ℝ) | normSq p.2 = 0} = 0 := by
    have : {p : ℝ × (Fin (n - 1) → ℝ) | normSq p.2 = 0} =
        Set.univ ×ˢ {G : Fin (n - 1) → ℝ | normSq G = 0} := by
      ext p; simp
    rw [this, Measure.prod_prod, stdGauss_normSq_zero (by omega), mul_zero]
  refine Measure.map_congr ?_
  have : ∀ᵐ p ∂((gaussianReal 0 1).prod (stdGauss (Fin (n - 1)))), normSq p.2 ≠ 0 := by
    rw [ae_iff]; simpa using hnull
  filter_upwards [this] with p hp
  exact sphPt_latitude hn1 hc hτ p.1 hp

/-- The direction `G'/|G'|` of a standard Gaussian vector has the uniform distribution on the
unit sphere. -/
theorem unitF_map_uniformSphere {k : ℕ} (hk : 1 ≤ k) :
    (stdGauss (Fin k)).map unitF53 = uniformSphere k := by
  ext s hs
  rw [Measure.map_apply measurable_unitF hs, ← lintegral_indicator_one hs,
    BstLean.Part56.uniformSphere_lintegral_gauss k hk _ (measurable_one.indicator hs),
    ← lintegral_indicator_one (measurable_unitF hs)]
  rfl

end BstLean.Part161

open BstLean.Part161 in
#print axioms hh_mul_transpose
open BstLean.Part161 in
#print axioms consV_map
open BstLean.Part161 in
#print axioms sphPt_latitude
open BstLean.Part161 in
#print axioms nuStand_latitude
open BstLean.Part161 in
#print axioms unitF_map_uniformSphere
