import BstLean.Part153JDefs
import BstLean.Part153S
import BstLean.Part153Inv

/-!
# Part 153 SJ: Lemma S (second assertion) with the tangent Jacobian, and the residual covariance

Paper source: `proofs/option-n/theorem5-04-standin-structure.tex` (Lemma J, Lemma S second
assertion), `theorem5-05-covariance.tex` (first paragraph; Lemma "The residual covariance").

Every result holds for EVERY pair of matrices `A₁`, `A₂` (no probability over them).
Notation: `y = c + τξ`, `x = sphPt y = y/|y|`, `t = 2/m`, `q(x) = √t • hid2 A₁ A₂ x`.

* `hid2_smul`, `jac_smul`: positive homogeneity of the feature map and of its Jacobian matrix.
* `opN_jacT_le_sj`: `‖𝒥(x)Π_x‖_op ≤ ‖A₂‖_op·‖A₁‖_op` for a unit vector `x`.
* `hid2_sph_local`: at a point `y ≠ 0` where the Jacobian formula holds, on the unit sphere near
  `x`: `|h(x') − h(x)| ≤ (‖𝒥(x)Π_x‖_op + δ)·|x' − x|`.
* **`lemmaS_jac`**: `Var_ξ φ(q(x)) ≤ L_φ²·Ξ` for a globally Lipschitz `φ`.
* **`XiS_le_Xi4`**: `Ξ ≤ Ξ₄`.
* **`cov_hid2_le`**: `t·Var_ξ ⟨w, h(x)⟩ ≤ Ξ·|w|²`.
* **`weak_var_le`**, **`XiS_le_op`**: the bounds from the global Lipschitz constant alone.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part153

open MeasureTheory ProbabilityTheory Filter Topology Set Matrix Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part148 (EuLip)
open BstLean.Part151 (jac JacAt mask measurable_mask lemmaJ_shift)

/-! ## §1 Vectors -/

section vec

variable {ι : Type*} [Fintype ι]

lemma nrm_tri3 (a b : ι → ℝ) : nrm a ≤ nrm (a - b) + nrm b := by
  have h := nrm_add_le (a - b) b
  rwa [sub_add_cancel] at h

lemma norm_le_nrm (v : ι → ℝ) : ‖v‖ ≤ nrm v := by
  refine (pi_norm_le_iff_of_nonneg (nrm_nonneg v)).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  unfold nrm normSq
  exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun i => v i ^ 2)
    (fun i _ => sq_nonneg _) (Finset.mem_univ i))

lemma nrm_mask_mul_le (a b : ι → ℝ) : nrm (fun i => mask (a i) * b i) ≤ nrm b := by
  unfold nrm normSq
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rw [mul_pow, BstLean.Part151.mask_sq]
  have h1 : mask (a i) ≤ 1 := by unfold mask; split_ifs <;> norm_num
  exact mul_le_of_le_one_left (sq_nonneg _) h1

/-- `P(a + δ')(b + δ') ≤ Pab + δ` for a small `δ' > 0`. -/
lemma prod_eps {P a b δ : ℝ} (hP : 0 ≤ P) (ha : 0 ≤ a) (hb : 0 ≤ b) (hδ : 0 < δ) :
    ∃ δ' : ℝ, 0 < δ' ∧ P * (a + δ') * (b + δ') ≤ P * a * b + δ := by
  have hD : 0 < P * (a + b + 1) + 1 := by positivity
  refine ⟨min 1 (δ / (P * (a + b + 1) + 1)), lt_min one_pos (div_pos hδ hD), ?_⟩
  set e := min 1 (δ / (P * (a + b + 1) + 1)) with he
  have he0 : 0 < e := lt_min one_pos (div_pos hδ hD)
  have h1 : e ≤ 1 := min_le_left _ _
  have h2 : e * (P * (a + b + 1) + 1) ≤ δ := by
    have : e ≤ δ / (P * (a + b + 1) + 1) := min_le_right _ _
    exact (le_div_iff₀ hD).mp this
  nlinarith [mul_nonneg (mul_nonneg hP he0.le) (sub_nonneg.mpr h1)]

end vec

/-! ## §2 The operator norm of the tangent Jacobian -/

section op

variable {n m₁ m₂ : ℕ}

lemma opN_le_of_bound {p q : ℕ} (M : Matrix (Fin p) (Fin q) ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ v, nrm (M *ᵥ v) ≤ C * nrm v) : opN M ≤ C := by
  by_cases hne : (opSet M).Nonempty
  · refine csSup_le hne ?_
    rintro x ⟨u, v, hu, hv, rfl⟩
    have h1 := abs_dot_le_nrm u (M *ᵥ v)
    have hu' : nrm u = 1 := by unfold nrm normSq; rw [hu, Real.sqrt_one]
    have hv' : nrm v = 1 := by unfold nrm normSq; rw [hv, Real.sqrt_one]
    have h2 := h v
    rw [hv', mul_one] at h2
    rw [hu', one_mul] at h1
    exact (le_abs_self _).trans (h1.trans h2)
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    unfold opN
    rw [hne, Real.sSup_empty]
    exact hC

/-- Positive homogeneity of the feature map. -/
lemma hid2_smul (A₁ : Matrix (Fin m₁) (Fin n) ℝ) (A₂ : Matrix (Fin m₂) (Fin m₁) ℝ) {s : ℝ}
    (hs : 0 ≤ s) (z : Fin n → ℝ) : hid2 A₁ A₂ (s • z) = s • hid2 A₁ A₂ z := by
  unfold hid2
  rw [Matrix.mulVec_smul, reluV_smul_of_nonneg hs, Matrix.mulVec_smul, reluV_smul_of_nonneg hs]

lemma mask_mul_pos {s : ℝ} (hs : 0 < s) (t : ℝ) : mask (s * t) = mask t := by
  by_cases ht : 0 < t
  · rw [BstLean.Part151.mask_of_pos (mul_pos hs ht), BstLean.Part151.mask_of_pos ht]
  · rw [BstLean.Part151.mask_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hs.le (not_lt.mp ht)),
      BstLean.Part151.mask_of_nonpos (not_lt.mp ht)]

/-- The Jacobian matrix does not change along a ray (the masks do not change). -/
lemma jac_smul (A₁ : Matrix (Fin m₁) (Fin n) ℝ) (A₂ : Matrix (Fin m₂) (Fin m₁) ℝ) {s : ℝ}
    (hs : 0 < s) (z : Fin n → ℝ) : jac A₁ A₂ (s • z) = jac A₁ A₂ z := by
  ext j l
  unfold jac
  simp only [Matrix.of_apply]
  rw [Matrix.mulVec_smul, reluV_smul_of_nonneg hs.le, Matrix.mulVec_smul]
  simp only [Pi.smul_apply, smul_eq_mul, mask_mul_pos hs]

lemma jac_mulVec_apply (A₁ : Matrix (Fin m₁) (Fin n) ℝ) (A₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (y v : Fin n → ℝ) (j : Fin m₂) :
    (jac A₁ A₂ y *ᵥ v) j = mask ((A₂ *ᵥ reluV (A₁ *ᵥ y)) j) *
      (A₂ *ᵥ (fun i => mask ((A₁ *ᵥ y) i) * (A₁ *ᵥ v) i)) j := by
  have e1 : (jac A₁ A₂ y *ᵥ v) j = ∑ l, ∑ i, mask ((A₂ *ᵥ reluV (A₁ *ᵥ y)) j) *
      (A₂ j i * mask ((A₁ *ᵥ y) i) * A₁ i l) * v l := by
    simp only [jac, Matrix.mulVec, dotProduct, Matrix.of_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  have e2 : mask ((A₂ *ᵥ reluV (A₁ *ᵥ y)) j) *
      (A₂ *ᵥ (fun i => mask ((A₁ *ᵥ y) i) * (A₁ *ᵥ v) i)) j =
      ∑ i, ∑ l, mask ((A₂ *ᵥ reluV (A₁ *ᵥ y)) j) *
        (A₂ j i * mask ((A₁ *ᵥ y) i) * A₁ i l) * v l := by
    have e3 : (A₂ *ᵥ (fun i => mask ((A₁ *ᵥ y) i) * (A₁ *ᵥ v) i)) j =
        ∑ i, A₂ j i * (mask ((A₁ *ᵥ y) i) * ∑ l, A₁ i l * v l) := rfl
    rw [e3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [e1, e2, Finset.sum_comm]

/-- `|𝒥(y)v| ≤ ‖A₂‖_op·‖A₁‖_op·|v|`. -/
lemma nrm_jac_mulVec_le (A₁ : Matrix (Fin m₁) (Fin n) ℝ) (A₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (y v : Fin n → ℝ) : nrm (jac A₁ A₂ y *ᵥ v) ≤ opN A₂ * opN A₁ * nrm v := by
  have e : jac A₁ A₂ y *ᵥ v = fun j => mask ((A₂ *ᵥ reluV (A₁ *ᵥ y)) j) *
      (A₂ *ᵥ (fun i => mask ((A₁ *ᵥ y) i) * (A₁ *ᵥ v) i)) j :=
    funext fun j => jac_mulVec_apply A₁ A₂ y v j
  rw [e]
  calc nrm (fun j => mask ((A₂ *ᵥ reluV (A₁ *ᵥ y)) j) *
        (A₂ *ᵥ (fun i => mask ((A₁ *ᵥ y) i) * (A₁ *ᵥ v) i)) j)
      ≤ nrm (A₂ *ᵥ (fun i => mask ((A₁ *ᵥ y) i) * (A₁ *ᵥ v) i)) := nrm_mask_mul_le _ _
    _ ≤ opN A₂ * nrm (fun i => mask ((A₁ *ᵥ y) i) * (A₁ *ᵥ v) i) := nrm_mulVec_le _ _
    _ ≤ opN A₂ * nrm (A₁ *ᵥ v) :=
        mul_le_mul_of_nonneg_left (nrm_mask_mul_le _ _) (opN_nonneg _)
    _ ≤ opN A₂ * (opN A₁ * nrm v) :=
        mul_le_mul_of_nonneg_left (nrm_mulVec_le _ _) (opN_nonneg _)
    _ = opN A₂ * opN A₁ * nrm v := by ring

lemma projT_mulVec_sj (x v : Fin n → ℝ) : projT x *ᵥ v = v - (x ⬝ᵥ v) • x := by
  unfold projT
  rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  congr 1
  funext i
  simp only [Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

lemma normSq_sub_smul (v x : Fin n → ℝ) (s : ℝ) :
    normSq (v - s • x) = normSq v - 2 * s * (v ⬝ᵥ x) + s ^ 2 * normSq x := by
  unfold normSq dotProduct
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma nrm_projT_le {x : Fin n → ℝ} (hx : normSq x = 1) (v : Fin n → ℝ) :
    nrm (projT x *ᵥ v) ≤ nrm v := by
  unfold nrm
  refine Real.sqrt_le_sqrt ?_
  rw [projT_mulVec_sj, normSq_sub_smul, hx, dotProduct_comm v x]
  nlinarith [sq_nonneg (x ⬝ᵥ v)]

/-- **The operator norm of the tangent Jacobian** at a unit vector:
`‖𝒥(x)Π_x‖_op ≤ ‖A₂‖_op·‖A₁‖_op`. -/
theorem opN_jacT_le_sj (A₁ : Matrix (Fin m₁) (Fin n) ℝ) (A₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    {x : Fin n → ℝ} (hx : normSq x = 1) : opN (jacT A₁ A₂ x) ≤ opN A₂ * opN A₁ := by
  refine opN_le_of_bound _ (mul_nonneg (opN_nonneg _) (opN_nonneg _)) fun v => ?_
  unfold jacT
  rw [← Matrix.mulVec_mulVec]
  exact (nrm_jac_mulVec_le A₁ A₂ x _).trans
    (mul_le_mul_of_nonneg_left (nrm_projT_le hx v) (mul_nonneg (opN_nonneg _) (opN_nonneg _)))

/-- The feature map is Lipschitz with the constant `‖A₂‖_op·‖A₁‖_op`. -/
lemma nrm_hid2_sub_le (A₁ : Matrix (Fin m₁) (Fin n) ℝ) (A₂ : Matrix (Fin m₂) (Fin m₁) ℝ)
    (z z' : Fin n → ℝ) :
    nrm (hid2 A₁ A₂ z - hid2 A₁ A₂ z') ≤ opN A₂ * opN A₁ * nrm (z - z') := by
  unfold hid2
  calc nrm (reluV (A₂ *ᵥ reluV (A₁ *ᵥ z)) - reluV (A₂ *ᵥ reluV (A₁ *ᵥ z')))
      ≤ nrm (A₂ *ᵥ reluV (A₁ *ᵥ z) - A₂ *ᵥ reluV (A₁ *ᵥ z')) := nrm_reluV_sub_le _ _
    _ = nrm (A₂ *ᵥ (reluV (A₁ *ᵥ z) - reluV (A₁ *ᵥ z'))) := by rw [Matrix.mulVec_sub]
    _ ≤ opN A₂ * nrm (reluV (A₁ *ᵥ z) - reluV (A₁ *ᵥ z')) := nrm_mulVec_le _ _
    _ ≤ opN A₂ * nrm (A₁ *ᵥ z - A₁ *ᵥ z') :=
        mul_le_mul_of_nonneg_left (nrm_reluV_sub_le _ _) (opN_nonneg _)
    _ = opN A₂ * nrm (A₁ *ᵥ (z - z')) := by rw [Matrix.mulVec_sub]
    _ ≤ opN A₂ * (opN A₁ * nrm (z - z')) :=
        mul_le_mul_of_nonneg_left (nrm_mulVec_le _ _) (opN_nonneg _)
    _ = opN A₂ * opN A₁ * nrm (z - z') := by ring

end op

/-! ## §3 The local Lipschitz constant on the sphere -/

section loc

variable {n m₁ m₂ : ℕ}

/-- Where the Jacobian formula holds, the feature map has the first-order expansion with the
matrix `jac`, in the Euclidean length. -/
lemma jacAt_local {A₁ : Matrix (Fin m₁) (Fin n) ℝ} {A₂ : Matrix (Fin m₂) (Fin m₁) ℝ}
    {y : Fin n → ℝ} (hJ : JacAt A₁ A₂ y) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : Fin n → ℝ, nrm (z - y) < r →
      nrm (hid2 A₁ A₂ z - hid2 A₁ A₂ y - jac A₁ A₂ y *ᵥ (z - y)) ≤ δ * nrm (z - y) := by
  classical
  obtain ⟨cc, hcc⟩ : ∃ cc : ℝ, cc = δ / ((m₂ : ℝ) + 1) := ⟨_, rfl⟩
  have hcc0 : 0 < cc := by rw [hcc]; positivity
  have hcoord : ∀ j : Fin m₂, ∀ᶠ z in 𝓝 y,
      |hid2 A₁ A₂ z j - hid2 A₁ A₂ y j - (jac A₁ A₂ y *ᵥ (z - y)) j| ≤ cc * nrm (z - y) := by
    intro j
    obtain ⟨hd, hpart⟩ := hJ j
    have hf := hd.hasFDerivAt
    have hlin : ∀ v : Fin n → ℝ,
        fderiv ℝ (fun z : Fin n → ℝ => hid2 A₁ A₂ z j) y v = (jac A₁ A₂ y *ᵥ v) j := by
      intro v
      conv_lhs => rw [pi_eq_sum_univ' v]
      rw [map_sum]
      simp only [map_smul, hpart, smul_eq_mul, Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun l _ => mul_comm _ _
    have hb := hf.isLittleO.bound hcc0
    filter_upwards [hb] with z hz
    rw [Real.norm_eq_abs, hlin] at hz
    exact hz.trans (mul_le_mul_of_nonneg_left (norm_le_nrm _) hcc0.le)
  have hall : ∀ᶠ z in 𝓝 y, ∀ j : Fin m₂,
      |hid2 A₁ A₂ z j - hid2 A₁ A₂ y j - (jac A₁ A₂ y *ᵥ (z - y)) j| ≤ cc * nrm (z - y) :=
    eventually_all.mpr hcoord
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨r, hr, fun z hz => ?_⟩
  have hdist : dist z y < r := by
    rw [dist_eq_norm]; exact lt_of_le_of_lt (norm_le_nrm _) hz
  have h := hball hdist
  have hN0 := nrm_nonneg (z - y)
  have hm : (m₂ : ℝ) * (δ / ((m₂ : ℝ) + 1)) ^ 2 ≤ δ ^ 2 := by
    rw [div_pow, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (sq_nonneg δ)
      (by positivity : (0 : ℝ) ≤ (m₂ : ℝ) ^ 2 + (m₂ : ℝ) + 1)]
  have hsq : normSq (hid2 A₁ A₂ z - hid2 A₁ A₂ y - jac A₁ A₂ y *ᵥ (z - y)) ≤
      (δ * nrm (z - y)) ^ 2 := by
    unfold normSq
    calc ∑ j, (hid2 A₁ A₂ z - hid2 A₁ A₂ y - jac A₁ A₂ y *ᵥ (z - y)) j ^ 2
        ≤ ∑ _j : Fin m₂, (cc * nrm (z - y)) ^ 2 := Finset.sum_le_sum fun j _ => by
          have h3 := pow_le_pow_left₀ (abs_nonneg _) (h j) 2
          rw [sq_abs] at h3
          exact h3
      _ = ((m₂ : ℝ) * (δ / ((m₂ : ℝ) + 1)) ^ 2) * nrm (z - y) ^ 2 := by
          rw [hcc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ δ ^ 2 * nrm (z - y) ^ 2 := mul_le_mul_of_nonneg_right hm (sq_nonneg _)
      _ = (δ * nrm (z - y)) ^ 2 := by ring
  have h4 := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq (mul_nonneg hδ.le hN0)] at h4

/-- The local estimate on the unit sphere, at `x` on the ray of a point `y = ρx` where the
Jacobian formula holds. -/
lemma hid2_sph_local_aux {A₁ : Matrix (Fin m₁) (Fin n) ℝ} {A₂ : Matrix (Fin m₂) (Fin m₁) ℝ}
    {x : Fin n → ℝ} {ρ : ℝ} (hρ0 : 0 < ρ) (hx1 : normSq x = 1) (hJ : JacAt A₁ A₂ (ρ • x))
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ ∀ x' : Fin n → ℝ, normSq x' = 1 → nrm (x' - x) < r →
      nrm (hid2 A₁ A₂ x' - hid2 A₁ A₂ x) ≤ (opN (jacT A₁ A₂ x) + δ) * nrm (x' - x) := by
  obtain ⟨r₁, hr₁, hA⟩ := jacAt_local hJ (half_pos hδ)
  rw [jac_smul _ _ hρ0] at hA
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = nrm (jac A₁ A₂ x *ᵥ x) / 2 := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hC]; exact div_nonneg (nrm_nonneg _) (by norm_num)
  refine ⟨min (r₁ / ρ) (δ / (2 * C + 1)), lt_min (div_pos hr₁ hρ0) (by positivity),
    fun x' hx'1 hd => ?_⟩
  have hd0 := nrm_nonneg (x' - x)
  have hd1 : nrm (x' - x) < r₁ / ρ := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : nrm (x' - x) < δ / (2 * C + 1) := lt_of_lt_of_le hd (min_le_right _ _)
  have hCd : C * nrm (x' - x) ≤ δ / 2 := by
    have h5 : nrm (x' - x) * (2 * C + 1) < δ := (lt_div_iff₀ (by positivity)).mp hd2
    nlinarith
  have ez : ρ • x' - ρ • x = ρ • (x' - x) := by rw [smul_sub]
  have hz : nrm (ρ • x' - ρ • x) < r₁ := by
    rw [ez, nrm_smul, abs_of_pos hρ0]
    calc ρ * nrm (x' - x) < ρ * (r₁ / ρ) := mul_lt_mul_of_pos_left hd1 hρ0
      _ = r₁ := by field_simp
  have h1 := hA (ρ • x') hz
  have e1 : hid2 A₁ A₂ (ρ • x') - hid2 A₁ A₂ (ρ • x) - jac A₁ A₂ x *ᵥ (ρ • x' - ρ • x) =
      ρ • (hid2 A₁ A₂ x' - hid2 A₁ A₂ x - jac A₁ A₂ x *ᵥ (x' - x)) := by
    rw [hid2_smul _ _ hρ0.le, hid2_smul _ _ hρ0.le, ez, Matrix.mulVec_smul, smul_sub, smul_sub]
  have h2 : nrm (hid2 A₁ A₂ x' - hid2 A₁ A₂ x - jac A₁ A₂ x *ᵥ (x' - x)) ≤
      δ / 2 * nrm (x' - x) := by
    rw [e1, ez, nrm_smul, nrm_smul, abs_of_pos hρ0] at h1
    have h6 : ρ * nrm (hid2 A₁ A₂ x' - hid2 A₁ A₂ x - jac A₁ A₂ x *ᵥ (x' - x)) ≤
        ρ * (δ / 2 * nrm (x' - x)) := by
      rw [show ρ * (δ / 2 * nrm (x' - x)) = δ / 2 * (ρ * nrm (x' - x)) by ring]
      exact h1
    exact le_of_mul_le_mul_left h6 hρ0
  have hdot : x ⬝ᵥ (x' - x) = -(nrm (x' - x) ^ 2) / 2 := by
    have e2 : nrm (x' - x) ^ 2 = normSq (x' - x) := nrm_sq _
    have e3 : normSq (x' - x) = normSq x' - 2 * 1 * (x' ⬝ᵥ x) + 1 ^ 2 * normSq x := by
      have := normSq_sub_smul x' x 1
      rwa [one_smul] at this
    have e4 : x ⬝ᵥ x = normSq x := by
      unfold normSq dotProduct
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [dotProduct_sub, e4, e2, e3, hx1, hx'1, dotProduct_comm x' x]
    ring
  have hJdec : jac A₁ A₂ x *ᵥ (x' - x) =
      jacT A₁ A₂ x *ᵥ (x' - x) + (x ⬝ᵥ (x' - x)) • (jac A₁ A₂ x *ᵥ x) := by
    unfold jacT
    rw [← Matrix.mulVec_mulVec, projT_mulVec_sj,
      Matrix.mulVec_sub (jac A₁ A₂ x) (x' - x) ((x ⬝ᵥ (x' - x)) • x), Matrix.mulVec_smul,
      sub_add_cancel]
  have habs : |-(nrm (x' - x) ^ 2) / 2| = nrm (x' - x) ^ 2 / 2 := by
    rw [neg_div, abs_neg, abs_of_nonneg (by positivity)]
  have h3 : nrm (jac A₁ A₂ x *ᵥ (x' - x)) ≤
      opN (jacT A₁ A₂ x) * nrm (x' - x) + C * nrm (x' - x) * nrm (x' - x) := by
    rw [hJdec]
    refine (nrm_add_le _ _).trans (add_le_add (nrm_mulVec_le _ _) ?_)
    rw [nrm_smul, hdot, habs, hC]
    exact le_of_eq (by ring)
  have h7 := mul_le_mul_of_nonneg_right hCd hd0
  calc nrm (hid2 A₁ A₂ x' - hid2 A₁ A₂ x)
      ≤ nrm (hid2 A₁ A₂ x' - hid2 A₁ A₂ x - jac A₁ A₂ x *ᵥ (x' - x)) +
        nrm (jac A₁ A₂ x *ᵥ (x' - x)) := nrm_tri3 _ _
    _ ≤ δ / 2 * nrm (x' - x) +
        (opN (jacT A₁ A₂ x) * nrm (x' - x) + C * nrm (x' - x) * nrm (x' - x)) :=
        add_le_add h2 h3
    _ ≤ (opN (jacT A₁ A₂ x) + δ) * nrm (x' - x) := by nlinarith

/-- **The local Lipschitz constant of the feature map on the unit sphere**: at `y ≠ 0` where
the Jacobian formula holds, for unit vectors `x'` near `x = y/|y|`:
`|h(x') − h(x)| ≤ (‖𝒥(x)Π_x‖_op + δ)·|x' − x|`. -/
theorem hid2_sph_local {A₁ : Matrix (Fin m₁) (Fin n) ℝ} {A₂ : Matrix (Fin m₂) (Fin m₁) ℝ}
    {y : Fin n → ℝ} (hy : normSq y ≠ 0) (hJ : JacAt A₁ A₂ y) {δ : ℝ} (hδ : 0 < δ) :
    ∃ r : ℝ, 0 < r ∧ ∀ x' : Fin n → ℝ, normSq x' = 1 → nrm (x' - sphPt y) < r →
      nrm (hid2 A₁ A₂ x' - hid2 A₁ A₂ (sphPt y)) ≤
        (opN (jacT A₁ A₂ (sphPt y)) + δ) * nrm (x' - sphPt y) := by
  have hs0 : 0 < normSq y := lt_of_le_of_ne (normSq_nonneg y) (Ne.symm hy)
  have hρ0 : 0 < √(normSq y) := Real.sqrt_pos.mpr hs0
  have hyx : √(normSq y) • sphPt y = y := by
    rw [sphPt_eq' hy, smul_smul, mul_one_div_cancel hρ0.ne', one_smul]
  have hx1 : normSq (sphPt y) = 1 := by
    rw [sphPt_eq' hy, normSq_smul, one_div, inv_pow, Real.sq_sqrt hs0.le]
    exact inv_mul_cancel₀ hy
  have hJ' : JacAt A₁ A₂ (√(normSq y) • sphPt y) := by rw [hyx]; exact hJ
  exact hid2_sph_local_aux hρ0 hx1 hJ' hδ

/-- The direction `y/|y|`, `y = c + τξ`, is locally Lipschitz in `ξ` with a constant near
`τ/|y|`. -/
lemma sph_local (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (ξ : Fin n → ℝ)
    (hy : normSq (c + τ • ξ) ≠ 0) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ ξ' in 𝓝 ξ, nrm (sphPt (c + τ • ξ') - sphPt (c + τ • ξ)) ≤
      (τ / nrm (c + τ • ξ) + η) * nrm (ξ' - ξ) := by
  have hs0 : 0 < normSq (c + τ • ξ) := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hy)
  have hsq0 : 0 < √(normSq (c + τ • ξ)) := Real.sqrt_pos.mpr hs0
  have hc := cont_ns c τ
  have hne' : ∀ᶠ ξ' in 𝓝 ξ, normSq (c + τ • ξ') ≠ 0 := hc.continuousAt.eventually_ne hy
  have hH : ContinuousAt (fun ξ' : Fin n → ℝ =>
      τ / √(√(normSq (c + τ • ξ')) * √(normSq (c + τ • ξ)))) ξ := by
    refine ContinuousAt.div continuousAt_const ?_ ?_
    · exact (Real.continuous_sqrt.comp
        ((Real.continuous_sqrt.comp hc).mul continuous_const)).continuousAt
    · exact (Real.sqrt_pos.mpr (mul_pos hsq0 hsq0)).ne'
  have hval : τ / √(√(normSq (c + τ • ξ)) * √(normSq (c + τ • ξ))) =
      τ / √(normSq (c + τ • ξ)) := by
    rw [Real.sqrt_mul_self (Real.sqrt_nonneg _)]
  have hlt : ∀ᶠ ξ' in 𝓝 ξ, τ / √(√(normSq (c + τ • ξ')) * √(normSq (c + τ • ξ))) <
      τ / √(normSq (c + τ • ξ)) + η := by
    have h0 : τ / √(√(normSq (c + τ • ξ)) * √(normSq (c + τ • ξ))) <
        τ / √(normSq (c + τ • ξ)) + η := by rw [hval]; linarith
    exact hH.tendsto.eventually (gt_mem_nhds h0)
  filter_upwards [hne', hlt] with ξ' h1 h2
  have hd := sphPt_dist_le (c + τ • ξ') (c + τ • ξ) h1 hy
  rw [affine_sq] at hd
  have e1 : nrm (sphPt (c + τ • ξ') - sphPt (c + τ • ξ)) =
      √(∑ i, (sphPt (c + τ • ξ') i - sphPt (c + τ • ξ) i) ^ 2) := rfl
  have e2 : nrm (ξ' - ξ) = √(∑ i, (ξ' i - ξ i) ^ 2) := rfl
  have e3 : nrm (c + τ • ξ) = √(normSq (c + τ • ξ)) := rfl
  rw [e1, e2, e3]
  calc √(∑ i, (sphPt (c + τ • ξ') i - sphPt (c + τ • ξ) i) ^ 2)
      ≤ √(τ ^ 2 * (∑ i, (ξ' i - ξ i) ^ 2) /
          (√(normSq (c + τ • ξ')) * √(normSq (c + τ • ξ)))) := Real.sqrt_le_sqrt hd
    _ = τ / √(√(normSq (c + τ • ξ')) * √(normSq (c + τ • ξ))) *
          √(∑ i, (ξ' i - ξ i) ^ 2) := by
        rw [Real.sqrt_div' _ (by positivity), Real.sqrt_mul (sq_nonneg _),
          Real.sqrt_sq hτ.le]
        ring
    _ ≤ (τ / √(normSq (c + τ • ξ)) + η) * √(∑ i, (ξ' i - ξ i) ^ 2) :=
        mul_le_mul_of_nonneg_right h2.le (Real.sqrt_nonneg _)

end loc

/-! ## §4 Lemma S, second assertion -/

section S

variable {n m : ℕ}

/-- `Φ(z) = φ(√t·h(z))` is Lipschitz with the constant `L_φ·√t·‖A₂‖_op·‖A₁‖_op`. -/
lemma phiq_eulip (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    {φ : (Fin m → ℝ) → ℝ} {Lφ : ℝ} (hL : 0 ≤ Lφ) (hφ : EuLip φ Lφ) (s : ℝ) (hs : 0 ≤ s) :
    EuLip (fun z : Fin n → ℝ => φ (s • hid2 A₁ A₂ z)) (Lφ * s * (opN A₂ * opN A₁)) := by
  intro z z'
  refine (hφ _ _).trans ?_
  have e1 : √(∑ i, ((s • hid2 A₁ A₂ z) i - (s • hid2 A₁ A₂ z') i) ^ 2) =
      nrm (s • hid2 A₁ A₂ z - s • hid2 A₁ A₂ z') := rfl
  have e2 : √(∑ i, (z i - z' i) ^ 2) = nrm (z - z') := rfl
  rw [e1, e2, ← smul_sub, nrm_smul, abs_of_nonneg hs]
  calc Lφ * (s * nrm (hid2 A₁ A₂ z - hid2 A₁ A₂ z'))
      ≤ Lφ * (s * (opN A₂ * opN A₁ * nrm (z - z'))) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (nrm_hid2_sub_le A₁ A₂ z z') hs) hL
    _ = Lφ * s * (opN A₂ * opN A₁) * nrm (z - z') := by ring

/-- **The gradient bound of Lemma S, second assertion**: at a point `ξ` with `y ≠ 0` where the
Jacobian formula holds at `y`: `|∇_ξ φ(q(x))|² ≤ L_φ²·t·τ²·‖𝒥(x)Π_x‖_op²/|y|²`. -/
theorem gradSq_jac_le (hn : 1 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {φ : (Fin m → ℝ) → ℝ} {Lφ : ℝ} (hL : 0 ≤ Lφ) (hφ : EuLip φ Lφ) (ξ : Fin n → ℝ)
    (hy : normSq (c + τ • ξ) ≠ 0) (hJ : JacAt A₁ A₂ (c + τ • ξ)) :
    ∑ i, (fderiv ℝ (fun ξ : Fin n → ℝ =>
        φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ)))) ξ (Pi.single i 1)) ^ 2 ≤
      Lφ ^ 2 * (2 / (m : ℝ) * τ ^ 2 * (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
        (normSq (c + τ • ξ))⁻¹)) := by
  have hs0 : 0 < normSq (c + τ • ξ) := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hy)
  have hρ0 : 0 < nrm (c + τ • ξ) := Real.sqrt_pos.mpr hs0
  have ht0 : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  have hst0 : 0 ≤ √(2 / (m : ℝ)) := Real.sqrt_nonneg _
  have hP0 : 0 ≤ Lφ * √(2 / (m : ℝ)) := mul_nonneg hL hst0
  have ha0 : 0 ≤ opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) := opN_nonneg _
  have hb0 : 0 ≤ τ / nrm (c + τ • ξ) := div_nonneg hτ.le hρ0.le
  have hℓ : Lφ ^ 2 * (2 / (m : ℝ) * τ ^ 2 * (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
        (normSq (c + τ • ξ))⁻¹)) =
      (Lφ * √(2 / (m : ℝ)) * opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) *
        (τ / nrm (c + τ • ξ))) ^ 2 := by
    rw [mul_pow, mul_pow, mul_pow, div_pow, Real.sq_sqrt ht0, nrm_sq]
    ring
  rw [hℓ]
  refine gradSq_le_of_local fun δ hδ => ?_
  obtain ⟨δ', hδ', hprod⟩ := prod_eps hP0 ha0 hb0 hδ
  obtain ⟨r, hr, hloc⟩ := hid2_sph_local hy hJ hδ'
  have hκ0 : 0 < τ / nrm (c + τ • ξ) + δ' := by positivity
  have hcN : Continuous (fun ξ' : Fin n → ℝ => √(∑ i, (ξ' i - ξ i) ^ 2)) := by fun_prop
  have hN0 : √(∑ i, (ξ i - ξ i) ^ 2) < r / (τ / nrm (c + τ • ξ) + δ') := by
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, Real.sqrt_zero]
    positivity
  have hsmall : ∀ᶠ ξ' in 𝓝 ξ,
      √(∑ i, (ξ' i - ξ i) ^ 2) < r / (τ / nrm (c + τ • ξ) + δ') :=
    hcN.continuousAt.tendsto.eventually (gt_mem_nhds hN0)
  filter_upwards [sph_local c hτ ξ hy hδ', hsmall] with ξ' h1 h2
  have eN : √(∑ i, (ξ' i - ξ i) ^ 2) = nrm (ξ' - ξ) := rfl
  rw [eN] at h2 ⊢
  have hN := nrm_nonneg (ξ' - ξ)
  have hdr : nrm (sphPt (c + τ • ξ') - sphPt (c + τ • ξ)) < r := by
    refine lt_of_le_of_lt h1 ?_
    have := mul_lt_mul_of_pos_left h2 hκ0
    rwa [mul_div_cancel₀ _ hκ0.ne'] at this
  have h3 := hloc (sphPt (c + τ • ξ')) (normSq_sphPt hn _) hdr
  refine (hφ _ _).trans ?_
  have e1 : √(∑ i, ((√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ'))) i -
      (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) i) ^ 2) =
      nrm (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ')) -
        √(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) := rfl
  rw [e1, ← smul_sub, nrm_smul, abs_of_nonneg hst0]
  have h4 : nrm (hid2 A₁ A₂ (sphPt (c + τ • ξ')) - hid2 A₁ A₂ (sphPt (c + τ • ξ))) ≤
      (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) + δ') *
        ((τ / nrm (c + τ • ξ) + δ') * nrm (ξ' - ξ)) :=
    h3.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
  calc Lφ * (√(2 / (m : ℝ)) *
        nrm (hid2 A₁ A₂ (sphPt (c + τ • ξ')) - hid2 A₁ A₂ (sphPt (c + τ • ξ))))
      ≤ Lφ * (√(2 / (m : ℝ)) * ((opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) + δ') *
        ((τ / nrm (c + τ • ξ) + δ') * nrm (ξ' - ξ)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hst0) hL
    _ = Lφ * √(2 / (m : ℝ)) * (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) + δ') *
        (τ / nrm (c + τ • ξ) + δ') * nrm (ξ' - ξ) := by ring
    _ ≤ (Lφ * √(2 / (m : ℝ)) * opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) *
        (τ / nrm (c + τ • ξ)) + δ) * nrm (ξ' - ξ) :=
        mul_le_mul_of_nonneg_right hprod hN

/-! ### Measurability and integrability -/

lemma measurable_jac (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ) :
    Measurable (fun y : Fin n → ℝ => jac A₁ A₂ y) := by
  refine measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun l => ?_
  have h1 : ∀ i : Fin m, Measurable (fun y : Fin n → ℝ => (A₁ *ᵥ y) i) := fun i =>
    ((continuous_apply i).comp
      (Continuous.matrix_mulVec continuous_const continuous_id)).measurable
  have h2 : Measurable (fun y : Fin n → ℝ => (A₂ *ᵥ reluV (A₁ *ᵥ y)) j) :=
    ((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
      (continuous_reluV.comp
        (Continuous.matrix_mulVec continuous_const continuous_id)))).measurable
  show Measurable (fun y : Fin n → ℝ => mask ((A₂ *ᵥ reluV (A₁ *ᵥ y)) j) *
    ∑ i, A₂ j i * mask ((A₁ *ᵥ y) i) * A₁ i l)
  exact (measurable_mask.comp h2).mul (Finset.measurable_sum _ fun i _ =>
    (measurable_const.mul (measurable_mask.comp (h1 i))).mul measurable_const)

lemma measurable_jacT (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ) :
    Measurable (fun x : Fin n → ℝ => jacT A₁ A₂ x) := by
  refine measurable_pi_iff.mpr fun j => measurable_pi_iff.mpr fun l => ?_
  show Measurable (fun x : Fin n → ℝ => ∑ k, jac A₁ A₂ x j k * projT x k l)
  refine Finset.measurable_sum _ fun k _ => ?_
  have h1 : Measurable (fun x : Fin n → ℝ => jac A₁ A₂ x j k) :=
    (measurable_pi_apply k).comp ((measurable_pi_apply j).comp (measurable_jac A₁ A₂))
  have h2 : Measurable (fun x : Fin n → ℝ => projT x k l) := by
    show Measurable (fun x : Fin n → ℝ => (1 : Matrix (Fin n) (Fin n) ℝ) k l - x k * x l)
    exact measurable_const.sub ((measurable_pi_apply k).mul (measurable_pi_apply l))
  exact h1.mul h2

lemma measurable_opN_jacT_sj (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun ξ : Fin n → ℝ => opN (jacT A₁ A₂ (sphPt (c + τ • ξ)))) :=
  opN_continuous.measurable.comp ((measurable_jacT A₁ A₂).comp
    (measurable_sphPt.comp (measurable_const.add (measurable_const_smul τ))))

/-- The integrand of `Ξ` is integrable (`n ≥ 4`). -/
theorem integrable_XiS (hn : 4 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun ξ : Fin n → ℝ => opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
      (normSq (c + τ • ξ))⁻¹) (stdGauss (Fin n)) := by
  have hi := (invMoment_one_le hn c hτ).1
  refine Integrable.mono' (hi.const_mul ((opN A₂ * opN A₁) ^ 2))
    (((measurable_opN_jacT_sj A₁ A₂ c τ).pow_const 2).mul
      (cont_ns c τ).measurable.inv).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
  have h0 : 0 ≤ (normSq (c + τ • ξ))⁻¹ := inv_nonneg.mpr (normSq_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) h0)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (opN_nonneg _)
    (opN_jacT_le_sj A₁ A₂ (normSq_sphPt (by omega) _)) 2) h0

/-- The integrand of `Ξ₄` is integrable (`n ≥ 6`). -/
theorem integrable_Xi4 (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun ξ : Fin n → ℝ => opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 4 *
      (normSq (c + τ • ξ))⁻¹ ^ 2) (stdGauss (Fin n)) := by
  have hi := (invMoment_two_le hn c hτ).1
  refine Integrable.mono' (hi.const_mul ((opN A₂ * opN A₁) ^ 4))
    (((measurable_opN_jacT_sj A₁ A₂ c τ).pow_const 4).mul
      ((cont_ns c τ).measurable.inv.pow_const 2)).aestronglyMeasurable (ae_of_all _ fun ξ => ?_)
  have h0 : 0 ≤ (normSq (c + τ • ξ))⁻¹ ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) h0)]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (opN_nonneg _)
    (opN_jacT_le_sj A₁ A₂ (normSq_sphPt (by omega) _)) 4) h0

/-- **Lemma S, second assertion, with the integrability of the variance integrand.** -/
theorem lemmaS_jac_full (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {φ : (Fin m → ℝ) → ℝ} {Lφ : ℝ} (hL : 0 ≤ Lφ) (hφ : EuLip φ Lφ) :
    Integrable (fun ξ : Fin n → ℝ => (φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) -
      ∫ ξ', φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ'))) ∂stdGauss (Fin n)) ^ 2)
      (stdGauss (Fin n)) ∧
    ∫ ξ, (φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) -
      ∫ ξ', φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ'))) ∂stdGauss (Fin n)) ^ 2
        ∂stdGauss (Fin n) ≤ Lφ ^ 2 * XiS A₁ A₂ c τ := by
  have hst0 : 0 ≤ √(2 / (m : ℝ)) := Real.sqrt_nonneg _
  have hK0 : 0 ≤ Lφ * √(2 / (m : ℝ)) * (opN A₂ * opN A₁) :=
    mul_nonneg (mul_nonneg hL hst0) (mul_nonneg (opN_nonneg _) (opN_nonneg _))
  have hne := ae_normSq_ne (n := n) (by omega) c hτ.ne'
  have hF := integrable_XiS (by omega : 4 ≤ n) A₁ A₂ c hτ
  have hgrad : ∀ᵐ ξ ∂stdGauss (Fin n),
      ∑ i, (fderiv ℝ (fun ξ : Fin n → ℝ =>
        (fun z : Fin n → ℝ => φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ z)) (sphPt (c + τ • ξ))) ξ
          (Pi.single i 1)) ^ 2 ≤
      Lφ ^ 2 * (2 / (m : ℝ) * τ ^ 2 * (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
        (normSq (c + τ • ξ))⁻¹)) := by
    filter_upwards [hne, lemmaJ_shift A₁ A₂ c hτ.ne'] with ξ h1 h2
    exact gradSq_jac_le (by omega) A₁ A₂ c hτ hL hφ ξ h1 h2
  obtain ⟨hi, hv⟩ := lemmaS_grad c hτ hK0 (phiq_eulip A₁ A₂ hL hφ _ hst0)
    (Γ := fun ξ => Lφ ^ 2 * (2 / (m : ℝ) * τ ^ 2 *
      (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹)))
    ((hF.const_mul _).const_mul _) hgrad (invMoment_two_le hn c hτ).1 hne
  refine ⟨hi, hv.trans (le_of_eq ?_)⟩
  rw [integral_const_mul, integral_const_mul]
  rfl

/-- **Lemma S, second assertion** (for a globally Lipschitz `φ`): for every pair of matrices
`A₁`, `A₂`, every `c`, `τ > 0`, `n ≥ 6`: `Var_ξ φ(q(x)) ≤ L_φ²·Ξ`, `q(x) = √t·h₂(x)`,
`x = y/|y|`, `y = c + τξ`. -/
theorem lemmaS_jac (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {φ : (Fin m → ℝ) → ℝ} {Lφ : ℝ} (hL : 0 ≤ Lφ) (hφ : EuLip φ Lφ) :
    Integrable (fun ξ : Fin n → ℝ => opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
      (normSq (c + τ • ξ))⁻¹) (stdGauss (Fin n)) ∧
    ∫ ξ, (φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) -
      ∫ ξ', φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ'))) ∂stdGauss (Fin n)) ^ 2
        ∂stdGauss (Fin n) ≤ Lφ ^ 2 * XiS A₁ A₂ c τ :=
  ⟨integrable_XiS (by omega) A₁ A₂ c hτ, (lemmaS_jac_full hn A₁ A₂ c hτ hL hφ).2⟩

/-! ## §5 `Ξ ≤ Ξ₄` and the bounds from the global Lipschitz constant -/

/-- **`Ξ ≤ Ξ₄`** (the Cauchy–Schwarz inequality on a probability space). -/
theorem XiS_le_Xi4 (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    XiS A₁ A₂ c τ ≤ Xi4 A₁ A₂ c τ := by
  have hF := integrable_XiS (by omega : 4 ≤ n) A₁ A₂ c hτ
  have hG := integrable_Xi4 hn A₁ A₂ c hτ
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = ∫ ξ, opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
    (normSq (c + τ • ξ))⁻¹ ∂stdGauss (Fin n) := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by
    rw [ha]
    exact integral_nonneg fun ξ =>
      mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (normSq_nonneg _))
  have h0 : 0 ≤ ∫ ξ, (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
      (normSq (c + τ • ξ))⁻¹ - a) ^ 2 ∂stdGauss (Fin n) :=
    integral_nonneg fun ξ => sq_nonneg _
  have e : (fun ξ : Fin n → ℝ => (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
      (normSq (c + τ • ξ))⁻¹ - a) ^ 2) = fun ξ =>
      opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 4 * (normSq (c + τ • ξ))⁻¹ ^ 2 -
        2 * a * (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹) +
        a ^ 2 := funext fun ξ => by ring
  have hGF : Integrable (fun ξ : Fin n → ℝ =>
      opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 4 * (normSq (c + τ • ξ))⁻¹ ^ 2 -
        2 * a * (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹))
      (stdGauss (Fin n)) := hG.sub (hF.const_mul _)
  rw [e, integral_add hGF (integrable_const _),
    integral_sub hG (hF.const_mul _), integral_const_mul, integral_const, ← ha] at h0
  rw [show (stdGauss (Fin n)).real Set.univ = 1 from by simp, one_smul] at h0
  have h1 : a ^ 2 ≤ ∫ ξ, opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 4 *
      (normSq (c + τ • ξ))⁻¹ ^ 2 ∂stdGauss (Fin n) := by nlinarith
  have h2 := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq ha0] at h2
  unfold XiS Xi4
  rw [← ha]
  exact mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **`Ξ ≤ t·‖A₂‖_op²·‖A₁‖_op²/(n − 3)`** (`n ≥ 4`). -/
theorem XiS_le_op (hn : 4 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    XiS A₁ A₂ c τ ≤ 2 / (m : ℝ) * opN A₂ ^ 2 * opN A₁ ^ 2 / ((n : ℝ) - 3) := by
  obtain ⟨hi, hb⟩ := invMoment_one_le hn c hτ
  have hF := integrable_XiS hn A₁ A₂ c hτ
  have h1 : ∫ ξ, opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 * (normSq (c + τ • ξ))⁻¹
      ∂stdGauss (Fin n) ≤ ∫ ξ, (opN A₂ * opN A₁) ^ 2 * (normSq (c + τ • ξ))⁻¹
      ∂stdGauss (Fin n) :=
    integral_mono hF (hi.const_mul _) fun ξ =>
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (opN_nonneg _)
        (opN_jacT_le_sj A₁ A₂ (normSq_sphPt (by omega) _)) 2)
        (inv_nonneg.mpr (normSq_nonneg _))
  rw [integral_const_mul] at h1
  have ht0 : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  have hC0 : 0 ≤ 2 / (m : ℝ) * (opN A₂ * opN A₁) ^ 2 := mul_nonneg ht0 (sq_nonneg _)
  unfold XiS
  calc 2 / (m : ℝ) * τ ^ 2 * ∫ ξ, opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 *
        (normSq (c + τ • ξ))⁻¹ ∂stdGauss (Fin n)
      ≤ 2 / (m : ℝ) * τ ^ 2 * ((opN A₂ * opN A₁) ^ 2 *
        ∫ ξ, (normSq (c + τ • ξ))⁻¹ ∂stdGauss (Fin n)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg ht0 (sq_nonneg _))
    _ = 2 / (m : ℝ) * (opN A₂ * opN A₁) ^ 2 *
        (τ ^ 2 * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ∂stdGauss (Fin n)) := by ring
    _ ≤ 2 / (m : ℝ) * (opN A₂ * opN A₁) ^ 2 * (1 / ((n : ℝ) - 3)) :=
        mul_le_mul_of_nonneg_left hb hC0
    _ = 2 / (m : ℝ) * opN A₂ ^ 2 * opN A₁ ^ 2 / ((n : ℝ) - 3) := by ring

/-- **The weak covariance bound with an explicit constant** (from the global Lipschitz constant
alone): `Var_ξ φ(q(x)) ≤ L_φ²·t·‖A₂‖_op²·‖A₁‖_op²/(n − 3)`, for every `A₁`, `A₂`, `n ≥ 6`. -/
theorem weak_var_le (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {φ : (Fin m → ℝ) → ℝ} {Lφ : ℝ} (hL : 0 ≤ Lφ) (hφ : EuLip φ Lφ) :
    ∫ ξ, (φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ))) -
      ∫ ξ', φ (√(2 / (m : ℝ)) • hid2 A₁ A₂ (sphPt (c + τ • ξ'))) ∂stdGauss (Fin n)) ^ 2
        ∂stdGauss (Fin n) ≤
      Lφ ^ 2 * (2 / (m : ℝ)) * opN A₂ ^ 2 * opN A₁ ^ 2 / ((n : ℝ) - 3) := by
  have hst0 : 0 ≤ √(2 / (m : ℝ)) := Real.sqrt_nonneg _
  have ht0 : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  have hK0 : 0 ≤ Lφ * √(2 / (m : ℝ)) * (opN A₂ * opN A₁) :=
    mul_nonneg (mul_nonneg hL hst0) (mul_nonneg (opN_nonneg _) (opN_nonneg _))
  obtain ⟨hi, hb⟩ := invMoment_one_le (by omega : 4 ≤ n) c hτ
  have h := lemmaS_weak c hτ hK0 (phiq_eulip A₁ A₂ hL hφ _ hst0)
    (invMoment_two_le hn c hτ).1 hi (ae_normSq_ne (n := n) (by omega) c hτ.ne')
  refine h.trans ?_
  calc τ ^ 2 * (Lφ * √(2 / (m : ℝ)) * (opN A₂ * opN A₁)) ^ 2 *
        ∫ ξ, (normSq (c + τ • ξ))⁻¹ ∂stdGauss (Fin n)
      = (Lφ * √(2 / (m : ℝ)) * (opN A₂ * opN A₁)) ^ 2 *
        (τ ^ 2 * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ∂stdGauss (Fin n)) := by ring
    _ ≤ (Lφ * √(2 / (m : ℝ)) * (opN A₂ * opN A₁)) ^ 2 * (1 / ((n : ℝ) - 3)) :=
        mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = Lφ ^ 2 * (2 / (m : ℝ)) * opN A₂ ^ 2 * opN A₁ ^ 2 / ((n : ℝ) - 3) := by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt ht0]
        ring

/-! ## §6 The covariance operator -/

/-- **The residual covariance, `‖t·Cov_x(h₂)‖_op ≤ Ξ`**: for every vector `w`,
`t·Var_ξ ⟨w, h₂(x)⟩ ≤ Ξ·|w|²`. -/
theorem cov_hid2_le (hn : 6 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (w : Fin m → ℝ) :
    2 / (m : ℝ) * ∫ ξ, (w ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ)) -
      ∫ ξ', w ⬝ᵥ hid2 A₁ A₂ (sphPt (c + τ • ξ')) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) ≤
      XiS A₁ A₂ c τ * normSq w := by
  have ht0 : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  have hφ : EuLip (fun v : Fin m → ℝ => w ⬝ᵥ v) (nrm w) := by
    intro a b
    have e : w ⬝ᵥ a - w ⬝ᵥ b = w ⬝ᵥ (a - b) := by rw [dotProduct_sub]
    rw [e]
    exact abs_dot_le_nrm w (a - b)
  have h := (lemmaS_jac hn A₁ A₂ c hτ (nrm_nonneg w) hφ).2
  have e : ∀ a b : ℝ, (√(2 / (m : ℝ)) * a - √(2 / (m : ℝ)) * b) ^ 2 =
      2 / (m : ℝ) * (a - b) ^ 2 := by
    intro a b
    rw [← mul_sub, mul_pow, Real.sq_sqrt ht0]
  simp only [dotProduct_smul, smul_eq_mul, integral_const_mul, e] at h
  rw [nrm_sq] at h
  rw [mul_comm (XiS A₁ A₂ c τ)]
  exact h

end S

end BstLean.Part153

open BstLean.Part153 in
#print axioms opN_jacT_le_sj
open BstLean.Part153 in
#print axioms hid2_sph_local
open BstLean.Part153 in
#print axioms gradSq_jac_le
open BstLean.Part153 in
#print axioms lemmaS_jac_full
open BstLean.Part153 in
#print axioms lemmaS_jac
open BstLean.Part153 in
#print axioms XiS_le_Xi4
open BstLean.Part153 in
#print axioms XiS_le_op
open BstLean.Part153 in
#print axioms weak_var_le
open BstLean.Part153 in
#print axioms cov_hid2_le
