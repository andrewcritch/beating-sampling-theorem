import BstLean.Part171All

/-!
# Part 172 (file `Adm`): admissibility of the first-layer directions

No proof is left open; no `native_decide` or `axiom` is used.

* `fr_rot_inv`: the law of `⟨p, V⟩` (`V` uniform on the sphere) depends only on `|p|`.
* **`a1Bar_adm`**: `ā_i(s)` depends on `A₁` only through `a_i·û` and `|a_i|²`.
* `fr_Adm x u e`: `e(A)` depends on `A` only through `Ax`, `Au` and the row lengths.
* **`e1v_adm`**, **`e2v_adm`**, **`cdir_adm`**: the directions `e₁`, `e₂` and
  `ĉ' = Π_{U⊥}a(x)/|Π_{U⊥}a(x)|` are admissible; `|e₁|², |e₂|² ≤ t_A`, `|ĉ'|² ≤ 1`.
-/

namespace BstLean.Part172

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157
open BstLean.Part161 (uHat xLat hhMat consV)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part169 (A1)

variable {k : ℕ}

lemma fr_normSq_orth {Q : Matrix (Fin k) (Fin k) ℝ} (hQ : Qᵀ * Q = 1) (v : Fin k → ℝ) :
    ∑ i, (Q *ᵥ v) i ^ 2 = ∑ i, v i ^ 2 := by
  have h : ∑ i, (Q *ᵥ v) i ^ 2 = v ⬝ᵥ ((Qᵀ * Q) *ᵥ v) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
    simp only [dotProduct, sq]
  rw [h, hQ, Matrix.one_mulVec]; simp only [dotProduct, sq]

lemma fr_unitF_orth {Q : Matrix (Fin k) (Fin k) ℝ} (hQ : Qᵀ * Q = 1) (v : Fin k → ℝ) :
    unitF53 (Q *ᵥ v) = Q *ᵥ unitF53 v := by
  unfold unitF53
  rw [fr_normSq_orth hQ, Matrix.mulVec_smul]

lemma fr_hh_invol (u : Fin k → ℝ) : hhMat u * hhMat u = 1 := by
  have h := BstLean.Part161.hh_mul_transpose u
  have ht : (hhMat u).transpose = hhMat u := by
    ext i j; exact BstLean.Part161.hh_symm u j i
  rwa [ht] at h

/-- An orthogonal matrix that maps `p` to `p'` when `|p| = |p'|`. -/
lemma fr_orthV (hk : 1 ≤ k) (p p' : Fin k → ℝ) (h : normSq p = normSq p') :
    ∃ V : Matrix (Fin k) (Fin k) ℝ, V * Vᵀ = 1 ∧ V *ᵥ p = p' := by
  by_cases hp : normSq p = 0
  · have h0 : p = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (p j))).mp hp i
        (Finset.mem_univ _)
      simpa using this
    have h0' : p' = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (p' j))).mp
        (show normSq p' = 0 by rw [← h]; exact hp) i
        (Finset.mem_univ _)
      simpa using this
    exact ⟨1, by simp, by rw [h0, h0']; simp⟩
  · have hp0 : 0 < normSq p := lt_of_le_of_ne (Finset.sum_nonneg fun j _ => sq_nonneg _) (Ne.symm hp)
    set r := √(normSq p) with hr
    have hr0 : 0 < r := Real.sqrt_pos.mpr hp0
    set u := r⁻¹ • p
    set u' := r⁻¹ • p'
    have hu : normSq u = 1 := by
      unfold normSq; simp only [u, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      have : r ^ 2 = normSq p := Real.sq_sqrt hp0.le
      rw [inv_pow, this]; exact inv_mul_cancel₀ hp
    have hu' : normSq u' = 1 := by
      unfold normSq; simp only [u', Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      have : r ^ 2 = normSq p := Real.sq_sqrt hp0.le
      have e : ∑ i, p' i ^ 2 = normSq p' := rfl
      rw [inv_pow, this, e, ← h]; exact inv_mul_cancel₀ hp
    refine ⟨hhMat u' * hhMat u, ?_, ?_⟩
    · rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (hhMat u),
        BstLean.Part161.hh_mul_transpose, Matrix.one_mul, BstLean.Part161.hh_mul_transpose]
    · have hpu : p = r • u := by simp only [u, smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
      have hpu' : p' = r • u' := by simp only [u', smul_smul, mul_inv_cancel₀ hr0.ne', one_smul]
      have he : hhMat u *ᵥ u = e0 k := by
        have h1 := BstLean.Part161.hh_e0 hk hu
        have h2 := congrArg (fun z => hhMat u *ᵥ z) h1
        simp only [Matrix.mulVec_mulVec, fr_hh_invol, Matrix.one_mulVec] at h2
        exact h2.symm
      rw [hpu, hpu', Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, he, BstLean.Part161.hh_e0 hk hu']

/-- **Rotation invariance of a sphere coordinate**: the law of `⟨p, V⟩` (`V` uniform on the
sphere) depends only on `|p|`. -/
theorem fr_rot_inv (hk : 1 ≤ k) {p p' : Fin k → ℝ} (h : normSq p = normSq p') {φ : ℝ → ℝ}
    (hφ : Measurable φ) :
    ∫ v, φ (∑ i, p i * unitF53 v i) ∂stdGauss (Fin k) =
      ∫ v, φ (∑ i, p' i * unitF53 v i) ∂stdGauss (Fin k) := by
  obtain ⟨V, hV, hVp⟩ := fr_orthV hk p p' h
  have hVt : Vᵀ * V = 1 := mul_eq_one_comm.mp hV
  have hVtt : Vᵀ * Vᵀᵀ = 1 := by rw [Matrix.transpose_transpose]; exact hVt
  have key : ∀ v, ∑ i, p' i * unitF53 v i = ∑ i, p i * unitF53 (Vᵀ *ᵥ v) i := by
    intro v
    have hVtV : Vᵀᵀ * Vᵀ = 1 := by rw [Matrix.transpose_transpose]; exact hV
    rw [fr_unitF_orth hVtV, ← hVp]
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp_rw [key]
  have hm : Measurable (fun v : Fin k → ℝ => φ (∑ i, p i * unitF53 v i)) :=
    hφ.comp (Finset.measurable_sum _ fun i _ =>
      measurable_const.mul ((measurable_pi_apply i).comp BstLean.Part53.measurable_unitF))
  have hmV : Measurable (fun v : Fin k → ℝ => Vᵀ *ᵥ v) := by fun_prop
  have hmap := BstLean.Part109.stdGauss_map_orth Vᵀ hVtt
  have := integral_map (μ := stdGauss (Fin k)) hmV.aemeasurable hm.aestronglyMeasurable
  rw [hmap] at this
  exact this


variable {n : ℕ}

/-- `a·H(s, t y) = (a·u)s + t⟨tail(Ha), y⟩`. -/
lemma fr_row_lat (hn : 1 ≤ n) {u : Fin n → ℝ} (hu : normSq u = 1) (a : Fin n → ℝ) (s t : ℝ)
    (y : Fin (n - 1) → ℝ) :
    ∑ j, a j * (hhMat u *ᵥ consV s (t • y)) j =
      (∑ j, a j * u j) * s + t * ∑ k : Fin (n - 1), (hhMat u *ᵥ a) ⟨k + 1, by omega⟩ * y k := by
  rw [← BstLean.Part167.hh_dot_comm, BstLean.Part169.sum_mul_consV hn]
  have h0 : (hhMat u *ᵥ a) ⟨0, by omega⟩ = ∑ j, a j * u j := by
    rw [← BstLean.Part167.dot_e0 hn (hhMat u *ᵥ a), BstLean.Part167.hh_dot_comm, BstLean.Part161.hh_e0 hn hu]
  rw [h0, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring

lemma fr_tail_normSq (hn : 1 ≤ n) {u : Fin n → ℝ} (hu : normSq u = 1) (a : Fin n → ℝ) :
    normSq (fun k : Fin (n - 1) => (hhMat u *ᵥ a) ⟨k + 1, by omega⟩) =
      ∑ j, a j ^ 2 - (∑ j, a j * u j) ^ 2 := by
  have h0 : (hhMat u *ᵥ a) ⟨0, by omega⟩ = ∑ j, a j * u j := by
    rw [← BstLean.Part167.dot_e0 hn (hhMat u *ᵥ a), BstLean.Part167.hh_dot_comm, BstLean.Part161.hh_e0 hn hu]
  have hN := BstLean.Part161.hh_normSq u a
  have hs : normSq (hhMat u *ᵥ a) = (hhMat u *ᵥ a) ⟨0, by omega⟩ ^ 2 +
      normSq (fun k : Fin (n - 1) => (hhMat u *ᵥ a) ⟨k + 1, by omega⟩) := by
    have := BstLean.Part169.sum_mul_consV hn (fun i => (hhMat u *ᵥ a) i) 0 0
    unfold normSq
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [Fin.sum_univ_succ]
    rfl
  rw [hs, h0] at hN
  unfold normSq at hN ⊢
  linarith

/-- **`ā = a1Bar` is admissible**: `ā_i(s)` depends on `A₁` only through `a_i·û` and `|a_i|²`. -/
theorem a1Bar_adm (hn : 2 ≤ n) {c c' : Ret n} (h1 : c.1 = c'.1) (hc : c.1.2 ≠ 0) (s : ℝ)
    (i : Fin (mA n)) (hu : (A1 c *ᵥ uHat c) i = (A1 c' *ᵥ uHat c) i)
    (hr : ∑ j, A1 c i j ^ 2 = ∑ j, A1 c' i j ^ 2) :
    BstLean.Part169.a1Bar c s i = BstLean.Part169.a1Bar c' s i := by
  have hn1 : 1 ≤ n := by omega
  have huc : uHat c' = uHat c := by unfold uHat; rw [h1]
  have hx : ∀ y, xLat c' s y = xLat c s y := fun y => by unfold xLat; rw [huc]
  have hU := BstLean.Part161.normSq_uHat hc
  unfold BstLean.Part169.a1Bar
  simp_rw [hx]
  set t := √(1 - s ^ 2)
  have key : ∀ (A : Matrix (Fin (mA n)) (Fin n) ℝ) (v : Fin (n - 1) → ℝ),
      (A *ᵥ xLat c s (unitF53 v)) i = (A *ᵥ uHat c) i * s +
        t * ∑ k : Fin (n - 1), (hhMat (uHat c) *ᵥ (fun j => A i j)) ⟨k + 1, by omega⟩ *
          unitF53 v k := by
    intro A v
    unfold xLat
    rw [show (A *ᵥ (hhMat (uHat c) *ᵥ consV s (t • unitF53 v))) i =
      ∑ j, A i j * (hhMat (uHat c) *ᵥ consV s (t • unitF53 v)) j from rfl,
      fr_row_lat hn1 hU (fun j => A i j)]
    rfl
  simp_rw [key]
  have hm : Measurable (fun y : ℝ => relu ((A1 c' *ᵥ uHat c) i * s + t * y)) :=
    BstLean.Part130.measurable_relu.comp (by fun_prop)
  rw [hu]
  have hp : normSq (fun k : Fin (n - 1) => (hhMat (uHat c) *ᵥ (fun j => A1 c i j)) ⟨k + 1, by omega⟩) =
      normSq (fun k : Fin (n - 1) => (hhMat (uHat c) *ᵥ (fun j => A1 c' i j)) ⟨k + 1, by omega⟩) := by
    rw [fr_tail_normSq hn1 hU, fr_tail_normSq hn1 hU]
    have e1 : ∑ j, A1 c i j * uHat c j = (A1 c *ᵥ uHat c) i := rfl
    have e2 : ∑ j, A1 c' i j * uHat c j = (A1 c' *ᵥ uHat c) i := rfl
    rw [e1, e2, hu, hr]
  exact fr_rot_inv (by omega) hp hm


open BstLean.Part169 (a1Bar nodeS)
open BstLean.Part170 (mkR hB tA)
open BstLean.Part171 (e1v e2v)
open BstLean.Part167 (perp)
open BstLean.Part134 (res)

lemma fr_c_eq (c : Ret n) : c.1.2 = √(normSq c.1.2) • uHat c := by
  unfold uHat
  by_cases h : √(normSq c.1.2) = 0
  · have h0 : normSq c.1.2 = 0 := by
      have := Real.sqrt_eq_zero'.mp h
      linarith [BstLean.Part130.normSq_nonneg c.1.2]
    have := BstLean.Part130.normSq_eq_zero h0
    rw [this]; simp
  · rw [smul_smul, mul_inv_cancel₀ h, one_smul]

/-- The hypothesis "admissible in the frame at `x`". -/
def fr_Adm (x u : Fin n → ℝ) (e : Matrix (Fin (mA n)) (Fin n) ℝ → Fin (mA n) → ℝ) : Prop :=
  ∀ A A' : Matrix (Fin (mA n)) (Fin n) ℝ, A *ᵥ x = A' *ᵥ x → A *ᵥ u = A' *ᵥ u →
    (∀ i, ∑ j, A i j ^ 2 = ∑ j, A' i j ^ 2) → e A = e A'

lemma fr_hB_eq (c₀ : Ret n) {A A' : Matrix (Fin (mA n)) (Fin n) ℝ}
    (hu : A *ᵥ uHat c₀ = A' *ᵥ uHat c₀) (hr : ∀ i, ∑ j, A i j ^ 2 = ∑ j, A' i j ^ 2) :
    hB (mkR c₀.1 (A, 0)) = hB (mkR c₀.1 (A', 0)) := by
  have hc : A *ᵥ c₀.1.2 = A' *ᵥ c₀.1.2 := by
    rw [fr_c_eq c₀, Matrix.mulVec_smul, Matrix.mulVec_smul, hu]
  exact (BstLean.Part167.hT_adm c₀.1.2 (BstLean.Part157.tau0p c₀.1.1) hc hr).1

/-- **(B1) `e₁` is admissible.** -/
theorem e1v_adm (c₀ : Ret n) (x : Fin n → ℝ) :
    fr_Adm x (uHat c₀) (fun A => e1v (mkR c₀.1 (A, 0))) := by
  intro A A' _ hu hr
  show e1v (mkR c₀.1 (A, 0)) = e1v (mkR c₀.1 (A', 0))
  unfold e1v
  rw [fr_hB_eq c₀ hu hr]

lemma fr_a1Bar_eq (hn : 2 ≤ n) (c₀ : Ret n) (hc : c₀.1.2 ≠ 0) (s : ℝ)
    {A A' : Matrix (Fin (mA n)) (Fin n) ℝ}
    (hu : A *ᵥ uHat c₀ = A' *ᵥ uHat c₀) (hr : ∀ i, ∑ j, A i j ^ 2 = ∑ j, A' i j ^ 2) :
    a1Bar (mkR c₀.1 (A, 0)) s = a1Bar (mkR c₀.1 (A', 0)) s := by
  funext i
  exact a1Bar_adm (c := mkR c₀.1 (A, 0)) (c' := mkR c₀.1 (A', 0)) hn rfl hc s i (congrFun hu i) (hr i)

/-- **(B3) `e₂` is admissible** (needs `ĉ ≠ 0`). -/
theorem e2v_adm (hn : 2 ≤ n) (c₀ : Ret n) (hc : c₀.1.2 ≠ 0) (g : ℕ) (x : Fin n → ℝ) :
    fr_Adm x (uHat c₀) (fun A => e2v (mkR c₀.1 (A, 0)) g) := by
  intro A A' _ hu hr
  show e2v (mkR c₀.1 (A, 0)) g = e2v (mkR c₀.1 (A', 0)) g
  have hs : nodeS (mkR c₀.1 (A, 0)) g = nodeS (mkR c₀.1 (A', 0)) g := rfl
  unfold e2v
  rw [fr_hB_eq c₀ hu hr, ← hs, fr_a1Bar_eq hn c₀ hc _ hu hr]

/-- **The unit direction** `ĉ' = Π_{U⊥}y/|Π_{U⊥}y|`, `U = span(h, ā(s))` (`0` if the projection
is `0`). -/
noncomputable def cdirP (c : Ret n) (s : ℝ) (y : Fin (mA n) → ℝ) : Fin (mA n) → ℝ :=
  (√(normSq (perp (res (hB c) (a1Bar c s)) (perp (hB c) y))))⁻¹ •
    perp (res (hB c) (a1Bar c s)) (perp (hB c) y)

lemma fr_unit_le {m : ℕ} (P : Fin m → ℝ) : normSq ((√(normSq P))⁻¹ • P) ≤ 1 := by
  have hP := BstLean.Part130.normSq_nonneg P
  have e : normSq ((√(normSq P))⁻¹ • P) = (√(normSq P))⁻¹ ^ 2 * normSq P := by
    unfold normSq; simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [e, inv_pow, Real.sq_sqrt hP]
  rcases hP.lt_or_eq with h | h
  · rw [inv_mul_cancel₀ h.ne']
  · rw [← h]; simp

lemma cdir_normSq_le (c : Ret n) (s : ℝ) (y : Fin (mA n) → ℝ) : normSq (cdirP c s y) ≤ 1 :=
  fr_unit_le _

/-- **(B4) `ĉ'(x)` is admissible.** -/
theorem cdir_adm (hn : 2 ≤ n) (c₀ : Ret n) (hc : c₀.1.2 ≠ 0) (s : ℝ) (x : Fin n → ℝ) :
    fr_Adm x (uHat c₀) (fun A => cdirP (mkR c₀.1 (A, 0)) s (reluV (A *ᵥ x))) := by
  intro A A' hx hu hr
  show cdirP (mkR c₀.1 (A, 0)) s (reluV (A *ᵥ x)) = cdirP (mkR c₀.1 (A', 0)) s (reluV (A' *ᵥ x))
  unfold cdirP
  rw [fr_hB_eq c₀ hu hr, fr_a1Bar_eq hn c₀ hc _ hu hr, hx]

lemma fr_scaled_le {m : ℕ} (P : Fin m → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    normSq ((√t * (√(normSq P))⁻¹) • P) ≤ t := by
  have e : normSq ((√t * (√(normSq P))⁻¹) • P) = t * normSq ((√(normSq P))⁻¹ • P) := by
    unfold normSq; simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    rw [Real.sq_sqrt ht]; ring
  rw [e]; nlinarith [fr_unit_le P]

lemma fr_qvec_le {m : ℕ} (h : Fin m → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    normSq (((normSq h)⁻¹ * (√t * √(normSq h))) • h) ≤ t := by
  have hh := BstLean.Part130.normSq_nonneg h
  have e : ((normSq h)⁻¹ * (√t * √(normSq h))) = √t * (√(normSq h))⁻¹ := by
    rcases hh.lt_or_eq with hp | hp
    · have hs : 0 < √(normSq h) := Real.sqrt_pos.mpr hp
      have gen : ∀ r : ℝ, 0 < r → (r ^ 2)⁻¹ * (√t * r) = √t * r⁻¹ := by
        intro r hr; field_simp
      have e2 := gen _ hs
      rwa [Real.sq_sqrt hh] at e2
    · rw [← hp]; simp
  rw [e]; exact fr_scaled_le h t ht

/-- `|e₁|² ≤ t_A`. -/
lemma e1v_normSq_le (c : Ret n) : normSq (e1v c) ≤ tA n :=
  fr_qvec_le _ _ (BstLean.Part171.tA_nonneg n)

/-- `|e₂|² ≤ t_A`. -/
lemma e2v_normSq_le (c : Ret n) (g : ℕ) : normSq (e2v c g) ≤ tA n :=
  fr_qvec_le _ _ (BstLean.Part171.tA_nonneg n)

end BstLean.Part172
