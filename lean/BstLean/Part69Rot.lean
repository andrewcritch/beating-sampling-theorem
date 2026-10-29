import BstLean.Part56MomProg_Sphere

/-! Two-direction invariance of the uniform sphere distribution: for orthonormal `p₁, p₂`, the
pair `(p₁·x, p₂·x)` has the same distribution as a pair of distinct coordinates `(x_a, x_b)`. -/

namespace BstLean.Part69

open MeasureTheory
open BstLean.Part29 (uniformSphere)

local notation "E69" n => EuclideanSpace ℝ (Fin n)

private lemma selfAdj69r {n : ℕ} (R : (E69 n) ≃ₗᵢ[ℝ] (E69 n)) (hR : ∀ x, R (R x) = x)
    (x y : E69 n) : inner ℝ (R x) y = inner ℝ x (R y) := by
  conv_lhs => rw [← hR y]
  exact R.inner_map_map x (R y)

private lemma dot69r {n : ℕ} (p x : Fin n → ℝ) :
    ∑ i, p i * x i = inner ℝ (WithLp.toLp 2 p : E69 n) (WithLp.toLp 2 x) := by
  simp [PiLp.inner_apply, mul_comm]

/-- Change of variables under an involutive linear isometry, for a pair of linear forms. -/
private lemma key69r {n : ℕ} (R : (E69 n) ≃ₗᵢ[ℝ] (E69 n)) (hR : ∀ x, R (R x) = x)
    (P Q : E69 n) (G : ℝ → ℝ → ℝ) (hG : Continuous (fun z : ℝ × ℝ => G z.1 z.2)) :
    ∫ x, G (inner ℝ P (WithLp.toLp 2 x)) (inner ℝ Q (WithLp.toLp 2 x)) ∂uniformSphere n =
      ∫ x, G (inner ℝ (R P) (WithLp.toLp 2 x)) (inner ℝ (R Q) (WithLp.toLp 2 x))
        ∂uniformSphere n := by
  set F : (Fin n → ℝ) → ℝ :=
    fun x => G (inner ℝ P (WithLp.toLp 2 x : E69 n)) (inner ℝ Q (WithLp.toLp 2 x : E69 n))
  have hF : Continuous F := by
    have h1 : Continuous fun x : Fin n → ℝ =>
        ((inner ℝ P (WithLp.toLp 2 x : E69 n)), (inner ℝ Q (WithLp.toLp 2 x : E69 n))) := by
      fun_prop
    exact hG.comp h1
  let φ : (Fin n → ℝ) → (Fin n → ℝ) := fun x => WithLp.ofLp (R (WithLp.toLp 2 x))
  have hφ : Measurable φ := by dsimp [φ]; fun_prop
  have hmap := BstLean.Part56.MomProg.uniformSphere_involution R hR
  calc ∫ x, F x ∂uniformSphere n
      = ∫ x, F x ∂(uniformSphere n).map φ := by rw [hmap]
    _ = ∫ x, F (φ x) ∂uniformSphere n :=
        integral_map hφ.aemeasurable hF.aestronglyMeasurable
    _ = _ := by
        apply integral_congr_ae
        filter_upwards with x
        simp only [F, φ, WithLp.toLp_ofLp]
        rw [← selfAdj69r R hR, ← selfAdj69r R hR]

theorem sphere_pair69 {n : ℕ} (hn : 1 ≤ n) (p1 p2 : Fin n → ℝ)
    (h1 : ∑ i, p1 i ^ 2 = 1) (h2 : ∑ i, p2 i ^ 2 = 1) (h12 : ∑ i, p1 i * p2 i = 0)
    (a b : Fin n) (hab : a ≠ b) (G : ℝ → ℝ → ℝ) (hG : Continuous (fun z : ℝ × ℝ => G z.1 z.2)) :
    ∫ x, G (∑ i, p1 i * x i) (∑ i, p2 i * x i) ∂BstLean.Part29.uniformSphere n =
      ∫ x, G (x a) (x b) ∂BstLean.Part29.uniformSphere n := by
  classical
  let P1 : E69 n := WithLp.toLp 2 p1
  let P2 : E69 n := WithLp.toLp 2 p2
  let ea : E69 n := EuclideanSpace.single a 1
  let eb : E69 n := EuclideanSpace.single b 1
  have hP1 : ‖P1‖ = 1 := by
    have h : ‖P1‖ ^ 2 = 1 := by simpa [P1, EuclideanSpace.real_norm_sq_eq] using h1
    nlinarith [norm_nonneg P1]
  have hP2 : ‖P2‖ = 1 := by
    have h : ‖P2‖ ^ 2 = 1 := by simpa [P2, EuclideanSpace.real_norm_sq_eq] using h2
    nlinarith [norm_nonneg P2]
  have hea : ‖ea‖ = 1 := by simp [ea]
  have heb : ‖eb‖ = 1 := by simp [eb]
  have hP12 : inner ℝ P2 P1 = 0 := by
    rw [← dot69r]; simpa [mul_comm] using h12
  have heab : inner ℝ eb ea = 0 := by
    simp [ea, eb, EuclideanSpace.inner_single_left, hab]
  -- first reflection
  let R1 := (ℝ ∙ (P1 - ea))ᗮ.reflection
  have hR1 (x) : R1 (R1 x) = x := R1.symm_apply_apply x
  have hR1P : R1 P1 = ea := Submodule.reflection_sub (hP1.trans hea.symm)
  have hR1e : R1 ea = P1 := by rw [← hR1P, hR1]
  let Q := R1 P2
  have hQ : ‖Q‖ = 1 := by simp [Q, hP2]
  have hQe : inner ℝ Q ea = 0 := by
    simp only [Q]; rw [selfAdj69r R1 hR1, hR1e, hP12]
  -- second reflection
  let R2 := (ℝ ∙ (Q - eb))ᗮ.reflection
  have hR2 (x) : R2 (R2 x) = x := R2.symm_apply_apply x
  have hR2Q : R2 Q = eb := Submodule.reflection_sub (hQ.trans heb.symm)
  have hR2e : R2 ea = ea := by
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_left, hQe, heab, sub_zero]
  have hstep1 := key69r R1 hR1 P1 P2 G hG
  have hstep2 := key69r R2 hR2 (R1 P1) (R1 P2) G hG
  rw [hR1P] at hstep2
  simp only [Q] at hR2Q
  rw [hR2e, hR2Q] at hstep2
  simp_rw [dot69r p1, dot69r p2]
  rw [hstep1, hR1P, hstep2]
  simp [ea, eb, EuclideanSpace.inner_single_left]

theorem exists_orth69 {n : ℕ} (hn : 2 ≤ n) (v : Fin n → ℝ) (hv : ∑ i, v i ^ 2 = 1) :
    ∃ u : Fin n → ℝ, ∑ i, u i ^ 2 = 1 ∧ ∑ i, v i * u i = 0 := by
  classical
  let V : E69 n := WithLp.toLp 2 v
  have hV : V ≠ 0 := by
    intro h
    have : ∑ i, v i ^ 2 = 0 := by
      have hv0 : v = 0 := by
        have := congrArg WithLp.ofLp h
        simpa [V] using this
      simp [hv0]
    linarith
  let K := (ℝ ∙ V)ᗮ
  have hK : Module.finrank ℝ K = n - 1 := by
    apply Submodule.finrank_add_finrank_orthogonal'
    rw [finrank_span_singleton hV, finrank_euclideanSpace, Fintype.card_fin]
    omega
  have hpos : 0 < Module.finrank ℝ K := by rw [hK]; omega
  obtain ⟨w, hw⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hpos
  have hw0 : (w : E69 n) ≠ 0 := by simpa using hw
  have hwK : inner ℝ V (w : E69 n) = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.2
  let U : E69 n := ‖(w : E69 n)‖⁻¹ • (w : E69 n)
  have hU : ‖U‖ = 1 := by
    simp only [U, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw0)
  refine ⟨WithLp.ofLp U, ?_, ?_⟩
  · have h : ‖U‖ ^ 2 = ∑ i, (WithLp.ofLp U) i ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
    rw [← h, hU]; norm_num
  · rw [dot69r]
    simp only [WithLp.toLp_ofLp, U, inner_smul_right]
    change ‖(w : E69 n)‖⁻¹ * inner ℝ V (w : E69 n) = 0
    rw [hwK, mul_zero]

end BstLean.Part69
