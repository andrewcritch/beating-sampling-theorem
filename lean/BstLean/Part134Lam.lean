import BstLean.Part134Var
import BstLean.Part107Poincare

/-!
# Part 134, item 3, further forms

* `lamOne μ b h`: the constant `λ₁` of the paper as an explicit quantity: the supremum of the
  Rayleigh quotient `wᵀ Σ_e w = E_u ⟨e(u), w⟩²` over unit vectors `w` (the largest eigenvalue of
  `Σ_e = E_u e(u) e(u)ᵀ`). `lamOne_frame`: it satisfies the hypothesis of `s1_var`;
  `lamOne_le`: it is the least such constant; `0 ≤ lamOne ≤ 1`.
* `s1_var_lamOne`, `s1_mse_lamOne`: `s1_var_standIn` and `s1_mse` with `L = lamOne`.
* `s1_var_family`: `s1_var` for a test function that depends on `u` (the family `f_u` of the
  paper proof).
* `s1_poincare`: the Poincaré form for a general smooth functional `Ψ` of the standard Gaussian
  matrix `G` whose gradient is `∇Ψ(G) = E_u γ_u(G) ⊗ e(u)`:
  `Var Ψ ≤ L · E E_u |γ_u(G)|²`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part134

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105 (BM bm_cauchy_schwarz)
open BstLean.Part130

variable {n m : ℕ} {U : Type*} [MeasurableSpace U]

section lam

variable (μ : Measure U) [IsProbabilityMeasure μ]

/-- **`λ₁`**: the supremum of `E_u ⟨e(u), w⟩²` over unit vectors `w ∈ ℝ^m`, `e(u) = eDir b (h u)`:
the largest eigenvalue of `Σ_e = E_u e(u) e(u)ᵀ`. -/
noncomputable def lamOne (b : Fin m → ℝ) (h : U → Fin m → ℝ) : ℝ :=
  sSup {x : ℝ | ∃ w : Fin m → ℝ, ∑ j, w j ^ 2 = 1 ∧
    x = ∫ u, (∑ j, eDir b (h u) j * w j) ^ 2 ∂μ}

omit [IsProbabilityMeasure μ] in
theorem lamOne_nonneg (b : Fin m → ℝ) (h : U → Fin m → ℝ) : 0 ≤ lamOne μ b h := by
  refine Real.sSup_nonneg ?_
  rintro x ⟨w, -, rfl⟩
  exact integral_nonneg fun u => sq_nonneg _

theorem lamOne_le_one (b : Fin m → ℝ) {h : U → Fin m → ℝ} (hh : Measurable h) :
    lamOne μ b h ≤ 1 := by
  refine Real.sSup_le ?_ zero_le_one
  rintro x ⟨w, hw, rfl⟩
  have := eDir_frame_one μ b hh w
  rwa [hw, mul_one] at this

omit [IsProbabilityMeasure μ] in
/-- `λ₁` is at most every constant `L ≥ 0` of the hypothesis of `s1_var`. -/
theorem lamOne_le (b : Fin m → ℝ) (h : U → Fin m → ℝ) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : Fin m → ℝ, ∫ u, (∑ j, eDir b (h u) j * w j) ^ 2 ∂μ ≤ L * ∑ j, w j ^ 2) :
    lamOne μ b h ≤ L := by
  refine Real.sSup_le ?_ hL0
  rintro x ⟨w, hw, rfl⟩
  have := hL w
  rwa [hw, mul_one] at this

/-- **`λ₁` satisfies the hypothesis of `s1_var`**: `E_u ⟨e(u), w⟩² ≤ λ₁·|w|²` for every `w`. -/
theorem lamOne_frame (b : Fin m → ℝ) {h : U → Fin m → ℝ} (hh : Measurable h) (w : Fin m → ℝ) :
    ∫ u, (∑ j, eDir b (h u) j * w j) ^ 2 ∂μ ≤ lamOne μ b h * ∑ j, w j ^ 2 := by
  set s := ∑ j, w j ^ 2 with hs
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun j _ => sq_nonneg _
  rcases hs0.eq_or_lt with h0 | hpos
  · have hw : w = 0 := eq_zero_of_normSq h0.symm
    rw [← h0, hw]
    simp
  · set w' : Fin m → ℝ := fun j => (Real.sqrt s)⁻¹ * w j with hw'
    have hsq : Real.sqrt s ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
    have h1 : ∑ j, w' j ^ 2 = 1 := by
      simp only [hw', mul_pow, inv_pow, Real.sq_sqrt hs0]
      rw [← Finset.mul_sum, ← hs, inv_mul_cancel₀ hpos.ne']
    have hbdd : BddAbove {x : ℝ | ∃ w : Fin m → ℝ, ∑ j, w j ^ 2 = 1 ∧
        x = ∫ u, (∑ j, eDir b (h u) j * w j) ^ 2 ∂μ} := by
      refine ⟨1, ?_⟩
      rintro x ⟨w, hw, rfl⟩
      have := eDir_frame_one μ b hh w
      rwa [hw, mul_one] at this
    have h2 : ∫ u, (∑ j, eDir b (h u) j * w' j) ^ 2 ∂μ ≤ lamOne μ b h :=
      le_csSup hbdd ⟨w', h1, rfl⟩
    have e : ∀ u, (∑ j, eDir b (h u) j * w j) ^ 2 = s * (∑ j, eDir b (h u) j * w' j) ^ 2 := by
      intro u
      have : ∑ j, eDir b (h u) j * w j = Real.sqrt s * ∑ j, eDir b (h u) j * w' j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hw']
        field_simp
      rw [this, mul_pow, Real.sq_sqrt hs0]
    simp_rw [e]
    rw [integral_const_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right h2 hs0

/-- **Theorem S1 (c) with the explicit constant `λ₁`**:
`Var(E_{μ_M} φ | c) ≤ λ₁ · Var_{ν_c} φ`. -/
theorem s1_var_lamOne (v : ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ) {h : U → Fin m → ℝ}
    (hh : Measurable h) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    Var[fun M' => ∫ x, φ x ∂muM μ h (glue b c (M' * projPerp b)); gaussMat n m v] ≤
      lamOne μ b h * Var[φ; standIn μ h v b c] :=
  s1_var_standIn μ v b c hh hφ (lamOne_nonneg μ b h) (lamOne_frame μ b hh)

/-- **The mean squared error of the stand-in with the explicit constant `λ₁`.** -/
theorem s1_mse_lamOne (v : ℝ) {b : Fin m → ℝ} (hb : b ≠ 0) {h : U → Fin m → ℝ}
    (hh : Measurable h) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ M, ((∫ x, φ x ∂muM μ h M) - ∫ x, φ x ∂standIn μ h v b (M.mulVec b)) ^ 2 ∂gaussMat n m v ≤
      lamOne μ b h * ∫ c, Var[φ; standIn μ h v b c] ∂cDist n v b :=
  s1_mse μ v hb hh hφ (lamOne_nonneg μ b h) (lamOne_frame μ b hh)

/-- **Theorem S1 (c) for a test function that depends on `u`** (the family `f_u` of the paper
proof): for bounded jointly measurable `g`,
`Var_{M'}(E_u g_u(M' r(u))) ≤ L · E_u Var_γ g_u(σ(u) γ)`. -/
theorem s1_var_family (v : ℝ) (b : Fin m → ℝ) {h : U → Fin m → ℝ} (hh : Measurable h)
    {g : U × (Fin n → ℝ) → ℝ} (hg : BM g) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : Fin m → ℝ, ∫ u, (∑ j, eDir b (h u) j * w j) ^ 2 ∂μ ≤ L * ∑ j, w j ^ 2) :
    Var[fun M' : Matrix (Fin n) (Fin m) ℝ => ∫ u, g (u, M'.mulVec (res b (h u))) ∂μ;
        gaussMat n m v] ≤
      L * ∫ u, Var[fun γ => g (u, sig v b (h u) • γ); stdGauss (Fin n)] ∂μ := by
  set f : U × (Fin n → ℝ) → ℝ := fun p => g (p.1, sig v b (h p.1) • p.2) with hf
  have bf : BM f := hg.comp (measurable_fst.prodMk
    (((measurable_sig v b).comp (hh.comp measurable_fst)).smul measurable_snd))
  have bΦ : BM (fun M' : Matrix (Fin n) (Fin m) ℝ => ∫ u, g (u, M'.mulVec (res b (h u))) ∂μ) := by
    have : BM (fun q : Matrix (Fin n) (Fin m) ℝ × U => g (q.2, q.1.mulVec (res b (h q.2)))) :=
      hg.comp (measurable_snd.prodMk (measurable_mulVec_joint.comp
        (measurable_fst.prodMk ((measurable_res b).comp (hh.comp measurable_snd)))))
    exact this.integral_right μ
  have core := var_core (n := n) μ ((measurable_eDir b).comp hh)
    (fun u => eDir_unit_or_zero b (h u)) bf hL0 hL
  have key : ∀ ξ : Fin n × Fin m → ℝ,
      ∫ u, g (u, (Matrix.of fun i j => Real.sqrt v * ξ (i, j) :
        Matrix (Fin n) (Fin m) ℝ).mulVec (res b (h u))) ∂μ =
      ∫ u, f (u, (rowMat n (eDir b (h u))).mulVec ξ) ∂μ := by
    intro ξ
    refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [hf]
    rw [resid_eq]
  have e1 : ∫ M' : Matrix (Fin n) (Fin m) ℝ, (∫ u, g (u, M'.mulVec (res b (h u))) ∂μ) ^ 2
      ∂gaussMat n m v =
      ∫ ξ, (∫ u, f (u, (rowMat n (eDir b (h u))).mulVec ξ) ∂μ) ^ 2
        ∂stdGauss (Fin n × Fin m) := by
    rw [integral_gaussMat v bΦ.sq.meas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only []
    rw [key ξ]
  have e2 : ∫ M' : Matrix (Fin n) (Fin m) ℝ, (∫ u, g (u, M'.mulVec (res b (h u))) ∂μ)
      ∂gaussMat n m v =
      ∫ ξ, (∫ u, f (u, (rowMat n (eDir b (h u))).mulVec ξ) ∂μ) ∂stdGauss (Fin n × Fin m) := by
    rw [integral_gaussMat v bΦ.meas]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    simp only []
    rw [key ξ]
  have e3 : ∀ u, Var[fun γ => g (u, sig v b (h u) • γ); stdGauss (Fin n)] =
      ∫ z, (f (u, z) - ∫ y, f (u, y) ∂stdGauss (Fin n)) ^ 2 ∂stdGauss (Fin n) := fun u =>
    var_bm' (stdGauss (Fin n)) (X := fun z => f (u, z)) (bf.comp measurable_prodMk_left)
  rw [var_bm (gaussMat n m v) bΦ, e1, e2]
  simp_rw [e3]
  exact core

/-- **The Poincaré form** (the route through the Gaussian Poincaré inequality `poincare107`).
`Ψ` a continuously differentiable square-integrable function of the standard Gaussian entries
`ξ` (the matrix `G`), whose gradient is `∂Ψ/∂ξ(i, j) = E_u γ_u(ξ)_i e(u)_j` for a bounded
measurable field `γ` and bounded measurable vectors `e(u)` with `E_u ⟨e(u), w⟩² ≤ L|w|²`. Then
`Var Ψ ≤ L · E_ξ E_u |γ_u(ξ)|²`. -/
theorem s1_poincare {Ψ : (Fin n × Fin m → ℝ) → ℝ} (hΨ : ContDiff ℝ 1 Ψ)
    (hΨ2 : MemLp Ψ 2 (stdGauss (Fin n × Fin m)))
    {e : U → Fin m → ℝ} (he : ∀ j, BM (fun u => e u j))
    {γ : U × (Fin n × Fin m → ℝ) → Fin n → ℝ} (hγ : ∀ i, BM (fun q => γ q i))
    (hder : ∀ (ξ : Fin n × Fin m → ℝ) (p : Fin n × Fin m),
      fderiv ℝ Ψ ξ (Pi.single p 1) = ∫ u, γ (u, ξ) p.1 * e u p.2 ∂μ)
    {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ w : Fin m → ℝ, ∫ u, (∑ j, e u j * w j) ^ 2 ∂μ ≤ L * ∑ j, w j ^ 2) :
    ∫ ξ, (Ψ ξ - ∫ ζ, Ψ ζ ∂stdGauss (Fin n × Fin m)) ^ 2 ∂stdGauss (Fin n × Fin m) ≤
      L * ∫ ξ, (∫ u, ∑ i, γ (u, ξ) i ^ 2 ∂μ) ∂stdGauss (Fin n × Fin m) := by
  classical
  have bD : ∀ p : Fin n × Fin m,
      BM (fun ξ : Fin n × Fin m → ℝ => ∫ u, γ (u, ξ) p.1 * e u p.2 ∂μ) := by
    intro p
    have : BM (fun q : (Fin n × Fin m → ℝ) × U => γ (q.2, q.1) p.1 * e q.2 p.2) :=
      ((hγ p.1).comp measurable_swap).mul ((he p.2).comp measurable_snd)
    exact this.integral_right μ
  have bG : BM (fun ξ : Fin n × Fin m → ℝ =>
      ∑ p : Fin n × Fin m, (∫ u, γ (u, ξ) p.1 * e u p.2 ∂μ) ^ 2) :=
    bm_sum Finset.univ fun p _ => (bD p).sq
  have bR : BM (fun ξ : Fin n × Fin m → ℝ => ∫ u, ∑ i, γ (u, ξ) i ^ 2 ∂μ) := by
    have : BM (fun q : (Fin n × Fin m → ℝ) × U => ∑ i, γ (q.2, q.1) i ^ 2) :=
      bm_sum Finset.univ fun i _ => ((hγ i).comp measurable_swap).sq
    exact this.integral_right μ
  have hG : Integrable (fun ξ => ∑ p, (fderiv ℝ Ψ ξ (Pi.single p 1)) ^ 2)
      (stdGauss (Fin n × Fin m)) := by
    simp_rw [hder]
    exact bG.integrable _
  have hp := BstLean.Part107.poincare107_C1 Ψ hΨ hΨ2 hG
  refine hp.trans ?_
  simp_rw [hder]
  rw [← integral_const_mul]
  refine integral_mono (bG.integrable _) (((BM.const L).mul bR).integrable _) fun ξ => ?_
  simp only []
  have bα : ∀ i, BM (fun u => γ (u, ξ) i) := fun i => (hγ i).comp measurable_prodMk_right
  have h1 : ∀ i, ∑ j, (∫ u, γ (u, ξ) i * e u j ∂μ) ^ 2 ≤ L * ∫ u, γ (u, ξ) i ^ 2 ∂μ :=
    fun i => frame_bound μ he (bα i) hL0 hL
  calc ∑ p : Fin n × Fin m, (∫ u, γ (u, ξ) p.1 * e u p.2 ∂μ) ^ 2
      = ∑ i, ∑ j, (∫ u, γ (u, ξ) i * e u j ∂μ) ^ 2 := Fintype.sum_prod_type _
    _ ≤ ∑ i, L * ∫ u, γ (u, ξ) i ^ 2 ∂μ := Finset.sum_le_sum fun i _ => h1 i
    _ = L * ∫ u, ∑ i, γ (u, ξ) i ^ 2 ∂μ := by
        rw [integral_finsetSum _ fun i _ => (bα i).sq.integrable μ, Finset.mul_sum]

end lam

/-- **The residual field is centred**: `E[((M P) h)_i] = 0`. -/
theorem s1_resid_mean (v : ℝ) (b h : Fin m → ℝ) (i : Fin n) :
    ∫ M, ((M * projPerp b).mulVec h) i ∂gaussMat n m v = 0 := by
  have hm : Measurable (fun y : Fin n → ℝ => y i) := measurable_pi_apply i
  have hs : Measurable (fun ξ : Fin n → ℝ => sig v b h • ξ) :=
    (continuous_id.const_smul (sig v b h)).measurable
  have hm2 : Measurable (fun M : Matrix (Fin n) (Fin m) ℝ => (M * projPerp b).mulVec h) :=
    (measurable_mulVec_right h).comp (measurable_mul_right (n := n) (projPerp b))
  calc ∫ M, ((M * projPerp b).mulVec h) i ∂gaussMat n m v
      = ∫ y, y i ∂(gaussMat n m v).map (fun M => (M * projPerp b).mulVec h) :=
        (integral_map hm2.aemeasurable hm.aestronglyMeasurable).symm
    _ = ∫ ξ, (sig v b h • ξ) i ∂stdGauss (Fin n) := by
        rw [s1_resid_gauss]
        exact integral_map hs.aemeasurable hm.aestronglyMeasurable
    _ = 0 := by
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [integral_const_mul, BstLean.Part112.coord_integral, mul_zero]

/-- **Theorem S1 (c) for the World network with the explicit constant `λ₁`.** -/
theorem s1_var_mlp_lamOne {N : ℕ} (hN : 1 ≤ N) (M₁ : Matrix (Fin m) (Fin N) ℝ)
    (M₂ : Matrix (Fin m) (Fin m) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    Var[fun M' => ∫ x, φ x ∂muWn ((M₁, M₂, glue b c (M' * projPerp b)) : MlpParam N m n);
        gaussMat n m (2 / (m : ℝ))] ≤
      lamOne (uniformSphere N) b (hid2 M₁ M₂) *
        Var[φ; standIn (uniformSphere N) (hid2 M₁ M₂) (2 / (m : ℝ)) b c] := by
  have := BstLean.Part29.uniformSphere_isProbability N hN
  exact s1_var_lamOne (uniformSphere N) (2 / (m : ℝ)) b c (continuous_hid2 M₁ M₂).measurable hφ

end BstLean.Part134

open BstLean.Part134 in
#print axioms s1_resid_mean
open BstLean.Part134 in
#print axioms lamOne_frame
open BstLean.Part134 in
#print axioms lamOne_le
open BstLean.Part134 in
#print axioms s1_var_lamOne
open BstLean.Part134 in
#print axioms s1_mse_lamOne
open BstLean.Part134 in
#print axioms s1_var_family
open BstLean.Part134 in
#print axioms s1_poincare
open BstLean.Part134 in
#print axioms s1_var_mlp_lamOne
