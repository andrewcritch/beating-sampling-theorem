import BstLean.Part158Basic

/-!
# Part 158 (file `Smooth`): the inequality (GP) for differentiable `f` from the derivative formula

Do not use `sorry`, `native_decide` or `axiom`.

* `frame_nonneg`: the bracket of the derivative formula is nonnegative under the frame bound
  (the Cauchy–Schwarz step of Lemma `t7:p02:GP`).
* **`gp_smooth_of_deriv`**: `PsiDerivStmt → GPSmoothStmt`.
-/

namespace BstLean.Part158

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq gaussMat)

/-! ## Bounded measurable functions -/

/-- A bounded measurable real function. -/
def BM {X : Type*} [MeasurableSpace X] (g : X → ℝ) : Prop :=
  Measurable g ∧ ∃ D, ∀ x, |g x| ≤ D

section BMsec

variable {X : Type*} [MeasurableSpace X]

lemma BM.mul {g₁ g₂ : X → ℝ} (h₁ : BM g₁) (h₂ : BM g₂) : BM (fun x => g₁ x * g₂ x) := by
  obtain ⟨m₁, D₁, b₁⟩ := h₁
  obtain ⟨m₂, D₂, b₂⟩ := h₂
  refine ⟨m₁.mul m₂, D₁ * D₂, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (b₁ x) (b₂ x) (abs_nonneg _) ((abs_nonneg _).trans (b₁ x))

lemma BM.add {g₁ g₂ : X → ℝ} (h₁ : BM g₁) (h₂ : BM g₂) : BM (fun x => g₁ x + g₂ x) := by
  obtain ⟨m₁, D₁, b₁⟩ := h₁
  obtain ⟨m₂, D₂, b₂⟩ := h₂
  exact ⟨m₁.add m₂, D₁ + D₂, fun x => (abs_add_le _ _).trans (add_le_add (b₁ x) (b₂ x))⟩

lemma BM.const (r : ℝ) : BM (fun _ : X => r) := ⟨measurable_const, |r|, fun _ => le_rfl⟩

lemma BM.sum {κ : Type*} (s : Finset κ) {g : κ → X → ℝ} (h : ∀ i ∈ s, BM (g i)) :
    BM (fun x => ∑ i ∈ s, g i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using BM.const (X := X) 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

lemma BM.integrable {g : X → ℝ} (h : BM g) (μ : Measure X) [IsFiniteMeasure μ] :
    Integrable g μ := by
  obtain ⟨m, D, b⟩ := h
  exact Integrable.of_bound m.aestronglyMeasurable D
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact b x)

end BMsec

/-! ## The Cauchy–Schwarz step -/

lemma abs_le_one_of_unit {m : ℕ} {v : Fin m → ℝ} (hv : normSq v = 1) (j : Fin m) : |v j| ≤ 1 := by
  rw [← sq_le_one_iff_abs_le_one, ← hv]
  unfold normSq
  exact Finset.single_le_sum (f := fun i => v i ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)

/-- **The bracket of the derivative formula is nonnegative.** `w x (i, j) = β_i(x)·e_j(x)` with
unit vectors `e(x)` and the frame bound `∫ ⟨e, v⟩² dμ ≤ L|v|²`. Then
`Σ_k (L⁻¹ ∫ w_k² dμ − (L⁻¹ ∫ w_k dμ)²) ≥ 0`. -/
theorem frame_nonneg {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    {q m : ℕ} (e : X → Fin m → ℝ) (he : Measurable e) (hunit : ∀ x, normSq (e x) = 1)
    (w : X → Fin q × Fin m → ℝ) (hw : ∀ k, BM (fun x => w x k))
    (hstr : ∀ x i j, w x (i, j) = (∑ j', w x (i, j') * e x j') * e x j)
    {L : ℝ} (hL : 0 < L)
    (hframe : ∀ v : Fin m → ℝ, ∫ x, (∑ j, e x j * v j) ^ 2 ∂μ ≤ L * ∑ j, v j ^ 2) :
    0 ≤ ∑ k, (L⁻¹ * ∫ x, w x k ^ 2 ∂μ - (L⁻¹ * ∫ x, w x k ∂μ) ^ 2) := by
  set V : Fin q × Fin m → ℝ := fun k => L⁻¹ * ∫ x, w x k ∂μ with hV
  set β : X → Fin q → ℝ := fun x i => ∑ j', w x (i, j') * e x j' with hβ
  set sI : X → Fin q → ℝ := fun x i => ∑ j, e x j * V (i, j) with hsI
  have hE : ∀ j, BM (fun x => e x j) := fun j =>
    ⟨(measurable_pi_apply j).comp he, 1, fun x => abs_le_one_of_unit (hunit x) j⟩
  have bβ : ∀ i, BM (fun x => β x i) := fun i =>
    BM.sum _ fun j _ => (hw (i, j)).mul (hE j)
  have bs : ∀ i, BM (fun x => sI x i) := fun i =>
    BM.sum _ fun j _ => (hE j).mul (BM.const _)
  have hee : ∀ x, ∑ j, e x j ^ 2 = 1 := hunit
  -- the sum of the squares of `V`
  have A : ∑ k, V k ^ 2 = L⁻¹ * ∫ x, ∑ i, β x i * sI x i ∂μ := by
    have e1 : ∀ x, ∑ i, β x i * sI x i = ∑ k, V k * w x k := by
      intro x
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hsI]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hstr x i j]
      ring
    simp_rw [e1]
    rw [integral_finsetSum _ fun k _ => ((hw k).integrable μ).const_mul _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, sq]
    simp only [hV]
    ring
  -- the frame bound for each row
  have B : ∀ i, ∫ x, sI x i ^ 2 ∂μ ≤ L * ∑ j, V (i, j) ^ 2 := fun i =>
    hframe fun j => V (i, j)
  have iβ2 : ∀ i, Integrable (fun x => β x i ^ 2) μ := fun i => by
    have := ((bβ i).mul (bβ i)).integrable μ
    simpa [sq] using this
  have is2 : ∀ i, Integrable (fun x => sI x i ^ 2) μ := fun i => by
    have := ((bs i).mul (bs i)).integrable μ
    simpa [sq] using this
  have iβs : ∀ i, Integrable (fun x => β x i * sI x i) μ := fun i =>
    ((bβ i).mul (bs i)).integrable μ
  set P : ℝ := ∫ x, ∑ i, β x i ^ 2 ∂μ with hP
  set S : ℝ := ∑ k, V k ^ 2 with hS
  have Cc : ∫ x, ∑ i, β x i * sI x i ∂μ ≤ P / 2 + L * S / 2 := by
    have h1 : ∫ x, ∑ i, β x i * sI x i ∂μ ≤
        ∫ x, ∑ i, (β x i ^ 2 / 2 + sI x i ^ 2 / 2) ∂μ := by
      refine integral_mono (integrable_finsetSum _ fun i _ => iβs i)
        (integrable_finsetSum _ fun i _ => ((iβ2 i).div_const 2).add ((is2 i).div_const 2))
        fun x => Finset.sum_le_sum fun i _ => ?_
      nlinarith [sq_nonneg (β x i - sI x i)]
    have h2 : ∫ x, ∑ i, (β x i ^ 2 / 2 + sI x i ^ 2 / 2) ∂μ =
        P / 2 + (∑ i, ∫ x, sI x i ^ 2 ∂μ) / 2 := by
      simp_rw [Finset.sum_add_distrib]
      rw [integral_add (integrable_finsetSum _ fun i _ => (iβ2 i).div_const 2)
        (integrable_finsetSum _ fun i _ => (is2 i).div_const 2)]
      simp_rw [← Finset.sum_div]
      rw [integral_div, integral_div, integral_finsetSum _ fun i _ => is2 i]
    have h3 : ∑ i, ∫ x, sI x i ^ 2 ∂μ ≤ L * S := by
      rw [hS, Fintype.sum_prod_type, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => B i
    linarith
  have D : ∑ k, L⁻¹ * ∫ x, w x k ^ 2 ∂μ = L⁻¹ * P := by
    have iw2 : ∀ k, Integrable (fun x => w x k ^ 2) μ := fun k => by
      have := ((hw k).mul (hw k)).integrable μ
      simpa [sq] using this
    rw [← Finset.mul_sum, ← integral_finsetSum _ fun k _ => iw2 k]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change ∑ k, w x k ^ 2 = ∑ i, β x i ^ 2
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∀ j, w x (i, j) ^ 2 = β x i ^ 2 * e x j ^ 2 := fun j => by
      rw [hstr x i j]; ring
    simp_rw [this]
    rw [← Finset.mul_sum, hee x, mul_one]
  rw [Finset.sum_sub_distrib, D]
  change 0 ≤ L⁻¹ * P - S
  have hLi : 0 < L⁻¹ := inv_pos.mpr hL
  have h4 : S ≤ L⁻¹ * (P / 2 + L * S / 2) :=
    A.le.trans (mul_le_mul_of_nonneg_left Cc hLi.le)
  have h5 : L⁻¹ * (P / 2 + L * S / 2) = L⁻¹ * P / 2 + S / 2 := by
    field_simp
  linarith

/-! ## The concrete family -/

/-- `Bv v ξ = G(ξ) v`: the matrix with entries `ξ (i, j)` applied to `v`. -/
def Bv {q m : ℕ} (v : Fin m → ℝ) (ξ : Fin q × Fin m → ℝ) : Fin q → ℝ :=
  fun i => ∑ j, ξ (i, j) * v j

/-- `Bv v` as a continuous linear map. -/
noncomputable def BvL {q m : ℕ} (v : Fin m → ℝ) : (Fin q × Fin m → ℝ) →L[ℝ] (Fin q → ℝ) :=
  ContinuousLinearMap.pi fun i =>
    ∑ j, v j • (ContinuousLinearMap.proj (i, j) : (Fin q × Fin m → ℝ) →L[ℝ] ℝ)

lemma BvL_apply {q m : ℕ} (v : Fin m → ℝ) (ξ : Fin q × Fin m → ℝ) : BvL v ξ = Bv v ξ := by
  funext i
  simp [BvL, Bv, mul_comm]

lemma of_mulVec {q m : ℕ} (v : Fin m → ℝ) (ξ : Fin q × Fin m → ℝ) :
    (Matrix.of fun i j => √1 * ξ (i, j) : Matrix (Fin q) (Fin m) ℝ).mulVec v = Bv v ξ := by
  funext i
  simp [Matrix.mulVec, dotProduct, Bv]

lemma measurable_Bv {X : Type*} [MeasurableSpace X] {q m : ℕ} {e : X → Fin m → ℝ}
    (he : Measurable e) :
    Measurable (fun p : X × (Fin q × Fin m → ℝ) => Bv (e p.1) p.2) := by
  refine measurable_pi_iff.mpr fun i => ?_
  exact Finset.measurable_sum _ fun j _ =>
    ((measurable_pi_apply (i, j)).comp measurable_snd).mul
      ((measurable_pi_apply j).comp (he.comp measurable_fst))

/-- The image of the standard Gaussian vector of `ℝ^{q×m}` under `Bv v`, `v` a unit vector, is
the standard Gaussian vector of `ℝ^q`. -/
lemma integral_Bv {q m : ℕ} {v : Fin m → ℝ} (hv : normSq v = 1) {g : (Fin q → ℝ) → ℝ}
    (hg : Measurable g) :
    ∫ ξ, g (Bv v ξ) ∂stdGauss (Fin q × Fin m) = ∫ z, g z ∂stdGauss (Fin q) := by
  have h1 := BstLean.Part130.gaussMat_mulVec (m := q) 1 v
  rw [hv] at h1
  simp only [Real.sqrt_one, mul_one, one_smul] at h1
  have h2 : (stdGauss (Fin q)).map (fun ξ => ξ) = stdGauss (Fin q) := Measure.map_id
  rw [h2] at h1
  have mM : Measurable (fun M : Matrix (Fin q) (Fin m) ℝ => M.mulVec v) :=
    (Continuous.matrix_mulVec continuous_id continuous_const).measurable
  rw [← h1, integral_map mM.aemeasurable hg.aestronglyMeasurable]
  unfold gaussMat
  rw [integral_map (f := fun M : Matrix (Fin q) (Fin m) ℝ => g (M.mulVec v))
    (BstLean.Part130.measurable_ofFlat _).aemeasurable (hg.comp mM).aestronglyMeasurable]
  simp_rw [of_mulVec]

/-- **The inequality (GP) for differentiable `f` from the derivative formula of the
interpolation.** -/
theorem gp_smooth_of_deriv (h : PsiDerivStmt) : GPSmoothStmt := by
  intro X _ μ _ q m e he hunit f hf f' hf' hd a b C ha hfa hfb hC L hL hframe
  set F : X → (Fin q × Fin m → ℝ) → ℝ := fun x ξ => f (x, Bv (e x) ξ) with hF
  set dF : X → (Fin q × Fin m → ℝ) → Fin q × Fin m → ℝ :=
    fun x ξ k => f' (x, Bv (e x) ξ) k.1 * e x k.2 with hdF
  have mB := measurable_Bv (q := q) he
  have mP : Measurable (fun p : X × (Fin q × Fin m → ℝ) => (p.1, Bv (e p.1) p.2)) :=
    measurable_fst.prodMk mB
  have fam : Fam F dF a b C := by
    refine ⟨hf.comp mP, ?_, ha, fun x ξ => hfa _, fun x ξ => hfb _, ?_, ?_⟩
    · refine measurable_pi_iff.mpr fun k => ?_
      exact ((measurable_pi_apply k.1).comp (hf'.comp mP)).mul
        ((measurable_pi_apply k.2).comp (he.comp measurable_fst))
    · intro x ξ
      have h1 := (hd x (BvL (e x) ξ)).comp ξ (BvL (e x)).hasFDerivAt
      have e1 : ((fun z => f (x, z)) ∘ (BvL (e x))) = F x := by
        funext ζ
        simp only [Function.comp, hF, BvL_apply]
      rw [e1] at h1
      convert h1 using 1
      ext ζ
      rw [ContinuousLinearMap.comp_apply, dotL_apply, dotL_apply, BvL_apply, BvL_apply,
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hdF, Bv]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    · intro x ξ k
      simp only [hdF]
      rw [abs_mul]
      have h1 := hC (x, Bv (e x) ξ) k.1
      have h2 := abs_le_one_of_unit (hunit x) k.2
      calc |f' (x, Bv (e x) ξ) k.1| * |e x k.2| ≤ |f' (x, Bv (e x) ξ) k.1| * 1 :=
            mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
        _ ≤ C := by rw [mul_one]; exact h1
  set Ψ : ℝ → ℝ := fun θ => Psi μ L F (cos θ) (sin θ) with hΨ
  have hder := fun θ => h μ fam L θ
  -- the bracket is nonnegative
  have hnn : ∀ (c s : ℝ) (ξ : Fin q × Fin m → ℝ),
      0 ≤ ∑ k, (L⁻¹ * ∫ x, wv F dF c s x ξ k ^ 2 ∂μ - Vv μ L F dF c s ξ k ^ 2) := by
    intro c s ξ
    refine frame_nonneg μ e he hunit (fun x k => wv F dF c s x ξ k) (fun k => ?_) ?_ hL hframe
    · exact ⟨(fam.measurable_wv c s k).comp measurable_prodMk_right, C / a,
        fun x => fam.wv_le c s x ξ k⟩
    · intro x i j
      have hA : ∀ j', Abar dF c s x ξ (i, j') =
          (∫ ξ', f' (x, Bv (e x) (c • ξ + s • ξ')) i ∂stdGauss (Fin q × Fin m)) * e x j' := by
        intro j'
        simp only [Abar, hdF]
        rw [integral_mul_const]
      simp only [wv]
      simp_rw [hA]
      have hsum : ∑ j', e x j' * e x j' = 1 := by
        have := hunit x
        unfold normSq at this
        simpa [sq] using this
      set Bq := ∫ ξ', f' (x, Bv (e x) (c • ξ + s • ξ')) i ∂stdGauss (Fin q × Fin m)
      have e2 : ∑ j', Bq * e x j' / U F c s x ξ * e x j' = Bq / U F c s x ξ := by
        have : ∀ j', Bq * e x j' / U F c s x ξ * e x j' =
            Bq / U F c s x ξ * (e x j' * e x j') := fun j' => by ring
        simp_rw [this]
        rw [← Finset.mul_sum, hsum, mul_one]
      rw [e2]
      ring
  -- monotonicity
  have hdiff : Differentiable ℝ Ψ := fun θ => (hder θ).differentiableAt
  have hmono : MonotoneOn Ψ (Set.Icc 0 (π / 2)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) hdiff.continuous.continuousOn
      hdiff.differentiableOn fun θ hθ => ?_
    rw [interior_Icc] at hθ
    rw [(hder θ).deriv]
    have hs : 0 ≤ sin θ := sin_nonneg_of_nonneg_of_le_pi hθ.1.le (by linarith [hθ.2, pi_pos])
    have hc : 0 ≤ cos θ := cos_nonneg_of_mem_Icc ⟨by linarith [hθ.1, pi_pos], hθ.2.le⟩
    exact mul_nonneg (mul_nonneg hs hc)
      (integral_nonneg fun ξ => mul_nonneg (exp_pos _).le (hnn _ _ ξ))
  have hle : Ψ 0 ≤ Ψ (π / 2) :=
    hmono ⟨le_rfl, by positivity⟩ ⟨by positivity, le_rfl⟩ (by positivity)
  -- the endpoints
  have e0 : Ψ 0 = ∫ G, exp (1 / L * ∫ x, log (f (x, G.mulVec (e x))) ∂μ) ∂gaussMat q m 1 := by
    have mJ : Measurable (fun p : Matrix (Fin q) (Fin m) ℝ × X =>
        log (f (p.2, p.1.mulVec (e p.2)))) :=
      (hf.comp (measurable_snd.prodMk
        ((Continuous.matrix_mulVec continuous_fst continuous_snd).measurable.comp
          (measurable_fst.prodMk (he.comp measurable_snd))))).log
    have mI : Measurable (fun G : Matrix (Fin q) (Fin m) ℝ =>
        exp (1 / L * ∫ x, log (f (x, G.mulVec (e x))) ∂μ)) :=
      ((mJ.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable.const_mul _).exp
    unfold gaussMat
    rw [integral_map (BstLean.Part130.measurable_ofFlat _).aemeasurable mI.aestronglyMeasurable]
    simp only [hΨ, Psi, T, cos_zero, sin_zero]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ξ => ?_)
    have hU : ∀ x, U F 1 0 x ξ = f (x, Bv (e x) ξ) := by
      intro x
      simp [U, hF]
    simp only [hU, of_mulVec, one_div]
  have e1 : Ψ (π / 2) = exp (1 / L * ∫ x, log (∫ z, f (x, z) ∂stdGauss (Fin q)) ∂μ) := by
    simp only [hΨ, Psi, T, cos_pi_div_two, sin_pi_div_two]
    have hU : ∀ (x : X) (ξ : Fin q × Fin m → ℝ),
        U F 0 1 x ξ = ∫ z, f (x, z) ∂stdGauss (Fin q) := by
      intro x ξ
      simp only [U, hF, zero_smul, one_smul, zero_add]
      exact integral_Bv (hunit x) (g := fun z => f (x, z)) (hf.comp measurable_prodMk_left)
    simp only [hU, one_div]
    simp
  rw [← e0, ← e1]
  exact hle

end BstLean.Part158

open BstLean.Part158 in
#print axioms frame_nonneg
open BstLean.Part158 in
#print axioms gp_smooth_of_deriv
