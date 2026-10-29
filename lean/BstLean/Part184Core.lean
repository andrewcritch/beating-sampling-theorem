import BstLean.Part184Def
import BstLean.Part184Mom
import BstLean.Part184Row

/-!
# Part 184 (file `Core`): the row moment expansion of the energy fluctuation at fixed plane coordinates

No proof is left open; no `native_decide` or `axiom` is used.

* `stdGauss_uncurry`, `lintegral_uncurry`, `integral_uncurry`: the standard Gaussian matrix is the
  product of its independent rows.
* `wT_mean`, `wT_cov`: the transverse field has mean zero and covariance at most `Λ`.
* `poly_amgm`, `Smom_sq_le`, `jensen4`: the AM–GM, Cauchy–Schwarz and Jensen steps.
* **`flQ_rows8`**: `E|Q − EQ|⁸ ≤ 107.59(4tΛ)⁴·E Q_v⁴ + (24563m+1)(π/2)⁸E|g|⁸(4tΛ)⁴·E Σ_j W_j⁴
  + 2800m(π/2)¹²E|g|¹²(4tΛ)⁶/σ²·E Σ_j W_j⁶ + 0.14σ⁴`: the rows of the transverse matrix are
  independent (`mom8_pi_lint`), the second row moment is paid by the sharp Gaussian Poincaré
  inequality (`row_var_sharp`, no factor `π/2`), and only the negligible higher row moments use
  Pisier's constant (`row_mom_p`).
-/

namespace BstLean.Part184

open MeasureTheory ProbabilityTheory Real Matrix Filter Topology
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part170
open BstLean.Part134 (res)
open BstLean.Part167 (perp normSq_perp_le)
open BstLean.Part162 (gmom gmom_nonneg)

/-! ## Rows of the standard Gaussian matrix -/

lemma stdGauss_uncurry (m : ℕ) :
    (Measure.pi fun _ : Fin m => stdGauss (Fin m)).map (Function.uncurry) =
      stdGauss (Fin m × Fin m) := by
  symm
  unfold stdGauss
  refine Measure.pi_eq (fun s hs => ?_)
  have hm : Measurable (Function.uncurry : (Fin m → Fin m → ℝ) → (Fin m × Fin m → ℝ)) :=
    (MeasurableEquiv.curry (Fin m) (Fin m) ℝ).symm.measurable
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (Function.uncurry : (Fin m → Fin m → ℝ) → (Fin m × Fin m → ℝ)) ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => Set.univ.pi (fun j => s (i, j))) := by
    ext y; simp [Set.mem_pi]
  rw [hpre, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [← Finset.prod_product', Finset.univ_product_univ]

lemma lintegral_uncurry (m : ℕ) (f : (Fin m × Fin m → ℝ) → ℝ≥0∞) :
    ∫⁻ ζ, f ζ ∂stdGauss (Fin m × Fin m) =
      ∫⁻ y, f (Function.uncurry y) ∂(Measure.pi fun _ : Fin m => stdGauss (Fin m)) := by
  rw [← stdGauss_uncurry]
  exact lintegral_map_equiv f (MeasurableEquiv.curry (Fin m) (Fin m) ℝ).symm

lemma integral_uncurry (m : ℕ) (f : (Fin m × Fin m → ℝ) → ℝ) :
    ∫ ζ, f ζ ∂stdGauss (Fin m × Fin m) =
      ∫ y, f (Function.uncurry y) ∂(Measure.pi fun _ : Fin m => stdGauss (Fin m)) := by
  rw [← stdGauss_uncurry]
  exact (MeasurableEquiv.curry (Fin m) (Fin m) ℝ).symm.measurableEmbedding.integral_map _

lemma matOf_uncurry_mulVec {m : ℕ} (t : ℝ) (y : Fin m → Fin m → ℝ) (x : Fin m → ℝ) (j : Fin m) :
    (matOf t (Function.uncurry y) *ᵥ x) j = √t * (y j ⬝ᵥ x) := by
  simp [Matrix.mulVec, dotProduct, matOf, Finset.mul_sum, mul_assoc]

/-! ## Elementary helpers -/

lemma dev_pow_le {x e : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    |x - e| ^ k ≤ 2 ^ k * (x ^ k + |e| ^ k) := by
  have h1 : |x - e| ≤ 2 * max x |e| := by
    have := abs_sub x e
    rw [abs_of_nonneg hx] at this
    linarith [le_max_left x |e|, le_max_right x |e|]
  have h2 : |x - e| ^ k ≤ (2 * max x |e|) ^ k := pow_le_pow_left₀ (abs_nonneg _) h1 k
  have h3 : (max x |e|) ^ k ≤ x ^ k + |e| ^ k := by
    rcases le_total x |e| with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg hx k]
    · rw [max_eq_left h]; linarith [pow_nonneg (abs_nonneg e) k]
  calc |x - e| ^ k ≤ (2 * max x |e|) ^ k := h2
    _ = 2 ^ k * (max x |e|) ^ k := mul_pow _ _ _
    _ ≤ 2 ^ k * (x ^ k + |e| ^ k) := by gcongr

lemma int_dev {X : Type*} [MeasurableSpace X] {ρ : Measure X} [IsProbabilityMeasure ρ]
    {f : X → ℝ} (hf : Measurable f) (hf0 : ∀ x, 0 ≤ f x) {k : ℕ}
    (hi : Integrable (fun x => f x ^ k) ρ) (e : ℝ) :
    Integrable (fun x => |f x - e| ^ k) ρ := by
  refine Integrable.mono' ((hi.add (integrable_const (|e| ^ k))).const_mul (2 ^ k))
    (((continuous_abs.measurable.comp (hf.sub_const e)).pow_const k).aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact dev_pow_le (hf0 x) k

/-- Jensen at order four in `lintegral` form. -/
lemma jensen4 {X : Type*} [MeasurableSpace X] {ρ : Measure X} [IsProbabilityMeasure ρ]
    {g : X → ℝ} (hg : Measurable g) (hg0 : ∀ x, 0 ≤ g x) :
    ENNReal.ofReal ((∫ x, g x ∂ρ) ^ 4) ≤ ∫⁻ x, ENNReal.ofReal (g x ^ 4) ∂ρ := by
  by_cases hi : Integrable (fun x => g x ^ 4) ρ
  · have hk : ∀ k, k ≤ 4 → Integrable (fun x => g x ^ k) ρ := by
      intro k hk
      refine Integrable.mono' ((integrable_const (1 : ℝ)).add hi) (hg.pow_const k).aestronglyMeasurable
        (Eventually.of_forall fun x => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hg0 x) k)]
      simp only [Pi.add_apply]
      rcases le_total (g x) 1 with h | h
      · have := pow_le_one₀ (hg0 x) h (n := k); have := pow_nonneg (hg0 x) 4; linarith
      · have := pow_le_pow_right₀ h hk; linarith
    have i1 : Integrable g ρ := by simpa using hk 1 (by norm_num)
    have i2 := hk 2 (by norm_num)
    have c1 := int_cs2 ρ (F := g) (G := fun _ => (1 : ℝ)) i2 (by simp) (by simpa using i1)
    have c2 := int_cs2 ρ (F := fun x => g x ^ 2) (G := fun _ => (1 : ℝ))
      (by simpa [← pow_mul] using hi) (by simp) (by simpa using i2)
    simp only [mul_one, one_pow, integral_const, probReal_univ, smul_eq_mul] at c1 c2
    have e4 : (fun x => (g x ^ 2) ^ 2) = fun x => g x ^ 4 := funext fun x => by ring
    rw [e4] at c2
    rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun x => pow_nonneg (hg0 x) 4)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h0 : 0 ≤ ∫ x, g x ∂ρ := integral_nonneg hg0
    calc (∫ x, g x ∂ρ) ^ 4 = ((∫ x, g x ∂ρ) ^ 2) ^ 2 := by ring
      _ ≤ (∫ x, g x ^ 2 ∂ρ) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) (by linarith) 2
      _ ≤ _ := by linarith
  · have : ∫⁻ x, ENNReal.ofReal (g x ^ 4) ∂ρ = ⊤ := by
      by_contra hne
      exact hi ⟨(hg.pow_const 4).aestronglyMeasurable,
        (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x => pow_nonneg (hg0 x) 4)).mpr
          (lt_top_iff_ne_top.mpr hne)⟩
    rw [this]; exact le_top

/-! ## The transverse field -/

section core
variable {m : ℕ} {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]

lemma wT_dot (a : V → Fin m → ℝ) (h e y : Fin m → ℝ) :
    e ⬝ᵥ BstLean.Part183.wT μ a h y =
      perp h (perp (res h (vmean μ a)) e) ⬝ᵥ (y - vmean μ a) := by
  have e2 : e ⬝ᵥ perp (res h (vmean μ a)) (perp h y) =
      perp h (perp (res h (vmean μ a)) e) ⬝ᵥ y := by
    rw [← BstLean.Part170.perp_dot, ← BstLean.Part170.perp_dot]
  have e3 : perp h (perp (res h (vmean μ a)) e) ⬝ᵥ vmean μ a = 0 := by
    rw [BstLean.Part170.perp_dot, BstLean.Part170.perp_dot, BstLean.Part170.perp_perp_res]; simp
  show e ⬝ᵥ perp (res h (vmean μ a)) (perp h y) = _
  rw [e2, dotProduct_sub, e3, sub_zero]

lemma wT_mean {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    (h : Fin m → ℝ) (i : Fin m) : ∫ v, BstLean.Part183.wT μ a h (a v) i ∂μ = 0 := by
  have e : ∀ v, BstLean.Part183.wT μ a h (a v) i =
      perp h (perp (res h (vmean μ a)) (Pi.single i 1)) ⬝ᵥ (a v - vmean μ a) := by
    intro v
    rw [← wT_dot]; simp [dotProduct, Pi.single_apply]
  simp_rw [e, dotProduct_sub]
  have cE : Continuous (fun y : Fin m → ℝ =>
      perp h (perp (res h (vmean μ a)) (Pi.single i 1)) ⬝ᵥ y) :=
    continuous_const.dotProduct continuous_id
  rw [integral_sub (BstLean.Part170.int_comp_bdd ha hK cE) (integrable_const _),
    BstLean.Part170.int_dot ha hK]
  simp

lemma wT_cov {a : V → Fin m → ℝ} {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ Λ * normSq e) (h e : Fin m → ℝ) :
    ∫ v, (e ⬝ᵥ BstLean.Part183.wT μ a h (a v)) ^ 2 ∂μ ≤ Λ * normSq e := by
  simp_rw [wT_dot]
  refine (hΛ _).trans (mul_le_mul_of_nonneg_left ?_ hΛ0)
  exact (normSq_perp_le h _).trans (normSq_perp_le _ e)

lemma bdd_comp {a : V → Fin m → ℝ} {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K) {E : Type*}
    [SeminormedAddCommGroup E] {f : (Fin m → ℝ) → E} (hf : Continuous f) :
    ∃ C, ∀ v, ‖f (a v)‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Fin m → ℝ) K).exists_bound_of_continuousOn
    hf.continuousOn
  exact ⟨C, fun v => hC _ (mem_closedBall_zero_iff.mpr (hK v))⟩

end core

section main
variable {m : ℕ} {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]

/-- The centred row energy of the plane-split matrix: `E_v (g_j(v) − E g_j)²`,
`g_j(v) = (M₀a(v))_j + (N w(v))_j`, `N = matOf t ζ`. -/
noncomputable def WgR (μ : Measure V) (a : V → Fin m → ℝ) (h : Fin m → ℝ)
    (M₀ : Matrix (Fin m) (Fin m) ℝ) (t : ℝ) (j : Fin m) (ζ : Fin m × Fin m → ℝ) : ℝ :=
  ∫ v, ((M₀ *ᵥ a v) j + (matOf t ζ *ᵥ BstLean.Part183.wT μ a h (a v)) j -
    ∫ v', ((M₀ *ᵥ a v') j + (matOf t ζ *ᵥ BstLean.Part183.wT μ a h (a v')) j) ∂μ) ^ 2 ∂μ

/-- Real Cauchy–Schwarz for one row: `(E|f|^k)² ≤ E|f|^{2k}`. -/
lemma row_cs_pow {X : Type*} [MeasurableSpace X] {ρ : Measure X} [IsProbabilityMeasure ρ]
    {f : X → ℝ} {k : ℕ} (hk : Integrable (fun x => |f x| ^ k) ρ)
    (h2k : Integrable (fun x => |f x| ^ (2 * k)) ρ) :
    (∫ x, |f x| ^ k ∂ρ) ^ 2 ≤ ∫ x, |f x| ^ (2 * k) ∂ρ := by
  have e : (fun x => (|f x| ^ k) ^ 2) = fun x => |f x| ^ (2 * k) := funext fun x => by
    rw [← pow_mul, mul_comm]
  have c := int_cs2 ρ (F := fun x => |f x| ^ k) (G := fun _ => (1 : ℝ)) (by rw [e]; exact h2k)
    (by simp) (by simpa using hk)
  simp only [mul_one, one_pow, integral_const, probReal_univ, smul_eq_mul] at c
  rw [e] at c; exact c

/-- Sum-level Cauchy–Schwarz: `S_k² ≤ m·S_{2k}`. -/
lemma Smom_sq_le {X : Type*} [MeasurableSpace X] (ρ : Measure X) [IsProbabilityMeasure ρ]
    (φ : Fin m → X → ℝ) {k : ℕ} (hk : ∀ j, Integrable (fun x => |φ j x| ^ k) ρ)
    (h2k : ∀ j, Integrable (fun x => |φ j x| ^ (2 * k)) ρ) :
    Smom ρ φ k ^ 2 ≤ m * Smom ρ φ (2 * k) := by
  unfold Smom
  refine (sq_sum_le_card_mul_sum_sq (s := Finset.univ)).trans ?_
  simp only [Finset.card_univ, Fintype.card_fin]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => row_cs_pow (hk j) (h2k j))
    (Nat.cast_nonneg m)

/-- The real form of `S_k` as a sum of `lintegral`s. -/
lemma ofReal_Smom {X : Type*} [MeasurableSpace X] (ρ : Measure X)
    (φ : Fin m → X → ℝ) {k : ℕ} (hk : ∀ j, Integrable (fun x => |φ j x| ^ k) ρ) :
    ENNReal.ofReal (Smom ρ φ k) = ∑ j, ∫⁻ x, ENNReal.ofReal (|φ j x| ^ k) ∂ρ := by
  unfold Smom
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => integral_nonneg fun x => by positivity)]
  exact Finset.sum_congr rfl fun j _ =>
    ofReal_integral_eq_lintegral_ofReal (hk j) (Eventually.of_forall fun x => by positivity)

/-- The real moment inequality after the AM–GM steps. -/
lemma poly_amgm {S2 S4 S6 S8 S12 σ M : ℝ} (h2 : 0 ≤ S2) (h4 : 0 ≤ S4) (h6 : 0 ≤ S6) (h8 : 0 ≤ S8)
    (hσ : 0 < σ) (hM : 0 ≤ M) (h48 : S4 ^ 2 ≤ M * S8) (h612 : S6 ^ 2 ≤ M * S12) :
    105 * S2 ^ 4 + 490 * S2 ^ 2 * S4 + 63 * S4 ^ 2 + 56 * S2 * S6 + S8 ≤
      10759 / 100 * S2 ^ 4 + (24563 * M + 1) * S8 + 2800 * M / σ ^ 2 * S12 + 14 / 100 * σ ^ 4 := by
  have a1 : 490 * S2 ^ 2 * S4 ≤ 245 / 100 * S2 ^ 4 + 24500 * S4 ^ 2 := by
    nlinarith [sq_nonneg (7 / 100 * S2 ^ 2 - 7 * S4)]
  have hσ2 : 0 < σ ^ 2 := by positivity
  have a2 : 56 * S2 * S6 ≤ 28 / 100 * σ ^ 2 * S2 ^ 2 + 2800 * S6 ^ 2 / σ ^ 2 := by
    set u := S6 / σ with hu
    have e1 : S6 = σ * u := by rw [hu]; field_simp
    have e2 : S6 ^ 2 / σ ^ 2 = u ^ 2 := by rw [hu, div_pow]
    rw [mul_div_assoc, e2, e1]
    nlinarith [sq_nonneg (σ * S2 - 100 * u)]
  have a3 : 28 / 100 * σ ^ 2 * S2 ^ 2 ≤ 14 / 100 * S2 ^ 4 + 14 / 100 * σ ^ 4 := by
    nlinarith [sq_nonneg (S2 ^ 2 - σ ^ 2)]
  have a4 : 2800 * S6 ^ 2 / σ ^ 2 ≤ 2800 * M / σ ^ 2 * S12 := by
    rw [div_mul_eq_mul_div, mul_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hσ2.le
  nlinarith

end main

section thm
variable {m : ℕ} {V : Type*} [MeasurableSpace V] {μ : Measure V} [IsProbabilityMeasure μ]

theorem flQ_rows8 {a : V → Fin m → ℝ} (ha : Measurable a) {K : ℝ} (hK : ∀ v, ‖a v‖ ≤ K)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : ∀ e, ∫ v, (e ⬝ᵥ (a v - vmean μ a)) ^ 2 ∂μ ≤ Λ * normSq e)
    (h : Fin m → ℝ) (M₀ : Matrix (Fin m) (Fin m) ℝ) {t : ℝ} (ht : 0 ≤ t) {σ : ℝ} (hσ : 0 < σ) :
    ∫⁻ ζ, ENNReal.ofReal (|flQ μ a h M₀ (matOf t ζ) -
        ∫ ζ', flQ μ a h M₀ (matOf t ζ') ∂stdGauss (Fin m × Fin m)| ^ 8) ∂stdGauss (Fin m × Fin m) ≤
      ENNReal.ofReal (10759 / 100 * (4 * (t * Λ)) ^ 4) *
          ∫⁻ ζ, ENNReal.ofReal (BstLean.Part183.flQv μ a h M₀ (matOf t ζ) ^ 4)
            ∂stdGauss (Fin m × Fin m) +
        ENNReal.ofReal ((24563 * m + 1) * ((π / 2) ^ 8 * gmom 8) * (4 * (t * Λ)) ^ 4) *
          ∫⁻ ζ, ENNReal.ofReal (∑ j, WgR μ a h M₀ t j ζ ^ 4) ∂stdGauss (Fin m × Fin m) +
        ENNReal.ofReal (2800 * m * ((π / 2) ^ 12 * gmom 12) * (4 * (t * Λ)) ^ 6 / σ ^ 2) *
          ∫⁻ ζ, ENNReal.ofReal (∑ j, WgR μ a h M₀ t j ζ ^ 6) ∂stdGauss (Fin m × Fin m) +
        ENNReal.ofReal (14 / 100 * σ ^ 4) := by
  set ρ := stdGauss (Fin m) with hρ
  set P := Measure.pi fun _ : Fin m => ρ with hP
  set w : V → Fin m → ℝ := fun v => BstLean.Part183.wT μ a h (a v) with hwd
  set c : Fin m → V → ℝ := fun j v => (M₀ *ᵥ a v) j with hcd
  have hw : Measurable w := (BstLean.Part183.continuous_wT (μ := μ) a h).measurable.comp ha
  have hc : ∀ j, Measurable (c j) := fun j =>
    ((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const
      continuous_id)).measurable.comp ha
  obtain ⟨Kw, hKw⟩ := bdd_comp hK (BstLean.Part183.continuous_wT (μ := μ) a h)
  have hcK : ∀ j, ∃ C, ∀ v, |c j v| ≤ C := fun j => by
    obtain ⟨C, hC⟩ := bdd_comp hK (f := fun y => (M₀ *ᵥ y) j)
      ((continuous_apply j).comp (Continuous.matrix_mulVec continuous_const continuous_id))
    exact ⟨C, fun v => by simpa [Real.norm_eq_abs] using hC v⟩
  choose Kc hKc using hcK
  have hw0 : ∀ i, ∫ v, w v i ∂μ = 0 := wT_mean ha hK h
  have hΛw : ∀ e, ∫ v, (e ⬝ᵥ w v) ^ 2 ∂μ ≤ Λ * normSq e := wT_cov hΛ0 hΛ h
  set E : Fin m → (Fin m → ℝ) → ℝ := fun j => rowE μ (c j) w t with hEd
  set Vr : Fin m → (Fin m → ℝ) → ℝ := fun j => rowV μ (c j) w t with hVd
  set φ : Fin m → (Fin m → ℝ) → ℝ := fun j ν => E j ν - ∫ ν', E j ν' ∂ρ with hφd
  have cE : ∀ j, Continuous (E j) := fun j => by
    have hS := sqrt_rowE_euLip (μ := μ) (hc j) hw (hKc j) hKw hw0 hΛ0 hΛw ht
    exact ((hS.continuous (Real.sqrt_nonneg _)).pow 2).congr fun ν =>
      Real.sq_sqrt (rowE_nonneg t ν)
  have mφ : ∀ j, Measurable (φ j) := fun j => (cE j).measurable.sub_const _
  have iEk : ∀ j k, Integrable (fun ν => E j ν ^ k) ρ := fun j k =>
    rowE_pow_integrable (μ := μ) (hc j) hw (hKc j) hKw hw0 hΛ0 hΛw ht k
  have iφ : ∀ j k, Integrable (fun ν => |φ j ν| ^ k) ρ := fun j k =>
    int_dev (cE j).measurable (fun ν => rowE_nonneg t ν) (iEk j k) _
  have iφ8 : ∀ j, Integrable (fun ν => φ j ν ^ 8) ρ := fun j =>
    (iφ j 8).congr (Eventually.of_forall fun ν => Even.pow_abs ⟨4, rfl⟩ _)
  have iE1 : ∀ j, Integrable (E j) ρ := fun j => by simpa using iEk j 1
  have hφ0 : ∀ j, ∫ ν, φ j ν ∂ρ = 0 := fun j => by
    simp only [φ]; rw [integral_sub (iE1 j) (integrable_const _)]; simp
  have mV : ∀ j, Measurable (Vr j) := fun j => measurable_rowV (μ := μ) (hc j) hw t
  have hV0 : ∀ j ν, 0 ≤ Vr j ν := fun j ν => rowV_nonneg (hc j) hw (hKc j) hKw t ν
  have iV : ∀ j, Integrable (Vr j) ρ := fun j =>
    Integrable.mono' (iE1 j) (mV j).aestronglyMeasurable (Eventually.of_forall fun ν => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hV0 j ν)]; exact rowV_le_rowE t ν)
  -- the row identities
  have hF : ∀ y : Fin m → Fin m → ℝ, flQ μ a h M₀ (matOf t (Function.uncurry y)) =
      ∑ j, E j (y j) := by
    intro y
    unfold flQ
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [E, rowE, rowG, c, w, matOf_uncurry_mulVec]
    rfl
  have hFv : ∀ y : Fin m → Fin m → ℝ,
      BstLean.Part183.flQv μ a h M₀ (matOf t (Function.uncurry y)) = ∑ j, Vr j (y j) := by
    intro y
    unfold BstLean.Part183.flQv
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Vr, rowV, rowG, c, w, matOf_uncurry_mulVec]
    rfl
  have hW : ∀ y : Fin m → Fin m → ℝ, ∀ j, WgR μ a h M₀ t j (Function.uncurry y) =
      ∫ v, (rowG (c j) w t (y j) v - ∫ v', rowG (c j) w t (y j) v' ∂μ) ^ 2 ∂μ := by
    intro y j
    simp only [WgR, rowG, c, w, matOf_uncurry_mulVec]
  have hcomp : ∀ j {f : (Fin m → ℝ) → ℝ}, AEStronglyMeasurable f ρ →
      ∫ y, f (y j) ∂P = ∫ ν, f ν ∂ρ := fun j f hf => integral_comp_eval hf
  have icomp : ∀ j {f : (Fin m → ℝ) → ℝ}, Integrable f ρ → Integrable (fun y : Fin m → Fin m → ℝ => f (y j)) P :=
    fun j f hf => (measurePreserving_eval (fun _ : Fin m => ρ) j).integrable_comp_of_integrable hf
  have hQ : ∫ ζ, flQ μ a h M₀ (matOf t ζ) ∂stdGauss (Fin m × Fin m) = ∑ j, ∫ ν, E j ν ∂ρ := by
    rw [integral_uncurry]
    simp_rw [hF]
    rw [integral_finset_sum _ fun j _ => icomp j (iE1 j)]
    exact Finset.sum_congr rfl fun j _ => hcomp j (iE1 j).aestronglyMeasurable
  have hU : ∫ ζ, BstLean.Part183.flQv μ a h M₀ (matOf t ζ) ∂stdGauss (Fin m × Fin m) =
      ∑ j, ∫ ν, Vr j ν ∂ρ := by
    rw [integral_uncurry]
    simp_rw [hFv]
    rw [integral_finset_sum _ fun j _ => icomp j (iV j)]
    exact Finset.sum_congr rfl fun j _ => hcomp j (iV j).aestronglyMeasurable
  -- step 1: the moment expansion
  have step1 : ∫⁻ ζ, ENNReal.ofReal (|flQ μ a h M₀ (matOf t ζ) -
        ∫ ζ', flQ μ a h M₀ (matOf t ζ') ∂stdGauss (Fin m × Fin m)| ^ 8) ∂stdGauss (Fin m × Fin m) =
      ∫⁻ y, ENNReal.ofReal ((∑ j, φ j (y j)) ^ 8) ∂P := by
    rw [lintegral_uncurry]
    refine lintegral_congr fun y => ?_
    rw [hF, hQ, ← Finset.sum_sub_distrib, Even.pow_abs ⟨4, rfl⟩]
  have hmom := mom8_pi_lint ρ φ mφ iφ8 hφ0
  rw [step1]
  refine hmom.trans ?_
  -- the real moments
  set S : ℕ → ℝ := fun k => Smom ρ φ k with hS
  have S0 : ∀ k, 0 ≤ S k := fun k => Smom_nonneg ρ φ k
  have h48 : S 4 ^ 2 ≤ m * S 8 := Smom_sq_le ρ φ (k := 4) (fun j => iφ j 4) (fun j => iφ j 8)
  have h612 : S 6 ^ 2 ≤ m * S 12 := Smom_sq_le ρ φ (k := 6) (fun j => iφ j 6) (fun j => iφ j 12)
  have hpoly := poly_amgm (S0 2) (S0 4) (S0 6) (S0 8) hσ (Nat.cast_nonneg m) h48 h612
  refine (ENNReal.ofReal_le_ofReal hpoly).trans ?_
  -- S₂ ≤ 4tΛ·U₁
  set U1 := ∑ j, ∫ ν, Vr j ν ∂ρ with hU1d
  have hU10 : 0 ≤ U1 := Finset.sum_nonneg fun j _ => integral_nonneg (hV0 j)
  have hS2 : S 2 ≤ 4 * (t * Λ) * U1 := by
    simp only [S, Smom, U1, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have := row_var_sharp (μ := μ) (hc j) hw (hKc j) hKw hw0 hΛ0 hΛw ht
    simpa [φ, sq_abs] using this
  have h4tΛ : 0 ≤ 4 * (t * Λ) := by positivity
  have hJ : ENNReal.ofReal (U1 ^ 4) ≤ ∫⁻ ζ, ENNReal.ofReal
      (BstLean.Part183.flQv μ a h M₀ (matOf t ζ) ^ 4) ∂stdGauss (Fin m × Fin m) := by
    rw [lintegral_uncurry]
    simp_rw [hFv]
    have hmg : Measurable (fun y : Fin m → Fin m → ℝ => ∑ j, Vr j (y j)) :=
      Finset.measurable_sum _ fun j _ => (mV j).comp (measurable_pi_apply j)
    have := jensen4 (ρ := P) hmg (fun y => Finset.sum_nonneg fun j _ => hV0 j (y j))
    refine le_trans (le_of_eq ?_) this
    congr 2
    rw [integral_finset_sum _ fun j _ => icomp j (iV j)]
    exact (Finset.sum_congr rfl fun j _ => hcomp j (iV j).aestronglyMeasurable).symm
  -- S_{2p} through the row variances and `WgR`
  have hSp : ∀ p : ℕ, 1 ≤ p → ENNReal.ofReal (S (2 * p)) ≤
      ENNReal.ofReal ((π / 2) ^ (2 * p) * gmom (2 * p) * (4 * (t * Λ)) ^ p) *
        ∫⁻ ζ, ENNReal.ofReal (∑ j, WgR μ a h M₀ t j ζ ^ p) ∂stdGauss (Fin m × Fin m) := by
    intro p hp
    simp only [S]
    rw [ofReal_Smom ρ φ (fun j => iφ j (2 * p))]
    have hR2 : ∀ j, ∫⁻ ν, ENNReal.ofReal (|φ j ν| ^ (2 * p)) ∂ρ ≤
        ENNReal.ofReal ((π / 2) ^ (2 * p) * gmom (2 * p) * (4 * (t * Λ)) ^ p) *
          ∫⁻ ν, ENNReal.ofReal (Vr j ν ^ p) ∂ρ := fun j =>
      row_mom_p (μ := μ) (hc j) hw (hKc j) hKw hw0 hΛ0 hΛw ht hp
    refine (Finset.sum_le_sum fun j _ => hR2 j).trans ?_
    rw [← Finset.mul_sum]
    gcongr
    have mVp : ∀ j, Measurable (fun ν => ENNReal.ofReal (Vr j ν ^ p)) := fun j =>
      ENNReal.measurable_ofReal.comp ((mV j).pow_const p)
    have e1 : ∑ j, ∫⁻ ν, ENNReal.ofReal (Vr j ν ^ p) ∂ρ =
        ∫⁻ y, ∑ j, ENNReal.ofReal (Vr j (y j) ^ p) ∂P := by
      have mVc : ∀ j, Measurable (fun y : Fin m → Fin m → ℝ => ENNReal.ofReal (Vr j (y j) ^ p)) :=
        fun j => (mVp j).comp (measurable_pi_apply j)
      rw [lintegral_finset_sum (f := fun j (y : Fin m → Fin m → ℝ) =>
        ENNReal.ofReal (Vr j (y j) ^ p)) _ fun j _ => mVc j]
      exact Finset.sum_congr rfl fun j _ =>
        ((measurePreserving_eval (fun _ : Fin m => ρ) j).lintegral_comp (mVp j)).symm
    rw [e1, lintegral_uncurry]
    refine lintegral_mono fun y => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => pow_nonneg (hV0 j (y j)) p)]
    refine ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun j _ => ?_)
    rw [hW y j]
    exact pow_le_pow_left₀ (hV0 j (y j)) (rowV_le_var (hc j) hw (hKc j) hKw t (y j)) p
  have h8 := hSp 4 (by norm_num)
  have h12 := hSp 6 (by norm_num)
  norm_num only at h8 h12
  -- assembly
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hσ2 : 0 < σ ^ 2 := by positivity
  have g8 := gmom_nonneg 8
  have g12 := gmom_nonneg 12
  rw [ENNReal.ofReal_add (by have := S0 2; have := S0 8; have := S0 12; positivity) (by positivity),
    ENNReal.ofReal_add (by have := S0 2; have := S0 8; positivity)
      (by have := S0 12; positivity),
    ENNReal.ofReal_add (by have := S0 2; positivity) (by have := S0 8; positivity)]
  gcongr
  · -- the main term
    calc ENNReal.ofReal (10759 / 100 * S 2 ^ 4)
        ≤ ENNReal.ofReal (10759 / 100 * (4 * (t * Λ)) ^ 4 * U1 ^ 4) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have := pow_le_pow_left₀ (S0 2) hS2 4
          rw [mul_pow] at this
          nlinarith [pow_nonneg h4tΛ 4]
      _ = ENNReal.ofReal (10759 / 100 * (4 * (t * Λ)) ^ 4) * ENNReal.ofReal (U1 ^ 4) :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ _ := by gcongr
  · calc ENNReal.ofReal ((24563 * m + 1) * S 8)
        = ENNReal.ofReal (24563 * m + 1) * ENNReal.ofReal (S 8) := ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal (24563 * m + 1) * (ENNReal.ofReal ((π / 2) ^ 8 * gmom 8 *
            (4 * (t * Λ)) ^ 4) * ∫⁻ ζ, ENNReal.ofReal (∑ j, WgR μ a h M₀ t j ζ ^ 4)
              ∂stdGauss (Fin m × Fin m)) := by gcongr
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2; ring
  · calc ENNReal.ofReal (2800 * m / σ ^ 2 * S 12)
        = ENNReal.ofReal (2800 * m / σ ^ 2) * ENNReal.ofReal (S 12) :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal (2800 * m / σ ^ 2) * (ENNReal.ofReal ((π / 2) ^ 12 * gmom 12 *
            (4 * (t * Λ)) ^ 6) * ∫⁻ ζ, ENNReal.ofReal (∑ j, WgR μ a h M₀ t j ζ ^ 6)
              ∂stdGauss (Fin m × Fin m)) := by gcongr
      _ = _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
          congr 2; ring

end thm

end BstLean.Part184

#print axioms BstLean.Part184.flQ_rows8
