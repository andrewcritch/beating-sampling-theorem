import BstLean.Part158Defs
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Part 158 (file `Approx1`): stability of the two sides of the inequality (GP)

Do not use `sorry`, `native_decide` or `axiom`.

* `gauss_unit_push`: for a unit vector `h`, `G h` is a standard Gaussian vector.
* `swap_push`: `E_G ∫ φ(x, G e(x)) dμ = ∫ φ d(μ ⊗ γ)` for unit vectors `e(x)`.
* `gp_compare`: if (GP) holds for `f1` and `∫ |log f1 − log f2| d(μ ⊗ γ) ≤ δ`, then (GP) holds
  for `f2` up to an explicit error that tends to zero with `δ`.
-/

namespace BstLean.Part158

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134

variable {q m : ℕ}

lemma integrable_of_bdd {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {φ : α → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, |φ x| ≤ B) : Integrable φ μ :=
  Integrable.of_bound hφ.aestronglyMeasurable B
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)

lemma measurable_mulVec_const (h : Fin m → ℝ) :
    Measurable (fun G : Matrix (Fin q) (Fin m) ℝ => G.mulVec h) :=
  measurable_mulVec_joint.comp (measurable_id.prodMk measurable_const)

/-- For a unit vector `h`, `G h` is a standard Gaussian vector. -/
lemma gauss_unit_push (h : Fin m → ℝ) (hh : normSq h = 1) (φ : (Fin q → ℝ) → ℝ)
    (hφ : Measurable φ) :
    ∫ G, φ (G.mulVec h) ∂gaussMat q m 1 = ∫ z, φ z ∂stdGauss (Fin q) := by
  have h1 := gaussMat_mulVec (m := q) 1 h
  rw [hh, Real.sqrt_one, mul_one] at h1
  simp only [one_smul] at h1
  rw [Measure.map_id'] at h1
  rw [← h1, integral_map (measurable_mulVec_const h).aemeasurable hφ.aestronglyMeasurable]

/-- `E_G ∫ φ(x, G e(x)) dμ = ∫ φ d(μ ⊗ γ)` for unit vectors `e(x)`. -/
lemma swap_push {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (e : X → Fin m → ℝ) (he : Measurable e) (hunit : ∀ x, normSq (e x) = 1)
    (φ : X × (Fin q → ℝ) → ℝ) (hφ : Measurable φ) {B : ℝ} (hB : ∀ y, |φ y| ≤ B) :
    ∫ G, ∫ x, φ (x, G.mulVec (e x)) ∂μ ∂gaussMat q m 1 =
      ∫ y, φ y ∂(μ.prod (stdGauss (Fin q))) := by
  have mJ : Measurable (fun p : Matrix (Fin q) (Fin m) ℝ × X => φ (p.2, p.1.mulVec (e p.2))) :=
    hφ.comp (measurable_snd.prodMk (measurable_mulVec_joint.comp
      (measurable_fst.prodMk (he.comp measurable_snd))))
  have iJ : Integrable (Function.uncurry fun (G : Matrix (Fin q) (Fin m) ℝ) (x : X) =>
      φ (x, G.mulVec (e x))) ((gaussMat q m 1).prod μ) :=
    integrable_of_bdd mJ (fun p => hB _)
  rw [integral_integral_swap iJ, integral_prod _ (integrable_of_bdd hφ hB)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  exact gauss_unit_push (e x) (hunit x) (fun z => φ (x, z)) (hφ.comp measurable_prodMk_left)

/-- **Stability of (GP).** -/
lemma gp_compare {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (e : X → Fin m → ℝ) (he : Measurable e) (hunit : ∀ x, normSq (e x) = 1)
    (f1 f2 : X × (Fin q → ℝ) → ℝ) (m1 : Measurable f1) (m2 : Measurable f2) {a0 b0 B : ℝ}
    (ha0 : 0 < a0) (hab : a0 ≤ b0) (l1 : ∀ y, a0 ≤ f1 y) (u1 : ∀ y, f1 y ≤ b0) (l2 : ∀ y, a0 ≤ f2 y)
    (u2 : ∀ y, f2 y ≤ b0) (B1 : ∀ y, |log (f1 y)| ≤ B) (B2 : ∀ y, |log (f2 y)| ≤ B)
    {L : ℝ} (hL : 0 < L) {δ : ℝ}
    (hδ : ∫ y, |log (f1 y) - log (f2 y)| ∂(μ.prod (stdGauss (Fin q))) ≤ δ)
    (h1 : ∫ G, exp (1 / L * ∫ x, log (f1 (x, G.mulVec (e x))) ∂μ) ∂gaussMat q m 1 ≤
      exp (1 / L * ∫ x, log (∫ z, f1 (x, z) ∂stdGauss (Fin q)) ∂μ)) :
    ∫ G, exp (1 / L * ∫ x, log (f2 (x, G.mulVec (e x))) ∂μ) ∂gaussMat q m 1 ≤
      exp (1 / L * ∫ x, log (∫ z, f2 (x, z) ∂stdGauss (Fin q)) ∂μ) *
          exp (1 / L * (b0 / a0) * δ) +
        exp (1 / L * (B * μ.real Set.univ)) * (1 / L) * δ := by
  set φ : X × (Fin q → ℝ) → ℝ := fun y => |log (f1 y) - log (f2 y)| with hφ
  have mφ : Measurable φ := (m1.log.sub m2.log).abs
  have φ0 : ∀ y, 0 ≤ φ y := fun y => abs_nonneg _
  have φB : ∀ y, |φ y| ≤ 2 * B := by
    intro y
    simp only [hφ, abs_abs]
    have := abs_sub (log (f1 y)) (log (f2 y))
    linarith [B1 y, B2 y]
  have mK : Measurable (fun p : Matrix (Fin q) (Fin m) ℝ × X => (p.2, p.1.mulVec (e p.2))) :=
    measurable_snd.prodMk (measurable_mulVec_joint.comp
      (measurable_fst.prodMk (he.comp measurable_snd)))
  have hM0 : 0 ≤ μ.real Set.univ := measureReal_nonneg
  -- the exponents
  have key : ∀ (g : X × (Fin q → ℝ) → ℝ), Measurable g → (∀ y, |g y| ≤ B) →
      Measurable (fun G : Matrix (Fin q) (Fin m) ℝ => ∫ x, g (x, G.mulVec (e x)) ∂μ) ∧
      (∀ G : Matrix (Fin q) (Fin m) ℝ, |∫ x, g (x, G.mulVec (e x)) ∂μ| ≤ B * μ.real Set.univ) ∧
      (∀ G : Matrix (Fin q) (Fin m) ℝ, Integrable (fun x => g (x, G.mulVec (e x))) μ) := by
    intro g mg gB
    refine ⟨?_, ?_, ?_⟩
    · exact ((mg.comp mK).stronglyMeasurable.integral_prod_right').measurable
    · intro G
      have := norm_integral_le_of_norm_le_const (μ := μ)
        (f := fun x => g (x, G.mulVec (e x))) (C := B)
        (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact gB _)
      rwa [Real.norm_eq_abs] at this
    · intro G
      exact integrable_of_bdd ((mg.comp mK).comp measurable_prodMk_left) (fun x => gB _)
  obtain ⟨mT1, bT1, iT1⟩ := key (fun y => log (f1 y)) m1.log B1
  obtain ⟨mT2, bT2, iT2⟩ := key (fun y => log (f2 y)) m2.log B2
  have mD : Measurable (fun G : Matrix (Fin q) (Fin m) ℝ => ∫ x, φ (x, G.mulVec (e x)) ∂μ) :=
    ((mφ.comp mK).stronglyMeasurable.integral_prod_right').measurable
  have bD : ∀ G : Matrix (Fin q) (Fin m) ℝ,
      |∫ x, φ (x, G.mulVec (e x)) ∂μ| ≤ 2 * B * μ.real Set.univ := by
    intro G
    have := norm_integral_le_of_norm_le_const (μ := μ)
      (f := fun x => φ (x, G.mulVec (e x))) (C := 2 * B)
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact φB _)
    rwa [Real.norm_eq_abs] at this
  have iφ : ∀ G : Matrix (Fin q) (Fin m) ℝ, Integrable (fun x => φ (x, G.mulVec (e x))) μ :=
    fun G => integrable_of_bdd ((mφ.comp mK).comp measurable_prodMk_left) (fun x => φB _)
  have hLi : 0 < 1 / L := by positivity
  set M := 1 / L * (B * μ.real Set.univ) with hM
  -- pointwise bound on the left
  have pw : ∀ G : Matrix (Fin q) (Fin m) ℝ,
      exp (1 / L * ∫ x, log (f2 (x, G.mulVec (e x))) ∂μ) ≤
        exp (1 / L * ∫ x, log (f1 (x, G.mulVec (e x))) ∂μ) +
          exp M * (1 / L) * ∫ x, φ (x, G.mulVec (e x)) ∂μ := by
    intro G
    set t1 := 1 / L * ∫ x, log (f1 (x, G.mulVec (e x))) ∂μ with ht1
    set t2 := 1 / L * ∫ x, log (f2 (x, G.mulVec (e x))) ∂μ with ht2
    set r := 1 / L * ∫ x, φ (x, G.mulVec (e x)) ∂μ with hr
    have hr0 : 0 ≤ r := mul_nonneg hLi.le (integral_nonneg fun x => φ0 _)
    have hd : t2 - t1 ≤ r := by
      rw [ht1, ht2, hr, ← mul_sub, ← integral_sub (iT2 G) (iT1 G)]
      refine mul_le_mul_of_nonneg_left ?_ hLi.le
      refine integral_mono ((iT2 G).sub (iT1 G)) (iφ G) fun x => ?_
      simp only [hφ]
      rw [abs_sub_comm]
      exact le_abs_self _
    have ht2M : t2 ≤ M := by
      rw [ht2, hM]
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (bT2 G)) hLi.le
    have h3 := Real.add_one_le_exp (t1 - t2)
    have h4 : exp t1 = exp t2 * exp (t1 - t2) := by rw [← Real.exp_add]; congr 1; ring
    have h5 : exp t2 * (t2 - t1) ≤ exp M * r := by
      have e2 : 0 < exp t2 := exp_pos _
      have eM : exp t2 ≤ exp M := exp_le_exp.mpr ht2M
      calc exp t2 * (t2 - t1) ≤ exp t2 * r := mul_le_mul_of_nonneg_left hd e2.le
        _ ≤ exp M * r := mul_le_mul_of_nonneg_right eM hr0
    have h6 : exp t2 * (t1 - t2 + 1) ≤ exp t1 := by
      rw [h4]; exact mul_le_mul_of_nonneg_left h3 (exp_pos _).le
    have : exp M * (1 / L) * ∫ x, φ (x, G.mulVec (e x)) ∂μ = exp M * r := by rw [hr]; ring
    rw [this]
    nlinarith
  have iE : ∀ (g : Matrix (Fin q) (Fin m) ℝ → ℝ), Measurable g →
      (∀ G, |g G| ≤ B * μ.real Set.univ) →
      Integrable (fun G => exp (1 / L * g G)) (gaussMat q m 1) := by
    intro g mg gb
    refine integrable_of_bdd (B := exp M) (mg.const_mul _).exp fun G => ?_
    rw [abs_of_pos (exp_pos _)]
    refine exp_le_exp.mpr ?_
    rw [hM]
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (gb G)) hLi.le
  have iD : Integrable (fun G : Matrix (Fin q) (Fin m) ℝ => ∫ x, φ (x, G.mulVec (e x)) ∂μ)
      (gaussMat q m 1) := integrable_of_bdd mD bD
  have left : ∫ G, exp (1 / L * ∫ x, log (f2 (x, G.mulVec (e x))) ∂μ) ∂gaussMat q m 1 ≤
      ∫ G, exp (1 / L * ∫ x, log (f1 (x, G.mulVec (e x))) ∂μ) ∂gaussMat q m 1 +
        exp M * (1 / L) * ∫ y, φ y ∂(μ.prod (stdGauss (Fin q))) := by
    rw [← swap_push μ e he hunit φ mφ φB, ← integral_const_mul,
      ← integral_add (iE _ mT1 bT1) (iD.const_mul _)]
    exact integral_mono (iE _ mT2 bT2) ((iE _ mT1 bT1).add (iD.const_mul _)) pw
  -- the right side
  have hb0 : 0 < b0 := lt_of_lt_of_le ha0 hab
  have mE : ∀ g : X × (Fin q → ℝ) → ℝ, Measurable g →
      Measurable (fun x => ∫ z, g (x, z) ∂stdGauss (Fin q)) :=
    fun g mg => (mg.stronglyMeasurable.integral_prod_right').measurable
  have iz : ∀ (g : X × (Fin q → ℝ) → ℝ), Measurable g → ∀ C : ℝ, (∀ y, |g y| ≤ C) → ∀ x,
      Integrable (fun z => g (x, z)) (stdGauss (Fin q)) :=
    fun g mg C hC x => integrable_of_bdd (mg.comp measurable_prodMk_left) (fun z => hC _)
  have fb : ∀ f : X × (Fin q → ℝ) → ℝ, (∀ y, a0 ≤ f y) → (∀ y, f y ≤ b0) → ∀ y, |f y| ≤ b0 := by
    intro f lo hi y
    rw [abs_le]
    exact ⟨by linarith [lo y], hi y⟩
  have El : ∀ f : X × (Fin q → ℝ) → ℝ, Measurable f → (∀ y, a0 ≤ f y) → (∀ y, f y ≤ b0) → ∀ x,
      a0 ≤ ∫ z, f (x, z) ∂stdGauss (Fin q) ∧ ∫ z, f (x, z) ∂stdGauss (Fin q) ≤ b0 := by
    intro f mf lo hi x
    have i := iz f mf b0 (fb f lo hi) x
    have h1 := integral_mono (integrable_const a0) i (fun z => lo (x, z))
    have h2 := integral_mono i (integrable_const b0) (fun z => hi (x, z))
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h1 h2
    exact ⟨h1, h2⟩
  have iφz := iz φ mφ (2 * B) φB
  have pr : ∀ x, log (∫ z, f1 (x, z) ∂stdGauss (Fin q)) ≤
      log (∫ z, f2 (x, z) ∂stdGauss (Fin q)) + b0 / a0 * ∫ z, φ (x, z) ∂stdGauss (Fin q) := by
    intro x
    obtain ⟨a1, c1⟩ := El f1 m1 l1 u1 x
    obtain ⟨a2, c2⟩ := El f2 m2 l2 u2 x
    set E1 := ∫ z, f1 (x, z) ∂stdGauss (Fin q) with hE1
    set E2 := ∫ z, f2 (x, z) ∂stdGauss (Fin q) with hE2
    set I := ∫ z, φ (x, z) ∂stdGauss (Fin q) with hI
    have hI0 : 0 ≤ I := integral_nonneg fun z => φ0 _
    have hd : E1 - E2 ≤ b0 * I := by
      rw [hE1, hE2, hI, ← integral_sub (iz f1 m1 b0 (fb f1 l1 u1) x) (iz f2 m2 b0 (fb f2 l2 u2) x),
        ← integral_const_mul]
      refine integral_mono ((iz f1 m1 b0 (fb f1 l1 u1) x).sub (iz f2 m2 b0 (fb f2 l2 u2) x))
        ((iφz x).const_mul _) fun z => ?_
      have p1 : 0 < f1 (x, z) := lt_of_lt_of_le ha0 (l1 _)
      have p2 : 0 < f2 (x, z) := lt_of_lt_of_le ha0 (l2 _)
      set u := log (f1 (x, z)) with hu
      set v := log (f2 (x, z)) with hv
      have eu : f1 (x, z) = exp u := (exp_log p1).symm
      have ev : f2 (x, z) = exp v := (exp_log p2).symm
      have h3 := Real.add_one_le_exp (v - u)
      have h4 : exp v = exp u * exp (v - u) := by rw [← Real.exp_add]; congr 1; ring
      have h6 : exp u * (v - u + 1) ≤ exp v := by
        rw [h4]; exact mul_le_mul_of_nonneg_left h3 (exp_pos _).le
      have h7 : exp u * (u - v) ≤ b0 * |u - v| := by
        calc exp u * (u - v) ≤ exp u * |u - v| :=
              mul_le_mul_of_nonneg_left (le_abs_self _) (exp_pos _).le
          _ ≤ b0 * |u - v| := mul_le_mul_of_nonneg_right (by rw [← eu]; exact u1 _) (abs_nonneg _)
      change f1 (x, z) - f2 (x, z) ≤ b0 * |u - v|
      rw [eu, ev]
      nlinarith
    have pE1 : 0 < E1 := lt_of_lt_of_le ha0 a1
    have pE2 : 0 < E2 := lt_of_lt_of_le ha0 a2
    have h8 : log E1 - log E2 ≤ E1 / E2 - 1 := by
      rw [← Real.log_div pE1.ne' pE2.ne']
      exact Real.log_le_sub_one_of_pos (div_pos pE1 pE2)
    have h9 : E1 / E2 - 1 ≤ b0 / a0 * I := by
      have : E1 / E2 - 1 = (E1 - E2) / E2 := by field_simp
      rw [this]
      calc (E1 - E2) / E2 ≤ b0 * I / E2 := div_le_div_of_nonneg_right hd pE2.le
        _ ≤ b0 * I / a0 := div_le_div_of_nonneg_left (mul_nonneg hb0.le hI0) ha0 a2
        _ = b0 / a0 * I := by ring
    linarith
  have iLog : ∀ f : X × (Fin q → ℝ) → ℝ, Measurable f → (∀ y, a0 ≤ f y) → (∀ y, f y ≤ b0) →
      Integrable (fun x => log (∫ z, f (x, z) ∂stdGauss (Fin q))) μ := by
    intro f mf lo hi
    refine integrable_of_bdd (B := |log a0| + |log b0|) (mE f mf).log fun x => ?_
    obtain ⟨a1, c1⟩ := El f mf lo hi x
    have g1 := Real.log_le_log ha0 a1
    have g2 := Real.log_le_log (lt_of_lt_of_le ha0 a1) c1
    rw [abs_le]
    constructor
    · linarith [neg_abs_le (log a0), abs_nonneg (log b0)]
    · linarith [le_abs_self (log b0), abs_nonneg (log a0)]
  have iφ2 : Integrable φ (μ.prod (stdGauss (Fin q))) := integrable_of_bdd mφ φB
  have right : ∫ x, log (∫ z, f1 (x, z) ∂stdGauss (Fin q)) ∂μ ≤
      ∫ x, log (∫ z, f2 (x, z) ∂stdGauss (Fin q)) ∂μ +
        b0 / a0 * ∫ y, φ y ∂(μ.prod (stdGauss (Fin q))) := by
    rw [integral_prod _ iφ2, ← integral_const_mul,
      ← integral_add (iLog f2 m2 l2 u2) (iφ2.integral_prod_left.const_mul _)]
    exact integral_mono (iLog f1 m1 l1 u1)
      ((iLog f2 m2 l2 u2).add (iφ2.integral_prod_left.const_mul _)) pr
  have hφδ0 : 0 ≤ ∫ y, φ y ∂(μ.prod (stdGauss (Fin q))) := integral_nonneg φ0
  have hc0 : 0 ≤ b0 / a0 := (div_pos hb0 ha0).le
  have rgt : exp (1 / L * ∫ x, log (∫ z, f1 (x, z) ∂stdGauss (Fin q)) ∂μ) ≤
      exp (1 / L * ∫ x, log (∫ z, f2 (x, z) ∂stdGauss (Fin q)) ∂μ) *
        exp (1 / L * (b0 / a0) * δ) := by
    rw [← Real.exp_add]
    refine exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left right hLi.le
    have h2 : 1 / L * (b0 / a0 * ∫ y, φ y ∂(μ.prod (stdGauss (Fin q)))) ≤
        1 / L * (b0 / a0 * δ) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδ hc0) hLi.le
    linarith
  have hcδ : exp M * (1 / L) * ∫ y, φ y ∂(μ.prod (stdGauss (Fin q))) ≤ exp M * (1 / L) * δ :=
    mul_le_mul_of_nonneg_left hδ (mul_nonneg (exp_pos _).le hLi.le)
  linarith

end BstLean.Part158
