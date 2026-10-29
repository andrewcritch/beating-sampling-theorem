import BstLean.Part167Fin

/-!
# Part 167 (file `Y`): the masked Frobenius moment `Y` (sub-lemma 6, second half)

No proof is left open; no `native_decide` or `axiom` is used.

* **`frob_le_Q`**: `‖P_lat(D₁A₁)ᵀ‖²_F ≤ Q(A₁) = Σ_i D_i(|a_i|² − ⟨a_i, x⟩²)` for an orthonormal
  pair `(u, w)` and `x = su + cw`, `s² + c² = 1` (no frame is needed for this bound).
-/

namespace BstLean.Part167

open MeasureTheory ProbabilityTheory Real Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part151 (mask mask_nonneg mask_sq measurable_mask)

variable {n m : ℕ}

/-- `Q(A₁) = Σ_i D_i(|a_i|² − ⟨a_i, x⟩²)`. -/
noncomputable def Qf (A₁ : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, mask ((A₁ *ᵥ x) i) * (normSq (A₁ i) - (∑ j, A₁ i j * x j) ^ 2)

/-- **`‖P_lat(D₁A₁)ᵀ‖²_F ≤ Q(A₁)`.** -/
theorem frob_le_Q {u w : Fin n → ℝ} (hu : normSq u = 1) (hw : normSq w = 1)
    (huw : ∑ i, u i * w i = 0) {s c : ℝ} (hsc : s ^ 2 + c ^ 2 = 1) (A₁ : Matrix (Fin m) (Fin n) ℝ) :
    frobSq (Pmat u w * (D1A1 A₁ (s • u + c • w))ᵀ) ≤ Qf A₁ (s • u + c • w) := by
  set x := s • u + c • w
  have hrow : frobSq (Pmat u w * (D1A1 A₁ x)ᵀ) = ∑ i, normSq (Pmat u w *ᵥ (D1A1 A₁ x i)) := by
    unfold frobSq normSq
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [hrow]
  unfold Qf
  refine Finset.sum_le_sum fun i _ => ?_
  have hD : D1A1 A₁ x i = mask ((A₁ *ᵥ x) i) • A₁ i := by
    funext l; simp [D1A1]
  rw [hD, ← latSq_eq hu hw huw]
  have hs : latSq (mask ((A₁ *ᵥ x) i) • A₁ i) u w = mask ((A₁ *ᵥ x) i) * latSq (A₁ i) u w := by
    rw [latSq_smul, mask_sq]
  rw [hs]
  refine mul_le_mul_of_nonneg_left ?_ (mask_nonneg _)
  unfold latSq
  set a := A₁ i
  have hx : ∑ j, a j * x j = s * ∑ j, a j * u j + c * ∑ j, a j * w j := by
    simp only [x, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun j _ => by ring
  rw [hx]
  have hcs : (s * ∑ j, a j * u j + c * ∑ j, a j * w j) ^ 2 ≤
      (∑ j, a j * u j) ^ 2 + (∑ j, a j * w j) ^ 2 := by
    nlinarith [sq_nonneg (s * ∑ j, a j * w j - c * ∑ j, a j * u j)]
  unfold normSq
  linarith

/-! ## One row -/

/-- `q(g) = D(g)(|g|² − ⟨g, x⟩²)` for one standardized row. -/
noncomputable def qrow (x g : Fin n → ℝ) : ℝ :=
  mask (∑ j, g j * x j) * (normSq g - (∑ j, g j * x j) ^ 2)

lemma qrow_hh (hn : 1 ≤ n) {x : Fin n → ℝ} (hx : normSq x = 1) (g : Fin n → ℝ) :
    qrow x ((BstLean.Part161.hhMat x).mulVec g) = mask (g ⟨0, by omega⟩) *
      (normSq g - g ⟨0, by omega⟩ ^ 2) := by
  have hd := BstLean.Part161.hh_dot x g (e0 n)
  rw [BstLean.Part161.hh_e0 hn hx] at hd
  have he : ∑ i, g i * e0 n i = g ⟨0, by omega⟩ := by
    rw [Finset.sum_eq_single ⟨0, by omega⟩]
    · simp [e0]
    · intro b _ hb
      have : (b : ℕ) ≠ 0 := fun h => hb (Fin.ext h)
      simp [e0, this]
    · simp
  rw [he] at hd
  unfold qrow
  rw [hd, BstLean.Part161.hh_normSq]

lemma qrow_nonneg_le (x g : Fin n → ℝ) (hx : normSq x = 1) : 0 ≤ qrow x g ∧ qrow x g ≤ normSq g := by
  have hcs : (∑ j, g j * x j) ^ 2 ≤ normSq g := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ g x
    unfold normSq at hx ⊢; rw [hx, mul_one] at this; exact this
  have h1 : mask (∑ j, g j * x j) ≤ 1 := mask_le_one _
  have h0 := mask_nonneg (∑ j, g j * x j)
  unfold qrow
  constructor
  · exact mul_nonneg h0 (by linarith)
  · have : 0 ≤ (∑ j, g j * x j) ^ 2 := sq_nonneg _
    nlinarith

lemma measurable_qrow (x : Fin n → ℝ) : Measurable (qrow x) := by
  unfold qrow
  have hs : Measurable (fun g : Fin n → ℝ => ∑ j, g j * x j) :=
    Continuous.measurable (by fun_prop)
  exact (measurable_mask.comp hs).mul
    ((Continuous.measurable (by unfold normSq; fun_prop)).sub (hs.pow_const 2))

/-- **One row**: `E exp(t·q(g)) ≤ (1 + φ₁(t)^{n−1})/2`. -/
theorem row_int (hn : 1 ≤ n) {x : Fin n → ℝ} (hx : normSq x = 1) {t : ℝ} (ht : 0 ≤ t)
    (ht2 : t < 1 / 2) :
    Integrable (fun g : Fin n → ℝ => exp (t * qrow x g)) (stdGauss (Fin n)) ∧
    ∫ g, exp (t * qrow x g) ∂stdGauss (Fin n) ≤ (1 + phi1 t ^ (n - 1)) / 2 := by
  have hmq : Measurable (fun g : Fin n → ℝ => exp (t * qrow x g)) :=
    continuous_exp.measurable.comp ((measurable_qrow x).const_mul t)
  -- integrability
  obtain ⟨hIq, -⟩ := int_exp_quad (m := n) (fun _ => 1) (t := t) (fun _ => by linarith)
  have hInt : Integrable (fun g : Fin n → ℝ => exp (t * qrow x g)) (stdGauss (Fin n)) := by
    refine hIq.mono' hmq.aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    have := (qrow_nonneg_le x g hx).2
    have e : ∑ j, (1 : ℝ) * g j ^ 2 = normSq g := by unfold normSq; simp
    rw [e]; exact mul_le_mul_of_nonneg_left this ht
  refine ⟨hInt, ?_⟩
  -- the reflection
  have hH := BstLean.Part161.stdGauss_map_hh x
  have hHm := BstLean.Part161.measurable_hh x
  have e1 : ∫ g, exp (t * qrow x g) ∂stdGauss (Fin n) =
      ∫ g, exp (t * qrow x ((BstLean.Part161.hhMat x).mulVec g)) ∂stdGauss (Fin n) := by
    conv_lhs => rw [← hH]
    rw [integral_map hHm.aemeasurable hmq.aestronglyMeasurable]
  rw [e1]
  simp_rw [qrow_hh hn hx]
  -- the coordinate split
  have hC := BstLean.Part161.consV_map hn
  have hCm : Measurable (fun p : ℝ × (Fin (n - 1) → ℝ) => BstLean.Part161.consV (n := n) p.1 p.2) :=
    BstLean.Part161.measurable_consV.comp measurable_id
  set φf : (Fin n → ℝ) → ℝ := fun g => exp (t * (mask (g ⟨0, by omega⟩) *
      (normSq g - g ⟨0, by omega⟩ ^ 2))) with hφf
  have hφm : Measurable φf := by
    refine continuous_exp.measurable.comp (Measurable.const_mul ?_ t)
    exact (measurable_mask.comp (measurable_pi_apply _)).mul
      ((Continuous.measurable (by unfold normSq; fun_prop)).sub
        ((measurable_pi_apply _).pow_const 2))
  have e2 : ∫ g, φf g ∂stdGauss (Fin n) =
      ∫ p, φf (BstLean.Part161.consV p.1 p.2) ∂(gaussianReal 0 1).prod (stdGauss (Fin (n - 1))) := by
    conv_lhs => rw [← hC]
    rw [integral_map hCm.aemeasurable hφm.aestronglyMeasurable]
  change ∫ g, φf g ∂stdGauss (Fin n) ≤ _
  rw [e2]
  have hval : ∀ p : ℝ × (Fin (n - 1) → ℝ), φf (BstLean.Part161.consV p.1 p.2) =
      exp (t * mask p.1 * ∑ j, p.2 j ^ 2) := by
    intro p
    simp only [hφf, BstLean.Part161.consV_zero hn, BstLean.Part161.normSq_consV hn]
    congr 1; unfold normSq; ring
  simp_rw [hval]
  -- integrate
  have hinner : ∀ z : ℝ, ∫ G, exp (t * mask z * ∑ j, G j ^ 2) ∂stdGauss (Fin (n - 1)) =
      (√(1 - 2 * (t * mask z)))⁻¹ ^ (n - 1) := by
    intro z
    have hta : ∀ j : Fin (n - 1), t * mask z < 1 / 2 := fun j =>
      lt_of_le_of_lt (mul_le_of_le_one_right ht (mask_le_one z)) ht2
    obtain ⟨-, hE⟩ := int_exp_quad (m := n - 1) (fun _ => mask z) (t := t) (fun j => by
      have := hta j; linarith [mul_le_of_le_one_right ht (mask_le_one z)])
    have e : ∀ G : Fin (n - 1) → ℝ, t * mask z * ∑ j, G j ^ 2 = t * ∑ j, mask z * G j ^ 2 := by
      intro G; rw [mul_assoc, Finset.mul_sum]
    simp_rw [e]
    rw [hE, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hψ : ∀ z : ℝ, (√(1 - 2 * (t * mask z)))⁻¹ ^ (n - 1) = 1 + mask z * (phi1 t ^ (n - 1) - 1) := by
    intro z; unfold phi1
    by_cases h : 0 < z
    · rw [BstLean.Part151.mask_of_pos h]; ring_nf
    · rw [BstLean.Part151.mask_of_nonpos (not_lt.mp h)]; simp
  have hprodInt : Integrable (fun p : ℝ × (Fin (n - 1) → ℝ) => exp (t * mask p.1 * ∑ j, p.2 j ^ 2))
      ((gaussianReal 0 1).prod (stdGauss (Fin (n - 1)))) := by
    obtain ⟨hIq', -⟩ := int_exp_quad (m := n - 1) (fun _ => 1) (t := t) (fun _ => by linarith)
    have h2 : Integrable (fun p : ℝ × (Fin (n - 1) → ℝ) => exp (t * ∑ j, (1 : ℝ) * p.2 j ^ 2))
        ((gaussianReal 0 1).prod (stdGauss (Fin (n - 1)))) := hIq'.comp_snd _
    have hm : Measurable (fun p : ℝ × (Fin (n - 1) → ℝ) => exp (t * mask p.1 * ∑ j, p.2 j ^ 2)) :=
      continuous_exp.measurable.comp (((measurable_mask.comp measurable_fst).const_mul t).mul
        (Finset.measurable_sum _ fun j _ => ((measurable_pi_apply j).comp measurable_snd).pow_const 2))
    refine h2.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    apply exp_le_exp.mpr
    have hS : 0 ≤ ∑ j, p.2 j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have e : ∑ j, (1 : ℝ) * p.2 j ^ 2 = ∑ j, p.2 j ^ 2 := by simp
    rw [e]
    have := mask_le_one p.1
    have := mask_nonneg p.1
    nlinarith [mul_nonneg ht hS]
  rw [integral_prod _ hprodInt]
  simp_rw [hinner, hψ]
  rw [integral_add (integrable_const _) (integrable_mask.mul_const _), integral_mul_const]
  have h1 : 1 ≤ phi1 t ^ (n - 1) := one_le_pow₀ (phi1_ge_one ht ht2)
  have h2 := int_mask_le
  simp
  nlinarith

/-! ## All rows -/

lemma gaussMat_rows (γ : ℝ) :
    gaussMat m n γ = (Measure.pi fun _ : Fin m => stdGauss (Fin n)).map
      (fun G => Matrix.of fun i j => √γ * G i j) := by
  unfold gaussMat
  rw [← BstLean.Part162.rows_map (m := m) (d := n)]
  have h1 : Measurable (fun Z : Fin m × Fin n → ℝ => fun i j => Z (i, j)) :=
    (by fun_prop : Continuous (fun Z : Fin m × Fin n → ℝ => fun i j => Z (i, j))).measurable
  have h2 : Measurable (fun G : Fin m → Fin n → ℝ => Matrix.of fun i j => √γ * G i j) :=
    by
      have hc : Continuous (fun G : Fin m → Fin n → ℝ => fun i j => √γ * G i j) := by fun_prop
      exact hc.measurable
  rw [Measure.map_map h2 h1]
  rfl

lemma Qf_scale {γ : ℝ} (hγ : 0 < γ) (G : Fin m → Fin n → ℝ) (x : Fin n → ℝ) :
    Qf (Matrix.of fun i j => √γ * G i j) x = γ * ∑ i, qrow x (G i) := by
  unfold Qf qrow
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hs : 0 < √γ := Real.sqrt_pos.mpr hγ
  have e1 : (Matrix.of (fun i j => √γ * G i j) *ᵥ x) i = √γ * ∑ j, G i j * x j := by
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j, (Matrix.of (fun i j => √γ * G i j)) i j * x j = √γ * ∑ j, G i j * x j := by
    simp only [Matrix.of_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : normSq ((Matrix.of fun i j => √γ * G i j) i) = γ * normSq (G i) := by
    unfold normSq; simp only [Matrix.of_apply, mul_pow, Real.sq_sqrt hγ.le, Finset.mul_sum]
  rw [e1, e2, e3, BstLean.Part153.mask_mul_pos hs, mul_pow, Real.sq_sqrt hγ.le]
  ring

/-- **All rows**: `E exp(t·Q) ≤ ((1 + φ₁(tγ)^{n−1})/2)^m`. -/
theorem Q_int (hn : 1 ≤ n) {x : Fin n → ℝ} (hx : normSq x = 1) {γ t : ℝ} (hγ : 0 < γ) (ht : 0 ≤ t)
    (ht2 : t * γ < 1 / 2) :
    Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => exp (t * Qf A x)) (gaussMat m n γ) ∧
    ∫ A, exp (t * Qf A x) ∂gaussMat m n γ ≤ ((1 + phi1 (t * γ) ^ (n - 1)) / 2) ^ m := by
  obtain ⟨hI1, hE1⟩ := row_int hn hx (mul_nonneg ht hγ.le) ht2
  have hS : Measurable (fun G : Fin m → Fin n → ℝ => Matrix.of fun i j => √γ * G i j) :=
    by
      have hc : Continuous (fun G : Fin m → Fin n → ℝ => fun i j => √γ * G i j) := by fun_prop
      exact hc.measurable
  have hQm : Measurable (fun A : Matrix (Fin m) (Fin n) ℝ => exp (t * Qf A x)) := by
    refine continuous_exp.measurable.comp (Measurable.const_mul ?_ t)
    unfold Qf
    refine Finset.measurable_sum _ fun i _ => ?_
    have hc1 : Continuous (fun A : Matrix (Fin m) (Fin n) ℝ => (A *ᵥ x) i) := by
      simp only [mulVec, dotProduct]; fun_prop
    have hc2 : Continuous (fun A : Matrix (Fin m) (Fin n) ℝ =>
        normSq (A i) - (∑ j, A i j * x j) ^ 2) := by
      unfold normSq; fun_prop
    exact (measurable_mask.comp hc1.measurable).mul hc2.measurable
  have hprod : ∀ G : Fin m → Fin n → ℝ, exp (t * Qf (Matrix.of fun i j => √γ * G i j) x) =
      ∏ i, exp ((t * γ) * qrow x (G i)) := by
    intro G
    rw [Qf_scale hγ, ← Real.exp_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1; exact Finset.sum_congr rfl fun i _ => by ring
  rw [gaussMat_rows γ]
  constructor
  · rw [integrable_map_measure hQm.aestronglyMeasurable hS.aemeasurable]
    simp only [Function.comp_def]
    simp_rw [hprod]
    exact Integrable.fintype_prod (f := fun _ g => exp ((t * γ) * qrow x g)) (fun _ => hI1)
  · rw [integral_map hS.aemeasurable hQm.aestronglyMeasurable]
    simp_rw [hprod]
    rw [integral_fintype_prod_eq_pow (fun g => exp ((t * γ) * qrow x g)), Fintype.card_fin]
    exact pow_le_pow_left₀ (integral_nonneg fun g => (exp_pos _).le) hE1 m

lemma Qf_eq (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) : Qf A x = ∑ i, qrow x (A i) := rfl

lemma Qf_nonneg (A : Matrix (Fin m) (Fin n) ℝ) {x : Fin n → ℝ} (hx : normSq x = 1) : 0 ≤ Qf A x := by
  rw [Qf_eq]; exact Finset.sum_nonneg fun i _ => (qrow_nonneg_le x (A i) hx).1

/-- **The moment of `Q`** from the moment generating function. -/
theorem Q_mom (hn : 1 ≤ n) {x : Fin n → ℝ} (hx : normSq x = 1) {γ M : ℝ} (hγ : 0 < γ) (hM : 0 < M)
    (h2 : 64 / M * γ < 1 / 2)
    (hnum : ((1 + phi1 (64 / M * γ) ^ (n - 1)) / 2) ^ m ≤ exp 64) :
    ∫⁻ A, ENNReal.ofReal (Qf A x ^ 64) ∂gaussMat m n γ ≤ ENNReal.ofReal (M ^ 64) := by
  have ht : 0 ≤ 64 / M := by positivity
  obtain ⟨hI, hE⟩ := Q_int (m := m) hn hx hγ ht h2
  have hpt : ∀ A : Matrix (Fin m) (Fin n) ℝ, ENNReal.ofReal (Qf A x ^ 64) ≤
      ENNReal.ofReal ((M / exp 1) ^ 64 * exp (64 / M * Qf A x)) := fun A =>
    ENNReal.ofReal_le_ofReal (BstLean.Part166.pow_le_exp_bound (Qf_nonneg A hx) hM 64)
  refine (lintegral_mono hpt).trans ?_
  have hInt : Integrable (fun A : Matrix (Fin m) (Fin n) ℝ => (M / exp 1) ^ 64 *
      exp (64 / M * Qf A x)) (gaussMat m n γ) := hI.const_mul _
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun A => by positivity),
    integral_const_mul]
  apply ENNReal.ofReal_le_ofReal
  calc (M / exp 1) ^ 64 * ∫ A, exp (64 / M * Qf A x) ∂gaussMat m n γ
      ≤ (M / exp 1) ^ 64 * exp 64 :=
        mul_le_mul_of_nonneg_left (hE.trans hnum) (by positivity)
    _ = M ^ 64 := by
        rw [div_pow, ← Real.exp_nat_mul, mul_one]; field_simp; norm_num

/-- **The numerics of `Y`**: for `d ≥ 8`, `m ≥ 10⁵`, `N = md/2`, `τ = 64/(1.001N)`:
`((1 + φ₁(τ)^d)/2)^m ≤ e^{64}`. -/
lemma Y_num {d m : ℕ} (hd : 8 ≤ d) (hm : 100000 ≤ m) :
    ((1 + phi1 (64 / (1001 / 1000 * ((m : ℝ) * d / 2))) ^ d) / 2) ^ m ≤ exp 64 := by
  have hdR : (8 : ℝ) ≤ d := by exact_mod_cast hd
  have hmR : (100000 : ℝ) ≤ m := by exact_mod_cast hm
  set τ : ℝ := 64 / (1001 / 1000 * ((m : ℝ) * d / 2)) with hτ
  have hτ0 : 0 < τ := by positivity
  have hτ1 : τ ≤ 1 / 4000 := by
    rw [hτ, div_le_iff₀ (by positivity)]; nlinarith
  -- `φ₁(τ) ≤ exp(τ + 2τ²)`
  have hphi : phi1 τ ≤ exp (τ + 2 * τ ^ 2) := by
    unfold phi1
    have h0 : 0 < 1 - 2 * τ := by linarith
    have hs : 0 < √(1 - 2 * τ) := Real.sqrt_pos.mpr h0
    rw [inv_le_iff_one_le_mul₀ hs]
    have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ 2 * τ + 4 * τ ^ 2 by positivity)
    have hsq : 1 ≤ (√(1 - 2 * τ) * exp (τ + 2 * τ ^ 2)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt h0.le, ← Real.exp_nat_mul]
      have e : ((2 : ℕ) : ℝ) * (τ + 2 * τ ^ 2) = 2 * τ + 4 * τ ^ 2 := by push_cast; ring
      rw [e]
      have : (1 - 2 * τ) * (1 + (2 * τ + 4 * τ ^ 2) + (2 * τ + 4 * τ ^ 2) ^ 2 / 2) ≥ 1 := by
        nlinarith [mul_pos hτ0 hτ0, mul_pos (mul_pos hτ0 hτ0) hτ0,
          mul_pos (mul_pos (mul_pos hτ0 hτ0) hτ0) hτ0]
      nlinarith
    have hpos : 0 ≤ √(1 - 2 * τ) * exp (τ + 2 * τ ^ 2) := by positivity
    nlinarith [hsq, hpos]
  set Y : ℝ := d * (τ + 2 * τ ^ 2) with hY
  have hY0 : 0 ≤ Y := by positivity
  have hphiY : phi1 τ ^ d ≤ exp Y := by
    calc phi1 τ ^ d ≤ exp (τ + 2 * τ ^ 2) ^ d :=
          pow_le_pow_left₀ (by unfold phi1; positivity) hphi d
      _ = exp Y := by rw [← Real.exp_nat_mul]
  have hcosh : (1 + exp Y) / 2 ≤ exp (Y / 2 + Y ^ 2 / 8) := by
    have hc := Real.cosh_le_exp_half_sq (Y / 2)
    rw [Real.cosh_eq] at hc
    have e1 : (1 + exp Y) / 2 = exp (Y / 2) * ((exp (Y / 2) + exp (-(Y / 2))) / 2) := by
      rw [mul_div_assoc', mul_add, ← Real.exp_add, ← Real.exp_add]
      ring_nf
      rw [Real.exp_zero]; ring
    rw [e1, Real.exp_add]
    exact mul_le_mul_of_nonneg_left (hc.trans (le_of_eq (by ring_nf))) (exp_pos _).le
  have hbase : (1 + phi1 τ ^ d) / 2 ≤ exp (Y / 2 + Y ^ 2 / 8) := by
    linarith
  calc ((1 + phi1 τ ^ d) / 2) ^ m ≤ exp (Y / 2 + Y ^ 2 / 8) ^ m :=
        pow_le_pow_left₀ (by have : 0 ≤ phi1 τ ^ d := by unfold phi1; positivity
                             positivity) hbase m
    _ = exp (m * (Y / 2 + Y ^ 2 / 8)) := by rw [← Real.exp_nat_mul]
    _ ≤ exp 64 := by
        apply exp_le_exp.mpr
        have hK : (m : ℝ) * d * τ = 128000 / 1001 := by
          rw [hτ]; field_simp; norm_num
        have e : (m : ℝ) * (Y / 2 + Y ^ 2 / 8) =
            (m * d * τ) * (1 + 2 * τ) / 2 + (m * d * τ) ^ 2 * (1 + 2 * τ) ^ 2 / (8 * m) := by
          rw [hY]; field_simp
        rw [e, hK]
        have h1 : (128000 / 1001 : ℝ) * (1 + 2 * τ) / 2 ≤ 64000 / 1001 * (1 + 2 / 4000) := by
          nlinarith
        have h2 : (128000 / 1001 : ℝ) ^ 2 * (1 + 2 * τ) ^ 2 / (8 * m) ≤
            (128000 / 1001) ^ 2 * (1 + 2 / 4000) ^ 2 / (8 * 100000) := by
          apply div_le_div₀ (by positivity) _ (by positivity) (by linarith)
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact pow_le_pow_left₀ (by positivity) (by linarith) 2
        have h3 : (64000 / 1001 : ℝ) * (1 + 2 / 4000) + (128000 / 1001) ^ 2 * (1 + 2 / 4000) ^ 2 /
            (8 * 100000) ≤ 64 := by norm_num
        linarith

/-! ## The moment `Y` for the Agent -/

open BstLean.Part161 (Ix uHat xLat)
open BstLean.Part162 (dirW)
open BstLean.Part166 (winC)
open BstLean.Part157 (latitude)
open BstLean.Part53 (unitF53)

/-- `Y2 = γ_A·1.001·m_A(n − 1)/2` (so `t_A·Y2 ≤ 2.002`). -/
noncomputable def Y2n (n : ℕ) : ℝ :=
  2 / (n : ℝ) * (1001 / 1000 * (((mA n : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) / 2))

lemma Y2n_pos (hn : 2 ≤ n) : 0 < Y2n n := by
  unfold Y2n
  have h1 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have h2 : (0 : ℝ) < ((mA n : ℕ) : ℝ) := by
    have : 0 < mA n := by unfold mA; positivity
    exact_mod_cast this
  have h3 : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
  positivity

/-- **The masked Frobenius moment is proved**: `Ymom ≤ Y2n^{64}` for every `n ≥ 80 000`. -/
theorem Y_bound (hn : 80000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hw : winC c τ) (a : Ix n)
    {v : Fin (n - 1) → ℝ} (hv : v ≠ 0) :
    Ymom c τ a v ≤ ENNReal.ofReal (Y2n n ^ 64) := by
  have hn1 : 1 ≤ n := by omega
  have hc := window_c_ne hn1 hw
  obtain ⟨hu, hw1, huw⟩ := frame_orth hn1 hc hv
  set s := latitude (n := n) (√(normSq c)) τ a with hsdef
  have hs : s ^ 2 ≤ 1 := BstLean.Part162.latitude_sq_le _ _ _
  set cc := √(1 - s ^ 2)
  have hsc : s ^ 2 + cc ^ 2 = 1 := by rw [Real.sq_sqrt (by linarith)]; ring
  have hc' : (rc c).1.2 ≠ 0 := hc
  have hx : xLat (rc c) s (unitF53 v) = s • uHat (rc c) + cc • dirW (rc c) (unitF53 v) :=
    BstLean.Part161.xLat_eq hn1 hc' s (unitF53 v)
  have hx1 : normSq (s • uHat (rc c) + cc • dirW (rc c) (unitF53 v)) = 1 := by
    rw [normSq_two, hu, hw1, huw]; linarith
  unfold Ymom
  rw [← hsdef, hx]
  have hpt : ∀ A₁ : Matrix (Fin (mA n)) (Fin n) ℝ,
      ENNReal.ofReal (frobSq (Pmat (uHat (rc c)) (dirW (rc c) (unitF53 v)) *
        (D1A1 A₁ (s • uHat (rc c) + cc • dirW (rc c) (unitF53 v)))ᵀ) ^ 64) ≤
      ENNReal.ofReal (Qf A₁ (s • uHat (rc c) + cc • dirW (rc c) (unitF53 v)) ^ 64) := fun A₁ =>
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (frobSq_nonneg _)
      (frob_le_Q hu hw1 huw hsc A₁) 64)
  refine (lintegral_mono hpt).trans ?_
  have hnR : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  have hγ : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  have hM := Y2n_pos (n := n) (by omega)
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hd : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    rw [Nat.cast_sub hn1]; simp
  have hτ : 64 / Y2n n * (2 / (n : ℝ)) =
      64 / (1001 / 1000 * (((mA n : ℕ) : ℝ) * ((n - 1 : ℕ) : ℝ) / 2)) := by
    unfold Y2n; field_simp
  refine Q_mom hn1 hx1 hγ hM ?_ ?_
  · rw [hτ, hmA, hd, div_lt_iff₀ (by nlinarith)]
    nlinarith
  · rw [hτ]
    exact Y_num (d := n - 1) (m := mA n) (by omega) (by unfold mA; nlinarith)

/-- **The remaining hypothesis of Lemma LJ: the plane moment `X` only.** -/
def X_hyp (n : ℕ) (X2 : ℝ) : Prop :=
  ∀ (c : Fin n → ℝ) (τ : ℝ), winC c τ → ∀ (a : Ix n) (v : Fin (n - 1) → ℝ), v ≠ 0 →
    Xmom c τ a v (fun A₁ => YF A₁ c τ) ≤ ENNReal.ofReal (X2 ^ 64) ∧
    Xmom c τ a v (fun A₁ => YS A₁ c τ) ≤ ENNReal.ofReal (X2 ^ 64)

theorem XY_of_X (hn : 80000 ≤ n) {X2 : ℝ} (h : X_hyp n X2) : XY_hyp n X2 (Y2n n) :=
  fun c τ hw a v hv => ⟨(h c τ hw a v hv).1, (h c τ hw a v hv).2, Y_bound hn hw a hv⟩

open BstLean.Part134 BstLean.Part150 BstLean.Part156 BstLean.Part157 BstLean.Part160 in
open BstLean.Part161 (BIAS_hyp) in
open BstLean.Part162 (dPaper) in
open BstLean.Part166 (goodD) in
/-- **The classifier theorem with Lemma LJ reduced to the plane moment `X` alone** (`Y` and `Z`
are proved; every `n ≥ 80 000`, floor `d_low = 0.22005`, room `roomE ≥ 0.001792`). -/
theorem classifier_paper_X80k (hn : 80000 ≤ n) {X2 : ℝ} (hX2 : 0 < X2) (hX : X_hyp n X2)
    (hK : K2XY n X2 (Y2n n) ≤ 47 / 10)
    (fT wT : Ret n → ℕ → ℝ)
    (hf : ∀ g, Measurable (fun c => fT c g)) (hw : ∀ g, Measurable (fun c => wT c g)) (t : ℝ)
    {EA : Set (Ret n)} (hEA : MeasurableSet EA) {δA : ℝ}
    (hA : (retDist (paperCentres n)).real (BstLean.Part159.HP n ∩
      BstLean.Part159.Ethm (paperCentres n) ∩ BstLean.Part159.Ethp (paperCentres n) ∩ EAᶜ) ≤ δA)
    (hroom : δA ≤ roomE)
    (hB : ∀ c ∈ goodD n (paperDesign n fT wT hf hw) EA,
      BIAS_hyp (paperDesign n fT wT hf hw) c
        (dPaper (paperDesign n fT wT hf hw) c (22 * √(2 / (n : ℝ)) ^ 2)
          (35 / 2 * (√(2 / (n : ℝ)) ^ 2 * √(2 / (n : ℝ)))) (√(2 / (n : ℝ)) * (4691 / 10000))
          (1 / 10000) (by norm_num) (by norm_num)) (4295 / 10 ^ 6)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut (paperDesign n fT wT hf hw) t aL (10 ^ 12) x.1 x.2)} :=
  classifier_paper_XY80k hn hX2 (Y2n_pos (by omega)) (XY_of_X hn hX) hK fT wT hf hw t hEA hA
    hroom hB

end BstLean.Part167
