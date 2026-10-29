import BstLean.Part161Six

/-!
# Part 162, item 3 (abstract part): the integrated sixth-order chi-square price

Role: `delegations/statements/p162-spec.md`, item 3. Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, proof of Proposition `t7:p07:FL`
("Apply the centred two-copy bound conditional on `s` … conditional products and
Cauchy–Schwarz … Jensen in `s` … These prove the chi-square price `𝒞`"), and the formulas
`t7:p07:FL-formulas` (`T₂`, `T_k`, `𝒞`).

* `tK κ n L x y = κ[(n/2)x² + y² + L·y·x]` (the paper's `𝒯`, `T_k`).
* `sixF`: the per-latitude bound of `chi_six` (Part 161) written in the scales
  `x_k = ‖ε‖_k`, `y_k = ‖a_c δ‖_k`.
* `priceC`: the Lean form of the paper's `𝒞` (with `T₄²T₆³/120` in place of `T₆⁵/120`).
* `cs_root`, `cs_prod_pow`, `mink_tK`: Cauchy–Schwarz and Minkowski steps.
* **`int_sixF`**: `∫ sixF(x(a), y(a)) dμ(a) ≤ priceC` from `∫ x₂⁴ ≤ A²`, `∫ y₂⁴ ≤ D²`,
  `∫ x₄⁸ ≤ e₄⁸`, `∫ y₄⁸ ≤ d₄⁸`, `∫ x₆¹² ≤ e₆¹²`, `∫ y₆¹² ≤ d₆¹²`.
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real

/-- The paper's `𝒯 = κ[(n/2)x² + y² + L·y·x]` for a scale `x` of `ε` and a scale `y` of `a_c δ`. -/
noncomputable def tK (κ n L x y : ℝ) : ℝ := κ * (n / 2 * x ^ 2 + y ^ 2 + L * y * x)

lemma tK_nonneg {κ n L x y : ℝ} (hκ : 0 ≤ κ) (hn : 0 ≤ n) (hL : 0 ≤ L) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    0 ≤ tK κ n L x y := by unfold tK; positivity

/-- The per-latitude sixth-order bound in the scales `x_k = ‖ε‖_k`, `y_k = ‖a_c δ‖_k`. -/
noncomputable def sixF (κ n L ε₀ E x2 y2 x4 y4 x6 y6 : ℝ) : ℝ :=
  κ * (n * x2 ^ 4 / 4 + (1 + ε₀) * y2 ^ 2 * x2 ^ 2) + tK κ n L x2 y2 ^ 2 / 2 +
    tK κ n L x2 y2 * tK κ n L x4 y4 ^ 2 / 6 + tK κ n L x4 y4 ^ 4 / 24 +
    tK κ n L x4 y4 ^ 2 * tK κ n L x6 y6 ^ 3 / 120 + E * tK κ n L x6 y6 ^ 6 / 720

/-- The integrated price `𝒞` (Lean form): `κ[nA²/4 + (1 + ε₀)AD] + T₂²/2 + T₂T₄²/6 + T₄⁴/24 +
T₄²T₆³/120 + E·T₆⁶/720`, `T₂ = κ[nA/2 + D + L√(AD)]`, `T_k = κ[n e_k²/2 + d_k² + L d_k e_k]`. -/
noncomputable def priceC (κ n L ε₀ E A D e4 d4 e6 d6 : ℝ) : ℝ :=
  κ * (n * A ^ 2 / 4 + (1 + ε₀) * A * D) +
    (κ * (n * A / 2 + D + L * √(A * D))) ^ 2 / 2 +
    κ * (n * A / 2 + D + L * √(A * D)) * tK κ n L e4 d4 ^ 2 / 6 + tK κ n L e4 d4 ^ 4 / 24 +
    tK κ n L e4 d4 ^ 2 * tK κ n L e6 d6 ^ 3 / 120 + E * tK κ n L e6 d6 ^ 6 / 720

section abstract

variable {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]

lemma int_bdd {f : α → ℝ} (hf : Measurable f) {M : ℝ} (hM : ∀ x, |f x| ≤ M) : Integrable f μ :=
  Integrable.of_bound hf.aestronglyMeasurable M
    (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hM x)

/-- Cauchy–Schwarz for nonnegative bounded functions, square-root form. -/
lemma cs_root {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) {M : ℝ}
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x) (hfM : ∀ x, f x ≤ M) (hgM : ∀ x, g x ≤ M)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hfa : ∫ x, f x ^ 2 ∂μ ≤ a ^ 2) (hgb : ∫ x, g x ^ 2 ∂μ ≤ b ^ 2) :
    ∫ x, f x * g x ∂μ ≤ a * b := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure μ
  have hM0 : 0 ≤ M := (hf0 (Classical.arbitrary _)).trans (hfM _)
  have b2 : ∀ {h : α → ℝ}, (∀ x, 0 ≤ h x) → (∀ x, h x ≤ M) → ∀ x, |h x ^ 2| ≤ M ^ 2 :=
    fun {h} h0 hM x => by
      rw [abs_of_nonneg (sq_nonneg _)]; exact pow_le_pow_left₀ (h0 x) (hM x) 2
  have i1 := int_bdd μ (hf.pow_const 2) (b2 hf0 hfM)
  have i2 := int_bdd μ (hg.pow_const 2) (b2 hg0 hgM)
  have i3 : Integrable (fun x => f x * g x) μ := int_bdd μ (hf.mul hg) (M := M ^ 2) fun x => by
    rw [abs_of_nonneg (mul_nonneg (hf0 x) (hg0 x)), sq]
    exact mul_le_mul (hfM x) (hgM x) (hg0 x) hM0
  have h := BstLean.Part138.cs_sq μ i1 i2 i3
  have h0 : 0 ≤ ∫ x, f x * g x ∂μ := integral_nonneg fun x => mul_nonneg (hf0 x) (hg0 x)
  have hA : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have hB : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun x => sq_nonneg _
  have h2 : (∫ x, f x * g x ∂μ) ^ 2 ≤ (a * b) ^ 2 := by
    rw [mul_pow]
    exact h.trans (mul_le_mul hfa hgb hB (sq_nonneg _))
  exact abs_le_of_sq_le_sq' h2 (mul_nonneg ha hb) |>.2


/-- `∫ g^k ≤ b^k` and `b ≥ 0` give `√(∫ g^{2j}) ≤ b^j` style bounds; here: `∫ (y x)^k ≤ (d e)^k`
from `∫ y^{2k} ≤ d^{2k}`, `∫ x^{2k} ≤ e^{2k}` (Cauchy–Schwarz). -/
lemma cs_prod_pow {x y : α → ℝ} (hx : Measurable x) (hy : Measurable y) {M : ℝ}
    (hx0 : ∀ a, 0 ≤ x a) (hy0 : ∀ a, 0 ≤ y a) (hxM : ∀ a, x a ≤ M) (hyM : ∀ a, y a ≤ M)
    (k : ℕ) {e d : ℝ} (he : 0 ≤ e) (hd : 0 ≤ d)
    (hxe : ∫ a, x a ^ (2 * k) ∂μ ≤ e ^ (2 * k)) (hyd : ∫ a, y a ^ (2 * k) ∂μ ≤ d ^ (2 * k)) :
    ∫ a, (y a * x a) ^ k ∂μ ≤ (d * e) ^ k := by
  have h := cs_root μ (f := fun a => y a ^ k) (g := fun a => x a ^ k) (hy.pow_const k)
    (hx.pow_const k) (M := M ^ k) (fun a => pow_nonneg (hy0 a) k) (fun a => pow_nonneg (hx0 a) k)
    (fun a => pow_le_pow_left₀ (hy0 a) (hyM a) k) (fun a => pow_le_pow_left₀ (hx0 a) (hxM a) k)
    (pow_nonneg hd k) (pow_nonneg he k)
    (by simpa only [← pow_mul, mul_comm k 2] using hyd)
    (by simpa only [← pow_mul, mul_comm k 2] using hxe)
  simpa only [mul_pow] using h

/-- **Minkowski for the three terms of `𝒯`**: if `∫ x^{2k} ≤ e^{2k}`, `∫ y^{2k} ≤ d^{2k}` and
`∫ (y x)^k ≤ (d e)^k`, then `∫ tK(x, y)^k ≤ tK(e, d)^k`. -/
lemma mink_tK {x y : α → ℝ} (hx : Measurable x) (hy : Measurable y) {M : ℝ}
    (hx0 : ∀ a, 0 ≤ x a) (hy0 : ∀ a, 0 ≤ y a) (hxM : ∀ a, x a ≤ M) (hyM : ∀ a, y a ≤ M)
    {κ n L : ℝ} (hκ : 0 ≤ κ) (hn : 0 ≤ n) (hL : 0 ≤ L) (k : ℕ) {e d : ℝ} (he : 0 ≤ e) (hd : 0 ≤ d)
    (hxe : ∫ a, x a ^ (2 * k) ∂μ ≤ e ^ (2 * k)) (hyd : ∫ a, y a ^ (2 * k) ∂μ ≤ d ^ (2 * k))
    (hxy : ∫ a, (y a * x a) ^ k ∂μ ≤ (d * e) ^ k) :
    ∫ a, tK κ n L (x a) (y a) ^ k ∂μ ≤ tK κ n L e d ^ k := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure μ
  have hM0 : 0 ≤ M := (hx0 (Classical.arbitrary _)).trans (hxM _)
  set M' := κ * (n / 2 * M ^ 2) + κ * M ^ 2 + κ * L * (M * M) with hM'
  have hb1 : ∀ a, κ * (n / 2 * x a ^ 2) ≤ M' := fun a => by
    have : x a ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (hx0 a) (hxM a) 2
    have h1 : κ * (n / 2 * x a ^ 2) ≤ κ * (n / 2 * M ^ 2) := by gcongr
    have : 0 ≤ κ * M ^ 2 := by positivity
    have : 0 ≤ κ * L * (M * M) := by positivity
    linarith
  have hb2 : ∀ a, κ * y a ^ 2 ≤ M' := fun a => by
    have : y a ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (hy0 a) (hyM a) 2
    have h1 : κ * y a ^ 2 ≤ κ * M ^ 2 := by gcongr
    have : 0 ≤ κ * (n / 2 * M ^ 2) := by positivity
    have : 0 ≤ κ * L * (M * M) := by positivity
    linarith
  have hb3 : ∀ a, κ * L * (y a * x a) ≤ M' := fun a => by
    have : y a * x a ≤ M * M := mul_le_mul (hyM a) (hxM a) (hx0 a) hM0
    have h1 : κ * L * (y a * x a) ≤ κ * L * (M * M) := by gcongr
    have : 0 ≤ κ * (n / 2 * M ^ 2) := by positivity
    have : 0 ≤ κ * M ^ 2 := by positivity
    linarith
  have hb4 : ∀ a, (fun _ : α => (0 : ℝ)) a ≤ M' := fun a => by
    show (0 : ℝ) ≤ M'; positivity
  have h := BstLean.Part161.mink4 μ k (g1 := fun a => κ * (n / 2 * x a ^ 2))
    (g2 := fun a => κ * y a ^ 2) (g3 := fun a => κ * L * (y a * x a)) (g4 := fun _ => 0)
    (by fun_prop) (by fun_prop) (by fun_prop) measurable_const
    (fun a => by have := hx0 a; positivity) (fun a => by have := hy0 a; positivity)
    (fun a => by have := hx0 a; have := hy0 a; positivity) (fun _ => le_rfl)
    hb1 hb2 hb3 hb4
    (b1 := κ * (n / 2 * e ^ 2)) (b2 := κ * d ^ 2) (b3 := κ * L * (d * e)) (b4 := 0)
    (by positivity) (by positivity) (by positivity) le_rfl
    (by
      have e1 : ∀ a, (κ * (n / 2 * x a ^ 2)) ^ k = (κ * (n / 2)) ^ k * x a ^ (2 * k) := fun a => by
        rw [pow_mul]; ring
      simp_rw [e1]
      rw [integral_const_mul, show (κ * (n / 2 * e ^ 2)) ^ k = (κ * (n / 2)) ^ k * e ^ (2 * k) by
        rw [pow_mul]; ring]
      exact mul_le_mul_of_nonneg_left hxe (by positivity))
    (by
      have e1 : ∀ a, (κ * y a ^ 2) ^ k = κ ^ k * y a ^ (2 * k) := fun a => by rw [pow_mul]; ring
      simp_rw [e1]
      rw [integral_const_mul, show (κ * d ^ 2) ^ k = κ ^ k * d ^ (2 * k) by rw [pow_mul]; ring]
      exact mul_le_mul_of_nonneg_left hyd (by positivity))
    (by
      have e1 : ∀ a, (κ * L * (y a * x a)) ^ k = (κ * L) ^ k * (y a * x a) ^ k := fun a => by ring
      simp_rw [e1]
      rw [integral_const_mul, show (κ * L * (d * e)) ^ k = (κ * L) ^ k * (d * e) ^ k by ring]
      exact mul_le_mul_of_nonneg_left hxy (by positivity))
    (by
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk; simp
      · simp [zero_pow hk.ne'])
  have e2 : ∀ a, tK κ n L (x a) (y a) =
      κ * (n / 2 * x a ^ 2) + κ * y a ^ 2 + κ * L * (y a * x a) + 0 := fun a => by unfold tK; ring
  simp_rw [e2]
  have e3 : tK κ n L e d = κ * (n / 2 * e ^ 2) + κ * d ^ 2 + κ * L * (d * e) + 0 := by unfold tK; ring
  rw [e3]
  exact h


/-- **The integrated sixth-order price (conditional products and Cauchy–Schwarz in the
latitude).** For bounded measurable nonnegative per-index scales `x_k` (of `ε`) and `y_k` (of
`a_c δ`) with `∫ x₂⁴ ≤ A²`, `∫ y₂⁴ ≤ D²`, `∫ x₄⁸ ≤ e₄⁸`, `∫ y₄⁸ ≤ d₄⁸`, `∫ x₆¹² ≤ e₆¹²`,
`∫ y₆¹² ≤ d₆¹²`: `∫ sixF(x, y) ≤ priceC`. -/
theorem int_sixF {x2 y2 x4 y4 x6 y6 : α → ℝ} (mx2 : Measurable x2) (my2 : Measurable y2)
    (mx4 : Measurable x4) (my4 : Measurable y4) (mx6 : Measurable x6) (my6 : Measurable y6)
    {M : ℝ} (hx2 : ∀ a, 0 ≤ x2 a ∧ x2 a ≤ M) (hy2 : ∀ a, 0 ≤ y2 a ∧ y2 a ≤ M)
    (hx4 : ∀ a, 0 ≤ x4 a ∧ x4 a ≤ M) (hy4 : ∀ a, 0 ≤ y4 a ∧ y4 a ≤ M)
    (hx6 : ∀ a, 0 ≤ x6 a ∧ x6 a ≤ M) (hy6 : ∀ a, 0 ≤ y6 a ∧ y6 a ≤ M)
    {κ n L ε₀ E : ℝ} (hκ : 0 ≤ κ) (hn : 0 ≤ n) (hL : 0 ≤ L) (hε : 0 ≤ 1 + ε₀) (hE : 0 ≤ E)
    {A D e4 d4 e6 d6 : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D) (he4 : 0 ≤ e4) (hd4 : 0 ≤ d4)
    (he6 : 0 ≤ e6) (hd6 : 0 ≤ d6)
    (IA : ∫ a, x2 a ^ 4 ∂μ ≤ A ^ 2) (ID : ∫ a, y2 a ^ 4 ∂μ ≤ D ^ 2)
    (Ie4 : ∫ a, x4 a ^ 8 ∂μ ≤ e4 ^ 8) (Id4 : ∫ a, y4 a ^ 8 ∂μ ≤ d4 ^ 8)
    (Ie6 : ∫ a, x6 a ^ 12 ∂μ ≤ e6 ^ 12) (Id6 : ∫ a, y6 a ^ 12 ∂μ ≤ d6 ^ 12) :
    ∫ a, sixF κ n L ε₀ E (x2 a) (y2 a) (x4 a) (y4 a) (x6 a) (y6 a) ∂μ ≤
      priceC κ n L ε₀ E A D e4 d4 e6 d6 := by
  have : Nonempty α := nonempty_of_isProbabilityMeasure μ
  have hM0 : 0 ≤ M := (hx2 (Classical.arbitrary _)).1.trans (hx2 _).2
  set t2 := fun a => tK κ n L (x2 a) (y2 a) with ht2
  set t4 := fun a => tK κ n L (x4 a) (y4 a) with ht4
  set t6 := fun a => tK κ n L (x6 a) (y6 a) with ht6
  set T2 := tK κ n L (√A) (√D) with hT2
  set T4 := tK κ n L e4 d4 with hT4
  set T6 := tK κ n L e6 d6 with hT6
  have T2eq : T2 = κ * (n * A / 2 + D + L * √(A * D)) := by
    rw [hT2]; unfold tK
    rw [Real.sq_sqrt hA, Real.sq_sqrt hD, Real.sqrt_mul hA]; ring
  set MT := tK κ n L M M with hMT
  have mt : ∀ {x y : α → ℝ}, Measurable x → Measurable y →
      Measurable (fun a => tK κ n L (x a) (y a)) := fun hx hy => by unfold tK; fun_prop
  have bt : ∀ {x y : α → ℝ}, (∀ a, 0 ≤ x a ∧ x a ≤ M) → (∀ a, 0 ≤ y a ∧ y a ≤ M) →
      ∀ a, 0 ≤ tK κ n L (x a) (y a) ∧ tK κ n L (x a) (y a) ≤ MT := fun {x y} hx hy a => by
    refine ⟨tK_nonneg hκ hn hL (hx a).1 (hy a).1, ?_⟩
    rw [hMT]; unfold tK
    have h1 := pow_le_pow_left₀ (hx a).1 (hx a).2 2
    have h2 := pow_le_pow_left₀ (hy a).1 (hy a).2 2
    have h3 := mul_le_mul (hy a).2 (hx a).2 (hx a).1 hM0
    have h4 : n / 2 * x a ^ 2 + y a ^ 2 + L * y a * x a ≤ n / 2 * M ^ 2 + M ^ 2 + L * M * M := by
      have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ n / 2)
      have := mul_le_mul_of_nonneg_left h3 hL
      nlinarith
    exact mul_le_mul_of_nonneg_left h4 hκ
  have T2n : 0 ≤ T2 := tK_nonneg hκ hn hL (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have T4n : 0 ≤ T4 := tK_nonneg hκ hn hL he4 hd4
  have T6n : 0 ≤ T6 := tK_nonneg hκ hn hL he6 hd6
  -- the three Minkowski bounds
  have I2 : ∫ a, t2 a ^ 2 ∂μ ≤ T2 ^ 2 := by
    refine mink_tK μ mx2 my2 (fun a => (hx2 a).1) (fun a => (hy2 a).1) (fun a => (hx2 a).2)
      (fun a => (hy2 a).2) hκ hn hL 2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) ?_ ?_ ?_
    · rw [show √A ^ (2 * 2) = A ^ 2 by rw [pow_mul, Real.sq_sqrt hA]]; exact IA
    · rw [show √D ^ (2 * 2) = D ^ 2 by rw [pow_mul, Real.sq_sqrt hD]]; exact ID
    · refine cs_prod_pow μ mx2 my2 (fun a => (hx2 a).1) (fun a => (hy2 a).1) (fun a => (hx2 a).2)
        (fun a => (hy2 a).2) 2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) ?_ ?_
      · rw [show √A ^ (2 * 2) = A ^ 2 by rw [pow_mul, Real.sq_sqrt hA]]; exact IA
      · rw [show √D ^ (2 * 2) = D ^ 2 by rw [pow_mul, Real.sq_sqrt hD]]; exact ID
  have I4 : ∫ a, t4 a ^ 4 ∂μ ≤ T4 ^ 4 :=
    mink_tK μ mx4 my4 (fun a => (hx4 a).1) (fun a => (hy4 a).1) (fun a => (hx4 a).2)
      (fun a => (hy4 a).2) hκ hn hL 4 he4 hd4 Ie4 Id4
      (cs_prod_pow μ mx4 my4 (fun a => (hx4 a).1) (fun a => (hy4 a).1) (fun a => (hx4 a).2)
        (fun a => (hy4 a).2) 4 he4 hd4 Ie4 Id4)
  have I6 : ∫ a, t6 a ^ 6 ∂μ ≤ T6 ^ 6 :=
    mink_tK μ mx6 my6 (fun a => (hx6 a).1) (fun a => (hy6 a).1) (fun a => (hx6 a).2)
      (fun a => (hy6 a).2) hκ hn hL 6 he6 hd6 Ie6 Id6
      (cs_prod_pow μ mx6 my6 (fun a => (hx6 a).1) (fun a => (hy6 a).1) (fun a => (hx6 a).2)
        (fun a => (hy6 a).2) 6 he6 hd6 Ie6 Id6)
  -- the first-order term
  have P1 : ∫ a, y2 a ^ 2 * x2 a ^ 2 ∂μ ≤ D * A :=
    cs_root μ (my2.pow_const 2) (mx2.pow_const 2) (M := M ^ 2) (fun a => sq_nonneg _)
      (fun a => sq_nonneg _) (fun a => pow_le_pow_left₀ (hy2 a).1 (hy2 a).2 2)
      (fun a => pow_le_pow_left₀ (hx2 a).1 (hx2 a).2 2) hD hA
      (by simpa only [← pow_mul] using ID) (by simpa only [← pow_mul] using IA)
  -- the two products
  have m2 := mt mx2 my2
  have m4 := mt mx4 my4
  have m6 := mt mx6 my6
  have b2 := bt hx2 hy2
  have b4 := bt hx4 hy4
  have b6 := bt hx6 hy6
  have hMT0 : 0 ≤ MT := (b2 (Classical.arbitrary _)).1.trans (b2 _).2
  have P5 : ∫ a, t2 a * t4 a ^ 2 ∂μ ≤ T2 * T4 ^ 2 := by
    refine cs_root μ m2 (m4.pow_const 2) (M := max MT (MT ^ 2)) (fun a => (b2 a).1)
      (fun a => sq_nonneg _) (fun a => ((b2 a).2).trans (le_max_left _ _))
      (fun a => (pow_le_pow_left₀ (b4 a).1 (b4 a).2 2).trans (le_max_right _ _)) T2n
      (pow_nonneg T4n 2) I2 ?_
    simpa only [← pow_mul] using I4
  have P6 : ∫ a, t4 a ^ 2 * t6 a ^ 3 ∂μ ≤ T4 ^ 2 * T6 ^ 3 := by
    refine cs_root μ (m4.pow_const 2) (m6.pow_const 3) (M := max (MT ^ 2) (MT ^ 3))
      (fun a => sq_nonneg _) (fun a => pow_nonneg (b6 a).1 3)
      (fun a => (pow_le_pow_left₀ (b4 a).1 (b4 a).2 2).trans (le_max_left _ _))
      (fun a => (pow_le_pow_left₀ (b6 a).1 (b6 a).2 3).trans (le_max_right _ _))
      (pow_nonneg T4n 2) (pow_nonneg T6n 3) ?_ ?_
    · simpa only [← pow_mul] using I4
    · simpa only [← pow_mul] using I6
  -- integrability
  have ib : ∀ {f : α → ℝ}, Measurable f → (∃ K, ∀ a, |f a| ≤ K) → Integrable f μ :=
    fun hf ⟨K, hK⟩ => int_bdd μ hf hK
  have bnd : ∀ {f : α → ℝ} {K : ℝ}, (∀ a, 0 ≤ f a ∧ f a ≤ K) → ∀ j : ℕ, ∀ a, |f a ^ j| ≤ K ^ j :=
    fun hf j a => by
      rw [abs_of_nonneg (pow_nonneg (hf a).1 j)]; exact pow_le_pow_left₀ (hf a).1 (hf a).2 j
  have i_x4 : Integrable (fun a => x2 a ^ 4) μ := ib (mx2.pow_const 4) ⟨_, bnd hx2 4⟩
  have i_yx : Integrable (fun a => y2 a ^ 2 * x2 a ^ 2) μ :=
    ib ((my2.pow_const 2).mul (mx2.pow_const 2)) ⟨M ^ 2 * M ^ 2, fun a => by
      rw [abs_mul]; exact mul_le_mul (bnd hy2 2 a) (bnd hx2 2 a) (abs_nonneg _) (by positivity)⟩
  have i_t2 : Integrable (fun a => t2 a ^ 2) μ := ib (m2.pow_const 2) ⟨_, bnd b2 2⟩
  have i_t24 : Integrable (fun a => t2 a * t4 a ^ 2) μ :=
    ib (m2.mul (m4.pow_const 2)) ⟨MT * MT ^ 2, fun a => by
      rw [abs_mul]
      exact mul_le_mul (by simpa using bnd b2 1 a) (bnd b4 2 a) (abs_nonneg _) hMT0⟩
  have i_t4 : Integrable (fun a => t4 a ^ 4) μ := ib (m4.pow_const 4) ⟨_, bnd b4 4⟩
  have i_t46 : Integrable (fun a => t4 a ^ 2 * t6 a ^ 3) μ :=
    ib ((m4.pow_const 2).mul (m6.pow_const 3)) ⟨MT ^ 2 * MT ^ 3, fun a => by
      rw [abs_mul]; exact mul_le_mul (bnd b4 2 a) (bnd b6 3 a) (abs_nonneg _) (by positivity)⟩
  have i_t6 : Integrable (fun a => t6 a ^ 6) μ := ib (m6.pow_const 6) ⟨_, bnd b6 6⟩
  have j1 := (i_x4.const_mul (κ * n / 4)).add (i_yx.const_mul (κ * (1 + ε₀)))
  have j2 := j1.add (i_t2.div_const 2)
  have j3 := j2.add (i_t24.div_const 6)
  have j4 := j3.add (i_t4.div_const 24)
  have j5 := j4.add (i_t46.div_const 120)
  have e : ∀ a, sixF κ n L ε₀ E (x2 a) (y2 a) (x4 a) (y4 a) (x6 a) (y6 a) =
      (((((κ * n / 4 * x2 a ^ 4 + κ * (1 + ε₀) * (y2 a ^ 2 * x2 a ^ 2)) + t2 a ^ 2 / 2) +
        t2 a * t4 a ^ 2 / 6) + t4 a ^ 4 / 24) + t4 a ^ 2 * t6 a ^ 3 / 120) +
        E / 720 * t6 a ^ 6 := fun a => by
    simp only [ht2, ht4, ht6]; unfold sixF; ring
  simp_rw [e]
  rw [integral_add, integral_add, integral_add, integral_add, integral_add, integral_add,
    integral_const_mul, integral_const_mul, integral_div, integral_div, integral_div, integral_div,
    integral_const_mul]
  · have q1 : κ * n / 4 * ∫ a, x2 a ^ 4 ∂μ ≤ κ * n / 4 * A ^ 2 :=
      mul_le_mul_of_nonneg_left IA (by positivity)
    have q2 : κ * (1 + ε₀) * ∫ a, y2 a ^ 2 * x2 a ^ 2 ∂μ ≤ κ * (1 + ε₀) * (D * A) :=
      mul_le_mul_of_nonneg_left P1 (by positivity)
    have q6 : E / 720 * ∫ a, t6 a ^ 6 ∂μ ≤ E / 720 * T6 ^ 6 :=
      mul_le_mul_of_nonneg_left I6 (by positivity)
    unfold priceC
    rw [← T2eq, ← hT4, ← hT6]
    have : κ * (n * A ^ 2 / 4 + (1 + ε₀) * A * D) = κ * n / 4 * A ^ 2 + κ * (1 + ε₀) * (D * A) := by
      ring
    rw [this]
    linarith
  all_goals first
    | exact i_x4.const_mul _ | exact i_yx.const_mul _ | exact i_t2.div_const _
    | exact i_t24.div_const _ | exact i_t4.div_const _ | exact i_t46.div_const _
    | exact i_t6.const_mul _ | exact j1 | exact j2 | exact j3 | exact j4 | exact j5

end abstract

end BstLean.Part162

open BstLean.Part162 in
#print axioms int_sixF
