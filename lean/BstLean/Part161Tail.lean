import BstLean.Part161Defs
import BstLean.Part152LM
import BstLean.Part109DiagB

/-!
# Part 161, item 3: the tails of the latitude (Lemma `t7:p07:tails`)

Role: `delegations/statements/p161-spec.md`, item 3. Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, Lemma `t7:p07:tails` ("Latitude
tails and clipping") and the tail formulas of "Formulas for the evaluator".

The latitude is `s = latitude a τ (Z, G) = (a + τ Z)/√((a + τ Z)² + τ²·|G|²)`, `Z` a standard
Gaussian number and `G` an independent standard Gaussian vector of `ℝ^{n−1}`. Put
`ρ = √(a² + n τ²)` and `θ = n τ²/ρ²`. The bulk interval is `I = [a/ρ − 6τ/ρ, a/ρ + 6τ/ρ]`.

* `lat_event`: outside a probability `4·e^{−20}`: `|Z| ≤ √40` and
  `k − 2√(20k) < |G|² < k + 2√(20k) + 40`, `k = n − 1` (Gaussian tail and Laurent–Massart).
* `lat_det`: for `n ≥ 16 384` and `0.46 ≤ θ ≤ 0.54`, these three bounds give `s ∈ I`. The paper
  certifies this inclusion by interval arithmetic on 4096 cells (for `n ≥ 15 660`); here it is an
  analytic proof (two polynomial inequalities) for `n ≥ 16 384`.
* **`latitude_tail`**: `Pr(s ∉ I) ≤ 4·e^{−20}`.
* `tail_root_num`: `√(2·4·e^{−20}) < 0.000129`.
* `bulk_subset`: `−1 < a/ρ − 6τ/ρ` and `a/ρ + 6τ/ρ < 1`.
-/

namespace BstLean.Part161

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part157

/-! ## Two polynomial inequalities -/

/-- The upper polynomial inequality: `A ≥ 0.9229·m`, `m ≥ 0`. -/
lemma poly_upper {m d : ℝ} (hm : 0 ≤ m) (hd : 0 ≤ d) :
    (9229 / 10000 * m + d + 63246 / 10000) ^ 2 * (m ^ 2 - 12 * (9229 / 10000 * m + d) - 36) ≤
      (9229 / 10000 * m + d + 6) ^ 2 * (m ^ 2 - 1 - 89444 / 10000 * m) := by
  nlinarith [mul_nonneg hd hm, mul_nonneg hd hd, mul_nonneg hm hm,
    mul_nonneg (mul_nonneg hd hd) hd, mul_nonneg (mul_nonneg hd hd) hm,
    mul_nonneg (mul_nonneg hd hm) hm, mul_nonneg (mul_nonneg hm hm) hm]

/-- The lower polynomial inequality: `A ≥ 0.9229·m`, `m = 128 + e ≥ 128`. -/
lemma poly_lower {e d : ℝ} (he : 0 ≤ e) (hd : 0 ≤ d) :
    (9229 / 10000 * (128 + e) + d - 6) ^ 2 * ((128 + e) ^ 2 + 89444 / 10000 * (128 + e) + 39) ≤
      (9229 / 10000 * (128 + e) + d - 63246 / 10000) ^ 2 *
        ((128 + e) ^ 2 + 12 * (9229 / 10000 * (128 + e) + d) - 36) := by
  nlinarith [mul_nonneg hd he, mul_nonneg hd hd, mul_nonneg he he,
    mul_nonneg (mul_nonneg hd hd) hd, mul_nonneg (mul_nonneg hd hd) he,
    mul_nonneg (mul_nonneg hd he) he, mul_nonneg (mul_nonneg he he) he]

/-- `x/√N ≤ y/√M` from `x²·M ≤ y²·N`. -/
lemma div_sqrt_le {x y N M : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hN : 0 < N) (hM : 0 < M)
    (h : x ^ 2 * M ≤ y ^ 2 * N) : x / √N ≤ y / √M := by
  rw [div_le_div_iff₀ (Real.sqrt_pos.2 hN) (Real.sqrt_pos.2 hM)]
  have h2 : (x * √M) ^ 2 ≤ (y * √N) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hM.le, Real.sq_sqrt hN.le]
    exact h
  exact (pow_le_pow_iff_left₀ (mul_nonneg hx (Real.sqrt_nonneg _))
    (mul_nonneg hy (Real.sqrt_nonneg _)) two_ne_zero).mp h2

/-! ## The deterministic inclusion -/

/-- The two inequalities in normalized variables (`A = a/τ`, `m = √n`, `T = A + Z`). -/
lemma det_core {m A T Q : ℝ} (hm : 128 ≤ m) (hA : 9229 / 10000 * m ≤ A)
    (hTu : T ≤ A + 63246 / 10000) (hTl : A - 63246 / 10000 ≤ T)
    (hQl : m ^ 2 - 1 - 89444 / 10000 * m ≤ Q) (hQu : Q ≤ m ^ 2 + 89444 / 10000 * m + 39) :
    (A - 6) ^ 2 * (T ^ 2 + Q) ≤ T ^ 2 * (A ^ 2 + m ^ 2) ∧
      T ^ 2 * (A ^ 2 + m ^ 2) ≤ (A + 6) ^ 2 * (T ^ 2 + Q) := by
  obtain ⟨d, hd, rfl⟩ : ∃ d, 0 ≤ d ∧ A = 9229 / 10000 * m + d :=
    ⟨A - 9229 / 10000 * m, by linarith, by ring⟩
  obtain ⟨e, he, rfl⟩ : ∃ e, 0 ≤ e ∧ m = 128 + e := ⟨m - 128, by linarith, by ring⟩
  have hAz : 0 ≤ 9229 / 10000 * (128 + e) + d - 63246 / 10000 := by linarith
  have hT0 : 0 ≤ T := by linarith
  have hQ0 : 0 ≤ Q := by nlinarith
  constructor
  · have h1 := mul_le_mul_of_nonneg_left hQu (sq_nonneg (9229 / 10000 * (128 + e) + d - 6))
    have h2 := poly_lower he hd
    have h3 : (9229 / 10000 * (128 + e) + d - 63246 / 10000) ^ 2 ≤ T ^ 2 :=
      pow_le_pow_left₀ hAz hTl 2
    have h4 : 0 ≤ (128 + e) ^ 2 + 12 * (9229 / 10000 * (128 + e) + d) - 36 := by nlinarith
    have h5 := mul_le_mul_of_nonneg_right h3 h4
    have h6 := h1.trans (h2.trans h5)
    have e1 : T ^ 2 * ((9229 / 10000 * (128 + e) + d) ^ 2 + (128 + e) ^ 2) -
        (9229 / 10000 * (128 + e) + d - 6) ^ 2 * (T ^ 2 + Q) =
        T ^ 2 * ((128 + e) ^ 2 + 12 * (9229 / 10000 * (128 + e) + d) - 36) -
          (9229 / 10000 * (128 + e) + d - 6) ^ 2 * Q := by ring
    linarith
  · have h1 := mul_le_mul_of_nonneg_left hQl (sq_nonneg (9229 / 10000 * (128 + e) + d + 6))
    have h2 := poly_upper (by linarith : (0 : ℝ) ≤ 128 + e) hd
    have h3 : T ^ 2 ≤ (9229 / 10000 * (128 + e) + d + 63246 / 10000) ^ 2 :=
      pow_le_pow_left₀ hT0 hTu 2
    have e1 : (9229 / 10000 * (128 + e) + d + 6) ^ 2 * (T ^ 2 + Q) -
        T ^ 2 * ((9229 / 10000 * (128 + e) + d) ^ 2 + (128 + e) ^ 2) =
        (9229 / 10000 * (128 + e) + d + 6) ^ 2 * Q -
          T ^ 2 * ((128 + e) ^ 2 - 12 * (9229 / 10000 * (128 + e) + d) - 36) := by ring
    by_cases h4 : 0 ≤ (128 + e) ^ 2 - 12 * (9229 / 10000 * (128 + e) + d) - 36
    · have h5 := mul_le_mul_of_nonneg_right h3 h4
      have h6 := h5.trans (h2.trans h1)
      linarith
    · have h5 : T ^ 2 * ((128 + e) ^ 2 - 12 * (9229 / 10000 * (128 + e) + d) - 36) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) (not_le.mp h4).le
      have h6 : 0 ≤ (9229 / 10000 * (128 + e) + d + 6) ^ 2 * Q :=
        mul_nonneg (sq_nonneg _) hQ0
      linarith

/-- The lower bound `A ≥ 0.9229·m` from the window. -/
lemma window_A {m A : ℝ} (hm : 0 ≤ m) (hA0 : 0 < A) (h : 46 / 100 * m ^ 2 ≤ 54 / 100 * A ^ 2) :
    9229 / 10000 * m ≤ A := by
  by_contra hc
  have hc' : A < 9229 / 10000 * m := not_le.mp hc
  have : A ^ 2 < (9229 / 10000 * m) ^ 2 := pow_lt_pow_left₀ hc' hA0.le two_ne_zero
  nlinarith

/-- **The deterministic part of Lemma `t7:p07:tails`.** For `n ≥ 16 384`, `a > 0`, `τ > 0` and
`0.46 ≤ θ ≤ 0.54` (`θ = n τ²/(a² + n τ²)`): if `|Z| ≤ √40` and
`n − 1 − 2√(20(n − 1)) ≤ Q ≤ n − 1 + 2√(20(n − 1)) + 40`, then
`(a + τ Z)/√((a + τ Z)² + τ² Q)` is in the bulk interval `[a/ρ − 6τ/ρ, a/ρ + 6τ/ρ]`. -/
theorem lat_det {n : ℕ} (hn : 16384 ≤ n) {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (hθ2 : n * τ ^ 2 ≤ 54 / 100 * (a ^ 2 + n * τ ^ 2)) {Z Q : ℝ} (hZ : |Z| ≤ √40)
    (hQ1 : (n : ℝ) - 1 - 2 * √(((n : ℝ) - 1) * 20) ≤ Q)
    (hQ2 : Q ≤ (n : ℝ) - 1 + 2 * √(((n : ℝ) - 1) * 20) + 40) :
    a / √(a ^ 2 + n * τ ^ 2) - 6 * τ / √(a ^ 2 + n * τ ^ 2) ≤
        (a + τ * Z) / √((a + τ * Z) ^ 2 + τ ^ 2 * Q) ∧
      (a + τ * Z) / √((a + τ * Z) ^ 2 + τ ^ 2 * Q) ≤
        a / √(a ^ 2 + n * τ ^ 2) + 6 * τ / √(a ^ 2 + n * τ ^ 2) := by
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  obtain ⟨m, hm0, hm2⟩ : ∃ m : ℝ, 0 ≤ m ∧ m ^ 2 = n :=
    ⟨√(n : ℝ), Real.sqrt_nonneg _, Real.sq_sqrt (by linarith)⟩
  have hm128 : 128 ≤ m := by
    by_contra hc
    have : m ^ 2 < 128 ^ 2 := pow_lt_pow_left₀ (not_le.mp hc) hm0 two_ne_zero
    linarith
  have hs20 : √(((n : ℝ) - 1) * 20) ≤ 44722 / 10000 * m :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by rw [← hm2]; nlinarith⟩
  have hz : √(40 : ℝ) ≤ 63246 / 10000 := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  obtain ⟨A, hA0, rfl⟩ : ∃ A, 0 < A ∧ a = A * τ := ⟨a / τ, by positivity, by field_simp⟩
  have hτ2 : 0 < τ ^ 2 := by positivity
  have hA2 : 46 / 100 * m ^ 2 ≤ 54 / 100 * A ^ 2 := by
    rw [hm2]
    have : τ ^ 2 * (46 / 100 * n) ≤ τ ^ 2 * (54 / 100 * A ^ 2) := by
      have e : (A * τ) ^ 2 = τ ^ 2 * A ^ 2 := by ring
      rw [e] at hθ2
      linarith
    exact le_of_mul_le_mul_left this hτ2
  have hA := window_A hm0 hA0 hA2
  obtain ⟨hZ1, hZ2⟩ := abs_le.mp hZ
  have hTu : A + Z ≤ A + 63246 / 10000 := by linarith
  have hTl : A - 63246 / 10000 ≤ A + Z := by linarith
  have hT0 : 0 < A + Z := by linarith
  have hQl : m ^ 2 - 1 - 89444 / 10000 * m ≤ Q := by rw [hm2]; linarith
  have hQu : Q ≤ m ^ 2 + 89444 / 10000 * m + 39 := by rw [hm2]; linarith
  have hQ0 : 0 < Q := by nlinarith
  obtain ⟨k1, k2⟩ := det_core hm128 hA hTu hTl hQl hQu
  have hM : 0 < (A * τ) ^ 2 + n * τ ^ 2 := by positivity
  have hx' : A * τ + τ * Z = τ * (A + Z) := by ring
  have hx : 0 ≤ A * τ + τ * Z := by rw [hx']; positivity
  have hN : 0 < (A * τ + τ * Z) ^ 2 + τ ^ 2 * Q := by positivity
  have hτ4 : 0 ≤ τ ^ 4 := by positivity
  have hA6 : 0 ≤ A * τ - 6 * τ := by
    have : A * τ - 6 * τ = τ * (A - 6) := by ring
    rw [this]
    exact mul_nonneg hτ.le (by linarith)
  constructor
  · rw [← sub_div]
    refine div_sqrt_le hA6 hx hM hN ?_
    have e1 : (A * τ - 6 * τ) ^ 2 * ((A * τ + τ * Z) ^ 2 + τ ^ 2 * Q) =
        τ ^ 4 * ((A - 6) ^ 2 * ((A + Z) ^ 2 + Q)) := by ring
    have e2 : (A * τ + τ * Z) ^ 2 * ((A * τ) ^ 2 + n * τ ^ 2) =
        τ ^ 4 * ((A + Z) ^ 2 * (A ^ 2 + m ^ 2)) := by rw [hm2]; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left k1 hτ4
  · rw [← add_div]
    refine div_sqrt_le hx (by positivity) hN hM ?_
    have e1 : (A * τ + τ * Z) ^ 2 * ((A * τ) ^ 2 + n * τ ^ 2) =
        τ ^ 4 * ((A + Z) ^ 2 * (A ^ 2 + m ^ 2)) := by rw [hm2]; ring
    have e2 : (A * τ + 6 * τ) ^ 2 * ((A * τ + τ * Z) ^ 2 + τ ^ 2 * Q) =
        τ ^ 4 * ((A + 6) ^ 2 * ((A + Z) ^ 2 + Q)) := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left k2 hτ4

/-- **The bulk interval is inside `(−1, 1)`** (`n ≥ 16 384`, `0.46 ≤ θ ≤ 0.54`). -/
theorem bulk_subset {n : ℕ} (hn : 16384 ≤ n) {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (hθ1 : 46 / 100 * (a ^ 2 + n * τ ^ 2) ≤ n * τ ^ 2) :
    -1 < a / √(a ^ 2 + n * τ ^ 2) - 6 * τ / √(a ^ 2 + n * τ ^ 2) ∧
      a / √(a ^ 2 + n * τ ^ 2) + 6 * τ / √(a ^ 2 + n * τ ^ 2) < 1 := by
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hM : 0 < a ^ 2 + n * τ ^ 2 := by positivity
  have hρ : 0 < √(a ^ 2 + n * τ ^ 2) := Real.sqrt_pos.2 hM
  have hρ2 : √(a ^ 2 + n * τ ^ 2) ^ 2 = a ^ 2 + n * τ ^ 2 := Real.sq_sqrt hM.le
  -- `a ≤ 1.0835·√n·τ`, in the form `a² ≤ (54/46)·n·τ²`
  have h6 : 6 * τ < √(a ^ 2 + n * τ ^ 2) := by
    refine Real.lt_sqrt_of_sq_lt ?_
    nlinarith [mul_pos hτ hτ, sq_nonneg a]
  constructor
  · rw [← sub_div, lt_div_iff₀ hρ]
    nlinarith
  · rw [← add_div, div_lt_one hρ]
    refine Real.lt_sqrt_of_sq_lt ?_
    -- `(a + 6τ)² < a² + nτ²` : `12 a τ + 36 τ² < n τ²`
    have h1 : a ^ 2 ≤ 54 / 46 * (n * τ ^ 2) := by nlinarith
    have h2 : a ≤ 11 / 10 * (√(n : ℝ) * τ) := by
      refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
      rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith)]
      nlinarith
    have hm128 : 128 ≤ √(n : ℝ) := Real.le_sqrt_of_sq_le (by norm_num; linarith)
    have hm2 : √(n : ℝ) ^ 2 = n := Real.sq_sqrt (by linarith)
    have h3 : 12 * a * τ ≤ 12 * (11 / 10 * (√(n : ℝ) * τ)) * τ := by
      have := mul_le_mul_of_nonneg_right h2 hτ.le
      nlinarith
    have h4 : (14 : ℝ) * √(n : ℝ) + 36 < n := by nlinarith
    have hτ2 : 0 < τ ^ 2 := by positivity
    nlinarith

/-! ## The probability of the three bounds -/

lemma card_fin_pred (n : ℕ) (hn : 1 ≤ n) : ((Fintype.card (Fin (n - 1)) : ℕ) : ℝ) = (n : ℝ) - 1 := by
  rw [Fintype.card_fin, Nat.cast_sub hn, Nat.cast_one]

/-- **The probability part of Lemma `t7:p07:tails`.** For `n ≥ 2`, outside a probability
`4·e^{−20}`: `|Z| ≤ √40` and `n − 1 − 2√(20(n − 1)) < |G|² < n − 1 + 2√(20(n − 1)) + 40`. -/
theorem lat_event {n : ℕ} (hn : 2 ≤ n) :
    ((gaussianReal 0 1).prod (stdGauss (Fin (n - 1)))).real
      {p | ¬ (|p.1| ≤ √40 ∧ (n : ℝ) - 1 - 2 * √(((n : ℝ) - 1) * 20) < normSq p.2 ∧
        normSq p.2 < (n : ℝ) - 1 + 2 * √(((n : ℝ) - 1) * 20) + 40)} ≤ 4 * exp (-20) := by
  have : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
  set μ := (gaussianReal 0 1).prod (stdGauss (Fin (n - 1))) with hμ
  set S1 : Set ℝ := {x | √40 < |x|} with hS1
  set S2 : Set (Fin (n - 1) → ℝ) :=
    {ξ | ∑ i, ξ i ^ 2 ≤ (Fintype.card (Fin (n - 1)) : ℝ) -
      2 * √((Fintype.card (Fin (n - 1)) : ℝ) * 20)} with hS2
  set S3 : Set (Fin (n - 1) → ℝ) :=
    {ξ | (Fintype.card (Fin (n - 1)) : ℝ) + 2 * √((Fintype.card (Fin (n - 1)) : ℝ) * 20) +
      2 * 20 ≤ ∑ i, ξ i ^ 2} with hS3
  have hc := card_fin_pred n (by omega)
  have hsub : {p : ℝ × (Fin (n - 1) → ℝ) | ¬ (|p.1| ≤ √40 ∧
      (n : ℝ) - 1 - 2 * √(((n : ℝ) - 1) * 20) < normSq p.2 ∧
        normSq p.2 < (n : ℝ) - 1 + 2 * √(((n : ℝ) - 1) * 20) + 40)} ⊆
      (S1 ×ˢ Set.univ) ∪ ((Set.univ ×ˢ S2) ∪ (Set.univ ×ˢ S3)) := by
    intro p hp
    simp only [Set.mem_ofPred_eq] at hp
    simp only [Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, true_and, hS1, hS2, hS3,
      Set.mem_ofPred_eq, hc]
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    refine hp ⟨h1, ?_, ?_⟩
    · exact h2
    · unfold normSq; linarith
  have e1 : μ.real (S1 ×ˢ Set.univ) = (gaussianReal 0 1).real S1 := by
    simp [hμ, measureReal_def, Measure.prod_prod]
  have e2 : μ.real (Set.univ ×ˢ S2) = (stdGauss (Fin (n - 1))).real S2 := by
    simp [hμ, measureReal_def, Measure.prod_prod]
  have e3 : μ.real (Set.univ ×ˢ S3) = (stdGauss (Fin (n - 1))).real S3 := by
    simp [hμ, measureReal_def, Measure.prod_prod]
  have b1 : (gaussianReal 0 1).real S1 ≤ 2 * exp (-20) := by
    have h := BstLean.Part109.gauss_tail_one (t := √40) (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt (by norm_num)] at h
    have e : (-40 : ℝ) / 2 = -20 := by norm_num
    rw [e] at h
    exact h
  have b2 : (stdGauss (Fin (n - 1))).real S2 ≤ exp (-20) :=
    BstLean.Part152.chiSq_lower_LM (by norm_num)
  have b3 : (stdGauss (Fin (n - 1))).real S3 ≤ exp (-20) :=
    BstLean.Part152.chiSq_upper_LM (by norm_num)
  calc μ.real _ ≤ μ.real ((S1 ×ˢ Set.univ) ∪ ((Set.univ ×ˢ S2) ∪ (Set.univ ×ˢ S3))) :=
        measureReal_mono hsub
    _ ≤ μ.real (S1 ×ˢ Set.univ) + (μ.real (Set.univ ×ˢ S2) + μ.real (Set.univ ×ˢ S3)) :=
        (measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le _ _))
    _ ≤ 4 * exp (-20) := by rw [e1, e2, e3]; linarith

/-! ## The headline -/

/-- **Lemma `t7:p07:tails` (the tail of the latitude).** For `n ≥ 16 384`, `a > 0`, `τ > 0` and
`0.46 ≤ θ ≤ 0.54` (`θ = n τ²/ρ²`, `ρ² = a² + n τ²`): the latitude `s = latitude a τ (Z, G)`,
`Z` standard Gaussian and `G` standard Gaussian in `ℝ^{n−1}`, is outside the bulk interval
`[a/ρ − 6τ/ρ, a/ρ + 6τ/ρ]` with probability at most `4·e^{−20}`. -/
theorem latitude_tail {n : ℕ} (hn : 16384 ≤ n) {a τ : ℝ} (ha : 0 < a) (hτ : 0 < τ)
    (hθ1 : 46 / 100 * (a ^ 2 + n * τ ^ 2) ≤ n * τ ^ 2)
    (hθ2 : n * τ ^ 2 ≤ 54 / 100 * (a ^ 2 + n * τ ^ 2)) :
    ((gaussianReal 0 1).prod (stdGauss (Fin (n - 1)))).real
      {p | latitude a τ p ∉ Set.Icc (a / √(a ^ 2 + n * τ ^ 2) - 6 * τ / √(a ^ 2 + n * τ ^ 2))
        (a / √(a ^ 2 + n * τ ^ 2) + 6 * τ / √(a ^ 2 + n * τ ^ 2))} ≤ 4 * exp (-20) := by
  refine (measureReal_mono ?_).trans (lat_event (n := n) (by omega))
  intro p hp
  simp only [Set.mem_ofPred_eq] at hp ⊢
  intro h
  apply hp
  obtain ⟨hZ, hQ1, hQ2⟩ := h
  have := lat_det hn ha hτ hθ2 hZ hQ1.le hQ2.le
  exact ⟨this.1, this.2⟩

/-- **The tail root**: `√(2·(4·e^{−20})) < 0.000129` (the paper: `h_tail = √(8e^{−20})`). -/
theorem tail_root_num : √(2 * (4 * exp (-20))) < 129 / 10 ^ 6 := by
  have h1 : (27182 / 10000 : ℝ) < exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h2 : (27182 / 10000 : ℝ) ^ 20 < exp 20 := by
    have h3 : exp 20 = exp 1 ^ 20 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h3]
    exact pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
  have h4 : exp (-20) < 1 / (27182 / 10000 : ℝ) ^ 20 := by
    rw [Real.exp_neg, ← one_div]
    exact one_div_lt_one_div_of_lt (by positivity) h2
  rw [Real.sqrt_lt' (by norm_num)]
  have h5 : 2 * (4 * (1 / (27182 / 10000 : ℝ) ^ 20)) < (129 / 10 ^ 6) ^ 2 := by norm_num
  linarith

end BstLean.Part161

open BstLean.Part161 in
#print axioms lat_det
open BstLean.Part161 in
#print axioms lat_event
open BstLean.Part161 in
#print axioms latitude_tail
open BstLean.Part161 in
#print axioms bulk_subset
open BstLean.Part161 in
#print axioms tail_root_num
