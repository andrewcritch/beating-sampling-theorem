import BstLean.Part156Comp

/-!
# Part 156 (item 4): the sampling step in root form

`X_1, …, X_k` are independent random variables with values in `{0, 1}` and mean `q` (Bernoulli
variables). `R` is their mean. Then, for `d > 0`,

`μ {|√R - √q| > d} ≤ 2 exp (-k d²)`   (`sampling_root`).

The proof is the Chernoff bound of the binomial distribution with the explicit tilt
`e^s = z (1-q) / (q (1-z))`, and the lower bound `D(z‖q) ≥ (√z - √q)²` of the binomial relative
entropy, in the form `rho_le` (from `log x ≤ x - 1`). This theorem has no assumed hypothesis
other than independence and the Bernoulli property.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part156

open MeasureTheory ProbabilityTheory Real

/-- The relative entropy bound in Hellinger form. For `0 < q < 1`, `0 < z < 1` and
`s = log (z (1-q) / (q (1-z)))`: `exp (-s z) (1 - q + q e^s) ≤ exp (-(√z - √q)²)`. -/
lemma rho_le {q z : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hz0 : 0 < z) (hz1 : z < 1) :
    exp (-(log z + log (1 - q) - log q - log (1 - z)) * z) *
      (1 - q + q * exp (log z + log (1 - q) - log q - log (1 - z))) ≤
      exp (-(√z - √q) ^ 2) := by
  have h1q : 0 < 1 - q := by linarith
  have h1z : 0 < 1 - z := by linarith
  set s := log z + log (1 - q) - log q - log (1 - z) with hs
  have hes : exp s = z * (1 - q) / (q * (1 - z)) := by
    rw [hs, Real.exp_sub, Real.exp_sub, Real.exp_add, Real.exp_log hz0, Real.exp_log h1q,
      Real.exp_log hq0, Real.exp_log h1z]
    field_simp
  have hfac : 1 - q + q * exp s = exp (log (1 - q) - log (1 - z)) := by
    rw [hes, Real.exp_sub, Real.exp_log h1q, Real.exp_log h1z]
    field_simp
    ring
  rw [hfac, ← Real.exp_add]
  refine exp_le_exp.2 ?_
  -- square roots
  set A := √q with hA
  set B := √z with hB
  set C := √(1 - q) with hC
  set D := √(1 - z) with hD
  have hApos : 0 < A := Real.sqrt_pos.2 hq0
  have hBpos : 0 < B := Real.sqrt_pos.2 hz0
  have hCpos : 0 < C := Real.sqrt_pos.2 h1q
  have hDpos : 0 < D := Real.sqrt_pos.2 h1z
  have hA2 : A ^ 2 = q := Real.sq_sqrt hq0.le
  have hB2 : B ^ 2 = z := Real.sq_sqrt hz0.le
  have hC2 : C ^ 2 = 1 - q := Real.sq_sqrt h1q.le
  have hD2 : D ^ 2 = 1 - z := Real.sq_sqrt h1z.le
  have hlq : log q = 2 * log A := by rw [hA, Real.log_sqrt hq0.le]; ring
  have hlz : log z = 2 * log B := by rw [hB, Real.log_sqrt hz0.le]; ring
  have hl1q : log (1 - q) = 2 * log C := by rw [hC, Real.log_sqrt h1q.le]; ring
  have hl1z : log (1 - z) = 2 * log D := by rw [hD, Real.log_sqrt h1z.le]; ring
  have h1 : log A - log B ≤ A / B - 1 := by
    rw [← Real.log_div hApos.ne' hBpos.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hApos hBpos)
  have h2 : log C - log D ≤ C / D - 1 := by
    rw [← Real.log_div hCpos.ne' hDpos.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hCpos hDpos)
  have h3 : B ^ 2 * (log A - log B) ≤ A * B - B ^ 2 := by
    have := mul_le_mul_of_nonneg_left h1 (sq_nonneg B)
    have e : B ^ 2 * (A / B - 1) = A * B - B ^ 2 := by field_simp
    linarith
  have h4 : D ^ 2 * (log C - log D) ≤ C * D - D ^ 2 := by
    have := mul_le_mul_of_nonneg_left h2 (sq_nonneg D)
    have e : D ^ 2 * (C / D - 1) = C * D - D ^ 2 := by field_simp
    linarith
  have h5 : -s * z + (log (1 - q) - log (1 - z)) =
      2 * (B ^ 2 * (log A - log B)) + 2 * (D ^ 2 * (log C - log D)) := by
    rw [hs, hlq, hlz, hl1q, hl1z, hD2, hB2]
    ring
  rw [h5]
  nlinarith [sq_nonneg (D - C)]

lemma tilt_nonneg {q z : ℝ} (hq0 : 0 < q) (hz1 : z < 1) (hqz : q ≤ z) :
    0 ≤ log z + log (1 - q) - log q - log (1 - z) := by
  have h1 : log q ≤ log z := Real.log_le_log hq0 hqz
  have h2 : log (1 - z) ≤ log (1 - q) := Real.log_le_log (by linarith) (by linarith)
  linarith

lemma tilt_nonpos {q z : ℝ} (hq1 : q < 1) (hz0 : 0 < z) (hqz : z ≤ q) :
    log z + log (1 - q) - log q - log (1 - z) ≤ 0 := by
  have h1 : log z ≤ log q := Real.log_le_log hz0 hqz
  have h2 : log (1 - q) ≤ log (1 - z) := Real.log_le_log (by linarith) (by linarith)
  linarith

section sampling

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The moment generating function of a `{0, 1}`-valued random variable. -/
lemma mgf_bernoulli [IsProbabilityMeasure μ] {X : Ω → ℝ} (hXm : Measurable X)
    (h01 : ∀ ω, X ω = 0 ∨ X ω = 1) (s : ℝ) :
    mgf X μ s = 1 - (∫ ω, X ω ∂μ) + (∫ ω, X ω ∂μ) * exp s := by
  have hpt : ∀ ω, exp (s * X ω) = 1 + X ω * (exp s - 1) := by
    intro ω
    rcases h01 ω with h | h <;> simp [h]
  have hint : Integrable X μ := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hXm.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rcases h01 ω with h | h <;> simp [h]
  simp only [mgf, hpt]
  rw [integral_add (integrable_const _) (hint.mul_const _), integral_const, integral_mul_const]
  simp
  ring

variable {k : ℕ} {X : Fin k → Ω → ℝ} {q : ℝ}

lemma mgf_sum_bernoulli [IsProbabilityMeasure μ] (hind : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hq : ∀ i, ∫ ω, X i ω ∂μ = q) (s : ℝ) :
    mgf (∑ i, X i) μ s = (1 - q + q * exp s) ^ k := by
  rw [hind.mgf_sum hXm Finset.univ]
  have : ∀ i ∈ (Finset.univ : Finset (Fin k)), mgf (X i) μ s = 1 - q + q * exp s := by
    intro i _
    rw [mgf_bernoulli (hXm i) (h01 i), hq i]
  rw [Finset.prod_congr rfl this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma integrable_exp_sum [IsProbabilityMeasure μ] (hind : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (s : ℝ) :
    Integrable (fun ω => exp (s * (∑ i, X i) ω)) μ := by
  refine hind.integrable_exp_mul_sum hXm (fun i _ => ?_)
  refine integrable_exp_mul μ (hXm i) (fun ω => ?_) (fun ω => ?_) s
  · rcases h01 i ω with h | h <;> simp [h]
  · rcases h01 i ω with h | h <;> simp [h]

/-- Chernoff bound, upper tail, with a free tilt `s ≥ 0`. -/
lemma chernoff_ge [IsProbabilityMeasure μ] (hind : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hq : ∀ i, ∫ ω, X i ω ∂μ = q) (z : ℝ) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | k * z ≤ ∑ i, X i ω} ≤ (exp (-s * z) * (1 - q + q * exp s)) ^ k := by
  have h := measure_ge_le_exp_mul_mgf (μ := μ) (X := ∑ i, X i) (k * z) hs
    (integrable_exp_sum hind hXm h01 s)
  rw [mgf_sum_bernoulli hind hXm h01 hq] at h
  have e1 : {ω | (k : ℝ) * z ≤ (∑ i, X i) ω} = {ω | (k : ℝ) * z ≤ ∑ i, X i ω} := by
    ext ω; simp [Finset.sum_apply]
  rw [e1] at h
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

/-- Chernoff bound, lower tail, with a free tilt `s ≤ 0`. -/
lemma chernoff_le [IsProbabilityMeasure μ] (hind : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hq : ∀ i, ∫ ω, X i ω ∂μ = q) (z : ℝ) {s : ℝ} (hs : s ≤ 0) :
    μ.real {ω | ∑ i, X i ω ≤ k * z} ≤ (exp (-s * z) * (1 - q + q * exp s)) ^ k := by
  have h := measure_le_le_exp_mul_mgf (μ := μ) (X := ∑ i, X i) (k * z) hs
    (integrable_exp_sum hind hXm h01 s)
  rw [mgf_sum_bernoulli hind hXm h01 hq] at h
  have e1 : {ω | (∑ i, X i) ω ≤ (k : ℝ) * z} = {ω | ∑ i, X i ω ≤ (k : ℝ) * z} := by
    ext ω; simp [Finset.sum_apply]
  rw [e1] at h
  refine h.trans (le_of_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

lemma pow_exp_le {ρ d : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ exp (-d ^ 2)) (k : ℕ) :
    ρ ^ k ≤ exp (-k * d ^ 2) := by
  calc ρ ^ k ≤ exp (-d ^ 2) ^ k := pow_le_pow_left₀ hρ0 hρ k
    _ = exp (-k * d ^ 2) := by rw [← Real.exp_nat_mul]; congr 1; ring

/-- **The sampling step in root form.** For independent `{0, 1}`-valued `X_1, …, X_k` with mean
`q` and `R = (X_1 + ⋯ + X_k)/k`: `μ {|√R - √q| > d} ≤ 2 exp (-k d²)`, for every `d > 0`. -/
theorem sampling_root [IsProbabilityMeasure μ] (hind : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1)
    (hq : ∀ i, ∫ ω, X i ω ∂μ = q) {d : ℝ} (hd : 0 < d) :
    μ.real {ω | d < |√((∑ i, X i ω) / k) - √q|} ≤ 2 * exp (-k * d ^ 2) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    have : μ.real {ω | d < |√((∑ i, X i ω) / (0 : ℕ)) - √q|} ≤ 1 := measureReal_le_one
    simp only [Nat.cast_zero, neg_zero, zero_mul, exp_zero, mul_one]
    simp only [Nat.cast_zero] at this
    linarith
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hX0 : ∀ i ω, 0 ≤ X i ω := fun i ω => by rcases h01 i ω with h | h <;> simp [h]
  have hX1 : ∀ i ω, X i ω ≤ 1 := fun i ω => by rcases h01 i ω with h | h <;> simp [h]
  have hq0 : 0 ≤ q := by rw [← hq ⟨0, hk⟩]; exact integral_nonneg (hX0 _)
  have hq1 : q ≤ 1 := by
    rw [← hq ⟨0, hk⟩]
    have := integral_mono_of_nonneg (μ := μ) (Filter.Eventually.of_forall (hX0 ⟨0, hk⟩))
      (integrable_const (1 : ℝ)) (Filter.Eventually.of_forall (hX1 ⟨0, hk⟩))
    simpa using this
  have hS0 : ∀ ω, 0 ≤ ∑ i, X i ω := fun ω => Finset.sum_nonneg (fun i _ => hX0 i ω)
  have hS1 : ∀ ω, ∑ i, X i ω ≤ k := fun ω => by
    have := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin k))) => hX1 i ω)
    simpa using this
  have hsq : (√q) ^ 2 = q := Real.sq_sqrt hq0
  -- upper part
  have hup : μ.real {ω | √q + d < √((∑ i, X i ω) / k)} ≤ exp (-k * d ^ 2) := by
    set z := (√q + d) ^ 2 with hz
    have hz0 : 0 < z := by have := Real.sqrt_nonneg q; positivity
    have hsz : √z = √q + d := Real.sqrt_sq (by have := Real.sqrt_nonneg q; linarith)
    by_cases hz1 : 1 ≤ z
    · have : {ω | √q + d < √((∑ i, X i ω) / k)} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        rw [← hsz]
        refine Real.sqrt_le_sqrt ?_
        rw [div_le_iff₀ hk']
        nlinarith [hS1 ω]
      rw [this, measureReal_empty]
      exact (exp_pos _).le
    · have hz1' : z < 1 := not_le.1 hz1
      have hsub : {ω | √q + d < √((∑ i, X i ω) / k)} ⊆ {ω | k * z ≤ ∑ i, X i ω} := by
        intro ω hω
        have h1 : √z < √((∑ i, X i ω) / k) := by rw [hsz]; exact hω
        have h2 : z < (∑ i, X i ω) / k := (Real.sqrt_lt_sqrt_iff hz0.le).1 h1
        rw [lt_div_iff₀ hk'] at h2
        show (k : ℝ) * z ≤ ∑ i, X i ω
        linarith
      have hqz : q < z := by rw [hz]; nlinarith [Real.sqrt_nonneg q]
      have hq1' : q < 1 := lt_trans hqz hz1'
      refine (measureReal_mono hsub).trans ?_
      rcases hq0.eq_or_lt with hq00 | hq00
      · -- `q = 0`
        have hzd : z = d ^ 2 := by rw [hz, ← hq00]; simp
        have h := chernoff_ge hind hXm h01 hq z (s := 1) zero_le_one
        refine h.trans (pow_exp_le (by positivity) ?_ k)
        rw [← hq00, hzd]
        simp
      · have h := chernoff_ge hind hXm h01 hq z (tilt_nonneg hq00 hz1' hqz.le)
        refine h.trans (pow_exp_le ?_ ?_ k)
        · have : 0 ≤ 1 - q + q * exp (log z + log (1 - q) - log q - log (1 - z)) := by
            have := (exp_pos (log z + log (1 - q) - log q - log (1 - z))).le
            nlinarith
          positivity
        · have h2 := rho_le hq00 hq1' hz0 hz1'
          rw [hsz] at h2
          have e : -(√q + d - √q) ^ 2 = -d ^ 2 := by ring
          rw [e] at h2
          exact h2
  -- lower part
  have hlow : μ.real {ω | √((∑ i, X i ω) / k) < √q - d} ≤ exp (-k * d ^ 2) := by
    by_cases hqd : √q - d ≤ 0
    · have : {ω | √((∑ i, X i ω) / k) < √q - d} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt]
        exact hqd.trans (Real.sqrt_nonneg _)
      rw [this, measureReal_empty]
      exact (exp_pos _).le
    · have hqd' : 0 < √q - d := not_le.1 hqd
      set z := (√q - d) ^ 2 with hz
      have hz0 : 0 < z := by positivity
      have hsz : √z = √q - d := Real.sqrt_sq hqd'.le
      have hq00 : 0 < q := by
        rcases hq0.eq_or_lt with h | h
        · rw [← h] at hqd'; simp at hqd'; linarith
        · exact h
      have hzq : z < q := by rw [hz]; nlinarith [Real.sqrt_nonneg q]
      have hz1' : z < 1 := lt_of_lt_of_le hzq hq1
      have hsub : {ω | √((∑ i, X i ω) / k) < √q - d} ⊆ {ω | ∑ i, X i ω ≤ k * z} := by
        intro ω hω
        have h1 : √((∑ i, X i ω) / k) < √z := by rw [hsz]; exact hω
        have h2 : (∑ i, X i ω) / k < z :=
          (Real.sqrt_lt_sqrt_iff (div_nonneg (hS0 ω) hk'.le)).1 h1
        rw [div_lt_iff₀ hk'] at h2
        show ∑ i, X i ω ≤ (k : ℝ) * z
        linarith
      refine (measureReal_mono hsub).trans ?_
      rcases hq1.eq_or_lt with hq11 | hq11
      · -- `q = 1`
        have hz1z : 0 < 1 - z := by linarith
        have h := chernoff_le hind hXm h01 hq z (s := -(d ^ 2 / (1 - z)))
          (by have := div_nonneg (sq_nonneg d) hz1z.le; linarith)
        refine h.trans (pow_exp_le (by rw [hq11]; positivity) ?_ k)
        rw [hq11]
        have e : (1 : ℝ) - 1 + 1 * exp (-(d ^ 2 / (1 - z))) = exp (-(d ^ 2 / (1 - z))) := by ring
        rw [e, ← Real.exp_add]
        refine exp_le_exp.2 (le_of_eq ?_)
        field_simp
        ring
      · have h := chernoff_le hind hXm h01 hq z (tilt_nonpos hq11 hz0 hzq.le)
        refine h.trans (pow_exp_le ?_ ?_ k)
        · have : 0 ≤ 1 - q + q * exp (log z + log (1 - q) - log q - log (1 - z)) := by
            have := (exp_pos (log z + log (1 - q) - log q - log (1 - z))).le
            nlinarith
          positivity
        · have h2 := rho_le hq00 hq11 hz0 hz1'
          rw [hsz] at h2
          have e : -(√q - d - √q) ^ 2 = -d ^ 2 := by ring
          rw [e] at h2
          exact h2
  have hsub : {ω | d < |√((∑ i, X i ω) / k) - √q|} ⊆
      {ω | √q + d < √((∑ i, X i ω) / k)} ∪ {ω | √((∑ i, X i ω) / k) < √q - d} := by
    intro ω hω
    have hω' : d < |√((∑ i, X i ω) / k) - √q| := hω
    rcases lt_abs.1 hω' with h | h
    · left
      show √q + d < √((∑ i, X i ω) / k)
      linarith
    · right
      show √((∑ i, X i ω) / k) < √q - d
      linarith
  calc μ.real {ω | d < |√((∑ i, X i ω) / k) - √q|}
      ≤ μ.real ({ω | √q + d < √((∑ i, X i ω) / k)} ∪ {ω | √((∑ i, X i ω) / k) < √q - d}) :=
        measureReal_mono hsub
    _ ≤ μ.real {ω | √q + d < √((∑ i, X i ω) / k)} +
          μ.real {ω | √((∑ i, X i ω) / k) < √q - d} := measureReal_union_le _ _
    _ ≤ 2 * exp (-k * d ^ 2) := by linarith

end sampling

end BstLean.Part156
