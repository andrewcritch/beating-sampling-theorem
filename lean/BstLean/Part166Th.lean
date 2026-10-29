import BstLean.Part165All

/-!
# Part 166 (file `Th`): the chi-square moments and the latitude moment bound

No proof is left open; no `native_decide` or `axiom` is used.

* `chi_mom`: `E(Σ ξ_i²)^k ≤ (N + 2k)^k` for the standard Gaussian on `ι → ℝ`, `N = |ι|`
  (by the moment generating function at `t = k/(N + 2k)`).
* `W128_le`: `W₁₂₈ ≤ (1.121·τ²/(|c|² + nτ²))¹²⁸` (`n ≥ 80 000`, `0.46 ≤ θ ≤ 0.55`; `ε = 0.055`
  in Part 160's `WqN_le`).
* `theta_mom`: `E_a(1 − s(a)²)⁶⁴ ≤ 0.619⁶⁴` for the latitude `s` (`n ≥ 80 000`,
  `0.46 ≤ θ ≤ 0.55`), by `1 − s² ≤ (τ²/|c' + τξ|²)·|ξ|²`, AM-GM, `W128_le` and `chi_mom`.
-/

namespace BstLean.Part166

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open scoped ENNReal

/-- `x^k ≤ ((N + 2k)/e)^k · exp(k x/(N + 2k))` for `x ≥ 0`. -/
lemma pow_le_exp_bound {x M : ℝ} (hx : 0 ≤ x) (hM : 0 < M) (k : ℕ) :
    x ^ k ≤ (M / exp 1) ^ k * exp (k / M * x) := by
  have hu := Real.add_one_le_exp (x / M - 1)
  rw [sub_add_cancel, Real.exp_sub] at hu
  have h1 : x ≤ M / exp 1 * exp (x / M) := by
    rw [le_div_iff₀ (exp_pos 1)] at hu
    have : x / M * exp 1 ≤ exp (x / M) := hu
    calc x = M * (x / M) := by field_simp
      _ ≤ M * (exp (x / M) / exp 1) := by
          apply mul_le_mul_of_nonneg_left _ hM.le
          rw [le_div_iff₀ (exp_pos 1)]; exact this
      _ = M / exp 1 * exp (x / M) := by ring
  have h2 := pow_le_pow_left₀ hx h1 k
  refine h2.trans (le_of_eq ?_)
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  field_simp

/-- **The moments of the chi-square distribution**: `E|ξ|^{2k} ≤ (N + 2k)^k`. -/
theorem chi_mom {ι : Type} [Fintype ι] (k : ℕ) :
    ∫⁻ ξ, ENNReal.ofReal ((∑ i, ξ i ^ 2) ^ k) ∂(stdGauss ι) ≤
      ENNReal.ofReal (((Fintype.card ι : ℝ) + 2 * k) ^ k) := by
  have hprob : IsProbabilityMeasure (stdGauss ι) := by unfold stdGauss; infer_instance
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; simp
  set N : ℕ := Fintype.card ι with hN
  rcases Nat.eq_zero_or_pos N with hN0 | hN0
  · have hE : IsEmpty ι := Fintype.card_eq_zero_iff.mp hN0
    have : (fun ξ : ι → ℝ => ENNReal.ofReal ((∑ i, ξ i ^ 2) ^ k)) = fun _ => 0 := by
      funext ξ; simp [zero_pow hk.ne']
    rw [this, lintegral_zero]; exact bot_le
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  set M : ℝ := (N : ℝ) + 2 * k with hM
  have hM0 : 0 < M := by positivity
  set t : ℝ := k / M with ht
  have ht2 : t < 1 / 2 := by
    rw [ht, div_lt_iff₀ hM0]; linarith
  obtain ⟨hI, hE⟩ := BstLean.Part152.gauss_mgf_sq ht2
  have hprod : ∀ ξ : ι → ℝ, exp (t * ∑ i, ξ i ^ 2) = ∏ i, exp (t * ξ i ^ 2) := by
    intro ξ; rw [Finset.mul_sum, Real.exp_sum]
  have hInt : Integrable (fun ξ : ι → ℝ => (M / exp 1) ^ k * exp (t * ∑ i, ξ i ^ 2))
      (stdGauss ι) := by
    refine Integrable.const_mul ?_ _
    simp_rw [hprod]
    unfold stdGauss
    exact Integrable.fintype_prod (f := fun _ z => exp (t * z ^ 2)) (fun _ => hI)
  have hval : ∫ ξ, (M / exp 1) ^ k * exp (t * ∑ i, ξ i ^ 2) ∂(stdGauss ι) =
      (M / exp 1) ^ k * ((√(1 - 2 * t))⁻¹) ^ N := by
    rw [integral_const_mul]
    congr 1
    simp_rw [hprod]
    unfold stdGauss
    rw [integral_fintype_prod_eq_pow (fun z => exp (t * z ^ 2)), hE]
  have hpt : ∀ ξ : ι → ℝ, ENNReal.ofReal ((∑ i, ξ i ^ 2) ^ k) ≤
      ENNReal.ofReal ((M / exp 1) ^ k * exp (t * ∑ i, ξ i ^ 2)) := by
    intro ξ
    apply ENNReal.ofReal_le_ofReal
    exact pow_le_exp_bound (Finset.sum_nonneg fun i _ => sq_nonneg _) hM0 k
  refine (lintegral_mono hpt).trans ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hInt (ae_of_all _ fun ξ => by positivity), hval]
  apply ENNReal.ofReal_le_ofReal
  -- `(√(1 − 2t))⁻¹ ^ N ≤ exp k`
  have h12 : 1 - 2 * t = N / M := by
    rw [ht]; field_simp; ring
  have hs : (√(1 - 2 * t))⁻¹ ≤ exp (k / N) := by
    rw [h12, Real.sqrt_div' _ hM0.le, inv_div]
    rw [div_le_iff₀ (Real.sqrt_pos.mpr hNR)]
    have hexp : M / N ≤ exp (k / N) ^ 2 := by
      rw [← Real.exp_nat_mul]
      have := Real.add_one_le_exp ((2 : ℕ) * (k / N))
      have e : M / N = (2 : ℕ) * (k / N) + 1 := by rw [hM]; field_simp; push_cast; ring
      rw [e]; exact this
    have h0 : M = N * (M / N) := by field_simp
    calc √M = √N * √(M / N) := by
          rw [← Real.sqrt_mul hNR.le, ← h0]
      _ ≤ √N * √(exp (k / N) ^ 2) := by
          apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hexp) (Real.sqrt_nonneg _)
      _ = exp (k / N) * √N := by rw [Real.sqrt_sq (exp_pos _).le]; ring
  have hsN : ((√(1 - 2 * t))⁻¹) ^ N ≤ exp k := by
    refine (pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg _)) hs N).trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  calc (M / exp 1) ^ k * ((√(1 - 2 * t))⁻¹) ^ N ≤ (M / exp 1) ^ k * exp k :=
        mul_le_mul_of_nonneg_left hsN (by positivity)
    _ = M ^ k := by
        rw [div_pow, ← Real.exp_nat_mul, mul_one]; field_simp


open BstLean.Part130
open BstLean.Part150 (rhoC thetaC)
open BstLean.Part160 (WqN WqN_le exp_neg_13_le integrable_wqq)
open BstLean.Part161 (consV muI consV_map normSq_consV consV_add consV_smul measurable_consV
  stdGauss_normSq_zero)
open BstLean.Part157 (latitude)

/-- `W₁₂₈ ≤ (1.121·τ²/(|c|² + nτ²))¹²⁸` for `n ≥ 80 000` and `0.46 ≤ θ ≤ 0.55`, for any vector
`c'` with `|c'|² = |c|²`. -/
lemma W128_le {n : ℕ} (hn : 80000 ≤ n) (c c' : Fin n → ℝ) (hc : normSq c' = normSq c) {τ : ℝ}
    (hτ : 0 < τ) (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) :
    WqN 128 c' τ ≤ (1121 / 1000 * (τ ^ 2 / (normSq c + (n : ℝ) * τ ^ 2))) ^ 128 := by
  have hnR : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := WqN_le (q := 128) (by omega) c' hτ (ε := 55 / 1000) (by norm_num) (by norm_num)
  rw [hc] at h
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = τ ^ 2 := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = normSq c + (n : ℝ) * τ ^ 2 := ⟨_, rfl⟩
  have hR0 : 0 < R := by
    have := normSq_nonneg c
    rw [hR]; nlinarith [sq_pos_of_pos hτ]
  have hθ : thetaC c τ = (n : ℝ) * T / R := by
    unfold thetaC rhoC
    rw [Real.sq_sqrt (by rw [← hR]; exact hR0.le), ← hR, ← hT]
  rw [hθ] at hθ0 hθ1
  rw [← hR, ← hT]
  rw [le_div_iff₀ hR0] at hθ0
  rw [div_le_iff₀ hR0] at hθ1
  rw [← hT, show normSq c + (n : ℝ) * T - T = R - T by rw [hR, hT]] at h
  have hTR1 : 80000 * T ≤ 55 / 100 * R := by nlinarith
  have hQ0 : 0 < R - T := by nlinarith
  have hTR0 : 0 ≤ T / R := by positivity
  -- the first term
  have h1 : T / ((1 - 55 / 1000) ^ 2 * (R - T)) ≤ 11199 / 10000 * (T / R) := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hR0]
    have : R ≤ 11199 / 10000 * ((1 - 55 / 1000) ^ 2 * (R - T)) := by nlinarith
    calc T * R ≤ T * (11199 / 10000 * ((1 - 55 / 1000) ^ 2 * (R - T))) :=
          mul_le_mul_of_nonneg_left this hT0.le
      _ = 11199 / 10000 * T * ((1 - 55 / 1000) ^ 2 * (R - T)) := by ring
  have h1' := pow_le_pow_left₀ (by positivity) h1 128
  -- the second term
  have hexp : exp (-((55 / 1000 : ℝ) ^ 2 * (R - T)) / (2 * T)) ≤ exp (-13) ^ 16 := by
    rw [← Real.exp_nat_mul]
    apply exp_le_exp.mpr
    rw [div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  have hE : exp (-13) ^ 16 ≤ ((1504 / 10 ^ 6 : ℝ) ^ 16) ^ 2 := by
    have := pow_le_pow_left₀ (exp_pos _).le exp_neg_13_le 16
    calc exp (-13) ^ 16 ≤ ((1504 / 10 ^ 6 : ℝ) ^ 2) ^ 16 := this
      _ = ((1504 / 10 ^ 6 : ℝ) ^ 16) ^ 2 := by ring
  have hsq : √(exp (-((55 / 1000 : ℝ) ^ 2 * (R - T)) / (2 * T))) ≤ (1504 / 10 ^ 6 : ℝ) ^ 16 := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ (1504 / 10 ^ 6) ^ 16 by norm_num)]
    exact Real.sqrt_le_sqrt (hexp.trans hE)
  have hd0 : (0 : ℝ) < (n : ℝ) - 1 - 4 * (128 : ℕ) := by push_cast; linarith
  have hTR : 46 / 100 / (n : ℝ) ≤ T / R := by
    rw [div_le_div_iff₀ hn0 hR0]
    linarith
  have hinv : ((n : ℝ) - 1 - 4 * (128 : ℕ))⁻¹ ≤ 219 / 100 * (T / R) := by
    have h4 : ((n : ℝ) - 1 - 4 * (128 : ℕ))⁻¹ ≤ 219 / 100 * (46 / 100 / (n : ℝ)) := by
      rw [inv_eq_one_div, mul_div_assoc', div_le_div_iff₀ hd0 hn0]
      push_cast
      nlinarith
    exact h4.trans (mul_le_mul_of_nonneg_left hTR (by norm_num))
  have h2' := pow_le_pow_left₀ (inv_nonneg.mpr hd0.le) hinv 128
  have h2 : √(exp (-((55 / 1000 : ℝ) ^ 2 * (R - T)) / (2 * T))) *
      (((n : ℝ) - 1 - 4 * (128 : ℕ))⁻¹) ^ 128 ≤
      (1504 / 10 ^ 6 : ℝ) ^ 16 * (219 / 100 * (T / R)) ^ 128 :=
    mul_le_mul hsq h2' (by positivity) (by norm_num)
  have hfin : (11199 / 10000 * (T / R)) ^ 128 +
      (1504 / 10 ^ 6 : ℝ) ^ 16 * (219 / 100 * (T / R)) ^ 128 ≤
      (1121 / 1000 * (T / R)) ^ 128 := by
    have e2 : (1121 / 1000 * (T / R)) ^ 128 - ((11199 / 10000 * (T / R)) ^ 128 +
        (1504 / 10 ^ 6 : ℝ) ^ 16 * (219 / 100 * (T / R)) ^ 128) =
        ((1121 / 1000 : ℝ) ^ 128 - (11199 / 10000) ^ 128 - (1504 / 10 ^ 6) ^ 16 * (219 / 100) ^ 128) *
          (T / R) ^ 128 := by ring
    have : 0 ≤ ((1121 / 1000 : ℝ) ^ 128 - (11199 / 10000) ^ 128 -
        (1504 / 10 ^ 6) ^ 16 * (219 / 100) ^ 128) * (T / R) ^ 128 :=
      mul_nonneg (by norm_num) (by positivity)
    linarith
  push_cast at h h2
  linarith


/-- The pointwise bound: where `|G| ≠ 0`, `1 − s² ≤ (τ²/D)·(Z² + |G|²)` and `0 ≤ 1 − s²`. -/
lemma lat_pt {n : ℕ} (hn : 1 ≤ n) (a0 τ : ℝ) (hτ : 0 < τ) (p : ℝ × (Fin (n - 1) → ℝ))
    (hG : normSq p.2 ≠ 0) :
    0 ≤ 1 - latitude (n := n) a0 τ p ^ 2 ∧
    1 - latitude (n := n) a0 τ p ^ 2 ≤
      τ ^ 2 * (normSq (consV (n := n) a0 0 + τ • consV p.1 p.2))⁻¹ * normSq (consV (n := n) p.1 p.2) := by
  have hG0 : 0 < normSq p.2 := lt_of_le_of_ne (normSq_nonneg _) (Ne.symm hG)
  have hD : normSq (consV (n := n) a0 0 + τ • consV p.1 p.2) =
      (a0 + τ * p.1) ^ 2 + τ ^ 2 * normSq p.2 := by
    rw [← consV_smul, ← consV_add, normSq_consV hn, zero_add, normSq_smul]
  have hD0 : 0 < (a0 + τ * p.1) ^ 2 + τ ^ 2 * normSq p.2 := by positivity
  have hs : latitude (n := n) a0 τ p ^ 2 = (a0 + τ * p.1) ^ 2 / ((a0 + τ * p.1) ^ 2 + τ ^ 2 * normSq p.2) := by
    unfold latitude
    rw [div_pow, Real.sq_sqrt hD0.le]
  have h1 : 1 - latitude (n := n) a0 τ p ^ 2 =
      τ ^ 2 * normSq p.2 / ((a0 + τ * p.1) ^ 2 + τ ^ 2 * normSq p.2) := by
    rw [hs]; field_simp; ring
  rw [h1, hD, normSq_consV hn]
  constructor
  · positivity
  · rw [← div_eq_mul_inv, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hD0.le
    nlinarith [mul_nonneg (sq_nonneg τ) (sq_nonneg p.1)]

open MeasureTheory in
/-- **The latitude moment bound**: `E(1 − s²)⁶⁴ ≤ 0.619⁶⁴` for `n ≥ 80 000`,
`0.46 ≤ θ ≤ 0.55`. -/
theorem theta_mom {n : ℕ} (hn : 80000 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ BstLean.Part150.thetaC c τ) (hθ1 : BstLean.Part150.thetaC c τ ≤ 55 / 100) :
    ∫⁻ a, ENNReal.ofReal ((1 - BstLean.Part157.latitude (n := n) (√(BstLean.Part130.normSq c)) τ a ^ 2) ^ 64)
        ∂(BstLean.Part161.muI n) ≤ ENNReal.ofReal ((619 / 1000 : ℝ) ^ 64) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (80000 : ℝ) ≤ n := by exact_mod_cast hn
  set a0 := √(normSq c) with ha0
  set c' : Fin n → ℝ := consV a0 0 with hc'
  have hcc : normSq c' = normSq c := by
    rw [hc', normSq_consV hn1, ha0, Real.sq_sqrt (normSq_nonneg c)]
    simp [normSq]
  set R : ℝ := normSq c + (n : ℝ) * τ ^ 2 with hR
  have hR0 : 0 < R := by
    have := normSq_nonneg c
    rw [hR]; nlinarith [sq_pos_of_pos hτ]
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = 1121 / 1000 * (τ ^ 2 / R) := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; positivity
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = (n : ℝ) + 2 * (128 : ℕ) := ⟨_, rfl⟩
  have hB0 : 0 < B := by rw [hB]; positivity
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = (B / A) ^ 64 := ⟨_, rfl⟩
  have hlam0 : 0 < lam := by rw [hlam]; positivity
  have hl2 : 0 ≤ lam / 2 := by linarith
  have hl2' : 0 ≤ (2 * lam)⁻¹ := inv_nonneg.mpr (by linarith)
  have hA128 : 0 ≤ A ^ 128 := pow_nonneg hA0.le _
  have hB128 : 0 ≤ B ^ 128 := pow_nonneg hB0.le _
  set f : (Fin n → ℝ) → ℝ := fun ξ => (τ ^ 2 * (normSq (c' + τ • ξ))⁻¹) ^ 128 with hf
  set g : (Fin n → ℝ) → ℝ := fun ξ => (normSq ξ) ^ 128 with hg
  set h : (Fin n → ℝ) → ℝ≥0∞ := fun ξ =>
    ENNReal.ofReal (lam / 2 * f ξ) + ENNReal.ofReal ((2 * lam)⁻¹ * g ξ) with hh
  have hfm : Measurable f := by
    rw [hf]
    exact (measurable_const.mul ((measurable_normSq.comp
      (measurable_const.add (measurable_id.const_smul τ))).inv)).pow_const _
  have hgm : Measurable g := measurable_normSq.pow_const _
  have hhm : Measurable h :=
    (ENNReal.measurable_ofReal.comp (measurable_const.mul hfm)).add
      (ENNReal.measurable_ofReal.comp (measurable_const.mul hgm))
  -- step 1: the pointwise bound off a null set
  have hnull : muI n {p : ℝ × (Fin (n - 1) → ℝ) | normSq p.2 = 0} = 0 := by
    have e : {p : ℝ × (Fin (n - 1) → ℝ) | normSq p.2 = 0} =
        Set.univ ×ˢ {G : Fin (n - 1) → ℝ | normSq G = 0} := by ext p; simp
    rw [e, muI, Measure.prod_prod, stdGauss_normSq_zero (by omega), mul_zero]
  have hae : ∀ᵐ p ∂(muI n), normSq p.2 ≠ 0 := by
    have := measure_eq_zero_iff_ae_notMem.mp hnull
    filter_upwards [this] with p hp
    exact hp
  have step1 : ∫⁻ a, ENNReal.ofReal ((1 - latitude (n := n) a0 τ a ^ 2) ^ 64) ∂(muI n) ≤
      ∫⁻ a, h (consV a.1 a.2) ∂(muI n) := by
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with p hp
    obtain ⟨h0, h1⟩ := lat_pt hn1 a0 τ hτ p hp
    set x := τ ^ 2 * (normSq (c' + τ • consV (n := n) p.1 p.2))⁻¹ with hx
    set y := normSq (consV (n := n) p.1 p.2) with hy
    have hx0 : 0 ≤ x := by rw [hx]; exact mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (normSq_nonneg _))
    have hy0 : 0 ≤ y := normSq_nonneg _
    have hp1 : (1 - latitude (n := n) a0 τ p ^ 2) ^ 64 ≤ x ^ 64 * y ^ 64 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ h0 h1 64
    have hamgm : x ^ 64 * y ^ 64 ≤ lam / 2 * x ^ 128 + (2 * lam)⁻¹ * y ^ 128 := by
      have hsq : 0 ≤ (lam * x ^ 64 - y ^ 64) ^ 2 := sq_nonneg _
      have e : lam / 2 * x ^ 128 + (2 * lam)⁻¹ * y ^ 128 - x ^ 64 * y ^ 64 =
          (lam * x ^ 64 - y ^ 64) ^ 2 / (2 * lam) := by
        field_simp; ring
      have : 0 ≤ (lam * x ^ 64 - y ^ 64) ^ 2 / (2 * lam) := div_nonneg hsq (by linarith)
      linarith
    rw [hh]
    simp only
    rw [← ENNReal.ofReal_add (mul_nonneg hl2 (pow_nonneg hx0 _))
      (mul_nonneg hl2' (pow_nonneg hy0 _))]
    apply ENNReal.ofReal_le_ofReal
    exact hp1.trans hamgm
  -- step 2: the change of variables
  have step2 : ∫⁻ a, h (consV a.1 a.2) ∂(muI n) = ∫⁻ ξ, h ξ ∂(BstLean.Part29.stdGauss (Fin n)) := by
    rw [← consV_map hn1, lintegral_map hhm measurable_consV]
    rfl
  -- step 3: the two terms
  have hprob : IsProbabilityMeasure (BstLean.Part29.stdGauss (Fin n)) := by
    unfold BstLean.Part29.stdGauss; infer_instance
  have hfI : ∫⁻ ξ, ENNReal.ofReal (f ξ) ∂(BstLean.Part29.stdGauss (Fin n)) ≤
      ENNReal.ofReal (A ^ 128) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (integrable_wqq (q := 128) (by omega) c' hτ)
      (ae_of_all _ fun ξ => BstLean.Part160.wqq_nonneg 128 c' τ ξ)]
    apply ENNReal.ofReal_le_ofReal
    have hW := W128_le hn c c' hcc hτ hθ0 hθ1
    rw [hA, hR]
    exact hW
  have hgI : ∫⁻ ξ, ENNReal.ofReal (g ξ) ∂(BstLean.Part29.stdGauss (Fin n)) ≤
      ENNReal.ofReal (B ^ 128) := by
    have := chi_mom (ι := Fin n) 128
    simpa [hg, hB, normSq] using this
  have step3 : ∫⁻ ξ, h ξ ∂(BstLean.Part29.stdGauss (Fin n)) ≤
      ENNReal.ofReal (lam / 2) * ENNReal.ofReal (A ^ 128) +
        ENNReal.ofReal ((2 * lam)⁻¹) * ENNReal.ofReal (B ^ 128) := by
    have hm1 : Measurable (fun ξ => ENNReal.ofReal (lam / 2 * f ξ)) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul hfm)
    show ∫⁻ ξ, (ENNReal.ofReal (lam / 2 * f ξ) + ENNReal.ofReal ((2 * lam)⁻¹ * g ξ))
      ∂(BstLean.Part29.stdGauss (Fin n)) ≤ _
    rw [lintegral_add_left hm1]
    simp_rw [ENNReal.ofReal_mul hl2, ENNReal.ofReal_mul hl2']
    rw [lintegral_const_mul _ hfm.ennreal_ofReal, lintegral_const_mul _ hgm.ennreal_ofReal]
    exact add_le_add (by gcongr) (by gcongr)
  -- step 4: the numbers
  have hval : lam / 2 * A ^ 128 + (2 * lam)⁻¹ * B ^ 128 = (A * B) ^ 64 := by
    have e1 : lam * A ^ 64 = B ^ 64 := by
      rw [hlam, div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hA0.ne')]
    have e2 : lam / 2 * A ^ 128 = B ^ 64 * A ^ 64 / 2 := by
      rw [← e1]; ring
    have e3 : (2 * lam)⁻¹ * B ^ 128 = A ^ 64 * B ^ 64 / 2 := by
      rw [show B ^ 128 = B ^ 64 * B ^ 64 by ring, ← e1]; field_simp
    rw [e2, e3, mul_pow]; ring
  have hAB : A * B ≤ 619 / 1000 := by
    have hθ : BstLean.Part150.thetaC c τ = (n : ℝ) * τ ^ 2 / R := by
      unfold BstLean.Part150.thetaC BstLean.Part150.rhoC
      rw [Real.sq_sqrt (by rw [← hR]; exact hR0.le)]
    rw [hθ, div_le_iff₀ hR0] at hθ1
    rw [hA, hB]
    push_cast
    rw [show 1121 / 1000 * (τ ^ 2 / R) * ((n : ℝ) + 2 * 128) =
      1121 / 1000 * (τ ^ 2 * ((n : ℝ) + 256)) / R by ring, div_le_iff₀ hR0]
    have hT := sq_nonneg τ
    have : τ ^ 2 * 256 ≤ 55 / 100 * R * (256 / 80000) := by
      have : 80000 * τ ^ 2 ≤ (n : ℝ) * τ ^ 2 := mul_le_mul_of_nonneg_right hnR hT
      linarith
    linarith
  have hfinal : (A * B) ^ 64 ≤ (619 / 1000 : ℝ) ^ 64 := pow_le_pow_left₀ (mul_nonneg hA0.le hB0.le) hAB 64
  calc ∫⁻ a, ENNReal.ofReal ((1 - latitude (n := n) a0 τ a ^ 2) ^ 64) ∂(muI n)
      ≤ ∫⁻ ξ, h ξ ∂(BstLean.Part29.stdGauss (Fin n)) := step1.trans step2.le
    _ ≤ ENNReal.ofReal (lam / 2) * ENNReal.ofReal (A ^ 128) +
        ENNReal.ofReal ((2 * lam)⁻¹) * ENNReal.ofReal (B ^ 128) := step3
    _ = ENNReal.ofReal ((A * B) ^ 64) := by
        rw [← ENNReal.ofReal_mul hl2, ← ENNReal.ofReal_mul hl2',
          ← ENNReal.ofReal_add (mul_nonneg hl2 hA128) (mul_nonneg hl2' hB128), hval]
    _ ≤ ENNReal.ofReal ((619 / 1000 : ℝ) ^ 64) := ENNReal.ofReal_le_ofReal hfinal

end BstLean.Part166

open BstLean.Part166 in
#print axioms chi_mom
open BstLean.Part166 in
#print axioms theta_mom
