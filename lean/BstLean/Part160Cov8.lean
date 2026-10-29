import BstLean.Part160Cov
import BstLean.Part160Mass8

/-!
# Part 160 (file `Cov8`): the noncentral bounds of `Ξ₄` and `Ξ₈`

Do not use `sorry`, `native_decide` or `axiom`.

The analogue of `Part160Cov.lean` for `Ξ₄ = Xi4` (Part 153) and `Ξ₈ = Xi8` (`Part160Mass8`), by
one proof for a general power `q` (`q = 2`: `Ξ₄`; `q = 4`: `Ξ₈`).

Notation: `y = c + τξ`, `w = τ²/|y|²`, `g = ‖𝒥(x)Π_x‖_op²`, `W_q = WqN q c τ = E_ξ w^q`,
`X_q = XqN q A₁ A₂ c τ = E_ξ[w^q g^q]`, so `Ξ₄ = t_A·X₂^{1/2}`, `Ξ₈ = t_A·X₄^{1/4}`.

* `WqN_le`: `W_q ≤ (τ²/((1 − ε)²(ρ² − τ²)))^q + √exp(−ε²(ρ² − τ²)/(2τ²))·(n − 1 − 4q)^{−q}`.
* `W2_le_theta`, `W4_le_theta`: `W₂ ≤ (1.0665·θ/n)²`, `W₄ ≤ (1.07·θ/n)⁴` (`n ≥ 16384`,
  `0.46 ≤ θ ≤ 0.55`).
* `jensen_gen`: Jensen for a weight. `markov_XqN`: `Pr(X_q > (M n)^q·W_q) ≤ (j²/M)^{q P'}`.
* `SXi4n`, `SXi8n`: the events `X_q ≤ (1.157·n)^q·W_q`; measurability; charge `≤ 5·10⁻⁵`.
* `Xi4_noncentral`: `Ξ₄ ≤ 0.679·γ_A/n`; `Xi8_noncentral`: `Ξ₈ ≤ 0.681·γ_A/n` on the events,
  in the window.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part148 (EuLip)
open BstLean.Part150 (rhoC thetaC)
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm XiS Xi4 jacT nuA jS)
open scoped ENNReal

variable {n : ℕ}

/-- `W_q = E_ξ[(τ²/|c + τξ|²)^q]`. -/
noncomputable def WqN (q : ℕ) (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  ∫ ξ, (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q ∂stdGauss (Fin n)

/-- `X_q = E_ξ[(τ²/|y|²)^q·‖𝒥(x)Π_x‖_op^{2q}]`. -/
noncomputable def XqN (q : ℕ) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  ∫ ξ, (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q *
    (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2) ^ q ∂stdGauss (Fin n)

lemma integrable_wqq {q : ℕ} (hq : 2 * q + 1 < n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun ξ : Fin n → ℝ => (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q)
      (stdGauss (Fin n)) := by
  have h := (BstLean.Part153.invMoment_le hq c hτ).1.const_mul ((τ ^ 2) ^ q)
  have e : (fun ξ : Fin n → ℝ => (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q) =
      fun ξ => (τ ^ 2) ^ q * (normSq (c + τ • ξ))⁻¹ ^ q := funext fun ξ => mul_pow _ _ _
  rw [e]; exact h

lemma wqq_nonneg (q : ℕ) (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) :
    0 ≤ (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q := pow_nonneg (wq_nonneg c τ ξ) q

lemma WqN_pos {q : ℕ} (hq : 2 * q + 1 < n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    0 < WqN q c τ := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hne := BstLean.Part153.ae_normSq_ne_zero (by omega : 1 ≤ n) c hτ.ne'
  unfold WqN
  rw [integral_pos_iff_support_of_nonneg_ae (ae_of_all _ (wqq_nonneg q c τ))
    (integrable_wqq hq c hτ)]
  by_contra hcon
  have h0 : stdGauss (Fin n)
      (Function.support fun ξ : Fin n → ℝ => (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q) = 0 :=
    le_antisymm (not_lt.mp hcon) bot_le
  have h1 := measure_eq_zero_iff_ae_notMem.mp h0
  obtain ⟨ξ, hξ1, hξ2⟩ := (h1.and hne).exists
  apply hξ1
  rw [Function.mem_support]
  exact pow_ne_zero q (mul_ne_zero (pow_ne_zero 2 hτ.ne') (inv_ne_zero hξ2))

/-! ## §1 The noncentral inverse radius moments -/

lemma prod_range_le_pow (f : ℕ → ℝ) {d : ℝ} (hd : 0 ≤ d) {k : ℕ} (h0 : ∀ i < k, 0 ≤ f i)
    (h1 : ∀ i < k, f i ≤ d) : ∏ i ∈ Finset.range k, f i ≤ d ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, pow_succ]
    exact mul_le_mul (ih (fun i hi => h0 i (by omega)) (fun i hi => h1 i (by omega)))
      (h1 k (by omega)) (h0 k (by omega)) (pow_nonneg hd k)

/-- **The noncentral inverse radius moment of order `q`** by concentration. -/
theorem WqN_le {q : ℕ} (hq : 4 * q + 1 < n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    WqN q c τ ≤ (τ ^ 2 / ((1 - ε) ^ 2 * (normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2))) ^ q +
      √(exp (-(ε ^ 2 * (normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2)) / (2 * τ ^ 2))) *
        (((n : ℝ) - 1 - 4 * q)⁻¹) ^ q := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hnR : (4 * (q : ℝ) + 1) < n := by exact_mod_cast hq
  have hd0 : (0 : ℝ) < (n : ℝ) - 1 - 4 * q := by linarith
  have htail := nrm_lower_tail (by omega : 1 ≤ n) c hτ hε0
  have hQ0 : 0 < normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2 := by
    have := normSq_nonneg c
    have h1 : (1 : ℝ) < n := by
      have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      linarith
    nlinarith [sq_pos_of_pos hτ]
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2 := ⟨_, rfl⟩
  rw [← hQ] at hQ0 htail ⊢
  obtain ⟨pb, hpb⟩ : ∃ pb : ℝ, pb = exp (-(ε ^ 2 * Q) / (2 * τ ^ 2)) := ⟨_, rfl⟩
  rw [← hpb] at htail ⊢
  have hpb0 : 0 < pb := by rw [hpb]; exact exp_pos _
  obtain ⟨dq, hdq⟩ : ∃ dq : ℝ, dq = (((n : ℝ) - 1 - 4 * q)⁻¹) ^ q := ⟨_, rfl⟩
  rw [← hdq]
  have hdq0 : 0 < dq := by rw [hdq]; positivity
  obtain ⟨Ib, hIb⟩ : ∃ Ib : ℝ, Ib = dq ^ 2 := ⟨_, rfl⟩
  have hIb0 : 0 < Ib := by rw [hIb]; positivity
  -- the moment of order `2q`
  obtain ⟨hi2, hI2'⟩ := BstLean.Part153.invMoment_le (p := 2 * q) (by omega) c hτ
  have hI2 : τ ^ (2 * (2 * q)) * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ (2 * q) ∂stdGauss (Fin n) ≤ Ib := by
    refine hI2'.trans ?_
    have h1 : ∏ i ∈ Finset.range (2 * q), ((n : ℝ) - 1 - 2 * ((i : ℝ) + 1))⁻¹ ≤
        (((n : ℝ) - 1 - 4 * q)⁻¹) ^ (2 * q) := by
      refine prod_range_le_pow _ (inv_nonneg.mpr hd0.le) (fun i hi' => ?_) (fun i hi' => ?_)
      · have : ((i : ℝ) + 1) ≤ 2 * q := by exact_mod_cast hi'
        exact inv_nonneg.mpr (by linarith)
      · have : ((i : ℝ) + 1) ≤ 2 * q := by exact_mod_cast hi'
        exact inv_anti₀ hd0 (by linarith)
    refine h1.trans (le_of_eq ?_)
    rw [hIb, hdq, ← pow_mul, mul_comm q 2]
  have hi1 := integrable_wqq (q := q) (by omega) c hτ
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = √(pb * Ib) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr (mul_pos hpb0 hIb0)
  have hs2 : s ^ 2 = pb * Ib := by rw [hs]; exact Real.sq_sqrt (mul_pos hpb0 hIb0).le
  have hsE : s = √pb * dq := by
    rw [hs, hIb, Real.sqrt_mul hpb0.le, Real.sqrt_sq hdq0.le]
  rw [← hsE]
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = s / pb := ⟨_, rfl⟩
  have ha0 : 0 < a := by rw [ha]; positivity
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (1 - ε) * √Q := ⟨_, rfl⟩
  have hr0 : 0 < r := by
    rw [hr]
    exact mul_pos (by linarith) (Real.sqrt_pos.mpr hQ0)
  have hr2 : r ^ 2 = (1 - ε) ^ 2 * Q := by rw [hr, mul_pow, Real.sq_sqrt hQ0.le]
  rw [← hr] at htail
  rw [← hr2]
  have hB : MeasurableSet {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} :=
    measurableSet_le (measurable_nrmShift c τ) measurable_const
  -- the pointwise bound
  have hpt : ∀ ξ : Fin n → ℝ, (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q ≤
      (τ ^ 2 / r ^ 2) ^ q + (a / 2 * Set.indicator {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r}
        (fun _ => (1 : ℝ)) ξ +
          1 / (2 * a) * (τ ^ (2 * (2 * q)) * (normSq (c + τ • ξ))⁻¹ ^ (2 * q))) := by
    intro ξ
    have hN0 : 0 ≤ (normSq (c + τ • ξ))⁻¹ := inv_nonneg.mpr (normSq_nonneg _)
    have hx0 : 0 ≤ τ ^ 2 * (normSq (c + τ • ξ))⁻¹ := mul_nonneg (sq_nonneg _) hN0
    have hq0 : 0 ≤ 1 / (2 * a) * (τ ^ (2 * (2 * q)) * (normSq (c + τ • ξ))⁻¹ ^ (2 * q)) := by
      positivity
    have hd0' : 0 ≤ (τ ^ 2 / r ^ 2) ^ q := by positivity
    by_cases hξ : nrm (c + τ • ξ) ≤ r
    · rw [Set.indicator_of_mem (show ξ ∈ {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} from hξ)]
      obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q := ⟨_, rfl⟩
      have e : τ ^ (2 * (2 * q)) * (normSq (c + τ • ξ))⁻¹ ^ (2 * q) = x ^ 2 := by
        rw [hx, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm q 2]
      rw [e, ← hx]
      have h1 : x ≤ a / 2 * 1 + 1 / (2 * a) * x ^ 2 := by
        have h2 : a / 2 * 1 + 1 / (2 * a) * x ^ 2 - x = (x - a) ^ 2 / (2 * a) := by
          field_simp
          ring
        have h3 : 0 ≤ (x - a) ^ 2 / (2 * a) := by positivity
        linarith
      linarith
    · rw [Set.indicator_of_notMem (show ξ ∉ {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} from hξ)]
      have hlt : r < nrm (c + τ • ξ) := not_le.mp hξ
      have h1 : r ^ 2 ≤ normSq (c + τ • ξ) := by
        rw [← BstLean.Part153.nrm_sq (c + τ • ξ)]
        exact pow_le_pow_left₀ hr0.le hlt.le 2
      have h2 : (normSq (c + τ • ξ))⁻¹ ≤ (r ^ 2)⁻¹ := inv_anti₀ (by positivity) h1
      have h3 : τ ^ 2 * (normSq (c + τ • ξ))⁻¹ ≤ τ ^ 2 / r ^ 2 := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      have h4 := pow_le_pow_left₀ hx0 h3 q
      linarith
  have hiI : Integrable (fun ξ : Fin n → ℝ => a / 2 *
      Set.indicator {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} (fun _ => (1 : ℝ)) ξ)
      (stdGauss (Fin n)) := ((integrable_const (1 : ℝ)).indicator hB).const_mul _
  have hiQ : Integrable (fun ξ : Fin n → ℝ => 1 / (2 * a) *
      (τ ^ (2 * (2 * q)) * (normSq (c + τ • ξ))⁻¹ ^ (2 * q))) (stdGauss (Fin n)) :=
    (hi2.const_mul _).const_mul _
  have hmono := integral_mono hi1
    ((integrable_const ((τ ^ 2 / r ^ 2) ^ q)).add (hiI.add hiQ)) hpt
  have hsum : ∫ ξ, ((τ ^ 2 / r ^ 2) ^ q + (a / 2 * Set.indicator
      {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} (fun _ => (1 : ℝ)) ξ +
        1 / (2 * a) * (τ ^ (2 * (2 * q)) * (normSq (c + τ • ξ))⁻¹ ^ (2 * q))))
          ∂stdGauss (Fin n) =
      (τ ^ 2 / r ^ 2) ^ q +
        (a / 2 * (stdGauss (Fin n)).real {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} +
        1 / (2 * a) * (τ ^ (2 * (2 * q)) *
          ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ (2 * q) ∂stdGauss (Fin n))) := by
    have h1 : ∫ ξ, ((τ ^ 2 / r ^ 2) ^ q + (a / 2 * Set.indicator
        {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} (fun _ => (1 : ℝ)) ξ +
          1 / (2 * a) * (τ ^ (2 * (2 * q)) * (normSq (c + τ • ξ))⁻¹ ^ (2 * q))))
            ∂stdGauss (Fin n) =
        ∫ _ξ, (τ ^ 2 / r ^ 2) ^ q ∂stdGauss (Fin n) + ∫ ξ, (a / 2 * Set.indicator
          {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} (fun _ => (1 : ℝ)) ξ +
          1 / (2 * a) * (τ ^ (2 * (2 * q)) * (normSq (c + τ • ξ))⁻¹ ^ (2 * q)))
            ∂stdGauss (Fin n) :=
      integral_add (integrable_const _) (hiI.add hiQ)
    have h2 : ∫ ξ, (a / 2 * Set.indicator
          {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} (fun _ => (1 : ℝ)) ξ +
          1 / (2 * a) * (τ ^ (2 * (2 * q)) * (normSq (c + τ • ξ))⁻¹ ^ (2 * q)))
            ∂stdGauss (Fin n) =
        ∫ ξ, a / 2 * Set.indicator {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r}
          (fun _ => (1 : ℝ)) ξ ∂stdGauss (Fin n) +
        ∫ ξ, 1 / (2 * a) * (τ ^ (2 * (2 * q)) * (normSq (c + τ • ξ))⁻¹ ^ (2 * q))
          ∂stdGauss (Fin n) :=
      integral_add hiI hiQ
    rw [h1, h2, integral_const, probReal_univ, one_smul, integral_const_mul,
      integral_indicator_const _ hB, smul_eq_mul, mul_one, integral_const_mul,
      integral_const_mul]
  have hW : WqN q c τ ≤ (τ ^ 2 / r ^ 2) ^ q +
      (a / 2 * (stdGauss (Fin n)).real {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} +
        1 / (2 * a) * (τ ^ (2 * (2 * q)) *
          ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ (2 * q) ∂stdGauss (Fin n))) := by
    rw [← hsum]; exact hmono
  have h1 : a / 2 * (stdGauss (Fin n)).real {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} ≤
      a / 2 * pb := mul_le_mul_of_nonneg_left htail (by positivity)
  have h2 : 1 / (2 * a) * (τ ^ (2 * (2 * q)) *
      ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ (2 * q) ∂stdGauss (Fin n)) ≤
      1 / (2 * a) * Ib := mul_le_mul_of_nonneg_left hI2 (by positivity)
  have h3 : a / 2 * pb + 1 / (2 * a) * Ib = s := by
    rw [ha]
    have hIb' : Ib = s ^ 2 / pb := by rw [hs2]; field_simp
    rw [hIb']
    field_simp
    ring
  linarith

/-- The window form for `1 ≤ q ≤ 4` (`ε = 3/100`):
`W_q ≤ (1.0629·θ/n)^q + 0.001504·(2.1762·θ/n)^q`. -/
theorem WqN_le_theta_gen (hn : 16384 ≤ n) {q : ℕ} (hq4 : q ≤ 4) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) :
    WqN q c τ ≤ (10629 / 10000 * (thetaC c τ / n)) ^ q +
      1504 / 10 ^ 6 * (21762 / 10000 * (thetaC c τ / n)) ^ q := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hqR : (q : ℝ) ≤ 4 := by exact_mod_cast hq4
  have h := WqN_le (q := q) (by omega) c hτ (ε := 3 / 100) (by norm_num) (by norm_num)
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = τ ^ 2 := ⟨_, rfl⟩
  have hT0 : 0 < T := by rw [hT]; positivity
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = normSq c + (n : ℝ) * τ ^ 2 := ⟨_, rfl⟩
  have hR0 : 0 < R := by
    have := normSq_nonneg c
    rw [hR]; nlinarith [sq_pos_of_pos hτ]
  have hθ : thetaC c τ = (n : ℝ) * T / R := by
    unfold thetaC rhoC
    rw [Real.sq_sqrt (by rw [← hR]; exact hR0.le), ← hR, ← hT]
  rw [hθ] at hθ0 hθ1 ⊢
  rw [le_div_iff₀ hR0] at hθ0
  rw [div_le_iff₀ hR0] at hθ1
  rw [← hT, show normSq c + (n : ℝ) * T - T = R - T by rw [hR, hT]] at h
  have hT16 : 16384 * T ≤ 55 / 100 * R := by nlinarith
  have hQ0 : 0 < R - T := by nlinarith
  have e : (n : ℝ) * T / R / n = T / R := by field_simp
  rw [e]
  have hTR0 : 0 ≤ T / R := by positivity
  -- the first term
  have h1 : T / ((1 - 3 / 100) ^ 2 * (R - T)) ≤ 10629 / 10000 * (T / R) := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hR0]
    have : R ≤ 10629 / 10000 * ((1 - 3 / 100) ^ 2 * (R - T)) := by nlinarith
    calc T * R ≤ T * (10629 / 10000 * ((1 - 3 / 100) ^ 2 * (R - T))) :=
          mul_le_mul_of_nonneg_left this hT0.le
      _ = 10629 / 10000 * T * ((1 - 3 / 100) ^ 2 * (R - T)) := by ring
  have h1' := pow_le_pow_left₀ (by positivity) h1 q
  -- the second term
  have hexp : exp (-((3 / 100 : ℝ) ^ 2 * (R - T)) / (2 * T)) ≤ exp (-13) := by
    apply exp_le_exp.mpr
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hsq : √(exp (-((3 / 100 : ℝ) ^ 2 * (R - T)) / (2 * T))) ≤ 1504 / 10 ^ 6 := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 1504 / 10 ^ 6 by norm_num)]
    exact Real.sqrt_le_sqrt (hexp.trans exp_neg_13_le)
  have hd0 : (0 : ℝ) < (n : ℝ) - 1 - 4 * q := by linarith
  have hTR : 46 / 100 / (n : ℝ) ≤ T / R := by
    rw [div_le_div_iff₀ hn0 hR0]
    linarith
  have hinv : ((n : ℝ) - 1 - 4 * q)⁻¹ ≤ 21762 / 10000 * (T / R) := by
    have h4 : ((n : ℝ) - 1 - 4 * q)⁻¹ ≤ 21762 / 10000 * (46 / 100 / (n : ℝ)) := by
      rw [inv_eq_one_div, mul_div_assoc', div_le_div_iff₀ hd0 hn0]
      nlinarith
    exact h4.trans (mul_le_mul_of_nonneg_left hTR (by norm_num))
  have h2' := pow_le_pow_left₀ (inv_nonneg.mpr hd0.le) hinv q
  have h2 : √(exp (-((3 / 100 : ℝ) ^ 2 * (R - T)) / (2 * T))) * (((n : ℝ) - 1 - 4 * q)⁻¹) ^ q ≤
      1504 / 10 ^ 6 * (21762 / 10000 * (T / R)) ^ q :=
    mul_le_mul hsq h2' (by positivity) (by norm_num)
  linarith

/-- **`E[(τ²/|y|²)²] ≤ (1.0665·θ/n)²`** for `n ≥ 16384`, `0.46 ≤ θ ≤ 0.55`. -/
theorem W2_le_theta (hn : 16384 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) :
    WqN 2 c τ ≤ (10665 / 10000 * (thetaC c τ / n)) ^ 2 := by
  have h := WqN_le_theta_gen hn (q := 2) (by norm_num) c hτ hθ0 hθ1
  refine h.trans (le_of_sub_nonneg ?_)
  have e : (10665 / 10000 * (thetaC c τ / n)) ^ 2 - ((10629 / 10000 * (thetaC c τ / n)) ^ 2 +
      1504 / 10 ^ 6 * (21762 / 10000 * (thetaC c τ / n)) ^ 2) =
      ((10665 / 10000 : ℝ) ^ 2 - (10629 / 10000) ^ 2 - 1504 / 10 ^ 6 * (21762 / 10000) ^ 2) *
        (thetaC c τ / n) ^ 2 := by ring
  rw [e]
  exact mul_nonneg (by norm_num) (sq_nonneg _)

/-- **`E[(τ²/|y|²)⁴] ≤ (1.07·θ/n)⁴`** for `n ≥ 16384`, `0.46 ≤ θ ≤ 0.55`. -/
theorem W4_le_theta (hn : 16384 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) :
    WqN 4 c τ ≤ (107 / 100 * (thetaC c τ / n)) ^ 4 := by
  have h := WqN_le_theta_gen hn (q := 4) (by norm_num) c hτ hθ0 hθ1
  refine h.trans (le_of_sub_nonneg ?_)
  have e : (107 / 100 * (thetaC c τ / n)) ^ 4 - ((10629 / 10000 * (thetaC c τ / n)) ^ 4 +
      1504 / 10 ^ 6 * (21762 / 10000 * (thetaC c τ / n)) ^ 4) =
      ((107 / 100 : ℝ) ^ 4 - (10629 / 10000) ^ 4 - 1504 / 10 ^ 6 * (21762 / 10000) ^ 4) *
        (thetaC c τ / n) ^ 4 := by ring
  rw [e]
  exact mul_nonneg (by norm_num) (by positivity)

/-! ## §2 Jensen for a weight and the Markov step -/

/-- **Jensen for a weight `v ≥ 0`** with `0 < ∫ v < ∞`: `(E[v·G])^P·V ≤ V^P·E[v·G^P]`,
`V = E v`, `G ≥ 0`, `P ≥ 1`. -/
lemma jensen_gen {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {v : Ω → ℝ}
    (hvm : Measurable v) (hv0 : ∀ ω, 0 ≤ v ω) (hvi : Integrable v μ) (hV : 0 < ∫ ω, v ω ∂μ)
    {P : ℕ} (hP : 1 ≤ P) {G : Ω → ℝ} (hG : Measurable G) (hG0 : ∀ ω, 0 ≤ G ω) :
    ENNReal.ofReal (∫ ω, v ω * G ω ∂μ) ^ P * ENNReal.ofReal (∫ ω, v ω ∂μ) ≤
      ENNReal.ofReal (∫ ω, v ω ∂μ) ^ P *
        ∫⁻ ω, ENNReal.ofReal (v ω) * ENNReal.ofReal (G ω ^ P) ∂μ := by
  obtain ⟨V, hVd⟩ : ∃ V : ℝ≥0∞, V = ENNReal.ofReal (∫ ω, v ω ∂μ) := ⟨_, rfl⟩
  rw [← hVd]
  have hV0 : V ≠ 0 := by rw [hVd]; exact (ENNReal.ofReal_pos.mpr hV).ne'
  have hVt : V ≠ ∞ := by rw [hVd]; exact ENNReal.ofReal_ne_top
  have hwm : Measurable (fun ω => ENNReal.ofReal (v ω)) := hvm.ennreal_ofReal
  have hVeq : ∫⁻ ω, ENNReal.ofReal (v ω) ∂μ = V := by
    rw [hVd]
    exact (ofReal_integral_eq_lintegral_ofReal hvi (ae_of_all _ hv0)).symm
  obtain ⟨μ', hμ'⟩ : ∃ μ' : Measure Ω, μ' = V⁻¹ • (μ.withDensity
      fun ω => ENNReal.ofReal (v ω)) := ⟨_, rfl⟩
  have hprob : IsProbabilityMeasure μ' := by
    constructor
    rw [hμ', Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      hVeq, smul_eq_mul, ENNReal.inv_mul_cancel hV0 hVt]
  have hlint : ∀ f : Ω → ℝ≥0∞, Measurable f → ∫⁻ ω, f ω ∂μ' =
      V⁻¹ * ∫⁻ ω, ENNReal.ofReal (v ω) * f ω ∂μ := by
    intro f hf
    rw [hμ', lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hwm hf, smul_eq_mul]
    rfl
  have h2 := BstLean.Part153.lp_mono_nat (μ := μ') hG hG0 (q := 1) (P := P) le_rfl hP
  simp only [Nat.cast_one, pow_one, div_one, ENNReal.rpow_one] at h2
  have h3 : (∫⁻ ω, ENNReal.ofReal (G ω) ∂μ') ^ P ≤ ∫⁻ ω, ENNReal.ofReal (G ω ^ P) ∂μ' := by
    calc (∫⁻ ω, ENNReal.ofReal (G ω) ∂μ') ^ P
        ≤ ((∫⁻ ω, ENNReal.ofReal (G ω ^ P) ∂μ') ^ (1 / (P : ℝ))) ^ P := pow_le_pow_left' h2 P
      _ = _ := BstLean.Part152.enn_root_pow _ (by omega)
  rw [hlint _ hG.ennreal_ofReal, hlint _ (hG.pow_const P).ennreal_ofReal] at h3
  obtain ⟨A, hA⟩ : ∃ A : ℝ≥0∞, A = ∫⁻ ω, ENNReal.ofReal (v ω) *
      ENNReal.ofReal (G ω) ∂μ := ⟨_, rfl⟩
  obtain ⟨Bp, hBp⟩ : ∃ Bp : ℝ≥0∞, Bp = ∫⁻ ω, ENNReal.ofReal (v ω) *
      ENNReal.ofReal (G ω ^ P) ∂μ := ⟨_, rfl⟩
  rw [← hA, ← hBp] at h3
  rw [← hBp]
  have hle : ENNReal.ofReal (∫ ω, v ω * G ω ∂μ) ≤ A := by
    rw [hA]
    have h := BstLean.Part153.ofReal_integral_le_lintegral (μ := μ)
      (f := fun ω => v ω * G ω) (fun ω => mul_nonneg (hv0 ω) (hG0 ω))
    refine h.trans (le_of_eq ?_)
    refine lintegral_congr fun ω => ?_
    exact ENNReal.ofReal_mul (hv0 ω)
  have eA : A = V * (V⁻¹ * A) := by
    rw [← mul_assoc, ENNReal.mul_inv_cancel hV0 hVt, one_mul]
  have eB : V⁻¹ * Bp * V = Bp := by
    rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hV0 hVt, one_mul]
  calc ENNReal.ofReal (∫ ω, v ω * G ω ∂μ) ^ P * V
      ≤ A ^ P * V := by gcongr
    _ = V ^ P * ((V⁻¹ * A) ^ P * V) := by
        conv_lhs => rw [eA]
        rw [mul_pow, mul_assoc]
    _ ≤ V ^ P * (V⁻¹ * Bp * V) := by gcongr
    _ = V ^ P * Bp := by rw [eB]

/-- **The Markov step for `X_q` with the weight `w^q`**: IF the moment bound
`E_θ ‖𝒥(x)Π_x‖_op^{2qP'} ≤ (√n·j)^{2qP'}` holds at every unit vector `x`, THEN
`Pr(X_q > (M n)^q·W_q) ≤ (j²/M)^{qP'}`. -/
theorem markov_XqN {q P' : ℕ} (hP : 1 ≤ P') (hn : 2 * q + 1 < n) (c : Fin n → ℝ) {τ : ℝ}
    (hτ : 0 < τ) {j : ℝ} (_hj : 0 ≤ j)
    (hmom : ∀ x : Fin n → ℝ, normSq x = 1 →
      ∫⁻ θ, ENNReal.ofReal (opN (jacT θ.1 θ.2 x) ^ (2 * (q * P'))) ∂nuA n ≤
        ENNReal.ofReal ((√(n : ℝ) * j) ^ (2 * (q * P'))))
    {M : ℝ} (hM : 0 < M) :
    (nuA n).real {θ | (M * n) ^ q * WqN q c τ < XqN q θ.1 θ.2 c τ} ≤ (j ^ 2 / M) ^ (q * P') := by
  have hprobG : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hW := WqN_pos hn c hτ
  obtain ⟨W, hWd⟩ : ∃ W : ℝ, W = WqN q c τ := ⟨_, rfl⟩
  rw [← hWd] at hW ⊢
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = (M * n) ^ q * W := ⟨_, rfl⟩
  rw [← hK]
  have hK0 : 0 < K := by rw [hK]; positivity
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = j ^ 2 / M := ⟨_, rfl⟩
  rw [← hD]
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  obtain ⟨V, hV⟩ : ∃ V : ℝ≥0∞, V = ENNReal.ofReal W := ⟨_, rfl⟩
  have hVt : V ≠ ∞ := by rw [hV]; exact ENNReal.ofReal_ne_top
  have hvm : Measurable (fun ξ : Fin n → ℝ => (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q) :=
    (measurable_wq c τ).pow_const q
  have hwm : Measurable (fun ξ : Fin n → ℝ =>
      ENNReal.ofReal ((τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q)) := hvm.ennreal_ofReal
  have hVeq : ∫⁻ ξ, ENNReal.ofReal ((τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q) ∂stdGauss (Fin n) =
      V := by
    rw [hV, hWd]
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_wqq hn c hτ)
      (ae_of_all _ (wqq_nonneg q c τ))).symm
  have hGm : Measurable (fun p : (Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × (Fin n → ℝ) =>
      (opN (jacT p.1.1 p.1.2 (sphPt (c + τ • p.2))) ^ 2) ^ q) :=
    ((BstLean.Part153.measurable_opN_jacT_sph c τ).pow_const 2).pow_const q
  have hFm : Measurable (fun p : (Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × (Fin n → ℝ) =>
      ENNReal.ofReal ((τ ^ 2 * (normSq (c + τ • p.2))⁻¹) ^ q) *
        ENNReal.ofReal (((opN (jacT p.1.1 p.1.2 (sphPt (c + τ • p.2))) ^ 2) ^ q) ^ P')) :=
    (hwm.comp measurable_snd).mul (hGm.pow_const P').ennreal_ofReal
  let Z : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ≥0∞ :=
    fun θ => ∫⁻ ξ, ENNReal.ofReal ((τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q) *
      ENNReal.ofReal (((opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 2) ^ q) ^ P')
        ∂stdGauss (Fin n)
  have hZm : Measurable Z := Measurable.lintegral_prod_right' (f := fun p :
      (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × (Fin n → ℝ) =>
      ENNReal.ofReal ((τ ^ 2 * (normSq (c + τ • p.2))⁻¹) ^ q) *
        ENNReal.ofReal (((opN (jacT p.1.1 p.1.2 (sphPt (c + τ • p.2))) ^ 2) ^ q) ^ P')) hFm
  have hJ : ∀ θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ,
      ENNReal.ofReal (XqN q θ.1 θ.2 c τ) ^ P' * V ≤ V ^ P' * Z θ := by
    intro θ
    have hm : Measurable (fun ξ : Fin n → ℝ =>
        (opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 2) ^ q) :=
      ((BstLean.Part153.measurable_opN_jacT_sj θ.1 θ.2 c τ).pow_const 2).pow_const q
    have h := jensen_gen (stdGauss (Fin n)) hvm (wqq_nonneg q c τ) (integrable_wqq hn c hτ)
      (by rw [← WqN, ← hWd]; exact hW) hP hm (fun ξ => by positivity)
    have e1 : ∫ ξ, (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q ∂stdGauss (Fin n) = W := by
      rw [hWd]; rfl
    rw [e1, ← hV] at h
    exact h
  have hsub : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      K < XqN q θ.1 θ.2 c τ} ⊆ {θ | ENNReal.ofReal K ^ P' * V ≤ V ^ P' * Z θ} := by
    intro θ hθ
    have h1 : ENNReal.ofReal K ≤ ENNReal.ofReal (XqN q θ.1 θ.2 c τ) :=
      ENNReal.ofReal_le_ofReal (le_of_lt hθ)
    change ENNReal.ofReal K ^ P' * V ≤ V ^ P' * Z θ
    calc ENNReal.ofReal K ^ P' * V
        ≤ ENNReal.ofReal (XqN q θ.1 θ.2 c τ) ^ P' * V := by gcongr
      _ ≤ V ^ P' * Z θ := hJ θ
  have hmk := mul_meas_ge_le_lintegral (μ := nuA n)
    (f := fun θ => V ^ P' * Z θ) (measurable_const.mul hZm) (ENNReal.ofReal K ^ P' * V)
  have hint : ∫⁻ θ, V ^ P' * Z θ ∂nuA n = V ^ P' * ∫⁻ θ, Z θ ∂nuA n := by
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top hVt)]
  rw [hint] at hmk
  -- Tonelli and the moment bound
  have hZ : ∫⁻ θ, Z θ ∂nuA n ≤ V * ENNReal.ofReal ((√(n : ℝ) * j) ^ (2 * (q * P'))) := by
    change ∫⁻ θ, ∫⁻ ξ, ENNReal.ofReal ((τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q) *
      ENNReal.ofReal (((opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 2) ^ q) ^ P')
        ∂stdGauss (Fin n) ∂nuA n ≤ _
    rw [lintegral_lintegral_swap (f := fun (θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (ξ : Fin n → ℝ) =>
      ENNReal.ofReal ((τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q) *
        ENNReal.ofReal (((opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 2) ^ q) ^ P'))
      hFm.aemeasurable]
    have hpt : ∀ ξ : Fin n → ℝ, ∫⁻ θ, ENNReal.ofReal ((τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q) *
        ENNReal.ofReal (((opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 2) ^ q) ^ P') ∂nuA n ≤
        ENNReal.ofReal ((τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q) *
          ENNReal.ofReal ((√(n : ℝ) * j) ^ (2 * (q * P'))) := by
      intro ξ
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      have h := hmom _ (normSq_sphPt hn1 (c + τ • ξ))
      have e : ∀ θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ,
          ((opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 2) ^ q) ^ P' =
            opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ (2 * (q * P')) := by
        intro θ
        symm
        rw [pow_mul, pow_mul]
      simp_rw [e]
      exact h
    refine (lintegral_mono hpt).trans (le_of_eq ?_)
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hVeq]
  -- the real computation
  have hE : (√(n : ℝ) * j) ^ (2 * (q * P')) = ((n : ℝ) * j ^ 2) ^ (q * P') := by
    rw [pow_mul, mul_pow, Real.sq_sqrt hn0.le]
  have hreal : W ^ P' * (W * (√(n : ℝ) * j) ^ (2 * (q * P'))) = K ^ P' * W * D ^ (q * P') := by
    have e3 : (n : ℝ) * j ^ 2 = M * n * (j ^ 2 / M) := by field_simp
    rw [hE, hK, hD, mul_pow ((M * (n : ℝ)) ^ q) W, ← pow_mul, e3, mul_pow (M * (n : ℝ)) (j ^ 2 / M)]
    ring
  have hfin : ENNReal.ofReal K ^ P' * V * nuA n {θ | K < XqN q θ.1 θ.2 c τ} ≤
      ENNReal.ofReal K ^ P' * V * ENNReal.ofReal (D ^ (q * P')) := by
    calc ENNReal.ofReal K ^ P' * V * nuA n {θ | K < XqN q θ.1 θ.2 c τ}
        ≤ ENNReal.ofReal K ^ P' * V *
          nuA n {θ | ENNReal.ofReal K ^ P' * V ≤ V ^ P' * Z θ} := by
          gcongr
      _ ≤ V ^ P' * ∫⁻ θ, Z θ ∂nuA n := hmk
      _ ≤ V ^ P' * (V * ENNReal.ofReal ((√(n : ℝ) * j) ^ (2 * (q * P')))) := by
          gcongr
      _ = ENNReal.ofReal (W ^ P' * (W * (√(n : ℝ) * j) ^ (2 * (q * P')))) := by
          rw [hV, ENNReal.ofReal_mul (pow_nonneg hW.le P'),
            ENNReal.ofReal_mul hW.le, ENNReal.ofReal_pow hW.le]
      _ = ENNReal.ofReal (K ^ P' * W * D ^ (q * P')) := by rw [hreal]
      _ = _ := by
          rw [hV, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (pow_nonneg hK0.le P'),
            ENNReal.ofReal_pow hK0.le]
  have htop : ENNReal.ofReal K ^ P' * V * ENNReal.ofReal (D ^ (q * P')) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hVt)
      ENNReal.ofReal_ne_top
  have hr := ENNReal.toReal_mono htop hfin
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hK0.le, ENNReal.toReal_ofReal (pow_nonneg hD0 _), hV,
    ENNReal.toReal_ofReal hW.le, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hK0.le, ENNReal.toReal_ofReal hW.le] at hr
  rw [measureReal_def]
  exact le_of_mul_le_mul_left hr (mul_pos (pow_pos hK0 P') hW)

/-! ## §3 The events, their measurability and their charges -/

/-- The event `X_q ≤ (1.157·n)^q·W_q`, as a set of `((c, τ), (A₁, A₂))`. -/
def SXqN (n q : ℕ) : Set (AgFam n) :=
  {x | XqN q x.2.1 x.2.2 x.1.1 x.1.2 ≤ (1157 / 1000 * (n : ℝ)) ^ q * WqN q x.1.1 x.1.2}

/-- **The event of the noncentral bound of `Ξ₄`**: `X₂ ≤ (1.157·n)²·W₂`. -/
def SXi4n (n : ℕ) : Set (AgFam n) := SXqN n 2

/-- **The event of the noncentral bound of `Ξ₈`**: `X₄ ≤ (1.157·n)⁴·W₄`. -/
def SXi8n (n : ℕ) : Set (AgFam n) := SXqN n 4

lemma measurable_WqN_fam (q : ℕ) : Measurable (fun x : AgFam n => WqN q x.1.1 x.1.2) := by
  have hy : Measurable (fun p : AgFam n × (Fin n → ℝ) => p.1.1.1 + p.1.1.2 • p.2) :=
    (measurable_fst.comp (measurable_fst.comp measurable_fst)).add
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).smul measurable_snd)
  have hF : Measurable (fun p : AgFam n × (Fin n → ℝ) =>
      (p.1.1.2 ^ 2 * (normSq (p.1.1.1 + p.1.1.2 • p.2))⁻¹) ^ q) :=
    (((measurable_snd.comp (measurable_fst.comp measurable_fst)).pow_const 2).mul
      (measurable_normSq.comp hy).inv).pow_const q
  unfold WqN
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable

lemma measurable_XqN_fam (q : ℕ) :
    Measurable (fun x : AgFam n => XqN q x.2.1 x.2.2 x.1.1 x.1.2) := by
  have hy : Measurable (fun p : AgFam n × (Fin n → ℝ) => p.1.1.1 + p.1.1.2 • p.2) :=
    (measurable_fst.comp (measurable_fst.comp measurable_fst)).add
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).smul measurable_snd)
  have hJ : Measurable (fun p : AgFam n × (Fin n → ℝ) =>
      opN (jacT p.1.2.1 p.1.2.2 (sphPt (p.1.1.1 + p.1.1.2 • p.2)))) := by
    have h := (BstLean.Part153.measurable_opN_jacT_joint (n := n) (m := mA n) (m₂ := mA n)).comp
      ((((measurable_fst.comp measurable_snd).comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_snd).comp measurable_fst)).prodMk
        (measurable_sphPt.comp hy))
    simpa only [Function.comp_def] using h
  have hF : Measurable (fun p : AgFam n × (Fin n → ℝ) =>
      (p.1.1.2 ^ 2 * (normSq (p.1.1.1 + p.1.1.2 • p.2))⁻¹) ^ q *
        (opN (jacT p.1.2.1 p.1.2.2 (sphPt (p.1.1.1 + p.1.1.2 • p.2))) ^ 2) ^ q) :=
    ((((measurable_snd.comp (measurable_fst.comp measurable_fst)).pow_const 2).mul
      (measurable_normSq.comp hy).inv).pow_const q).mul ((hJ.pow_const 2).pow_const q)
  unfold XqN
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable

theorem measurableSet_SXqN (n q : ℕ) : MeasurableSet (SXqN n q) :=
  measurableSet_le (measurable_XqN_fam q) ((measurable_WqN_fam q).const_mul _)

/-- The event `SXi4n n` is measurable (jointly in `(c, τ, A₁, A₂)`). -/
theorem measurableSet_SXi4n (n : ℕ) : MeasurableSet (SXi4n n) := measurableSet_SXqN n 2

/-- The event `SXi8n n` is measurable (jointly in `(c, τ, A₁, A₂)`). -/
theorem measurableSet_SXi8n (n : ℕ) : MeasurableSet (SXi8n n) := measurableSet_SXqN n 4

/-- The charge of `SXqN n q` when `q·P' = 200`: at most `5·10⁻⁵` (`n ≥ 16384`, `τ > 0`;
`P = 200`, `η = 6/1000`, `jS ≤ 1.0488`). -/
theorem SXqN_charge (hn : 16384 ≤ n) {q P' : ℕ} (hq : q ≤ 4) (hP : 1 ≤ P')
    (hqP : q * P' = 200) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SXqN n q} ≤ 5 / 100000 := by
  have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      ((c, τ), θ) ∉ SXqN n q} =
      {θ | (1157 / 1000 * (n : ℝ)) ^ q * WqN q c τ < XqN q θ.1 θ.2 c τ} := by
    ext θ
    change ¬ (XqN q θ.1 θ.2 c τ ≤ (1157 / 1000 * (n : ℝ)) ^ q * WqN q c τ) ↔ _
    exact not_le
  rw [e]
  have h := markov_XqN (n := n) (q := q) (P' := P') hP (by omega) c hτ
    (BstLean.Part153.jS_nonneg n 200 (6 / 1000))
    (fun _ hx => by
      rw [hqP]
      exact BstLean.Part153.lemmaPP_i_sharp (by omega) (by norm_num)
        (by norm_num : (0 : ℝ) ≤ 6 / 1000) hx) (M := 1157 / 1000) (by norm_num)
  refine h.trans ?_
  rw [hqP]
  have hj0 := BstLean.Part153.jS_nonneg n 200 (6 / 1000)
  have hj := BstLean.Part153.jS_200_le_16384 hn
  have hj2 : jS n 200 (6 / 1000) ^ 2 ≤ (10488 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hj0 hj 2
  have hratio : jS n 200 (6 / 1000) ^ 2 / (1157 / 1000) ≤ 951 / 1000 := by
    rw [div_le_iff₀ (by norm_num)]
    refine hj2.trans (by norm_num)
  exact (pow_le_pow_left₀ (by positivity) hratio 200).trans BstLean.Part153.pow_951_le

/-- **The charge of `SXi4n`**: at most `5·10⁻⁵` (`n ≥ 16384`, `τ > 0`). -/
theorem SXi4n_charge (hn : 16384 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SXi4n n} ≤ 5 / 100000 :=
  SXqN_charge hn (q := 2) (P' := 100) (by norm_num) (by norm_num) (by norm_num) c τ hτ

/-- **The charge of `SXi8n`**: at most `5·10⁻⁵` (`n ≥ 16384`, `τ > 0`). -/
theorem SXi8n_charge (hn : 16384 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SXi8n n} ≤ 5 / 100000 :=
  SXqN_charge hn (q := 4) (P' := 50) (by norm_num) (by norm_num) (by norm_num) c τ hτ

/-! ## §4 The bounds of `Ξ₄` and `Ξ₈` on the events -/

/-- `Ξ₄ = t_A·√X₂`. -/
lemma Xi4_eq_XqN (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) :
    Xi4 A₁ A₂ c τ = 2 / ((mA n : ℕ) : ℝ) * √(XqN 2 A₁ A₂ c τ) := by
  have e : XqN 2 A₁ A₂ c τ = (τ ^ 2) ^ 2 * ∫ ξ, opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 4 *
      (normSq (c + τ • ξ))⁻¹ ^ 2 ∂stdGauss (Fin n) := by
    unfold XqN
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    ring
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg τ)]
  unfold Xi4
  ring

/-- `Ξ₈ = t_A·X₄^{1/4}`. -/
lemma Xi8_eq_XqN (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ) (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ)
    (c : Fin n → ℝ) (τ : ℝ) :
    Xi8 A₁ A₂ c τ = 2 / ((mA n : ℕ) : ℝ) * √(√(XqN 4 A₁ A₂ c τ)) := by
  have e : XqN 4 A₁ A₂ c τ = ((τ ^ 2) ^ 2) ^ 2 * ∫ ξ, opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 8 *
      (normSq (c + τ • ξ))⁻¹ ^ 4 ∂stdGauss (Fin n) := by
    unfold XqN
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    ring
  rw [e, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg _),
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (sq_nonneg τ)]
  unfold Xi8
  ring

/-- **The noncentral bound of `Ξ₄`**: on the event `SXi4n n`, for `n ≥ 16384` and
`0.46 ≤ θ_in ≤ 0.55`: `Ξ₄ ≤ 0.679·γ_A/n` (`1.157·1.0665·0.55 ≤ 0.679`). -/
theorem Xi4_noncentral (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXi4n n) :
    Xi4 A₁ A₂ c τ ≤ 679 / 1000 * (2 / (n : ℝ)) / n := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have h1 : XqN 2 A₁ A₂ c τ ≤ (1157 / 1000 * (n : ℝ)) ^ 2 * WqN 2 c τ := h
  have h2 := W2_le_theta hn c hτ hθ0 hθ1
  have hθn : (0 : ℝ) ≤ thetaC c τ := by linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 1157 / 1000 * (10665 / 10000) * thetaC c τ := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have h3 : XqN 2 A₁ A₂ c τ ≤ B ^ 2 := by
    refine h1.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq ?_))
    rw [hB]; field_simp
  have h4 : √(XqN 2 A₁ A₂ c τ) ≤ B := by
    rw [← Real.sqrt_sq hB0]; exact Real.sqrt_le_sqrt h3
  rw [Xi4_eq_XqN A₁ A₂ c τ, hmA]
  have hB' : B ≤ 679 / 1000 := by rw [hB]; nlinarith
  have h5 : 2 / (n : ℝ) ^ 2 * √(XqN 2 A₁ A₂ c τ) ≤ 2 / (n : ℝ) ^ 2 * (679 / 1000) :=
    mul_le_mul_of_nonneg_left (h4.trans hB') (by positivity)
  refine h5.trans (le_of_eq ?_)
  field_simp

/-- **The noncentral bound of `Ξ₈`**: on the event `SXi8n n`, for `n ≥ 16384` and
`0.46 ≤ θ_in ≤ 0.55`: `Ξ₈ ≤ 0.681·γ_A/n` (`1.157·1.07·0.55 ≤ 0.681`). -/
theorem Xi8_noncentral (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXi8n n) :
    Xi8 A₁ A₂ c τ ≤ 681 / 1000 * (2 / (n : ℝ)) / n := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have h1 : XqN 4 A₁ A₂ c τ ≤ (1157 / 1000 * (n : ℝ)) ^ 4 * WqN 4 c τ := h
  have h2 := W4_le_theta hn c hτ hθ0 hθ1
  have hθn : (0 : ℝ) ≤ thetaC c τ := by linarith
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 1157 / 1000 * (107 / 100) * thetaC c τ := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have h3 : XqN 4 A₁ A₂ c τ ≤ (B ^ 2) ^ 2 := by
    refine h1.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq ?_))
    rw [hB]; field_simp
  have h4 : √(XqN 4 A₁ A₂ c τ) ≤ B ^ 2 := by
    rw [← Real.sqrt_sq (sq_nonneg B)]; exact Real.sqrt_le_sqrt h3
  have h4' : √(√(XqN 4 A₁ A₂ c τ)) ≤ B := by
    rw [← Real.sqrt_sq hB0]; exact Real.sqrt_le_sqrt h4
  rw [Xi8_eq_XqN A₁ A₂ c τ, hmA]
  have hB' : B ≤ 681 / 1000 := by rw [hB]; nlinarith
  have h5 : 2 / (n : ℝ) ^ 2 * √(√(XqN 4 A₁ A₂ c τ)) ≤ 2 / (n : ℝ) ^ 2 * (681 / 1000) :=
    mul_le_mul_of_nonneg_left (h4'.trans hB') (by positivity)
  refine h5.trans (le_of_eq ?_)
  field_simp

end BstLean.Part160

open BstLean.Part160 in
#print axioms WqN_le
open BstLean.Part160 in
#print axioms W2_le_theta
open BstLean.Part160 in
#print axioms W4_le_theta
open BstLean.Part160 in
#print axioms jensen_gen
open BstLean.Part160 in
#print axioms markov_XqN
open BstLean.Part160 in
#print axioms measurableSet_SXi4n
open BstLean.Part160 in
#print axioms measurableSet_SXi8n
open BstLean.Part160 in
#print axioms SXi4n_charge
open BstLean.Part160 in
#print axioms SXi8n_charge
open BstLean.Part160 in
#print axioms Xi4_noncentral
open BstLean.Part160 in
#print axioms Xi8_noncentral
