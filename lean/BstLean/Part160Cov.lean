import BstLean.Part160Event

/-!
# Part 160 (file `Cov`): the short covariance bound with the noncentrality factor `θ`

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `proofs/option-n/theorem7-04-frame-numerator.tex`, Lemma `t7:p04:radius` (the short
covariance bound: Jensen for the weight `w = τ₀²/|y|²`, Fubini, Lemma PP (i), Markov).

Notation: `y = c + τ ξ`, `w(ξ) = τ²/|y|²`, `W = Winv c τ = E_ξ w`, `ρ² = |c|² + n τ²`,
`θ = n τ²/ρ²`, `Ξ = XiS = t_A·E_ξ[w·‖𝒥(x)Π_x‖_op²]`.

* `Winv_le`: `W ≤ τ²/((1 − ε)²(ρ² − τ²)) + √(exp(−ε²(ρ² − τ²)/(2τ²))/((n − 3)(n − 5)))`
  (the Gaussian concentration of `|y|`, a `τ`-Lipschitz function of `ξ`; NOT the paper's route by
  the Poisson mixture).
* `Winv_le_theta`: `W ≤ 1.067·θ/n` for `n ≥ 16384`, `0.46 ≤ θ ≤ 0.55` (the paper:
  `(θ/n)/(1 − 4θ/n)`).
* `jensen_w`: `(E[w G])^P·W ≤ W^P·E[w G^P]` (Jensen for the weight `w`).
* `markov_XiS_w`: `Pr(Ξ > M·γ_A·W) ≤ (j²/M)^P` from the moment bound of Lemma PP (i).
* `SXi n`: the event `Ξ ≤ 1.157·γ_A·W` as a set of `((c, τ), (A₁, A₂))`; `measurableSet_SXi`;
  `SXi_charge`: complement probability at most `5·10⁻⁵` (`n ≥ 16384`, `τ > 0`).
* `XiS_noncentral`: on the event, `Ξ ≤ 0.679·γ_A/n` for `0.46 ≤ θ ≤ 0.55`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part148 (EuLip)
open BstLean.Part150 (rhoC thetaC)
open BstLean.Part152 (opN)
open BstLean.Part153 (nrm XiS jacT nuA jS)
open scoped ENNReal

variable {n : ℕ}

/-- `W = E_ξ[τ²/|c + τξ|²]`: the mean of the weight of the Poincaré matrix. -/
noncomputable def Winv (c : Fin n → ℝ) (τ : ℝ) : ℝ :=
  ∫ ξ, τ ^ 2 * (normSq (c + τ • ξ))⁻¹ ∂stdGauss (Fin n)

/-! ## §1 The noncentral inverse radius moment -/

/-- `ξ ↦ |c + τξ|` is `τ`-Lipschitz. -/
lemma nrmShift_lip (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    EuLip (fun ξ : Fin n → ℝ => nrm (c + τ • ξ)) τ := by
  intro x y
  have h := BstLean.Part153.abs_nrm_sub_le (c + τ • x) (c + τ • y)
  have e : c + τ • x - (c + τ • y) = τ • (x - y) := by rw [smul_sub]; abel
  rw [e, BstLean.Part153.nrm_smul, abs_of_nonneg hτ] at h
  exact h

lemma measurable_nrmShift (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun ξ : Fin n → ℝ => nrm (c + τ • ξ)) :=
  (BstLean.Part153.cont_ns c τ).measurable.sqrt

/-- `(E|y|)² ≥ ρ² − τ²` (Poincaré for the `τ`-Lipschitz function `|y|`). -/
lemma mean_nrm_sq_ge (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2 ≤ (∫ ξ, nrm (c + τ • ξ) ∂stdGauss (Fin n)) ^ 2 := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hL := nrmShift_lip c hτ
  have hi := (BstLean.Part152.gaussConc_mgf_sharp hτ hL 0).1
  obtain ⟨-, hv2⟩ := BstLean.Part152.gaussVar_le_sharp hτ hL
  obtain ⟨hs1, hs2⟩ := BstLean.Part153.int_normSq_shift c τ
  obtain ⟨m₁, hm⟩ : ∃ m₁ : ℝ, m₁ = ∫ ξ, nrm (c + τ • ξ) ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← hm] at hv2 ⊢
  have e : ∀ ξ : Fin n → ℝ, (nrm (c + τ • ξ) - m₁) ^ 2 =
      normSq (c + τ • ξ) - 2 * m₁ * nrm (c + τ • ξ) + m₁ ^ 2 := by
    intro ξ
    rw [← BstLean.Part153.nrm_sq (c + τ • ξ)]
    ring
  have i2 := hi.const_mul (2 * m₁)
  have hA : ∫ ξ, (normSq (c + τ • ξ) - 2 * m₁ * nrm (c + τ • ξ) + m₁ ^ 2) ∂stdGauss (Fin n) =
      ∫ ξ, (normSq (c + τ • ξ) - 2 * m₁ * nrm (c + τ • ξ)) ∂stdGauss (Fin n) +
        ∫ _ξ, m₁ ^ 2 ∂stdGauss (Fin n) :=
    integral_add (hs1.sub i2) (integrable_const _)
  have hB : ∫ ξ, (normSq (c + τ • ξ) - 2 * m₁ * nrm (c + τ • ξ)) ∂stdGauss (Fin n) =
      ∫ ξ, normSq (c + τ • ξ) ∂stdGauss (Fin n) -
        ∫ ξ, 2 * m₁ * nrm (c + τ • ξ) ∂stdGauss (Fin n) :=
    integral_sub hs1 i2
  simp_rw [e] at hv2
  rw [hA, hB, integral_const_mul, ← hm, hs2, integral_const, probReal_univ, one_smul] at hv2
  linarith

/-- The lower tail of `|y|`: `Pr(|y| ≤ (1 − ε)·√(ρ² − τ²)) ≤ exp(−ε²(ρ² − τ²)/(2τ²))`. -/
lemma nrm_lower_tail (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {ε : ℝ} (hε : 0 ≤ ε) :
    (stdGauss (Fin n)).real
        {ξ | nrm (c + τ • ξ) ≤ (1 - ε) * √(normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2)} ≤
      exp (-(ε ^ 2 * (normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2)) / (2 * τ ^ 2)) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hL := nrmShift_lip c hτ.le
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hQ0 : 0 ≤ normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2 := by
    have := normSq_nonneg c
    nlinarith [sq_nonneg τ]
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2 := ⟨_, rfl⟩
  rw [← hQ] at hQ0 ⊢
  have hm := mean_nrm_sq_ge c hτ.le
  rw [← hQ] at hm
  have hm0 : 0 ≤ ∫ ξ, nrm (c + τ • ξ) ∂stdGauss (Fin n) :=
    integral_nonneg fun ξ => BstLean.Part153.nrm_nonneg _
  have hr : √Q ≤ ∫ ξ, nrm (c + τ • ξ) ∂stdGauss (Fin n) := by
    rw [← Real.sqrt_sq hm0]
    exact Real.sqrt_le_sqrt hm
  have ht := BstLean.Part152.gaussConc_lower_sharp hτ.le hL (t := ε * √Q)
    (mul_nonneg hε (Real.sqrt_nonneg _))
  have e : -(ε * √Q) ^ 2 / (2 * τ ^ 2) = -(ε ^ 2 * Q) / (2 * τ ^ 2) := by
    rw [mul_pow, Real.sq_sqrt hQ0]
  rw [e] at ht
  refine (measureReal_mono ?_).trans ht
  intro ξ hξ
  have h1 : nrm (c + τ • ξ) ≤ (1 - ε) * √Q := hξ
  show nrm (c + τ • ξ) ≤ ∫ y, nrm (c + τ • y) ∂stdGauss (Fin n) - ε * √Q
  linarith

/-- **The noncentral inverse radius moment** by concentration: for `0 ≤ ε < 1`,
`E[τ²/|y|²] ≤ τ²/((1 − ε)²(ρ² − τ²)) + √(exp(−ε²(ρ² − τ²)/(2τ²))·1/((n − 3)(n − 5)))`. -/
theorem Winv_le (hn : 6 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) :
    Winv c τ ≤ τ ^ 2 / ((1 - ε) ^ 2 * (normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2)) +
      √(exp (-(ε ^ 2 * (normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2)) / (2 * τ ^ 2)) *
        (1 / (((n : ℝ) - 3) * ((n : ℝ) - 5)))) := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have htail := nrm_lower_tail (by omega : 1 ≤ n) c hτ hε0
  have hQ0 : 0 < normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2 := by
    have := normSq_nonneg c
    nlinarith [sq_pos_of_pos hτ]
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2 := ⟨_, rfl⟩
  rw [← hQ] at hQ0 htail ⊢
  obtain ⟨pb, hpb⟩ : ∃ pb : ℝ, pb = exp (-(ε ^ 2 * Q) / (2 * τ ^ 2)) := ⟨_, rfl⟩
  rw [← hpb] at htail ⊢
  have hpb0 : 0 < pb := by rw [hpb]; exact exp_pos _
  obtain ⟨Ib, hIb⟩ : ∃ Ib : ℝ, Ib = 1 / (((n : ℝ) - 3) * ((n : ℝ) - 5)) := ⟨_, rfl⟩
  rw [← hIb]
  have hIb0 : 0 < Ib := by
    rw [hIb]
    have h1 : (0 : ℝ) < (n : ℝ) - 3 := by linarith
    have h2 : (0 : ℝ) < (n : ℝ) - 5 := by linarith
    positivity
  obtain ⟨hi2, hI2⟩ := BstLean.Part153.invMoment_two_le hn c hτ
  rw [← hIb] at hI2
  have hi1 := (BstLean.Part153.invMoment_one_le (by omega : 4 ≤ n) c hτ).1
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = √(pb * Ib) := ⟨_, rfl⟩
  rw [← hs]
  have hs0 : 0 < s := by rw [hs]; exact Real.sqrt_pos.mpr (mul_pos hpb0 hIb0)
  have hs2 : s ^ 2 = pb * Ib := by rw [hs]; exact Real.sq_sqrt (mul_pos hpb0 hIb0).le
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
  have hpt : ∀ ξ : Fin n → ℝ, τ ^ 2 * (normSq (c + τ • ξ))⁻¹ ≤
      τ ^ 2 / r ^ 2 + (a / 2 * Set.indicator {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r}
        (fun _ => (1 : ℝ)) ξ + 1 / (2 * a) * (τ ^ 4 * (normSq (c + τ • ξ))⁻¹ ^ 2)) := by
    intro ξ
    have hN0 : 0 ≤ (normSq (c + τ • ξ))⁻¹ := inv_nonneg.mpr (normSq_nonneg _)
    have hx0 : 0 ≤ τ ^ 2 * (normSq (c + τ • ξ))⁻¹ := mul_nonneg (sq_nonneg _) hN0
    have hq0 : 0 ≤ 1 / (2 * a) * (τ ^ 4 * (normSq (c + τ • ξ))⁻¹ ^ 2) := by positivity
    have hd0 : 0 ≤ τ ^ 2 / r ^ 2 := by positivity
    by_cases hξ : nrm (c + τ • ξ) ≤ r
    · rw [Set.indicator_of_mem (show ξ ∈ {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} from hξ)]
      obtain ⟨x, hx⟩ : ∃ x : ℝ, x = τ ^ 2 * (normSq (c + τ • ξ))⁻¹ := ⟨_, rfl⟩
      have e : τ ^ 4 * (normSq (c + τ • ξ))⁻¹ ^ 2 = x ^ 2 := by rw [hx]; ring
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
      have h3 : τ ^ 2 * (normSq (c + τ • ξ))⁻¹ ≤ τ ^ 2 * (r ^ 2)⁻¹ :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      rw [div_eq_mul_inv]
      linarith
  have hiw : Integrable (fun ξ : Fin n → ℝ => τ ^ 2 * (normSq (c + τ • ξ))⁻¹)
      (stdGauss (Fin n)) := hi1.const_mul _
  have hiI : Integrable (fun ξ : Fin n → ℝ => a / 2 *
      Set.indicator {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} (fun _ => (1 : ℝ)) ξ)
      (stdGauss (Fin n)) := ((integrable_const (1 : ℝ)).indicator hB).const_mul _
  have hiQ : Integrable (fun ξ : Fin n → ℝ => 1 / (2 * a) *
      (τ ^ 4 * (normSq (c + τ • ξ))⁻¹ ^ 2)) (stdGauss (Fin n)) :=
    (hi2.const_mul _).const_mul _
  have hmono := integral_mono hiw ((integrable_const (τ ^ 2 / r ^ 2)).add (hiI.add hiQ)) hpt
  have hsum : ∫ ξ, (τ ^ 2 / r ^ 2 + (a / 2 * Set.indicator
      {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} (fun _ => (1 : ℝ)) ξ +
        1 / (2 * a) * (τ ^ 4 * (normSq (c + τ • ξ))⁻¹ ^ 2))) ∂stdGauss (Fin n) =
      τ ^ 2 / r ^ 2 + (a / 2 * (stdGauss (Fin n)).real {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} +
        1 / (2 * a) * (τ ^ 4 * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ 2 ∂stdGauss (Fin n))) := by
    have h1 : ∫ ξ, (τ ^ 2 / r ^ 2 + (a / 2 * Set.indicator
        {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} (fun _ => (1 : ℝ)) ξ +
          1 / (2 * a) * (τ ^ 4 * (normSq (c + τ • ξ))⁻¹ ^ 2))) ∂stdGauss (Fin n) =
        ∫ _ξ, τ ^ 2 / r ^ 2 ∂stdGauss (Fin n) + ∫ ξ, (a / 2 * Set.indicator
          {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} (fun _ => (1 : ℝ)) ξ +
          1 / (2 * a) * (τ ^ 4 * (normSq (c + τ • ξ))⁻¹ ^ 2)) ∂stdGauss (Fin n) :=
      integral_add (integrable_const _) (hiI.add hiQ)
    have h2 : ∫ ξ, (a / 2 * Set.indicator
          {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} (fun _ => (1 : ℝ)) ξ +
          1 / (2 * a) * (τ ^ 4 * (normSq (c + τ • ξ))⁻¹ ^ 2)) ∂stdGauss (Fin n) =
        ∫ ξ, a / 2 * Set.indicator {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r}
          (fun _ => (1 : ℝ)) ξ ∂stdGauss (Fin n) +
        ∫ ξ, 1 / (2 * a) * (τ ^ 4 * (normSq (c + τ • ξ))⁻¹ ^ 2) ∂stdGauss (Fin n) :=
      integral_add hiI hiQ
    rw [h1, h2, integral_const, probReal_univ, one_smul, integral_const_mul,
      integral_indicator_const _ hB, smul_eq_mul, mul_one, integral_const_mul,
      integral_const_mul]
  have hW : Winv c τ ≤ τ ^ 2 / r ^ 2 +
      (a / 2 * (stdGauss (Fin n)).real {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} +
        1 / (2 * a) * (τ ^ 4 * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ 2 ∂stdGauss (Fin n))) := by
    rw [← hsum]; exact hmono
  have h1 : a / 2 * (stdGauss (Fin n)).real {ξ : Fin n → ℝ | nrm (c + τ • ξ) ≤ r} ≤
      a / 2 * pb := mul_le_mul_of_nonneg_left htail (by positivity)
  have h2 : 1 / (2 * a) * (τ ^ 4 * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ 2 ∂stdGauss (Fin n)) ≤
      1 / (2 * a) * Ib := mul_le_mul_of_nonneg_left hI2 (by positivity)
  have h3 : a / 2 * pb + 1 / (2 * a) * Ib = s := by
    rw [ha]
    have hIb' : Ib = s ^ 2 / pb := by rw [hs2]; field_simp
    rw [hIb']
    field_simp
    ring
  linarith

lemma exp_neg_13_le : exp (-13) ≤ (1504 / 10 ^ 6 : ℝ) ^ 2 := by
  have h1 : exp (-1) ≤ 36788 / 100000 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (exp_pos _) (by norm_num)]
    have := Real.exp_one_gt_d9
    linarith
  have h2 : exp (-13) = exp (-1) ^ 13 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [h2]
  exact (pow_le_pow_left₀ (exp_pos _).le h1 13).trans (by norm_num)

/-- **`E[τ²/|y|²] ≤ 1.067·θ/n`** for `n ≥ 16384` and `0.46 ≤ θ ≤ 0.55` (`ε = 3/100`). The paper
has `(θ/n)/(1 − 4θ/n)` by the Poisson mixture of central chi-square distributions. -/
theorem Winv_le_theta (hn : 16384 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100) :
    Winv c τ ≤ 1067 / 1000 * (thetaC c τ / n) := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := Winv_le (by omega : 6 ≤ n) c hτ (ε := 3 / 100) (by norm_num) (by norm_num)
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
  -- the first term
  have h1 : T / ((1 - 3 / 100) ^ 2 * (R - T)) ≤ 10629 / 10000 * (T / R) := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) hR0]
    have : R ≤ 10629 / 10000 * ((1 - 3 / 100) ^ 2 * (R - T)) := by nlinarith
    calc T * R ≤ T * (10629 / 10000 * ((1 - 3 / 100) ^ 2 * (R - T))) :=
          mul_le_mul_of_nonneg_left this hT0.le
      _ = 10629 / 10000 * T * ((1 - 3 / 100) ^ 2 * (R - T)) := by ring
  -- the second term
  have hn5 : (0 : ℝ) < (n : ℝ) - 5 := by linarith
  have hn3 : (0 : ℝ) < (n : ℝ) - 3 := by linarith
  have hexp : exp (-((3 / 100 : ℝ) ^ 2 * (R - T)) / (2 * T)) ≤ exp (-13) := by
    apply exp_le_exp.mpr
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hI : 1 / (((n : ℝ) - 3) * ((n : ℝ) - 5)) ≤ 1 / (((n : ℝ) - 5) ^ 2) := by
    apply one_div_le_one_div_of_le (pow_pos hn5 2)
    nlinarith
  have h2 : √(exp (-((3 / 100 : ℝ) ^ 2 * (R - T)) / (2 * T)) *
      (1 / (((n : ℝ) - 3) * ((n : ℝ) - 5)))) ≤ 1504 / 10 ^ 6 / ((n : ℝ) - 5) := by
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ 1504 / 10 ^ 6 / ((n : ℝ) - 5) by positivity)]
    apply Real.sqrt_le_sqrt
    have e : (1504 / 10 ^ 6 / ((n : ℝ) - 5)) ^ 2 =
        (1504 / 10 ^ 6 : ℝ) ^ 2 * (1 / (((n : ℝ) - 5) ^ 2)) := by
      field_simp
    rw [e]
    exact mul_le_mul (hexp.trans exp_neg_13_le) hI (by positivity) (by positivity)
  have h3 : 1504 / 10 ^ 6 / ((n : ℝ) - 5) ≤ 33 / 10000 * (T / R) := by
    have hTR : 46 / 100 / (n : ℝ) ≤ T / R := by
      rw [div_le_div_iff₀ hn0 hR0]
      linarith
    have h4 : 1504 / 10 ^ 6 / ((n : ℝ) - 5) ≤ 33 / 10000 * (46 / 100 / (n : ℝ)) := by
      rw [mul_div_assoc', div_le_div_iff₀ hn5 hn0]
      nlinarith
    exact h4.trans (mul_le_mul_of_nonneg_left hTR (by norm_num))
  have e : 1067 / 1000 * ((n : ℝ) * T / R / n) = 1067 / 1000 * (T / R) := by
    field_simp
  rw [e]
  have hTR0 : 0 ≤ T / R := by positivity
  linarith

/-! ## §2 Jensen for the weight and the Markov step -/

lemma measurable_wq (c : Fin n → ℝ) (τ : ℝ) :
    Measurable (fun ξ : Fin n → ℝ => τ ^ 2 * (normSq (c + τ • ξ))⁻¹) :=
  ((BstLean.Part153.cont_ns c τ).measurable.inv).const_mul _

lemma integrable_wq (hn : 4 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun ξ : Fin n → ℝ => τ ^ 2 * (normSq (c + τ • ξ))⁻¹) (stdGauss (Fin n)) :=
  (BstLean.Part153.invMoment_one_le hn c hτ).1.const_mul _

lemma wq_nonneg (c : Fin n → ℝ) (τ : ℝ) (ξ : Fin n → ℝ) :
    0 ≤ τ ^ 2 * (normSq (c + τ • ξ))⁻¹ :=
  mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (normSq_nonneg _))

/-- `W > 0`. -/
lemma Winv_pos (hn : 4 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) : 0 < Winv c τ := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hne := BstLean.Part153.ae_normSq_ne_zero (by omega : 1 ≤ n) c hτ.ne'
  unfold Winv
  rw [integral_pos_iff_support_of_nonneg_ae (ae_of_all _ (wq_nonneg c τ)) (integrable_wq hn c hτ)]
  by_contra hcon
  have h0 : stdGauss (Fin n)
      (Function.support fun ξ : Fin n → ℝ => τ ^ 2 * (normSq (c + τ • ξ))⁻¹) = 0 :=
    le_antisymm (not_lt.mp hcon) bot_le
  have h1 := measure_eq_zero_iff_ae_notMem.mp h0
  obtain ⟨ξ, hξ1, hξ2⟩ := (h1.and hne).exists
  apply hξ1
  rw [Function.mem_support]
  exact mul_ne_zero (pow_ne_zero 2 hτ.ne') (inv_ne_zero hξ2)

/-- **Jensen for the weight `w`**: `(E[w·G])^P·W ≤ W^P·E[w·G^P]` for `G ≥ 0`, `P ≥ 1`. -/
lemma jensen_w (hn : 4 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {P : ℕ} (hP : 1 ≤ P)
    {G : (Fin n → ℝ) → ℝ} (hG : Measurable G) (hG0 : ∀ ξ, 0 ≤ G ξ) :
    ENNReal.ofReal (∫ ξ, τ ^ 2 * (normSq (c + τ • ξ))⁻¹ * G ξ ∂stdGauss (Fin n)) ^ P *
        ENNReal.ofReal (Winv c τ) ≤
      ENNReal.ofReal (Winv c τ) ^ P *
        ∫⁻ ξ, ENNReal.ofReal (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) * ENNReal.ofReal (G ξ ^ P)
          ∂stdGauss (Fin n) := by
  have hW := Winv_pos hn c hτ
  obtain ⟨V, hV⟩ : ∃ V : ℝ≥0∞, V = ENNReal.ofReal (Winv c τ) := ⟨_, rfl⟩
  rw [← hV]
  have hV0 : V ≠ 0 := by rw [hV]; exact (ENNReal.ofReal_pos.mpr hW).ne'
  have hVt : V ≠ ∞ := by rw [hV]; exact ENNReal.ofReal_ne_top
  have hwm : Measurable (fun ξ : Fin n → ℝ =>
      ENNReal.ofReal (τ ^ 2 * (normSq (c + τ • ξ))⁻¹)) := (measurable_wq c τ).ennreal_ofReal
  have hVeq : ∫⁻ ξ, ENNReal.ofReal (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ∂stdGauss (Fin n) = V := by
    rw [hV]
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_wq hn c hτ)
      (ae_of_all _ (wq_nonneg c τ))).symm
  obtain ⟨μ', hμ'⟩ : ∃ μ' : Measure (Fin n → ℝ), μ' = V⁻¹ • ((stdGauss (Fin n)).withDensity
      fun ξ => ENNReal.ofReal (τ ^ 2 * (normSq (c + τ • ξ))⁻¹)) := ⟨_, rfl⟩
  have hprob : IsProbabilityMeasure μ' := by
    constructor
    rw [hμ', Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      hVeq, smul_eq_mul, ENNReal.inv_mul_cancel hV0 hVt]
  have hlint : ∀ f : (Fin n → ℝ) → ℝ≥0∞, Measurable f → ∫⁻ ξ, f ξ ∂μ' =
      V⁻¹ * ∫⁻ ξ, ENNReal.ofReal (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) * f ξ ∂stdGauss (Fin n) := by
    intro f hf
    rw [hμ', lintegral_smul_measure, lintegral_withDensity_eq_lintegral_mul _ hwm hf, smul_eq_mul]
    rfl
  have h2 := BstLean.Part153.lp_mono_nat (μ := μ') hG hG0 (q := 1) (P := P) le_rfl hP
  simp only [Nat.cast_one, pow_one, div_one, ENNReal.rpow_one] at h2
  have h3 : (∫⁻ ξ, ENNReal.ofReal (G ξ) ∂μ') ^ P ≤ ∫⁻ ξ, ENNReal.ofReal (G ξ ^ P) ∂μ' := by
    calc (∫⁻ ξ, ENNReal.ofReal (G ξ) ∂μ') ^ P
        ≤ ((∫⁻ ξ, ENNReal.ofReal (G ξ ^ P) ∂μ') ^ (1 / (P : ℝ))) ^ P := pow_le_pow_left' h2 P
      _ = _ := BstLean.Part152.enn_root_pow _ (by omega)
  rw [hlint _ hG.ennreal_ofReal, hlint _ (hG.pow_const P).ennreal_ofReal] at h3
  obtain ⟨A, hA⟩ : ∃ A : ℝ≥0∞, A = ∫⁻ ξ, ENNReal.ofReal (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) *
      ENNReal.ofReal (G ξ) ∂stdGauss (Fin n) := ⟨_, rfl⟩
  obtain ⟨Bp, hBp⟩ : ∃ Bp : ℝ≥0∞, Bp = ∫⁻ ξ, ENNReal.ofReal (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) *
      ENNReal.ofReal (G ξ ^ P) ∂stdGauss (Fin n) := ⟨_, rfl⟩
  rw [← hA, ← hBp] at h3
  rw [← hBp]
  have hle : ENNReal.ofReal (∫ ξ, τ ^ 2 * (normSq (c + τ • ξ))⁻¹ * G ξ ∂stdGauss (Fin n)) ≤ A := by
    rw [hA]
    have h := BstLean.Part153.ofReal_integral_le_lintegral (μ := stdGauss (Fin n))
      (f := fun ξ => τ ^ 2 * (normSq (c + τ • ξ))⁻¹ * G ξ)
      (fun ξ => mul_nonneg (wq_nonneg c τ ξ) (hG0 ξ))
    refine h.trans (le_of_eq ?_)
    refine lintegral_congr fun ξ => ?_
    exact ENNReal.ofReal_mul (wq_nonneg c τ ξ)
  have eA : A = V * (V⁻¹ * A) := by
    rw [← mul_assoc, ENNReal.mul_inv_cancel hV0 hVt, one_mul]
  have eB : V⁻¹ * Bp * V = Bp := by
    rw [mul_comm, ← mul_assoc, ENNReal.mul_inv_cancel hV0 hVt, one_mul]
  calc ENNReal.ofReal (∫ ξ, τ ^ 2 * (normSq (c + τ • ξ))⁻¹ * G ξ ∂stdGauss (Fin n)) ^ P * V
      ≤ A ^ P * V := by gcongr
    _ = V ^ P * ((V⁻¹ * A) ^ P * V) := by
        conv_lhs => rw [eA]
        rw [mul_pow, mul_assoc]
    _ ≤ V ^ P * (V⁻¹ * Bp * V) := by gcongr
    _ = V ^ P * Bp := by rw [eB]

/-- **The Markov step with the weight `w`** (Lemma `t7:p04:radius`): IF the moment bound
`E_θ ‖𝒥(x)Π_x‖_op^{2P} ≤ (√n·j)^{2P}` holds at every unit vector `x`, THEN
`Pr(Ξ > M·γ_A·W) ≤ (j²/M)^P`, `W = E_ξ[τ²/|y|²]`. -/
theorem markov_XiS_w {P : ℕ} (hP : 1 ≤ P) (hn : 4 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {j : ℝ} (_hj : 0 ≤ j)
    (hmom : ∀ x : Fin n → ℝ, normSq x = 1 →
      ∫⁻ θ, ENNReal.ofReal (opN (jacT θ.1 θ.2 x) ^ (2 * P)) ∂nuA n ≤
        ENNReal.ofReal ((√(n : ℝ) * j) ^ (2 * P)))
    {M : ℝ} (hM : 0 < M) :
    (nuA n).real {θ | M * (2 / (n : ℝ)) * Winv c τ < XiS θ.1 θ.2 c τ} ≤ (j ^ 2 / M) ^ P := by
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hW := Winv_pos hn c hτ
  obtain ⟨W, hWd⟩ : ∃ W : ℝ, W = Winv c τ := ⟨_, rfl⟩
  rw [← hWd] at hW ⊢
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = M * (2 / (n : ℝ)) * W := ⟨_, rfl⟩
  rw [← hK]
  have hK0 : 0 < K := by rw [hK]; positivity
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 2 / ((mA n : ℕ) : ℝ) := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := by rw [ht]; positivity
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = j ^ 2 / M := ⟨_, rfl⟩
  rw [← hD]
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  obtain ⟨V, hV⟩ : ∃ V : ℝ≥0∞, V = ENNReal.ofReal W := ⟨_, rfl⟩
  have hVt : V ≠ ∞ := by rw [hV]; exact ENNReal.ofReal_ne_top
  have hwm : Measurable (fun ξ : Fin n → ℝ =>
      ENNReal.ofReal (τ ^ 2 * (normSq (c + τ • ξ))⁻¹)) := (measurable_wq c τ).ennreal_ofReal
  have hVeq : ∫⁻ ξ, ENNReal.ofReal (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ∂stdGauss (Fin n) = V := by
    rw [hV, hWd]
    exact (ofReal_integral_eq_lintegral_ofReal (integrable_wq hn c hτ)
      (ae_of_all _ (wq_nonneg c τ))).symm
  have hGm : Measurable (fun q : (Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × (Fin n → ℝ) =>
      opN (jacT q.1.1 q.1.2 (sphPt (c + τ • q.2))) ^ 2) :=
    (BstLean.Part153.measurable_opN_jacT_sph c τ).pow_const 2
  have hFm : Measurable (fun q : (Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × (Fin n → ℝ) =>
      ENNReal.ofReal (τ ^ 2 * (normSq (c + τ • q.2))⁻¹) *
        ENNReal.ofReal ((opN (jacT q.1.1 q.1.2 (sphPt (c + τ • q.2))) ^ 2) ^ P)) :=
    (hwm.comp measurable_snd).mul (hGm.pow_const P).ennreal_ofReal
  let Z : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ → ℝ≥0∞ :=
    fun θ => ∫⁻ ξ, ENNReal.ofReal (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) *
      ENNReal.ofReal ((opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 2) ^ P) ∂stdGauss (Fin n)
  have hZm : Measurable Z := Measurable.lintegral_prod_right' (f := fun q :
      (Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ) × (Fin n → ℝ) =>
      ENNReal.ofReal (τ ^ 2 * (normSq (c + τ • q.2))⁻¹) *
        ENNReal.ofReal ((opN (jacT q.1.1 q.1.2 (sphPt (c + τ • q.2))) ^ 2) ^ P)) hFm
  have hXi : ∀ θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ,
      XiS θ.1 θ.2 c τ = t * ∫ ξ, τ ^ 2 * (normSq (c + τ • ξ))⁻¹ *
        opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 2 ∂stdGauss (Fin n) := by
    intro θ
    unfold XiS
    rw [ht, mul_assoc, ← integral_const_mul]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    ring
  have hJ : ∀ θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ,
      ENNReal.ofReal (∫ ξ, τ ^ 2 * (normSq (c + τ • ξ))⁻¹ *
        opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 2 ∂stdGauss (Fin n)) ^ P * V ≤ V ^ P * Z θ := by
    intro θ
    have hm : Measurable (fun ξ : Fin n → ℝ => opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 2) :=
      (BstLean.Part153.measurable_opN_jacT_sj θ.1 θ.2 c τ).pow_const 2
    have h := jensen_w hn c hτ hP hm (fun ξ => sq_nonneg _)
    rw [← hWd, ← hV] at h
    exact h
  have hsub : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      K < XiS θ.1 θ.2 c τ} ⊆
      {θ | ENNReal.ofReal K ^ P * V ≤ ENNReal.ofReal t ^ P * (V ^ P * Z θ)} := by
    intro θ hθ
    have h1 : ENNReal.ofReal K ≤ ENNReal.ofReal t * ENNReal.ofReal (∫ ξ,
        τ ^ 2 * (normSq (c + τ • ξ))⁻¹ * opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 2
          ∂stdGauss (Fin n)) := by
      rw [← ENNReal.ofReal_mul ht0, ← hXi θ]
      exact ENNReal.ofReal_le_ofReal (le_of_lt hθ)
    show ENNReal.ofReal K ^ P * V ≤ ENNReal.ofReal t ^ P * (V ^ P * Z θ)
    calc ENNReal.ofReal K ^ P * V
        ≤ (ENNReal.ofReal t * ENNReal.ofReal (∫ ξ,
          τ ^ 2 * (normSq (c + τ • ξ))⁻¹ * opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 2
            ∂stdGauss (Fin n))) ^ P * V := by gcongr
      _ = ENNReal.ofReal t ^ P * (ENNReal.ofReal (∫ ξ,
          τ ^ 2 * (normSq (c + τ • ξ))⁻¹ * opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 2
            ∂stdGauss (Fin n)) ^ P * V) := by rw [mul_pow, mul_assoc]
      _ ≤ ENNReal.ofReal t ^ P * (V ^ P * Z θ) := mul_le_mul' le_rfl (hJ θ)
  have hmk := mul_meas_ge_le_lintegral (μ := nuA n)
    (f := fun θ => ENNReal.ofReal t ^ P * (V ^ P * Z θ))
    (measurable_const.mul (measurable_const.mul hZm)) (ENNReal.ofReal K ^ P * V)
  have hint : ∫⁻ θ, ENNReal.ofReal t ^ P * (V ^ P * Z θ) ∂nuA n =
      ENNReal.ofReal t ^ P * (V ^ P * ∫⁻ θ, Z θ ∂nuA n) := by
    rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
      lintegral_const_mul' _ _ (ENNReal.pow_ne_top hVt)]
  rw [hint] at hmk
  -- Tonelli and the moment bound
  have hZ : ∫⁻ θ, Z θ ∂nuA n ≤ V * ENNReal.ofReal ((√(n : ℝ) * j) ^ (2 * P)) := by
    show ∫⁻ θ, ∫⁻ ξ, ENNReal.ofReal (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) *
      ENNReal.ofReal ((opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 2) ^ P) ∂stdGauss (Fin n)
        ∂nuA n ≤ _
    rw [lintegral_lintegral_swap (f := fun (θ : Matrix (Fin (mA n)) (Fin n) ℝ ×
      Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (ξ : Fin n → ℝ) =>
      ENNReal.ofReal (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) *
        ENNReal.ofReal ((opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 2) ^ P)) hFm.aemeasurable]
    have hpt : ∀ ξ : Fin n → ℝ, ∫⁻ θ, ENNReal.ofReal (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) *
        ENNReal.ofReal ((opN (jacT θ.1 θ.2 (sphPt (c + τ • ξ))) ^ 2) ^ P) ∂nuA n ≤
        ENNReal.ofReal (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) *
          ENNReal.ofReal ((√(n : ℝ) * j) ^ (2 * P)) := by
      intro ξ
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      gcongr
      have h := hmom _ (normSq_sphPt hn1 (c + τ • ξ))
      simp_rw [pow_mul] at h ⊢
      exact h
    refine (lintegral_mono hpt).trans (le_of_eq ?_)
    rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, hVeq]
  -- the real computation
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  have hE : (√(n : ℝ) * j) ^ (2 * P) = ((n : ℝ) * j ^ 2) ^ P := by
    rw [pow_mul, mul_pow, Real.sq_sqrt hn0.le]
  have hreal : t ^ P * (W ^ P * (W * (√(n : ℝ) * j) ^ (2 * P))) = K ^ P * W * D ^ P := by
    rw [hE]
    have e1 : t ^ P * (W ^ P * (W * ((n : ℝ) * j ^ 2) ^ P)) =
        (t * W * ((n : ℝ) * j ^ 2)) ^ P * W := by
      rw [mul_pow, mul_pow]; ring
    have e2 : K ^ P * W * D ^ P = (K * D) ^ P * W := by rw [mul_pow]; ring
    have e3 : t * W * ((n : ℝ) * j ^ 2) = K * D := by
      rw [ht, hK, hD, hmA]
      field_simp
    rw [e1, e2, e3]
  have hfin : ENNReal.ofReal K ^ P * V * nuA n {θ | K < XiS θ.1 θ.2 c τ} ≤
      ENNReal.ofReal K ^ P * V * ENNReal.ofReal (D ^ P) := by
    calc ENNReal.ofReal K ^ P * V * nuA n {θ | K < XiS θ.1 θ.2 c τ}
        ≤ ENNReal.ofReal K ^ P * V *
          nuA n {θ | ENNReal.ofReal K ^ P * V ≤ ENNReal.ofReal t ^ P * (V ^ P * Z θ)} := by
          gcongr
      _ ≤ ENNReal.ofReal t ^ P * (V ^ P * ∫⁻ θ, Z θ ∂nuA n) := hmk
      _ ≤ ENNReal.ofReal t ^ P * (V ^ P * (V * ENNReal.ofReal ((√(n : ℝ) * j) ^ (2 * P)))) := by
          gcongr
      _ = ENNReal.ofReal (t ^ P * (W ^ P * (W * (√(n : ℝ) * j) ^ (2 * P)))) := by
          rw [hV, ENNReal.ofReal_mul (pow_nonneg ht0 P), ENNReal.ofReal_mul (pow_nonneg hW.le P),
            ENNReal.ofReal_mul hW.le, ENNReal.ofReal_pow ht0, ENNReal.ofReal_pow hW.le]
      _ = ENNReal.ofReal (K ^ P * W * D ^ P) := by rw [hreal]
      _ = _ := by
          rw [hV, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (pow_nonneg hK0.le P),
            ENNReal.ofReal_pow hK0.le]
  have htop : ENNReal.ofReal K ^ P * V * ENNReal.ofReal (D ^ P) ≠ ∞ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hVt)
      ENNReal.ofReal_ne_top
  have hr := ENNReal.toReal_mono htop hfin
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hK0.le, ENNReal.toReal_ofReal (pow_nonneg hD0 _), hV,
    ENNReal.toReal_ofReal hW.le, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hK0.le, ENNReal.toReal_ofReal hW.le] at hr
  rw [measureReal_def]
  exact le_of_mul_le_mul_left hr (mul_pos (pow_pos hK0 P) hW)

/-! ## §3 The event, its measurability and its charge -/

/-- **The event of the short covariance bound**, as a set of `((c, τ), (A₁, A₂))`:
`Ξ ≤ 1.157·γ_A·W`, `W = E_ξ[τ²/|c + τξ|²]`. -/
def SXi (n : ℕ) : Set (AgFam n) :=
  {x | XiS x.2.1 x.2.2 x.1.1 x.1.2 ≤ 1157 / 1000 * (2 / (n : ℝ)) * Winv x.1.1 x.1.2}

lemma measurable_Winv_fam : Measurable (fun x : AgFam n => Winv x.1.1 x.1.2) := by
  have hy : Measurable (fun q : AgFam n × (Fin n → ℝ) => q.1.1.1 + q.1.1.2 • q.2) :=
    (measurable_fst.comp (measurable_fst.comp measurable_fst)).add
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).smul measurable_snd)
  have hF : Measurable (fun q : AgFam n × (Fin n → ℝ) =>
      q.1.1.2 ^ 2 * (normSq (q.1.1.1 + q.1.1.2 • q.2))⁻¹) :=
    ((measurable_snd.comp (measurable_fst.comp measurable_fst)).pow_const 2).mul
      (measurable_normSq.comp hy).inv
  unfold Winv
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable

lemma measurable_XiS_fam : Measurable (fun x : AgFam n => XiS x.2.1 x.2.2 x.1.1 x.1.2) := by
  have hy : Measurable (fun q : AgFam n × (Fin n → ℝ) => q.1.1.1 + q.1.1.2 • q.2) :=
    (measurable_fst.comp (measurable_fst.comp measurable_fst)).add
      ((measurable_snd.comp (measurable_fst.comp measurable_fst)).smul measurable_snd)
  have hJ : Measurable (fun q : AgFam n × (Fin n → ℝ) =>
      opN (jacT q.1.2.1 q.1.2.2 (sphPt (q.1.1.1 + q.1.1.2 • q.2)))) := by
    have h := (BstLean.Part153.measurable_opN_jacT_joint (n := n) (m := mA n) (m₂ := mA n)).comp
      ((((measurable_fst.comp measurable_snd).comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_snd).comp measurable_fst)).prodMk
        (measurable_sphPt.comp hy))
    simpa only [Function.comp_def] using h
  have hF : Measurable (fun q : AgFam n × (Fin n → ℝ) =>
      opN (jacT q.1.2.1 q.1.2.2 (sphPt (q.1.1.1 + q.1.1.2 • q.2))) ^ 2 *
        (normSq (q.1.1.1 + q.1.1.2 • q.2))⁻¹) :=
    (hJ.pow_const 2).mul (measurable_normSq.comp hy).inv
  unfold XiS
  exact (((measurable_snd.comp measurable_fst).pow_const 2).const_mul _).mul
    (hF.stronglyMeasurable.integral_prod_right' (ν := stdGauss (Fin n))).measurable

/-- The event `SXi n` is measurable (jointly in `(c, τ, A₁, A₂)`). -/
theorem measurableSet_SXi (n : ℕ) : MeasurableSet (SXi n) :=
  measurableSet_le measurable_XiS_fam (measurable_Winv_fam.const_mul _)

/-- **The charge of the event**: for `n ≥ 16384` and `τ > 0`,
`Pr(Ξ > 1.157·γ_A·W) ≤ 5·10⁻⁵` (`P = 200`, `η = 6/1000`, `jS ≤ 1.0488`). -/
theorem SXi_charge (hn : 16384 ≤ n) (c : Fin n → ℝ) (τ : ℝ) (hτ : 0 < τ) :
    (nuA n).real {θ | ((c, τ), θ) ∉ SXi n} ≤ 5 / 100000 := by
  have e : {θ : Matrix (Fin (mA n)) (Fin n) ℝ × Matrix (Fin (mA n)) (Fin (mA n)) ℝ |
      ((c, τ), θ) ∉ SXi n} =
      {θ | 1157 / 1000 * (2 / (n : ℝ)) * Winv c τ < XiS θ.1 θ.2 c τ} := by
    ext θ
    show ¬ (XiS θ.1 θ.2 c τ ≤ 1157 / 1000 * (2 / (n : ℝ)) * Winv c τ) ↔ _
    exact not_le
  rw [e]
  have h := markov_XiS_w (n := n) (P := 200) (by norm_num) (by omega) c hτ
    (BstLean.Part153.jS_nonneg n 200 (6 / 1000))
    (fun _ hx => BstLean.Part153.lemmaPP_i_sharp (by omega) (by norm_num)
      (by norm_num : (0 : ℝ) ≤ 6 / 1000) hx) (M := 1157 / 1000) (by norm_num)
  refine h.trans ?_
  have hj0 := BstLean.Part153.jS_nonneg n 200 (6 / 1000)
  have hj := BstLean.Part153.jS_200_le_16384 hn
  have hj2 : jS n 200 (6 / 1000) ^ 2 ≤ (10488 / 10000 : ℝ) ^ 2 := pow_le_pow_left₀ hj0 hj 2
  have hratio : jS n 200 (6 / 1000) ^ 2 / (1157 / 1000) ≤ 951 / 1000 := by
    rw [div_le_iff₀ (by norm_num)]
    refine hj2.trans (by norm_num)
  exact (pow_le_pow_left₀ (by positivity) hratio 200).trans BstLean.Part153.pow_951_le

/-- **The short covariance bound with the noncentrality factor** (Lemma `t7:p04:radius`): on
the event `SXi n`, for `n ≥ 16384` and `0.46 ≤ θ_in ≤ 0.55`: `Ξ ≤ 0.679·γ_A/n`
(`1.157·1.067·0.55 ≤ 0.679`). -/
theorem XiS_noncentral (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXi n) :
    XiS A₁ A₂ c τ ≤ 679 / 1000 * (2 / (n : ℝ)) / n := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h1 : XiS A₁ A₂ c τ ≤ 1157 / 1000 * (2 / (n : ℝ)) * Winv c τ := h
  have h2 := Winv_le_theta hn c hτ hθ0 hθ1
  have h3 : 1067 / 1000 * (thetaC c τ / n) ≤ 1067 / 1000 * (55 / 100 / (n : ℝ)) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hθ1 hn0.le) (by norm_num)
  have h4 : 1157 / 1000 * (2 / (n : ℝ)) * Winv c τ ≤
      1157 / 1000 * (2 / (n : ℝ)) * (1067 / 1000 * (55 / 100 / (n : ℝ))) :=
    mul_le_mul_of_nonneg_left (h2.trans h3) (by positivity)
  refine h1.trans (h4.trans ?_)
  have e : 1157 / 1000 * (2 / (n : ℝ)) * (1067 / 1000 * (55 / 100 / (n : ℝ))) =
      (1157 / 1000 * (1067 / 1000) * (55 / 100)) * (2 / (n : ℝ)) / n := by ring
  rw [e]
  have hg : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num) hg) hn0.le

end BstLean.Part160

open BstLean.Part160 in
#print axioms Winv_le
open BstLean.Part160 in
#print axioms Winv_le_theta
open BstLean.Part160 in
#print axioms jensen_w
open BstLean.Part160 in
#print axioms markov_XiS_w
open BstLean.Part160 in
#print axioms measurableSet_SXi
open BstLean.Part160 in
#print axioms SXi_charge
open BstLean.Part160 in
#print axioms XiS_noncentral
