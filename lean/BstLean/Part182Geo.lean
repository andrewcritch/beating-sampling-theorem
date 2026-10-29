import BstLean.Part182Def
import BstLean.Part150P45b
import BstLean.Part152LM
import BstLean.Part131Block
import BstLean.Part132Cos

/-!
# Part 182 (file `Geo`): the input sets `Ω`, `Γ` of the Schur test — geometry and tails

No proof is left open; no `native_decide` or `axiom` is used.

Paper source: `proofs/option-n/theorem7-04-frame-numerator.tex`, § "Input sets and the weighted
Schur test". Here `y = c + τξ`, `x = sphPt y`, `θ = thetaC c τ`, `ρ² = rhoC c τ ^ 2`,
`u = uC c`, `a_n = √(θ(1−θ)/n)`, `b_n = t₀√(θ/((1−θ)n))`, `r₋ = 2t₀a_n + 2θ√(z₀/n)`,
`r₊ = r₋ + 2θz₀/n`.

* `omega_radius`: on `Ω`, `(1 − r₋)ρ² ≤ |y|² ≤ (1 + r₊)ρ²`.
* `omega_weight`: on `Ω` (`r₋ < 1`), `w = τ²/|y|² ≤ (θ/n)/(1 − r₋)`.
* `gamma_dot`: on `Γ` (`b_n < 1`, `r₋ < 1`), `x·x' ≤ c₊`, and `c₋ ≤ x·x'` when the numerator of
  `c₋` is nonnegative (the paper's formulas for `c₊`, `c₋`).
* `lin_tail`: `Pr(|v·ξ| > t) ≤ 2e^{−t²/(2L²)}` for `|v| ≤ L`.
* `omega_compl_le`: `Pr(Ωᶜ) ≤ 2e^{−t₀²/2} + 2e^{−z₀}` (paper: `erfc(t₀/√2) + 2e^{−z₀}`; the
  Gaussian tail here is the weaker Chernoff form).
* `gamma_row_le`: for fixed `ξ ∈ Ω`, `Pr_{ξ'}(ξ' ∈ Ω, (ξ, ξ') ∉ Γ) ≤ 2e^{−t₁²/2}` (paper:
  `erfc(t₁/√2)`).
* `measurableSet_OmegaS`, `measurableSet_GammaS`.
-/

namespace BstLean.Part182

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part152
open BstLean.Part153 (nrm abs_dot_le_nrm)
open BstLean.Part150 (thetaC rhoC)

variable {n : ℕ}

lemma geo_normSq_add_smul (c ξ : Fin n → ℝ) (τ : ℝ) :
    normSq (c + τ • ξ) = normSq c + 2 * τ * (c ⬝ᵥ ξ) + τ ^ 2 * normSq ξ := by
  unfold normSq dotProduct
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma geo_nrm_sq (v : Fin n → ℝ) : nrm v ^ 2 = normSq v := by
  unfold nrm; exact Real.sq_sqrt (BstLean.Part130.normSq_nonneg v)

lemma c_dot_uC {c : Fin n → ℝ} (hc : c ≠ 0) (ξ : Fin n → ℝ) :
    c ⬝ᵥ ξ = nrm c * (uC c ⬝ᵥ ξ) := by
  have hC : nrm c ≠ 0 := by
    intro h
    have h2 := geo_nrm_sq c
    rw [h] at h2
    apply hc
    funext i
    have : c i ^ 2 ≤ normSq c := Finset.single_le_sum (f := fun j => c j ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have : c i ^ 2 = 0 := le_antisymm (by rw [← h2] at this; simpa using this) (sq_nonneg _)
    simpa using this
  unfold uC
  rw [smul_dotProduct, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hC, one_mul]

lemma normSq_uC_le (c : Fin n → ℝ) : normSq (uC c) ≤ 1 := by
  unfold uC
  rw [show normSq ((nrm c)⁻¹ • c) = (nrm c)⁻¹ ^ 2 * normSq c by
    unfold normSq; simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring]
  rw [← geo_nrm_sq, ← mul_pow]
  by_cases h : nrm c = 0
  · simp [h]
  · rw [inv_mul_cancel₀ h]; norm_num

lemma uC_dot_self {c : Fin n → ℝ} (hc : c ≠ 0) : uC c ⬝ᵥ uC c = 1 := by
  have h := c_dot_uC hc (uC c)
  have h2 : c ⬝ᵥ uC c = nrm c := by
    unfold uC
    rw [dotProduct_smul, smul_eq_mul]
    have : c ⬝ᵥ c = nrm c ^ 2 := by rw [geo_nrm_sq]; unfold normSq dotProduct; simp [sq]
    rw [this]
    have hC : nrm c ≠ 0 := by
      intro h0; have := c_dot_uC hc c; rw [h0] at this
      have hcc : c ⬝ᵥ c = 0 := by simpa using this
      apply hc; funext i
      have : ∑ j, c j * c j = 0 := hcc
      have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (c j))).1 this i
        (Finset.mem_univ _)
      simpa using hs
    field_simp
  rw [h2] at h
  have hC : nrm c ≠ 0 := by
    intro h0; rw [h0] at h2
    have : c ⬝ᵥ c = 0 := by
      have := c_dot_uC hc c; rw [h0] at this; simpa using this
    apply hc; funext i
    have hs := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (c j))).1 this i
      (Finset.mem_univ _)
    simpa using hs
  have := mul_left_cancel₀ hC (h.symm.trans (mul_one _).symm)
  exact this


/-- The constants: `ρ² θ = nτ²`, `ρ²(1−θ) = |c|²`. -/
lemma geo_rho_theta (hn : 0 < n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    0 < rhoC c τ ^ 2 ∧ rhoC c τ ^ 2 * thetaC c τ = (n : ℝ) * τ ^ 2 ∧
      rhoC c τ ^ 2 * (1 - thetaC c τ) = normSq c ∧ rhoC c τ ^ 2 = normSq c + (n : ℝ) * τ ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hc0 := BstLean.Part130.normSq_nonneg c
  have hR : rhoC c τ ^ 2 = normSq c + (n : ℝ) * τ ^ 2 := by
    unfold rhoC; rw [Real.sq_sqrt (by positivity)]
  have hR0 : 0 < rhoC c τ ^ 2 := by rw [hR]; positivity
  have hρ : rhoC c τ ≠ 0 := by intro h; rw [h] at hR0; norm_num at hR0
  refine ⟨hR0, ?_, ?_, hR⟩
  · unfold thetaC; field_simp
  · unfold thetaC; rw [mul_sub, mul_one, mul_div_cancel₀ _ (pow_ne_zero 2 hρ), hR]; ring

/-- `τ|c| = ρ²·√(θ(1−θ)/n)`. -/
lemma tau_nrm_eq (hn : 0 < n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    τ * nrm c = rhoC c τ ^ 2 * √(thetaC c τ * (1 - thetaC c τ) / n) := by
  obtain ⟨hR0, h1, h2, -⟩ := geo_rho_theta hn c hτ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have e : thetaC c τ * (1 - thetaC c τ) / n = (τ * nrm c / rhoC c τ ^ 2) ^ 2 := by
    rw [div_pow, mul_pow, geo_nrm_sq, ← h2]
    have : thetaC c τ = (n : ℝ) * τ ^ 2 / rhoC c τ ^ 2 := by
      rw [eq_div_iff hR0.ne']; linarith
    rw [this]; field_simp
  rw [e, Real.sqrt_sq (by unfold nrm; positivity)]
  rw [mul_div_cancel₀ _ hR0.ne']

/-- `√(z/n) = √(n z)/n`. -/
lemma geo_sqrt_div_n (hn : 0 < n) {z : ℝ} (hz : 0 ≤ z) : √(z / n) = √((n : ℝ) * z) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have e : z / n = (√((n : ℝ) * z) / n) ^ 2 := by
    rw [div_pow, Real.sq_sqrt (by positivity)]; field_simp
  rw [e, Real.sqrt_sq (by positivity)]

/-- **The radius on `Ω`** (paper: `1 − r₋ ≤ |y|²/ρ² ≤ 1 + r₊`). -/
theorem omega_radius (hn : 0 < n) {c : Fin n → ℝ} (hc : c ≠ 0) {τ t0 z0 : ℝ} (hτ : 0 < τ)
    (ht0 : 0 ≤ t0) (hz0 : 0 ≤ z0) {ξ : Fin n → ℝ} (hξ : ξ ∈ OmegaS c t0 z0) :
    (1 - (2 * t0 * √(thetaC c τ * (1 - thetaC c τ) / n) + 2 * thetaC c τ * √(z0 / n))) *
        rhoC c τ ^ 2 ≤ normSq (c + τ • ξ) ∧
      normSq (c + τ • ξ) ≤ (1 + (2 * t0 * √(thetaC c τ * (1 - thetaC c τ) / n) +
        2 * thetaC c τ * √(z0 / n) + 2 * thetaC c τ * z0 / n)) * rhoC c τ ^ 2 := by
  obtain ⟨hR0, h1, h2, hR⟩ := geo_rho_theta hn c hτ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hs, hQ1, hQ2⟩ := hξ
  have hTC := tau_nrm_eq hn c hτ
  have hsq := geo_sqrt_div_n hn hz0
  rw [geo_normSq_add_smul, c_dot_uC hc]
  set R := rhoC c τ ^ 2
  set θ := thetaC c τ
  set a := √(θ * (1 - θ) / n)
  set s := uC c ⬝ᵥ ξ
  set C := nrm c
  have hC0 : 0 ≤ τ * C := by unfold C nrm; positivity
  have hs1 := (abs_le.mp hs).1
  have hs2 := (abs_le.mp hs).2
  have hcs1 : -(τ * C * t0) ≤ τ * C * s := by nlinarith
  have hcs2 : τ * C * s ≤ τ * C * t0 := by nlinarith
  have hθR : θ * R = (n : ℝ) * τ ^ 2 := by rw [mul_comm]; exact h1
  have hCC : normSq c = C ^ 2 := (geo_nrm_sq c).symm
  have key : θ * R * √(z0 / n) = τ ^ 2 * √((n : ℝ) * z0) := by
    rw [hθR, hsq]; field_simp
  have key2 : θ * R * z0 / n = τ ^ 2 * z0 := by rw [hθR]; field_simp
  have hτ2 : 0 ≤ τ ^ 2 := by positivity
  constructor
  · have e : (1 - (2 * t0 * a + 2 * θ * √(z0 / n))) * R =
        (normSq c + n * τ ^ 2) - 2 * t0 * (R * a) - 2 * (θ * R * √(z0 / n)) := by
      rw [← hR]; ring
    rw [e, key, ← hTC]
    nlinarith [mul_le_mul_of_nonneg_left hQ1 hτ2]
  · have e : (1 + (2 * t0 * a + 2 * θ * √(z0 / n) + 2 * θ * z0 / n)) * R =
        (normSq c + n * τ ^ 2) + 2 * t0 * (R * a) + 2 * (θ * R * √(z0 / n)) +
          2 * (θ * R * z0 / n) := by
      rw [← hR]; ring
    rw [e, key, key2, ← hTC]
    nlinarith [mul_le_mul_of_nonneg_left hQ2 hτ2]

/-- **The weight on `Ω`**: `w = τ²/|y|² ≤ (θ/n)/(1 − r₋)` if `r₋ < 1`. -/
theorem omega_weight (hn : 0 < n) {c : Fin n → ℝ} (hc : c ≠ 0) {τ t0 z0 : ℝ} (hτ : 0 < τ)
    (ht0 : 0 ≤ t0) (hz0 : 0 ≤ z0) {ξ : Fin n → ℝ} (hξ : ξ ∈ OmegaS c t0 z0)
    (hr : 2 * t0 * √(thetaC c τ * (1 - thetaC c τ) / n) + 2 * thetaC c τ * √(z0 / n) < 1) :
    τ ^ 2 * (normSq (c + τ • ξ))⁻¹ ≤
      thetaC c τ / n / (1 - (2 * t0 * √(thetaC c τ * (1 - thetaC c τ) / n) +
        2 * thetaC c τ * √(z0 / n))) := by
  obtain ⟨hR0, h1, -, -⟩ := geo_rho_theta hn c hτ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hy := (omega_radius hn hc hτ ht0 hz0 hξ).1
  set r := 2 * t0 * √(thetaC c τ * (1 - thetaC c τ) / n) + 2 * thetaC c τ * √(z0 / n)
  have hpos : 0 < (1 - r) * rhoC c τ ^ 2 := mul_pos (by linarith) hR0
  have hy0 : 0 < normSq (c + τ • ξ) := lt_of_lt_of_le hpos hy
  rw [← div_eq_mul_inv, div_le_div_iff₀ hy0 (by linarith)]
  have : τ ^ 2 = thetaC c τ / n * rhoC c τ ^ 2 := by
    rw [div_mul_eq_mul_div, eq_div_iff hnR.ne']; linarith
  rw [this]
  have hθ : 0 ≤ thetaC c τ / n := by
    unfold thetaC; positivity
  nlinarith [mul_le_mul_of_nonneg_left hy hθ]


/-- `ξ_⊥·ξ'_⊥ = ξ_⊥·ξ'` (for `u` a unit vector or `0`). -/
lemma perpC_dot (c ξ ξ' : Fin n → ℝ) : perpC c ξ ⬝ᵥ perpC c ξ' = perpC c ξ ⬝ᵥ ξ' := by
  by_cases hc : c = 0
  · have : uC c = 0 := by unfold uC; rw [hc]; simp
    unfold perpC; rw [this]; simp
  · have hu := uC_dot_self hc
    unfold perpC
    rw [dotProduct_sub, dotProduct_smul, smul_eq_mul]
    have : (ξ - (uC c ⬝ᵥ ξ) • uC c) ⬝ᵥ uC c = 0 := by
      rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, hu, dotProduct_comm]; ring
    rw [this]; ring

/-- `ξ·ξ' = (u·ξ)(u·ξ') + ξ_⊥·ξ'_⊥` (`c ≠ 0`). -/
lemma geo_dot_split {c : Fin n → ℝ} (hc : c ≠ 0) (ξ ξ' : Fin n → ℝ) :
    ξ ⬝ᵥ ξ' = (uC c ⬝ᵥ ξ) * (uC c ⬝ᵥ ξ') + perpC c ξ ⬝ᵥ perpC c ξ' := by
  rw [perpC_dot]
  unfold perpC
  rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]; ring

/-- `y·y' = (|c| + τ u·ξ)(|c| + τ u·ξ') + τ² ξ_⊥·ξ'_⊥`. -/
lemma geo_yy_eq {c : Fin n → ℝ} (hc : c ≠ 0) (τ : ℝ) (ξ ξ' : Fin n → ℝ) :
    (c + τ • ξ) ⬝ᵥ (c + τ • ξ') = (nrm c + τ * (uC c ⬝ᵥ ξ)) * (nrm c + τ * (uC c ⬝ᵥ ξ')) +
      τ ^ 2 * (perpC c ξ ⬝ᵥ perpC c ξ') := by
  have hcc : c ⬝ᵥ c = nrm c ^ 2 := by rw [geo_nrm_sq]; unfold normSq dotProduct; simp [sq]
  have e : (c + τ • ξ) ⬝ᵥ (c + τ • ξ') = c ⬝ᵥ c + τ * (c ⬝ᵥ ξ') + τ * (ξ ⬝ᵥ c) +
      τ ^ 2 * (ξ ⬝ᵥ ξ') := by
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]; ring
  rw [e, hcc, dotProduct_comm ξ c, c_dot_uC hc ξ', c_dot_uC hc ξ, geo_dot_split hc ξ ξ']; ring

/-- Real-number step: bounds of a quotient. -/
lemma geo_quot_bounds {Y P R U L rm rp : ℝ} (hR : 0 < R) (hrm : rm < 1)
    (Plo : (1 - rm) * R ≤ P) (Pup : P ≤ (1 + rp) * R) (Yup : Y ≤ R * U) (hU : 0 ≤ U)
    (Ylo : R * L ≤ Y) :
    Y / P ≤ U / (1 - rm) ∧ (0 ≤ L → L / (1 + rp) ≤ Y / P) := by
  have hP0 : 0 < (1 - rm) * R := mul_pos (by linarith) hR
  have hPP : 0 < P := lt_of_lt_of_le hP0 Plo
  have h1p : 0 < 1 + rp := by
    by_contra h; push_neg at h
    have : (1 + rp) * R ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hR.le
    linarith
  constructor
  · calc Y / P ≤ R * U / P := div_le_div_of_nonneg_right Yup hPP.le
      _ ≤ R * U / ((1 - rm) * R) := div_le_div_of_nonneg_left (by positivity) hP0 Plo
      _ = U / (1 - rm) := by rw [mul_comm (1 - rm) R, mul_div_mul_left _ _ hR.ne']
  · intro hL
    calc L / (1 + rp) = R * L / ((1 + rp) * R) := by
          rw [mul_comm (1 + rp) R, mul_div_mul_left _ _ hR.ne']
      _ ≤ R * L / P := div_le_div_of_nonneg_left (by positivity) hPP Pup
      _ ≤ Y / P := div_le_div_of_nonneg_right Ylo hPP.le

lemma geo_nrm_c_pos {c : Fin n → ℝ} (hc : c ≠ 0) : 0 < nrm c := by
  have : 0 < normSq c := by
    rcases (BstLean.Part130.normSq_nonneg c).lt_or_eq with h | h
    · exact h
    · exfalso; apply hc
      have h0 : ∑ i, c i ^ 2 = 0 := h.symm
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (c j))).1 h0 i
        (Finset.mem_univ _)
      simpa using this
  unfold nrm; exact Real.sqrt_pos.mpr this

/-- `τ t₀ = |c|·b_n`. -/
lemma tau_t0_eq (hn : 0 < n) {c : Fin n → ℝ} (hc : c ≠ 0) {τ : ℝ} (hτ : 0 < τ) (t0 : ℝ) :
    τ * t0 = nrm c * (t0 * √(thetaC c τ / ((1 - thetaC c τ) * n))) := by
  obtain ⟨hR0, h1, h2, -⟩ := geo_rho_theta hn c hτ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hC := geo_nrm_c_pos hc
  have hc2 : normSq c = nrm c ^ 2 := (geo_nrm_sq c).symm
  have e : thetaC c τ / ((1 - thetaC c τ) * n) = (τ / nrm c) ^ 2 := by
    have : thetaC c τ = (n : ℝ) * τ ^ 2 / rhoC c τ ^ 2 := by rw [eq_div_iff hR0.ne']; linarith
    have h1θ : 1 - thetaC c τ = nrm c ^ 2 / rhoC c τ ^ 2 := by
      rw [eq_div_iff hR0.ne']; linarith
    have hρ : rhoC c τ ≠ 0 := by intro h; rw [h] at hR0; norm_num at hR0
    rw [h1θ, this, div_pow]; field_simp
  rw [e, Real.sqrt_sq (by positivity)]; field_simp

/-- The numerator bounds on `Γ`: `R·L ≤ y·y' ≤ R·U`. -/
lemma yy_bounds (hn : 0 < n) {c : Fin n → ℝ} (hc : c ≠ 0) {τ t0 z0 t1 : ℝ} (hτ : 0 < τ)
    {ξ ξ' : Fin n → ℝ} (hp : (ξ, ξ') ∈ GammaS c t0 z0 t1)
    (hb : t0 * √(thetaC c τ / ((1 - thetaC c τ) * n)) < 1) :
    (c + τ • ξ) ⬝ᵥ (c + τ • ξ') ≤ rhoC c τ ^ 2 * ((1 - thetaC c τ) *
        (1 + t0 * √(thetaC c τ / ((1 - thetaC c τ) * n))) ^ 2 +
        thetaC c τ / n * t1 * gPlus n z0) ∧
    rhoC c τ ^ 2 * ((1 - thetaC c τ) * (1 - t0 * √(thetaC c τ / ((1 - thetaC c τ) * n))) ^ 2 -
        thetaC c τ / n * t1 * gPlus n z0) ≤ (c + τ • ξ) ⬝ᵥ (c + τ • ξ') := by
  obtain ⟨hR0, h1, h2, -⟩ := geo_rho_theta hn c hτ
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have htb := tau_t0_eq hn hc hτ t0
  have hC := geo_nrm_c_pos hc
  obtain ⟨hξ, hξ', hpp⟩ := hp
  have hs := (abs_le.mp hξ.1)
  have hs' := (abs_le.mp hξ'.1)
  have hp1 := abs_le.mp hpp
  rw [geo_yy_eq hc]
  generalize hbg : t0 * √(thetaC c τ / ((1 - thetaC c τ) * n)) = b at htb hb ⊢
  generalize uC c ⬝ᵥ ξ = s at hs ⊢
  generalize uC c ⬝ᵥ ξ' = s' at hs' ⊢
  generalize perpC c ξ ⬝ᵥ perpC c ξ' = p at hp1 ⊢
  have hτ2 : τ ^ 2 = thetaC c τ / n * rhoC c τ ^ 2 := by
    rw [div_mul_eq_mul_div, eq_div_iff hnR.ne']; linarith
  have hCR : nrm c ^ 2 = (1 - thetaC c τ) * rhoC c τ ^ 2 := by
    rw [geo_nrm_sq, ← h2]; ring
  generalize nrm c = C at htb hC hCR ⊢
  have hb0 : 0 ≤ b := by
    rw [← hbg]
    have : 0 ≤ t0 := le_trans (abs_nonneg _) hξ.1
    positivity
  have f1 : C * (1 - b) ≤ C + τ * s := by nlinarith
  have f2 : C + τ * s ≤ C * (1 + b) := by nlinarith
  have f1' : C * (1 - b) ≤ C + τ * s' := by nlinarith
  have f2' : C + τ * s' ≤ C * (1 + b) := by nlinarith
  have hCb : 0 ≤ C * (1 - b) := mul_nonneg hC.le (by linarith)
  have P1 : (C + τ * s) * (C + τ * s') ≤ C ^ 2 * (1 + b) ^ 2 := by
    rw [← mul_pow, sq]; exact mul_le_mul f2 f2' (by linarith) (by linarith)
  have P2 : C ^ 2 * (1 - b) ^ 2 ≤ (C + τ * s) * (C + τ * s') := by
    rw [← mul_pow, sq]; exact mul_le_mul f1 f1' hCb (by linarith)
  have hτ0 : 0 ≤ τ ^ 2 := by positivity
  have q1 : τ ^ 2 * p ≤ τ ^ 2 * (t1 * gPlus n z0) := mul_le_mul_of_nonneg_left hp1.2 hτ0
  have q2 : τ ^ 2 * (-(t1 * gPlus n z0)) ≤ τ ^ 2 * p := mul_le_mul_of_nonneg_left hp1.1 hτ0
  rw [hCR, hτ2] at *
  constructor <;> nlinarith

/-- The product of the norms on `Γ`. -/
lemma nrm_prod_bounds (hn : 0 < n) {c : Fin n → ℝ} (hc : c ≠ 0) {τ t0 z0 : ℝ} (hτ : 0 < τ)
    (ht0 : 0 ≤ t0) (hz0 : 0 ≤ z0) {ξ ξ' : Fin n → ℝ} (hξ : ξ ∈ OmegaS c t0 z0)
    (hξ' : ξ' ∈ OmegaS c t0 z0) {rm rp : ℝ}
    (hrm : rm = 2 * t0 * √(thetaC c τ * (1 - thetaC c τ) / n) + 2 * thetaC c τ * √(z0 / n))
    (hrp : rp = rm + 2 * thetaC c τ * z0 / n) (hr : rm < 1) :
    (1 - rm) * rhoC c τ ^ 2 ≤ nrm (c + τ • ξ) * nrm (c + τ • ξ') ∧
      nrm (c + τ • ξ) * nrm (c + τ • ξ') ≤ (1 + rp) * rhoC c τ ^ 2 := by
  obtain ⟨hR0, -, -, -⟩ := geo_rho_theta hn c hτ
  have r1 := omega_radius hn hc hτ ht0 hz0 hξ
  have r2 := omega_radius hn hc hτ ht0 hz0 hξ'
  rw [← hrm] at r1 r2
  rw [show rm + 2 * thetaC c τ * z0 / n = rp by rw [hrp]] at r1 r2
  have hy0 : 0 < normSq (c + τ • ξ) := lt_of_lt_of_le (mul_pos (by linarith) hR0) r1.1
  have hy0' : 0 < normSq (c + τ • ξ') := lt_of_lt_of_le (mul_pos (by linarith) hR0) r2.1
  have eP : nrm (c + τ • ξ) * nrm (c + τ • ξ') =
      √(normSq (c + τ • ξ) * normSq (c + τ • ξ')) := by
    unfold nrm; rw [Real.sqrt_mul hy0.le]
  rw [eP]
  constructor
  · apply Real.le_sqrt_of_sq_le
    have := mul_le_mul r1.1 r2.1 (mul_pos (by linarith) hR0).le hy0.le
    rw [sq]; exact this
  · have hrp0 : 0 ≤ (1 + rp) * rhoC c τ ^ 2 := le_trans hy0.le r1.2
    have := mul_le_mul r1.2 r2.2 hy0'.le hrp0
    calc √(normSq (c + τ • ξ) * normSq (c + τ • ξ')) ≤ √(((1 + rp) * rhoC c τ ^ 2) ^ 2) :=
          Real.sqrt_le_sqrt (by rw [sq]; exact this)
      _ = (1 + rp) * rhoC c τ ^ 2 := Real.sqrt_sq hrp0

/-- **The inner product of inputs on `Γ`** (paper: `c₋ ≤ x·x' ≤ c₊`). With
`a_n = √(θ(1−θ)/n)`, `b_n = t₀√(θ/((1−θ)n)) < 1`, `r₋ = 2t₀a_n + 2θ√(z₀/n) < 1`,
`r₊ = r₋ + 2θz₀/n`: `x·x' ≤ ((1−θ)(1+b_n)² + (θ/n)t₁g₊)/(1 − r₋)`, and, if the numerator
`L = (1−θ)(1−b_n)² − (θ/n)t₁g₊ ≥ 0`, `x·x' ≥ L/(1 + r₊)`. -/
theorem gamma_dot (hn : 0 < n) {c : Fin n → ℝ} (hc : c ≠ 0) {τ t0 z0 t1 : ℝ} (hτ : 0 < τ)
    (ht0 : 0 ≤ t0) (hz0 : 0 ≤ z0) (ht1 : 0 ≤ t1) (hθ1 : thetaC c τ < 1)
    {ξ ξ' : Fin n → ℝ} (hp : (ξ, ξ') ∈ GammaS c t0 z0 t1)
    (hb : t0 * √(thetaC c τ / ((1 - thetaC c τ) * n)) < 1)
    (hr : 2 * t0 * √(thetaC c τ * (1 - thetaC c τ) / n) + 2 * thetaC c τ * √(z0 / n) < 1) :
    sphPt (c + τ • ξ) ⬝ᵥ sphPt (c + τ • ξ') ≤
      ((1 - thetaC c τ) * (1 + t0 * √(thetaC c τ / ((1 - thetaC c τ) * n))) ^ 2 +
        thetaC c τ / n * t1 * gPlus n z0) /
        (1 - (2 * t0 * √(thetaC c τ * (1 - thetaC c τ) / n) + 2 * thetaC c τ * √(z0 / n))) ∧
    (0 ≤ (1 - thetaC c τ) * (1 - t0 * √(thetaC c τ / ((1 - thetaC c τ) * n))) ^ 2 -
        thetaC c τ / n * t1 * gPlus n z0 →
      ((1 - thetaC c τ) * (1 - t0 * √(thetaC c τ / ((1 - thetaC c τ) * n))) ^ 2 -
        thetaC c τ / n * t1 * gPlus n z0) /
        (1 + (2 * t0 * √(thetaC c τ * (1 - thetaC c τ) / n) + 2 * thetaC c τ * √(z0 / n) +
          2 * thetaC c τ * z0 / n)) ≤ sphPt (c + τ • ξ) ⬝ᵥ sphPt (c + τ • ξ')) := by
  obtain ⟨hR0, -, -, -⟩ := geo_rho_theta hn c hτ
  have hY := yy_bounds hn hc hτ hp hb
  have hN := nrm_prod_bounds hn hc hτ ht0 hz0 hp.1 hp.2.1 rfl rfl hr
  have hy0 : 0 < normSq (c + τ • ξ) :=
    lt_of_lt_of_le (mul_pos (by linarith) hR0) (omega_radius hn hc hτ ht0 hz0 hp.1).1
  have hy0' : 0 < normSq (c + τ • ξ') :=
    lt_of_lt_of_le (mul_pos (by linarith) hR0) (omega_radius hn hc hτ ht0 hz0 hp.2.1).1
  have hdot : sphPt (c + τ • ξ) ⬝ᵥ sphPt (c + τ • ξ') =
      (c + τ • ξ) ⬝ᵥ (c + τ • ξ') / (nrm (c + τ • ξ) * nrm (c + τ • ξ')) :=
    BstLean.Part132.dotp_sphPt _ _ hy0.ne' hy0'.ne'
  have hθ0 : 0 ≤ thetaC c τ := by unfold thetaC; positivity
  have hU : 0 ≤ (1 - thetaC c τ) * (1 + t0 * √(thetaC c τ / ((1 - thetaC c τ) * n))) ^ 2 +
      thetaC c τ / n * t1 * gPlus n z0 := by
    have : 0 ≤ gPlus n z0 := Real.sqrt_nonneg _
    have : 0 ≤ 1 - thetaC c τ := by linarith
    positivity
  rw [hdot]
  exact geo_quot_bounds hR0 hr hN.1 hN.2 hY.1 hU hY.2


/-! ## Tails -/

lemma geo_measurable_dot (v : Fin n → ℝ) : Measurable (fun ξ : Fin n → ℝ => v ⬝ᵥ ξ) := by
  unfold dotProduct; fun_prop

lemma geo_measurable_normSq : Measurable (fun ξ : Fin n → ℝ => normSq ξ) := by
  unfold normSq; fun_prop

lemma geo_integral_dot_zero (v : Fin n → ℝ) : ∫ ξ, v ⬝ᵥ ξ ∂stdGauss (Fin n) = 0 := by
  have e : (fun ξ : Fin n → ℝ => v ⬝ᵥ ξ) = fun ξ => ξ ⬝ᵥ v := by
    funext ξ; exact dotProduct_comm v ξ
  rw [e]
  have m1 : Measurable (fun ξ : Fin n → ℝ => ξ ⬝ᵥ v) := by unfold dotProduct; fun_prop
  have h := integral_map (μ := stdGauss (Fin n)) m1.aemeasurable
    (f := fun x : ℝ => x) measurable_id.aestronglyMeasurable
  rw [BstLean.Part131.stdGauss_dot, integral_id_gaussianReal] at h
  exact h.symm

/-- **Gaussian tail of a linear form**: `Pr(|v·ξ| > t) ≤ 2 exp(−t²/(2L²))` for `|v| ≤ L`. -/
theorem lin_tail (v : Fin n → ℝ) {L t : ℝ} (hL : 0 < L) (hv : nrm v ≤ L) (ht : 0 ≤ t) :
    (stdGauss (Fin n)).real {ξ | t < |v ⬝ᵥ ξ|} ≤ 2 * exp (-t ^ 2 / (2 * L ^ 2)) := by
  have hLip : BstLean.Part148.EuLip (fun ξ : Fin n → ℝ => v ⬝ᵥ ξ) L := by
    intro x y
    have e : v ⬝ᵥ x - v ⬝ᵥ y = v ⬝ᵥ (x - y) := by rw [dotProduct_sub]
    rw [e]
    refine (abs_dot_le_nrm v (x - y)).trans ?_
    have e2 : nrm (x - y) = √(∑ i, (x i - y i) ^ 2) := rfl
    rw [e2]
    exact mul_le_mul_of_nonneg_right hv (Real.sqrt_nonneg _)
  have h1 := gaussConc_upper_sharp hL.le hLip ht
  have h2 := gaussConc_lower_sharp hL.le hLip ht
  rw [geo_integral_dot_zero] at h1 h2
  have hsub : {ξ : Fin n → ℝ | t < |v ⬝ᵥ ξ|} ⊆
      {x | 0 + t ≤ v ⬝ᵥ x} ∪ {x | v ⬝ᵥ x ≤ 0 - t} := by
    intro ξ hξ
    simp only [Set.mem_ofPred_eq] at hξ
    rcases lt_abs.mp hξ with h | h
    · left; simp only [Set.mem_ofPred_eq]; linarith
    · right; simp only [Set.mem_ofPred_eq]; linarith
  calc (stdGauss (Fin n)).real {ξ | t < |v ⬝ᵥ ξ|}
      ≤ (stdGauss (Fin n)).real ({x | 0 + t ≤ v ⬝ᵥ x} ∪ {x | v ⬝ᵥ x ≤ 0 - t}) :=
        measureReal_mono hsub
    _ ≤ (stdGauss (Fin n)).real {x | 0 + t ≤ v ⬝ᵥ x} +
        (stdGauss (Fin n)).real {x | v ⬝ᵥ x ≤ 0 - t} := measureReal_union_le _ _
    _ ≤ 2 * exp (-t ^ 2 / (2 * L ^ 2)) := by linarith

lemma nrm_uC_le (c : Fin n → ℝ) : nrm (uC c) ≤ 1 := by
  unfold nrm
  rw [show (1 : ℝ) = √1 by simp]
  exact Real.sqrt_le_sqrt (normSq_uC_le c)

/-- **The mass outside `Ω`**: `Pr(Ωᶜ) ≤ 2e^{−t₀²/2} + 2e^{−z₀}` (Gaussian tail of `u·ξ` and the
two Laurent–Massart tails of `|ξ|²`). -/
theorem omega_compl_le (hn : 0 < n) (c : Fin n → ℝ) {t0 z0 : ℝ} (ht0 : 0 ≤ t0) (hz0 : 0 ≤ z0) :
    (stdGauss (Fin n)).real (OmegaS c t0 z0)ᶜ ≤ 2 * exp (-t0 ^ 2 / 2) + 2 * exp (-z0) := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hA := lin_tail (uC c) one_pos (nrm_uC_le c) ht0
  have hB := chiSq_upper_LM (ι := Fin n) hz0
  have hC := chiSq_lower_LM (ι := Fin n) hz0
  simp only [Fintype.card_fin, one_pow, mul_one] at hA hB hC
  have hsub : (OmegaS c t0 z0)ᶜ ⊆ ({ξ | t0 < |uC c ⬝ᵥ ξ|} ∪
      {ξ : Fin n → ℝ | ∑ i, ξ i ^ 2 ≤ (n : ℝ) - 2 * √((n : ℝ) * z0)}) ∪
      {ξ | (n : ℝ) + 2 * √((n : ℝ) * z0) + 2 * z0 ≤ ∑ i, ξ i ^ 2} := by
    intro ξ hξ
    simp only [OmegaS, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_le] at hξ
    have e : normSq ξ = ∑ i, ξ i ^ 2 := rfl
    rw [e] at hξ
    rcases hξ with h | h | h
    · left; left; exact h
    · left; right; exact h.le
    · right; exact h.le
  calc (stdGauss (Fin n)).real (OmegaS c t0 z0)ᶜ
      ≤ (stdGauss (Fin n)).real (({ξ | t0 < |uC c ⬝ᵥ ξ|} ∪
      {ξ : Fin n → ℝ | ∑ i, ξ i ^ 2 ≤ (n : ℝ) - 2 * √((n : ℝ) * z0)}) ∪
      {ξ | (n : ℝ) + 2 * √((n : ℝ) * z0) + 2 * z0 ≤ ∑ i, ξ i ^ 2}) := measureReal_mono hsub
    _ ≤ (stdGauss (Fin n)).real {ξ | t0 < |uC c ⬝ᵥ ξ|} +
        (stdGauss (Fin n)).real {ξ : Fin n → ℝ | ∑ i, ξ i ^ 2 ≤ (n : ℝ) - 2 * √((n : ℝ) * z0)} +
        (stdGauss (Fin n)).real {ξ | (n : ℝ) + 2 * √((n : ℝ) * z0) + 2 * z0 ≤ ∑ i, ξ i ^ 2} :=
        (measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl)
    _ ≤ 2 * exp (-t0 ^ 2 / 2) + 2 * exp (-z0) := by linarith

lemma gPlus_pos (hn : 0 < n) {z0 : ℝ} (hz0 : 0 ≤ z0) : 0 < gPlus n z0 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  unfold gPlus; apply Real.sqrt_pos.mpr; positivity

lemma normSq_perpC_le (c ξ : Fin n → ℝ) : normSq (perpC c ξ) ≤ normSq ξ := by
  have e : normSq (perpC c ξ) = perpC c ξ ⬝ᵥ perpC c ξ := by
    unfold normSq dotProduct; simp [sq]
  rw [e, perpC_dot]
  unfold perpC
  rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
  have e2 : normSq ξ = ξ ⬝ᵥ ξ := by unfold normSq dotProduct; simp [sq]
  rw [e2, dotProduct_comm (uC c) ξ]
  nlinarith [sq_nonneg (ξ ⬝ᵥ uC c)]

/-- **The pair row tail**: for a fixed `ξ ∈ Ω`,
`Pr_{ξ'}(ξ' ∈ Ω, (ξ, ξ') ∉ Γ) ≤ 2e^{−t₁²/2}`. -/
theorem gamma_row_le (hn : 0 < n) (c : Fin n → ℝ) {t0 z0 t1 : ℝ} (hz0 : 0 ≤ z0) (ht1 : 0 ≤ t1)
    {ξ : Fin n → ℝ} (hξ : ξ ∈ OmegaS c t0 z0) :
    (stdGauss (Fin n)).real {ξ' | ξ' ∈ OmegaS c t0 z0 ∧ (ξ, ξ') ∉ GammaS c t0 z0 t1} ≤
      2 * exp (-t1 ^ 2 / 2) := by
  have hg := gPlus_pos hn hz0
  have hv : nrm (perpC c ξ) ≤ gPlus n z0 := by
    unfold nrm gPlus
    refine Real.sqrt_le_sqrt ((normSq_perpC_le c ξ).trans hξ.2.2)
  have h := lin_tail (perpC c ξ) hg hv (mul_nonneg ht1 hg.le)
  have e : -(t1 * gPlus n z0) ^ 2 / (2 * gPlus n z0 ^ 2) = -t1 ^ 2 / 2 := by
    field_simp
  rw [e] at h
  refine le_trans (measureReal_mono ?_) h
  intro ξ' hξ'
  obtain ⟨h1, h2⟩ := hξ'
  simp only [GammaS, Set.mem_ofPred_eq, not_and, not_le] at h2
  have := h2 hξ h1
  rw [perpC_dot] at this
  exact this

/-- `Ω` and `Γ` are measurable. -/
theorem measurableSet_OmegaS (c : Fin n → ℝ) (t0 z0 : ℝ) : MeasurableSet (OmegaS c t0 z0) := by
  have m1 := geo_measurable_dot (uC c)
  have m2 := geo_measurable_normSq (n := n)
  exact (measurableSet_le m1.abs measurable_const).inter
    ((measurableSet_le measurable_const m2).inter (measurableSet_le m2 measurable_const))

lemma measurable_perpC (c : Fin n → ℝ) : Measurable (perpC c) := by
  unfold perpC
  exact measurable_id.sub ((geo_measurable_dot (uC c)).smul_const _)

theorem measurableSet_GammaS (c : Fin n → ℝ) (t0 z0 t1 : ℝ) :
    MeasurableSet (GammaS c t0 z0 t1) := by
  have hO := measurableSet_OmegaS c t0 z0
  have mp : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => perpC c p.1 ⬝ᵥ perpC c p.2) := by
    have h1 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => perpC c p.1) :=
      (measurable_perpC c).comp measurable_fst
    have h2 : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) => perpC c p.2) :=
      (measurable_perpC c).comp measurable_snd
    unfold dotProduct
    exact Finset.measurable_sum _ fun i _ =>
      ((measurable_pi_apply i).comp h1).mul ((measurable_pi_apply i).comp h2)
  exact (measurable_fst hO).inter ((measurable_snd hO).inter
    (measurableSet_le mp.abs measurable_const))

end BstLean.Part182

open BstLean.Part182 in
#print axioms omega_radius
open BstLean.Part182 in
#print axioms omega_weight
open BstLean.Part182 in
#print axioms gamma_dot
open BstLean.Part182 in
#print axioms lin_tail
open BstLean.Part182 in
#print axioms omega_compl_le
open BstLean.Part182 in
#print axioms gamma_row_le
open BstLean.Part182 in
#print axioms measurableSet_GammaS
