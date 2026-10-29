import BstLean.Part181W

/-!
# Part 181 (file `Jen`): the covariance functionals `Ξ`, `Ξ₄`, `Ξ₈` from the moment `X₂₀`

No proof is left open; no `native_decide` or `axiom` is used.

Part 160 bounds `Ξ`, `Ξ₄`, `Ξ₈` on three events with Lemma PP at order 200 (`M = 1.157`) and
the inverse radius moments `W₁, W₂, W₄` (`K = 1.067, 1.0665, 1.07`). Here the three functionals
come from the ONE event `SXM22` (Lemma PP at order 800, `M = 1.1`) and the layered bound of `W₂₀`
(`K = 1.0182`) by the Lyapunov (Jensen) inequality `X_q ≤ X₂₀^{q/20}`, proved with the weighted
arithmetic–geometric mean inequality pointwise:

* `xq_pt`: `y^q ≤ (q/20)·y²⁰ + (1 − q/20)` for `y ≥ 0`, `1 ≤ q ≤ 20`.
* `integrable_xq`: the integrand of `X_q` is integrable (`2q + 1 < n`).
* **`Xq_le_of_X20`**: `X₂₀ ≤ B²⁰ → X_q ≤ B^q`.
* **`Xi4_SXM22`, `Xi8_SXM22`, `XiS_SXM22`**: on `SXM22`, for `n ≥ 22 000` and
  `0.46 ≤ θ_in ≤ θh ≤ 0.528`: `Ξ, Ξ₄, Ξ₈ ≤ 1.1·1.0182·θh·γ_A/n`.
-/

namespace BstLean.Part181

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part157
open BstLean.Part156 BstLean.Part160
open BstLean.Part153 (XiS Xi4 jacT)
open BstLean.Part152 (opN opN_nonneg)

variable {n : ℕ}

/-- **The pointwise Lyapunov step**: `y^q ≤ (q/20)·y²⁰ + (1 − q/20)` for `y ≥ 0`, `q ≤ 20`. -/
lemma xq_pt {q : ℕ} (hq : q ≤ 20) {y : ℝ} (hy : 0 ≤ y) :
    y ^ q ≤ (q : ℝ) / 20 * y ^ 20 + (1 - (q : ℝ) / 20) := by
  have hq' : (q : ℝ) ≤ 20 := by exact_mod_cast hq
  have hw1 : (0 : ℝ) ≤ (q : ℝ) / 20 := by positivity
  have hw2 : (0 : ℝ) ≤ 1 - (q : ℝ) / 20 := by linarith
  have h := Real.geom_mean_le_arith_mean2_weighted hw1 hw2 (pow_nonneg hy 20) zero_le_one
    (by ring)
  rw [Real.one_rpow, mul_one, mul_one] at h
  have e : (y ^ 20) ^ ((q : ℝ) / 20) = y ^ q := by
    rw [← Real.rpow_natCast y 20, ← Real.rpow_mul hy, ← Real.rpow_natCast y q]
    congr 1
    push_cast
    ring
  rw [e] at h
  linarith

/-- The integrand of `X_q` is integrable for `2q + 1 < n`. -/
lemma integrable_xq {q : ℕ} (hq : 2 * q + 1 < n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    Integrable (fun ξ : Fin n → ℝ => (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q *
      (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2) ^ q) (stdGauss (Fin n)) := by
  have hi := (integrable_wqq hq c hτ).const_mul (((opN A₂ * opN A₁) ^ 2) ^ q)
  refine Integrable.mono' hi ?_ (ae_of_all _ fun ξ => ?_)
  · have h1 : Measurable (fun ξ : Fin n → ℝ => (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q) :=
      (measurable_const.mul (BstLean.Part153.cont_ns c τ).measurable.inv).pow_const q
    have h2 := ((BstLean.Part153.measurable_opN_jacT_sj A₁ A₂ c τ).pow_const 2).pow_const q
    exact (h1.mul h2).aestronglyMeasurable
  · have hw0 : 0 ≤ (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q :=
      pow_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (normSq_nonneg _))) q
    have hJ0 : 0 ≤ (opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2) ^ q := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 hJ0), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ hw0
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_left₀ (opN_nonneg _)
      (BstLean.Part153.opN_jacT_le_sj A₁ A₂ (normSq_sphPt (by omega) _)) 2) q

/-- **Lyapunov for the gradient moments**: if `X₂₀ ≤ B²⁰` (`B > 0`) then `X_q ≤ B^q` for
`1 ≤ q ≤ 20`, `n ≥ 42`. -/
theorem Xq_le_of_X20 {q : ℕ} (hq : q ≤ 20) (hn : 42 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) {B : ℝ}
    (hB : 0 < B) (h20 : XqN 20 A₁ A₂ c τ ≤ B ^ 20) : XqN q A₁ A₂ c τ ≤ B ^ q := by
  set f : (Fin n → ℝ) → ℝ := fun ξ =>
    τ ^ 2 * (normSq (c + τ • ξ))⁻¹ * opN (jacT A₁ A₂ (sphPt (c + τ • ξ))) ^ 2 with hf
  have hf0 : ∀ ξ, 0 ≤ f ξ := fun ξ =>
    mul_nonneg (mul_nonneg (sq_nonneg _) (inv_nonneg.mpr (normSq_nonneg _))) (sq_nonneg _)
  have eq : ∀ p : ℕ, XqN p A₁ A₂ c τ = ∫ ξ, f ξ ^ p ∂stdGauss (Fin n) := fun p => by
    unfold XqN
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    simp only [hf, mul_pow]
  have hiq : ∀ p : ℕ, 2 * p + 1 < n → Integrable (fun ξ => f ξ ^ p) (stdGauss (Fin n)) :=
    fun p hp => (integrable_xq hp A₁ A₂ c hτ).congr (ae_of_all _ fun ξ => by
      simp only [hf, mul_pow])
  have hi20 := hiq 20 (by omega)
  rw [eq] at h20 ⊢
  have hBq : 0 < B ^ q := pow_pos hB q
  have hB20 : 0 < B ^ 20 := pow_pos hB 20
  have hpt : ∀ ξ, f ξ ^ q ≤ B ^ q * ((q : ℝ) / 20 * (f ξ ^ 20 / B ^ 20) + (1 - (q : ℝ) / 20)) :=
    fun ξ => by
      have h := xq_pt hq (div_nonneg (hf0 ξ) hB.le)
      rw [div_pow, div_pow] at h
      have e : f ξ ^ q = B ^ q * (f ξ ^ q / B ^ q) := by field_simp
      rw [e]
      exact mul_le_mul_of_nonneg_left h hBq.le
  have hrhs : Integrable (fun ξ => B ^ q * ((q : ℝ) / 20 * (f ξ ^ 20 / B ^ 20) +
      (1 - (q : ℝ) / 20))) (stdGauss (Fin n)) :=
    (((hi20.div_const _).const_mul _).add (integrable_const _)).const_mul _
  by_cases hint : Integrable (fun ξ => f ξ ^ q) (stdGauss (Fin n))
  · refine (integral_mono hint hrhs hpt).trans ?_
    rw [integral_const_mul, integral_add ((hi20.div_const _).const_mul _) (integrable_const _),
      integral_const_mul, integral_div, integral_const]
    simp only [probReal_univ, one_smul]
    have hq' : (q : ℝ) ≤ 20 := by exact_mod_cast hq
    have h1 : (∫ ξ, f ξ ^ 20 ∂stdGauss (Fin n)) / B ^ 20 ≤ 1 := by
      rw [div_le_one hB20]; exact h20
    have h2 : (q : ℝ) / 20 * ((∫ ξ, f ξ ^ 20 ∂stdGauss (Fin n)) / B ^ 20) ≤ (q : ℝ) / 20 :=
      by have : (0 : ℝ) ≤ (q : ℝ) / 20 := by positivity
         nlinarith
    nlinarith
  · rw [integral_undef hint]; exact hBq.le

/-- On `SXM22` in the window `0.46 ≤ θ_in ≤ 0.528`: `X₂₀ ≤ (1.1·1.0182·θ_in)²⁰`. -/
lemma X20_SXM22 (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXM22 n) :
    XqN 20 A₁ A₂ c τ ≤ (11 / 10 * (10182 / 10000) * thetaC c τ) ^ 20 := by
  have hn0 : (0 : ℝ) < n := by
    have : (22000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have h1 : XqN 20 A₁ A₂ c τ ≤ (11 / 10 * (n : ℝ)) ^ 20 * WqN 20 c τ := h
  have h2 := W20_le_22 hn c hτ hθ0 hθ1
  refine h1.trans ((mul_le_mul_of_nonneg_left h2 (by positivity)).trans (le_of_eq ?_))
  rw [← mul_pow]; congr 1; field_simp

/-- **`Ξ₄ ≤ 1.1·1.0182·θh·γ_A/n` on `SXM22`** (`n ≥ 22 000`, `0.46 ≤ θ_in ≤ θh ≤ 0.528`). -/
theorem Xi4_SXM22 (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ θh : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θh) (hθh : θh ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXM22 n) :
    Xi4 A₁ A₂ c τ ≤ 11 / 10 * (10182 / 10000) * θh * (2 / (n : ℝ)) / n := by
  have hn0 : (0 : ℝ) < n := by
    have : (22000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 11 / 10 * (10182 / 10000) * thetaC c τ := ⟨_, rfl⟩
  have hBp : 0 < B := by rw [hB]; nlinarith
  have h20 := X20_SXM22 hn hτ hθ0 (hθ1.trans hθh) h
  rw [← hB] at h20
  have h2 := Xq_le_of_X20 (q := 2) (by norm_num) (by omega) A₁ A₂ c hτ hBp h20
  have h4 : √(XqN 2 A₁ A₂ c τ) ≤ B := by
    rw [← Real.sqrt_sq hBp.le]; exact Real.sqrt_le_sqrt h2
  rw [Xi4_eq_XqN A₁ A₂ c τ, hmA]
  have hB' : B ≤ 11 / 10 * (10182 / 10000) * θh := by
    rw [hB]; exact mul_le_mul_of_nonneg_left hθ1 (by norm_num)
  have h5 : 2 / (n : ℝ) ^ 2 * √(XqN 2 A₁ A₂ c τ) ≤
      2 / (n : ℝ) ^ 2 * (11 / 10 * (10182 / 10000) * θh) :=
    mul_le_mul_of_nonneg_left (h4.trans hB') (by positivity)
  refine h5.trans (le_of_eq ?_)
  field_simp

/-- **`Ξ₈ ≤ 1.1·1.0182·θh·γ_A/n` on `SXM22`**. -/
theorem Xi8_SXM22 (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ θh : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θh) (hθh : θh ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXM22 n) :
    Xi8 A₁ A₂ c τ ≤ 11 / 10 * (10182 / 10000) * θh * (2 / (n : ℝ)) / n := by
  have hn0 : (0 : ℝ) < n := by
    have : (22000 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hmA : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = 11 / 10 * (10182 / 10000) * thetaC c τ := ⟨_, rfl⟩
  have hBp : 0 < B := by rw [hB]; nlinarith
  have h20 := X20_SXM22 hn hτ hθ0 (hθ1.trans hθh) h
  rw [← hB] at h20
  have h3 : XqN 4 A₁ A₂ c τ ≤ (B ^ 2) ^ 2 := by
    rw [← pow_mul]; exact Xq_le_of_X20 (q := 4) (by norm_num) (by omega) A₁ A₂ c hτ hBp h20
  have h4 : √(XqN 4 A₁ A₂ c τ) ≤ B ^ 2 := by
    rw [← Real.sqrt_sq (sq_nonneg B)]; exact Real.sqrt_le_sqrt h3
  have h4' : √(√(XqN 4 A₁ A₂ c τ)) ≤ B := by
    rw [← Real.sqrt_sq hBp.le]; exact Real.sqrt_le_sqrt h4
  rw [Xi8_eq_XqN A₁ A₂ c τ, hmA]
  have hB' : B ≤ 11 / 10 * (10182 / 10000) * θh := by
    rw [hB]; exact mul_le_mul_of_nonneg_left hθ1 (by norm_num)
  have h5 : 2 / (n : ℝ) ^ 2 * √(√(XqN 4 A₁ A₂ c τ)) ≤
      2 / (n : ℝ) ^ 2 * (11 / 10 * (10182 / 10000) * θh) :=
    mul_le_mul_of_nonneg_left (h4'.trans hB') (by positivity)
  refine h5.trans (le_of_eq ?_)
  field_simp

/-- **`Ξ ≤ 1.1·1.0182·θh·γ_A/n` on `SXM22`** (`Ξ ≤ Ξ₄`). -/
theorem XiS_SXM22 (hn : 22000 ≤ n) {c : Fin n → ℝ} {τ θh : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θh) (hθh : θh ≤ 528 / 1000)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : ((c, τ), (A₁, A₂)) ∈ SXM22 n) :
    XiS A₁ A₂ c τ ≤ 11 / 10 * (10182 / 10000) * θh * (2 / (n : ℝ)) / n :=
  (BstLean.Part153.XiS_le_Xi4 (by omega) A₁ A₂ c hτ).trans (Xi4_SXM22 hn hτ hθ0 hθ1 hθh h)

end BstLean.Part181

open BstLean.Part181 in
#print axioms Xq_le_of_X20
open BstLean.Part181 in
#print axioms XiS_SXM22
open BstLean.Part181 in
#print axioms Xi8_SXM22
