import BstLean.Part150P45

/-!
# Part 150: Proposition P45 (ii), (iii), (iv) of `onW45-opus-prover.md` §3, deterministic form

The events of the paper are HYPOTHESES here (no probability):
* (E1a) `t‖A₁‖²_F ≤ 4w`; (E1b) `cs·τ² ≤ s²`; (Ee) `γ_Γ ≤ (1 + δe)·γρ²` (`γ = 2/n`);
* (Eχ) `|A₂e|² ≤ t|e|²·m(1 + δχ)`, `e = h̃ − h̄`.
`a₁ = alphaJ J₁`, `q₁ = betaJ J₁`, `a₂ = alphaJ J₂` (the main route of the paper),
`θ = thetaC c τ = nτ²/ρ²`, `g(θ) = gP δe cs θ = 2(1 + δe)/θ − cs`.

* `p45_ii_e`, `p45_ii_g`, `p45_ii_s0`, `p45_ii_s`: Proposition P45 (ii).
* **`p45_iii`**: `√t·|b̃′ − b′|/ρ ≤ epsJ·√(γ/n)` with the paper's `ϵ_J` (line 97).
* `p45_iv`, `p45_iv_mono`: Proposition P45 (iv).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open Real
open BstLean.Part130 BstLean.Part132 BstLean.Part137 BstLean.Part141

variable {n m : ℕ}

lemma rhoC_sqP (c : Fin n → ℝ) (τ : ℝ) : rhoC c τ ^ 2 = normSq c + (n : ℝ) * τ ^ 2 := by
  unfold rhoC
  exact Real.sq_sqrt (add_nonneg (normSq_nonneg c) (by positivity))

lemma rhoC_posP (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) : 0 < rhoC c τ := by
  unfold rhoC
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact Real.sqrt_pos.mpr (add_pos_of_nonneg_of_pos (normSq_nonneg c) (by positivity))

/-- `θ = nτ²/ρ²`. -/
noncomputable def thetaC (c : Fin n → ℝ) (τ : ℝ) : ℝ := (n : ℝ) * τ ^ 2 / rhoC c τ ^ 2

/-- `g(θ) = 2(1 + δe)/θ − cs`. -/
noncomputable def gP (δe cs θ : ℝ) : ℝ := 2 * (1 + δe) / θ - cs

/-- The paper's `ϵ_J` (onW45 §3, line 97), with `φ(0) = 1/√(2π)`. -/
noncomputable def epsJ (n J₁ J₂ : ℕ) (w cs δe δχ : ℝ) : ℝ :=
  alphaJ J₂ * √(2 * (1 + δe) * (1 + 2 * w * betaJ J₁) * n) +
    2 * alphaJ J₁ * √(2 * (1 + δe) * w * n * (1 + δχ + 2 / π) / cs) +
    4 * (1 / √(2 * π)) * w * √((n : ℝ) / cs) * (betaJ J₁ + alphaJ J₁ ^ 2)

lemma thetaC_bounds (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    0 < thetaC c τ ∧ thetaC c τ ≤ 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ := rhoC_posP hn c hτ
  have h2 := rhoC_sqP c τ
  have hc := normSq_nonneg c
  unfold thetaC
  refine ⟨by positivity, ?_⟩
  rw [div_le_one (by positivity)]
  linarith only [h2, hc]

lemma gP_tau (hn : 1 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ) (δe cs : ℝ) :
    gP δe cs (thetaC c τ) * τ ^ 2 = (1 + δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2 - cs * τ ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hρ := rhoC_posP hn c hτ
  unfold gP thetaC
  field_simp

lemma normSq_sub_eq (x y : Fin m → ℝ) : normSq (x - y) = ∑ i, (x i - y i) ^ 2 := rfl

/-- **P45 (ii), first part**: `t|e|² ≤ 4w·a₁²·τ²`. -/
theorem p45_ii_e {J₁ : ℕ} (hJ₁ : 1 ≤ J₁) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    {τ w : ℝ} (hτ : 0 ≤ τ) (hE1a : 2 / (m : ℝ) * froSq A₁ ≤ 4 * w) :
    2 / (m : ℝ) * normSq (hT J₁ A₁ c τ - hO A₁ c τ) ≤ 4 * w * alphaJ J₁ ^ 2 * τ ^ 2 := by
  have h := (centre150_first hJ₁ A₁ c hτ).1
  rw [normSq_sub_eq]
  have h0 : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  have h1 := mul_le_mul_of_nonneg_left h h0
  have h2 := mul_le_mul_of_nonneg_left hE1a
    (by positivity : (0 : ℝ) ≤ alphaJ J₁ ^ 2 * τ ^ 2)
  linarith only [h1, h2]

/-- **P45 (ii), second part**: `|γ̃_Γ − γ_Γ| ≤ 4w·q₁·τ²`. -/
theorem p45_ii_g {J₁ : ℕ} (hJ₁ : 1 ≤ J₁) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    {τ w : ℝ} (hτ : 0 ≤ τ) (hE1a : 2 / (m : ℝ) * froSq A₁ ≤ 4 * w) :
    |gT J₁ A₁ c τ - gO A₁ c τ| ≤ 4 * w * betaJ J₁ * τ ^ 2 := by
  have h := (centre150_first hJ₁ A₁ c hτ).2.1
  have hb := betaJ_nonneg J₁
  have h2 := mul_le_mul_of_nonneg_left hE1a (by positivity : (0 : ℝ) ≤ betaJ J₁ * τ ^ 2)
  linarith only [h, h2]

lemma a_sqrt_mul {a : ℝ} (ha : 0 ≤ a) (F H : ℝ) : a * (√F * √H) = √(a * F) * √(a * H) := by
  rw [Real.sqrt_mul ha, Real.sqrt_mul ha]
  have := Real.mul_self_sqrt ha
  linear_combination (-(√F * √H)) * this

/-- **P45 (ii), third part**, without `θ`:
`|s̃² − s²| ≤ 4wq₁τ² + 4a₁τ√(w((1 + δe)γρ² − cs·τ²)) + 4wa₁²τ²`. -/
theorem p45_ii_s0 {J₁ : ℕ} (hJ₁ : 1 ≤ J₁) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    {τ w cs δe : ℝ} (hτ : 0 ≤ τ) (hw : 0 ≤ w) (hE1a : 2 / (m : ℝ) * froSq A₁ ≤ 4 * w)
    (hE1b : cs * τ ^ 2 ≤ sO2 A₁ c τ)
    (hEe : gO A₁ c τ ≤ (1 + δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2) :
    |sT2 J₁ A₁ c τ - sO2 A₁ c τ| ≤ 4 * w * betaJ J₁ * τ ^ 2 +
      4 * alphaJ J₁ * τ * √(w * ((1 + δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2 - cs * τ ^ 2)) +
      4 * w * alphaJ J₁ ^ 2 * τ ^ 2 := by
  have h := (centre150_first hJ₁ A₁ c hτ).2.2.2.2
  have ha := alphaJ_nonneg J₁
  have hb := betaJ_nonneg J₁
  have h0 : (0 : ℝ) ≤ 2 / (m : ℝ) := by positivity
  have hF0 : 0 ≤ froSq A₁ := froSq_nonneg A₁
  have eH : 2 / (m : ℝ) * ∑ i, hO A₁ c τ i ^ 2 = gO A₁ c τ - sO2 A₁ c τ := by
    unfold sO2; ring
  have hH : 2 / (m : ℝ) * ∑ i, hO A₁ c τ i ^ 2 ≤
      (1 + δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2 - cs * τ ^ 2 := by
    rw [eH]; linarith only [hE1b, hEe]
  have hcross : 2 / (m : ℝ) * (√(froSq A₁) * √(∑ i, hO A₁ c τ i ^ 2)) ≤
      2 * √(w * ((1 + δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2 - cs * τ ^ 2)) := by
    rw [a_sqrt_mul h0, csqrt (by norm_num : (0 : ℝ) ≤ 2)]
    have e : (2 : ℝ) ^ 2 * (w * ((1 + δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2 - cs * τ ^ 2)) =
        4 * w * ((1 + δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2 - cs * τ ^ 2) := by ring
    rw [e, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 4 * w)]
    exact mul_le_mul (Real.sqrt_le_sqrt hE1a) (Real.sqrt_le_sqrt hH) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  have h1 := mul_le_mul_of_nonneg_left hE1a (by positivity : (0 : ℝ) ≤ betaJ J₁ * τ ^ 2)
  have h2 := mul_le_mul_of_nonneg_left hE1a
    (by positivity : (0 : ℝ) ≤ alphaJ J₁ ^ 2 * τ ^ 2)
  have h3 := mul_le_mul_of_nonneg_left hcross (by positivity : (0 : ℝ) ≤ 2 * alphaJ J₁ * τ)
  have e3 : 2 / (m : ℝ) * (2 * (alphaJ J₁ * τ * √(froSq A₁)) * √(∑ i, hO A₁ c τ i ^ 2) +
      alphaJ J₁ ^ 2 * τ ^ 2 * froSq A₁) =
      2 * alphaJ J₁ * τ * (2 / (m : ℝ) * (√(froSq A₁) * √(∑ i, hO A₁ c τ i ^ 2))) +
        alphaJ J₁ ^ 2 * τ ^ 2 * (2 / (m : ℝ) * froSq A₁) := by ring
  rw [e3] at h
  linarith only [h, h1, h2, h3]

/-- `g(θ) ≥ 0` on the events. -/
lemma gP_nonneg (hn : 1 ≤ n) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) {τ cs δe : ℝ}
    (hτ : 0 < τ) (hE1b : cs * τ ^ 2 ≤ sO2 A₁ c τ)
    (hEe : gO A₁ c τ ≤ (1 + δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2) :
    0 ≤ gP δe cs (thetaC c τ) := by
  have hg := gP_tau hn c hτ δe cs
  have h0 : (0 : ℝ) ≤ 2 / (m : ℝ) * ∑ i, hO A₁ c τ i ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have eH : 2 / (m : ℝ) * ∑ i, hO A₁ c τ i ^ 2 = gO A₁ c τ - sO2 A₁ c τ := by
    unfold sO2; ring
  have h1 : 0 ≤ gP δe cs (thetaC c τ) * τ ^ 2 := by
    rw [hg]; linarith only [h0, eH, hE1b, hEe]
  exact nonneg_of_mul_nonneg_left h1 (by positivity)

/-- **P45 (ii), third part**, the paper's form:
`|s̃² − s²| ≤ τ²·(4wq₁ + 4a₁√(w·g(θ)) + 4wa₁²)`. -/
theorem p45_ii_s (hn : 1 ≤ n) {J₁ : ℕ} (hJ₁ : 1 ≤ J₁) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) {τ w cs δe : ℝ} (hτ : 0 < τ) (hw : 0 ≤ w)
    (hE1a : 2 / (m : ℝ) * froSq A₁ ≤ 4 * w) (hE1b : cs * τ ^ 2 ≤ sO2 A₁ c τ)
    (hEe : gO A₁ c τ ≤ (1 + δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2) :
    |sT2 J₁ A₁ c τ - sO2 A₁ c τ| ≤ τ ^ 2 * (4 * w * betaJ J₁ +
      4 * alphaJ J₁ * √(w * gP δe cs (thetaC c τ)) + 4 * w * alphaJ J₁ ^ 2) := by
  have h := p45_ii_s0 hJ₁ A₁ c hτ.le hw hE1a hE1b hEe
  rw [← gP_tau hn c hτ δe cs] at h
  have e : √(w * (gP δe cs (thetaC c τ) * τ ^ 2)) = τ * √(w * gP δe cs (thetaC c τ)) := by
    rw [csqrt hτ.le]; congr 1; ring
  rw [e] at h
  refine h.trans (le_of_eq ?_)
  ring

/-- **P45 (iv)**: `s̃² ≥ (cs − 4a₁√(w·g(θ)) − 4w(q₁ + a₁²))·τ²`. -/
theorem p45_iv (hn : 1 ≤ n) {J₁ : ℕ} (hJ₁ : 1 ≤ J₁) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) {τ w cs δe : ℝ} (hτ : 0 < τ) (hw : 0 ≤ w)
    (hE1a : 2 / (m : ℝ) * froSq A₁ ≤ 4 * w) (hE1b : cs * τ ^ 2 ≤ sO2 A₁ c τ)
    (hEe : gO A₁ c τ ≤ (1 + δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2) :
    (cs - 4 * alphaJ J₁ * √(w * gP δe cs (thetaC c τ)) -
        4 * w * (betaJ J₁ + alphaJ J₁ ^ 2)) * τ ^ 2 ≤ sT2 J₁ A₁ c τ := by
  have h := p45_ii_s hn hJ₁ A₁ c hτ hw hE1a hE1b hEe
  have h1 := (abs_le.mp h).1
  have e : (cs - 4 * alphaJ J₁ * √(w * gP δe cs (thetaC c τ)) -
        4 * w * (betaJ J₁ + alphaJ J₁ ^ 2)) * τ ^ 2 =
      cs * τ ^ 2 - τ ^ 2 * (4 * w * betaJ J₁ +
        4 * alphaJ J₁ * √(w * gP δe cs (thetaC c τ)) + 4 * w * alphaJ J₁ ^ 2) := by ring
  rw [e]
  linarith only [h1, hE1b]

/-- **P45 (iv), for `θ ≥ θ₀`** (`g` is decreasing). -/
theorem p45_iv_mono (hn : 1 ≤ n) {J₁ : ℕ} (hJ₁ : 1 ≤ J₁) (A₁ : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) {τ w cs δe θ₀ : ℝ} (hτ : 0 < τ) (hw : 0 ≤ w) (hδe : 0 ≤ δe)
    (hE1a : 2 / (m : ℝ) * froSq A₁ ≤ 4 * w) (hE1b : cs * τ ^ 2 ≤ sO2 A₁ c τ)
    (hEe : gO A₁ c τ ≤ (1 + δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2)
    (hθ₀ : 0 < θ₀) (hθ : θ₀ ≤ thetaC c τ) :
    (cs - 4 * alphaJ J₁ * √(w * gP δe cs θ₀) -
        4 * w * (betaJ J₁ + alphaJ J₁ ^ 2)) * τ ^ 2 ≤ sT2 J₁ A₁ c τ := by
  have h := p45_iv hn hJ₁ A₁ c hτ hw hE1a hE1b hEe
  have ha := alphaJ_nonneg J₁
  have hg : gP δe cs (thetaC c τ) ≤ gP δe cs θ₀ := by
    unfold gP
    have : 2 * (1 + δe) / thetaC c τ ≤ 2 * (1 + δe) / θ₀ :=
      div_le_div_of_nonneg_left (by positivity) hθ₀ hθ
    linarith only [this]
  have hs : √(w * gP δe cs (thetaC c τ)) ≤ √(w * gP δe cs θ₀) :=
    Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hg hw)
  have h2 := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ 4 * alphaJ J₁ * τ ^ 2)
  refine le_trans ?_ h
  linarith only [h2]

/-- **Proposition P45 (iii), deterministic form**: `√t·|b̃′ − b′|/ρ ≤ ϵ_J·√(γ/n)`. -/
theorem p45_iii (hn : 1 ≤ n) (hm : 1 ≤ m) {J₁ J₂ : ℕ} (hJ₁ : 1 ≤ J₁) (hJ₂ : 1 ≤ J₂)
    (A₁ : Matrix (Fin m) (Fin n) ℝ) (A₂ : Matrix (Fin m) (Fin m) ℝ) (c : Fin n → ℝ)
    {τ w cs δe δχ : ℝ} (hτ : 0 < τ) (hw : 0 < w) (hcs : 0 < cs) (hδe : 0 ≤ δe) (hδχ : 0 ≤ δχ)
    (hE1a : 2 / (m : ℝ) * froSq A₁ ≤ 4 * w) (hE1b : cs * τ ^ 2 ≤ sO2 A₁ c τ)
    (hEe : gO A₁ c τ ≤ (1 + δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2)
    (hEχ : normSq (A₂.mulVec (hT J₁ A₁ c τ - hO A₁ c τ)) ≤
      2 / (m : ℝ) * normSq (hT J₁ A₁ c τ - hO A₁ c τ) * m * (1 + δχ)) :
    √(2 / (m : ℝ)) * nrm (bT J₁ J₂ A₁ A₂ c τ - bO A₁ A₂ c τ) / rhoC c τ ≤
      epsJ n J₁ J₂ w cs δe δχ * √(2 / (n : ℝ) / n) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hρ := rhoC_posP hn c hτ
  have hρ2 := rhoC_sqP c τ
  have hc0 := normSq_nonneg c
  have ha₁ := alphaJ_nonneg J₁
  have ha₂ := alphaJ_nonneg J₂
  have hq₁ := betaJ_nonneg J₁
  have hnτ : (n : ℝ) * τ ^ 2 ≤ rhoC c τ ^ 2 := by linarith only [hρ2, hc0]
  have hfirst := centre150_first hJ₁ A₁ c hτ.le
  have hsT0 : 0 ≤ sT2 J₁ A₁ c τ := hfirst.2.2.1
  -- `s̃² ≤ (1 + δe)(1 + 2wq₁)γρ²`
  have hG : 2 * τ ^ 2 ≤ 2 / (n : ℝ) * rhoC c τ ^ 2 := by
    have e : 2 / (n : ℝ) * rhoC c τ ^ 2 = 2 * (rhoC c τ ^ 2 / n) := by ring
    rw [e]
    have : τ ^ 2 ≤ rhoC c τ ^ 2 / n := by rw [le_div_iff₀ hnR]; linarith only [hnτ]
    linarith only [this]
  have hG0 : 0 ≤ 2 / (n : ℝ) * rhoC c τ ^ 2 := by positivity
  have hsg : sT2 J₁ A₁ c τ ≤ gT J₁ A₁ c τ := by
    have h0 : (0 : ℝ) ≤ 2 / (m : ℝ) * ∑ i, hT J₁ A₁ c τ i ^ 2 :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    unfold sT2; linarith only [h0]
  have hgg := p45_ii_g hJ₁ A₁ c hτ.le hE1a
  have h1 : sT2 J₁ A₁ c τ ≤
      (1 + δe) * (1 + 2 * w * betaJ J₁) * (2 / (n : ℝ)) * rhoC c τ ^ 2 := by
    have t1 := mul_le_mul_of_nonneg_left hG (by positivity : (0 : ℝ) ≤ 2 * w * betaJ J₁)
    have t2 : 2 * w * betaJ J₁ * (2 / (n : ℝ) * rhoC c τ ^ 2) ≤
        (1 + δe) * (2 * w * betaJ J₁ * (2 / (n : ℝ) * rhoC c τ ^ 2)) := by
      have h0 : 0 ≤ 2 * w * betaJ J₁ * (2 / (n : ℝ) * rhoC c τ ^ 2) := by positivity
      have := mul_le_mul_of_nonneg_right (by linarith only [hδe] : (1 : ℝ) ≤ 1 + δe) h0
      linarith only [this]
    have t3 := (abs_le.mp hgg).2
    linarith only [hsg, t1, t2, t3, hEe]
  have hK : cs * τ ^ 2 ≤ (1 + δe) * (2 / (n : ℝ)) * rhoC c τ ^ 2 := by
    have h0 : (0 : ℝ) ≤ 2 / (m : ℝ) * ∑ i, hO A₁ c τ i ^ 2 :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    have eH : 2 / (m : ℝ) * ∑ i, hO A₁ c τ i ^ 2 = gO A₁ c τ - sO2 A₁ c τ := by
      unfold sO2; ring
    linarith only [h0, eH, hE1b, hEe]
  have h3 := p45_ii_s0 hJ₁ A₁ c hτ.le hw.le hE1a hE1b hEe
  have h4 : 2 / (m : ℝ) * normSq (A₂.mulVec (hT J₁ A₁ c τ - hO A₁ c τ)) ≤
      8 * (1 + δχ) * w * alphaJ J₁ ^ 2 * τ ^ 2 := by
    have he := p45_ii_e hJ₁ A₁ c hτ.le hE1a
    have t1 := mul_le_mul_of_nonneg_left hEχ (by positivity : (0 : ℝ) ≤ 2 / (m : ℝ))
    have e : 2 / (m : ℝ) * (2 / (m : ℝ) * normSq (hT J₁ A₁ c τ - hO A₁ c τ) * m * (1 + δχ)) =
        2 * (1 + δχ) * (2 / (m : ℝ) * normSq (hT J₁ A₁ c τ - hO A₁ c τ)) := by
      field_simp
    rw [e] at t1
    have t2 := mul_le_mul_of_nonneg_left he (by positivity : (0 : ℝ) ≤ 2 * (1 + δχ))
    linarith only [t1, t2]
  have hX : √(2 / (m : ℝ)) * nrm (bT J₁ J₂ A₁ A₂ c τ - bO A₁ A₂ c τ) ≤
      √2 * (alphaJ J₂ * √(sT2 J₁ A₁ c τ) +
        1 / √(2 * π) * |√(sT2 J₁ A₁ c τ) - √(sO2 A₁ c τ)|) +
      √(2 / (m : ℝ) * normSq (A₂.mulVec (hT J₁ A₁ c τ - hO A₁ c τ))) := by
    have h := (centre150_second J₁ hJ₂ A₁ A₂ c τ).2
    have t := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg (2 / (m : ℝ)))
    have e2 : √(2 / (m : ℝ)) * √(m : ℝ) = √2 := by
      rw [← Real.sqrt_mul (by positivity)]; congr 1; field_simp
    have e3 : √(2 / (m : ℝ)) * nrm (A₂.mulVec (hT J₁ A₁ c τ - hO A₁ c τ)) =
        √(2 / (m : ℝ) * normSq (A₂.mulVec (hT J₁ A₁ c τ - hO A₁ c τ))) := by
      unfold nrm; rw [← Real.sqrt_mul (by positivity)]
    refine t.trans (le_of_eq ?_)
    rw [mul_add, e3, ← mul_assoc, e2]
    rfl
  have hmain := p45_arith hρ hnR hcs hτ hw hδe hδχ ha₁ ha₂ hq₁ hnτ hsT0 h1 hE1b hK h3 h4 hX
  rw [div_le_iff₀ hρ]
  refine hmain.trans (le_of_eq ?_)
  unfold epsJ; ring

end BstLean.Part150

open BstLean.Part150 in
#print axioms p45_arith
open BstLean.Part150 in
#print axioms p45_ii_e
open BstLean.Part150 in
#print axioms p45_ii_g
open BstLean.Part150 in
#print axioms p45_ii_s0
open BstLean.Part150 in
#print axioms p45_ii_s
open BstLean.Part150 in
#print axioms p45_iii
open BstLean.Part150 in
#print axioms p45_iv
open BstLean.Part150 in
#print axioms p45_iv_mono
