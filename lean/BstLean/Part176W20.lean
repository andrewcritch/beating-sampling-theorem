import BstLean.Part160Cov8
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Part 176 (file `W20`): the layered bound of the radius moment `W_q`

No proof is left open; no `native_decide` or `axiom` is used.

Part 160's `WqN_le` splits `E_ξ(τ²/|y|²)^q` at one level `|y| = (1 − ε)√Q` (`Q = ρ² − τ²`) and pays
`(1 − ε)^{−2q}` on the whole bulk. Here the split has `K + 1` levels `ε₀ ≤ ε₁ ≤ … ≤ ε_K`
(a discrete layer-cake formula): with `f(ε) = (τ²/((1 − ε)²Q))^q`,

`W_q ≤ f(ε₀) + Σ_{k<K} (f(ε_{k+1}) − f(ε_k))·exp(−ε_k²Q/(2τ²)) + √exp(−ε_K²Q/(2τ²))·(n − 1 − 4q)^{−q}`.

* `layer_pt`: the pointwise inequality (pure real analysis).
* **`WqN_le_layer`**: the bound above.
-/

namespace BstLean.Part176

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130
open BstLean.Part153 (nrm)
open BstLean.Part160 (WqN integrable_wqq)

/-- The partial layer sum `S_K = F₀ + Σ_{k<K} (F_{k+1} − F_k)·[N ≤ R_k]`. -/
noncomputable def layerS (F R : ℕ → ℝ) (N : ℝ) (K : ℕ) : ℝ :=
  F 0 + ∑ k ∈ Finset.range K, (F (k + 1) - F k) * (if N ≤ R k then 1 else 0)

lemma layer_inv (F R : ℕ → ℝ) (N x : ℝ) (hF : ∀ k, F k ≤ F (k + 1)) (hR : ∀ k, R (k + 1) ≤ R k)
    (hx : ∀ k, R k < N → x ≤ F k) (K : ℕ) :
    (N ≤ R K → layerS F R N K = F K) ∧ (R K < N → x ≤ layerS F R N K) := by
  induction K with
  | zero => exact ⟨fun _ => by simp [layerS], fun h => by simpa [layerS] using hx 0 h⟩
  | succ K ih =>
    have e : layerS F R N (K + 1) = layerS F R N K + (F (K + 1) - F K) * (if N ≤ R K then 1 else 0) := by
      unfold layerS; rw [Finset.sum_range_succ]; ring
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have h' : N ≤ R K := h.trans (hR K)
      rw [e, ih.1 h', if_pos h']; ring
    · by_cases hK : N ≤ R K
      · rw [e, ih.1 hK, if_pos hK]
        have := hx (K + 1) h
        linarith
      · push_neg at hK
        rw [e, if_neg (not_le.mpr hK)]
        have := ih.2 hK
        linarith

/-- **The pointwise layer inequality**: `x ≤ S_K + [N ≤ R_K]·x`. -/
lemma layer_pt (F R : ℕ → ℝ) (N x : ℝ) (hF0 : 0 ≤ F 0) (hF : ∀ k, F k ≤ F (k + 1))
    (hR : ∀ k, R (k + 1) ≤ R k) (hx : ∀ k, R k < N → x ≤ F k) (K : ℕ) :
    x ≤ layerS F R N K + (if N ≤ R K then x else 0) := by
  have hFK : 0 ≤ F K := by
    induction K with
    | zero => exact hF0
    | succ K ih => exact ih.trans (hF K)
  obtain ⟨h1, h2⟩ := layer_inv F R N x hF hR hx K
  by_cases h : N ≤ R K
  · rw [if_pos h, h1 h]; linarith
  · rw [if_neg h]; have := h2 (not_le.mp h); linarith


variable {n : ℕ}

/-- `f(ε) = (τ²/((1 − ε)²Q))^q`. -/
noncomputable def fL (q : ℕ) (τ Q e : ℝ) : ℝ := (τ ^ 2 / ((1 - e) ^ 2 * Q)) ^ q

lemma fL_mono {q : ℕ} {τ Q e e' : ℝ} (hQ : 0 < Q) (he : e ≤ e') (he' : e' < 1) :
    fL q τ Q e ≤ fL q τ Q e' := by
  unfold fL
  have h1 : 0 < 1 - e' := by linarith
  have h2 : (1 - e') ^ 2 ≤ (1 - e) ^ 2 := pow_le_pow_left₀ h1.le (by linarith) 2
  have h3 : 0 < (1 - e') ^ 2 * Q := by positivity
  have h4 : 0 < (1 - e) ^ 2 * Q := lt_of_lt_of_le h3 (mul_le_mul_of_nonneg_right h2 hQ.le)
  apply pow_le_pow_left₀ (by positivity)
  exact div_le_div_of_nonneg_left (sq_nonneg τ) h3 (mul_le_mul_of_nonneg_right h2 hQ.le)

/-- **The layered bound of the radius moment.** With `Q = |c|² + nτ² − τ²` and levels
`0 ≤ ε₀ ≤ ε₁ ≤ …`, all `< 1`:
`W_q ≤ f(ε₀) + Σ_{k<K} (f(ε_{k+1}) − f(ε_k))·exp(−ε_k²Q/(2τ²)) + √exp(−ε_K²Q/(2τ²))·(n − 1 − 4q)^{−q}`. -/
theorem WqN_le_layer {q : ℕ} (hq : 4 * q + 1 < n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (ε : ℕ → ℝ) (K : ℕ) (hε0 : 0 ≤ ε 0) (hεm : ∀ k, ε k ≤ ε (k + 1)) (hε1 : ∀ k, ε k < 1) :
    WqN q c τ ≤ fL q τ (normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2) (ε 0) +
      ∑ k ∈ Finset.range K, (fL q τ (normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2) (ε (k + 1)) -
        fL q τ (normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2) (ε k)) *
        exp (-(ε k ^ 2 * (normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2)) / (2 * τ ^ 2)) +
      √(exp (-(ε K ^ 2 * (normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2)) / (2 * τ ^ 2))) *
        (((n : ℝ) - 1 - 4 * q)⁻¹) ^ q := by
  have hprob : IsProbabilityMeasure (stdGauss (Fin n)) := by unfold stdGauss; infer_instance
  have hnR : (4 * (q : ℝ) + 1) < n := by exact_mod_cast hq
  have hd0 : (0 : ℝ) < (n : ℝ) - 1 - 4 * q := by linarith
  have hQ0 : 0 < normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2 := by
    have := normSq_nonneg c
    have h1 : (1 : ℝ) < n := by
      have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
      linarith
    nlinarith [sq_pos_of_pos hτ]
  have he0 : ∀ k, 0 ≤ ε k := by
    intro k
    induction k with
    | zero => exact hε0
    | succ k ih => exact ih.trans (hεm k)
  obtain ⟨Q, hQ⟩ : ∃ Q : ℝ, Q = normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2 := ⟨_, rfl⟩
  rw [← hQ] at hQ0 ⊢
  set F : ℕ → ℝ := fun k => fL q τ Q (ε k) with hFd
  set R : ℕ → ℝ := fun k => (1 - ε k) * √Q with hRd
  have hF : ∀ k, F k ≤ F (k + 1) := fun k => fL_mono hQ0 (hεm k) (hε1 (k + 1))
  have hR : ∀ k, R (k + 1) ≤ R k := fun k =>
    mul_le_mul_of_nonneg_right (by linarith [hεm k]) (Real.sqrt_nonneg _)
  have hR0 : ∀ k, 0 < R k := fun k => mul_pos (by linarith [hε1 k]) (Real.sqrt_pos.mpr hQ0)
  have hR2 : ∀ k, R k ^ 2 = (1 - ε k) ^ 2 * Q := fun k => by
    simp only [hRd]; rw [mul_pow, Real.sq_sqrt hQ0.le]
  have hF0 : 0 ≤ F 0 := by simp only [hFd]; unfold fL; have := hR2 0; positivity
  have hFR : ∀ k, F k = (τ ^ 2 / R k ^ 2) ^ q := fun k => by simp only [hFd]; unfold fL; rw [hR2 k]
  -- the last level
  obtain ⟨pb, hpb⟩ : ∃ pb : ℝ, pb = exp (-(ε K ^ 2 * Q) / (2 * τ ^ 2)) := ⟨_, rfl⟩
  rw [← hpb]
  have hpb0 : 0 < pb := by rw [hpb]; exact exp_pos _
  obtain ⟨dq, hdq⟩ : ∃ dq : ℝ, dq = (((n : ℝ) - 1 - 4 * q)⁻¹) ^ q := ⟨_, rfl⟩
  rw [← hdq]
  have hdq0 : 0 < dq := by rw [hdq]; positivity
  obtain ⟨Ib, hIb⟩ : ∃ Ib : ℝ, Ib = dq ^ 2 := ⟨_, rfl⟩
  have hIb0 : 0 < Ib := by rw [hIb]; positivity
  obtain ⟨hi2, hI2'⟩ := BstLean.Part153.invMoment_le (p := 2 * q) (by omega) c hτ
  have hI2 : τ ^ (2 * (2 * q)) * ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ (2 * q) ∂stdGauss (Fin n) ≤ Ib := by
    refine hI2'.trans ?_
    have h1 : ∏ i ∈ Finset.range (2 * q), ((n : ℝ) - 1 - 2 * ((i : ℝ) + 1))⁻¹ ≤
        (((n : ℝ) - 1 - 4 * q)⁻¹) ^ (2 * q) := by
      refine BstLean.Part160.prod_range_le_pow _ (inv_nonneg.mpr hd0.le) (fun i hi' => ?_)
        (fun i hi' => ?_)
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
  set B : ℕ → Set (Fin n → ℝ) := fun k => {ξ | nrm (c + τ • ξ) ≤ R k} with hBd
  have hB : ∀ k, MeasurableSet (B k) := fun k =>
    measurableSet_le (BstLean.Part160.measurable_nrmShift c τ) measurable_const
  have htail : ∀ k, (stdGauss (Fin n)).real (B k) ≤ exp (-(ε k ^ 2 * Q) / (2 * τ ^ 2)) := by
    intro k
    have := BstLean.Part160.nrm_lower_tail (by omega : 1 ≤ n) c hτ (he0 k)
    rw [← hQ] at this
    exact this
  -- the pointwise bound
  have hpt : ∀ ξ : Fin n → ℝ, (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q ≤
      F 0 + ∑ k ∈ Finset.range K, (F (k + 1) - F k) * Set.indicator (B k) (fun _ => (1 : ℝ)) ξ +
        (a / 2 * Set.indicator (B K) (fun _ => (1 : ℝ)) ξ +
          1 / (2 * a) * (τ ^ (2 * (2 * q)) * (normSq (c + τ • ξ))⁻¹ ^ (2 * q))) := by
    intro ξ
    set N := nrm (c + τ • ξ) with hN
    set x := (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q with hx
    have hN0 : 0 ≤ (normSq (c + τ • ξ))⁻¹ := inv_nonneg.mpr (normSq_nonneg _)
    have hx0 : 0 ≤ x := by rw [hx]; exact pow_nonneg (mul_nonneg (sq_nonneg _) hN0) _
    have hxF : ∀ k, R k < N → x ≤ F k := by
      intro k hlt
      have h1 : R k ^ 2 ≤ normSq (c + τ • ξ) := by
        rw [← BstLean.Part153.nrm_sq (c + τ • ξ)]
        exact pow_le_pow_left₀ (hR0 k).le hlt.le 2
      have h2 : (normSq (c + τ • ξ))⁻¹ ≤ (R k ^ 2)⁻¹ := inv_anti₀ (by have := hR0 k; positivity) h1
      have h3 : τ ^ 2 * (normSq (c + τ • ξ))⁻¹ ≤ τ ^ 2 / R k ^ 2 := by
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      rw [hFR k, hx]
      exact pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) hN0) h3 q
    have hL := layer_pt F R N x hF0 hF hR hxF K
    have hS : layerS F R N K = F 0 + ∑ k ∈ Finset.range K, (F (k + 1) - F k) *
        Set.indicator (B k) (fun _ => (1 : ℝ)) ξ := by
      unfold layerS
      congr 1
    rw [hS] at hL
    have hlast : (if N ≤ R K then x else 0) ≤ a / 2 * Set.indicator (B K) (fun _ => (1 : ℝ)) ξ +
        1 / (2 * a) * (τ ^ (2 * (2 * q)) * (normSq (c + τ • ξ))⁻¹ ^ (2 * q)) := by
      have e : τ ^ (2 * (2 * q)) * (normSq (c + τ • ξ))⁻¹ ^ (2 * q) = x ^ 2 := by
        rw [hx, mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm q 2]
      rw [e]
      have hq0 : 0 ≤ 1 / (2 * a) * x ^ 2 := by positivity
      by_cases hK : N ≤ R K
      · rw [if_pos hK, Set.indicator_of_mem (show ξ ∈ B K from hK)]
        have h2 : a / 2 * 1 + 1 / (2 * a) * x ^ 2 - x = (x - a) ^ 2 / (2 * a) := by
          field_simp
          ring
        have h3 : 0 ≤ (x - a) ^ 2 / (2 * a) := by positivity
        linarith
      · rw [if_neg hK, Set.indicator_of_notMem (show ξ ∉ B K from hK)]
        linarith
    linarith
  have hiI : ∀ (k : ℕ) (b : ℝ), Integrable (fun ξ : Fin n → ℝ => b *
      Set.indicator (B k) (fun _ => (1 : ℝ)) ξ) (stdGauss (Fin n)) := fun k b =>
    ((integrable_const (1 : ℝ)).indicator (hB k)).const_mul _
  have hiS : Integrable (fun ξ : Fin n → ℝ => ∑ k ∈ Finset.range K, (F (k + 1) - F k) *
      Set.indicator (B k) (fun _ => (1 : ℝ)) ξ) (stdGauss (Fin n)) :=
    integrable_finset_sum _ fun k _ => hiI k _
  have hiQ : Integrable (fun ξ : Fin n → ℝ => 1 / (2 * a) *
      (τ ^ (2 * (2 * q)) * (normSq (c + τ • ξ))⁻¹ ^ (2 * q))) (stdGauss (Fin n)) :=
    (hi2.const_mul _).const_mul _
  have hmono := integral_mono hi1
    (((integrable_const (F 0)).add hiS).add ((hiI K (a / 2)).add hiQ)) hpt
  have hint : ∫ ξ, (F 0 + ∑ k ∈ Finset.range K, (F (k + 1) - F k) *
        Set.indicator (B k) (fun _ => (1 : ℝ)) ξ +
        (a / 2 * Set.indicator (B K) (fun _ => (1 : ℝ)) ξ +
          1 / (2 * a) * (τ ^ (2 * (2 * q)) * (normSq (c + τ • ξ))⁻¹ ^ (2 * q)))) ∂stdGauss (Fin n) =
      F 0 + ∑ k ∈ Finset.range K, (F (k + 1) - F k) * (stdGauss (Fin n)).real (B k) +
        (a / 2 * (stdGauss (Fin n)).real (B K) +
          1 / (2 * a) * (τ ^ (2 * (2 * q)) *
            ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ (2 * q) ∂stdGauss (Fin n))) := by
    have hA : Integrable (fun ξ : Fin n → ℝ => F 0 + ∑ k ∈ Finset.range K, (F (k + 1) - F k) *
        Set.indicator (B k) (fun _ => (1 : ℝ)) ξ) (stdGauss (Fin n)) := (integrable_const _).add hiS
    have hC : Integrable (fun ξ : Fin n → ℝ => a / 2 * Set.indicator (B K) (fun _ => (1 : ℝ)) ξ +
          1 / (2 * a) * (τ ^ (2 * (2 * q)) * (normSq (c + τ • ξ))⁻¹ ^ (2 * q)))
        (stdGauss (Fin n)) := (hiI K (a / 2)).add hiQ
    rw [integral_add hA hC, integral_add (integrable_const (F 0)) hiS, integral_add (hiI K (a / 2)) hiQ,
      integral_finset_sum _ fun k _ => hiI k _]
    simp only [integral_const, probReal_univ, one_smul, integral_const_mul,
      integral_indicator_const _ (hB _), smul_eq_mul, mul_one, one_mul]
  have hsum : ∑ k ∈ Finset.range K, (F (k + 1) - F k) * (stdGauss (Fin n)).real (B k) ≤
      ∑ k ∈ Finset.range K, (F (k + 1) - F k) * exp (-(ε k ^ 2 * Q) / (2 * τ ^ 2)) :=
    Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (htail k) (by linarith [hF k])
  have h1 : a / 2 * (stdGauss (Fin n)).real (B K) ≤ a / 2 * pb := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hpb]; exact htail K
  have h2 : 1 / (2 * a) * (τ ^ (2 * (2 * q)) *
      ∫ ξ, (normSq (c + τ • ξ))⁻¹ ^ (2 * q) ∂stdGauss (Fin n)) ≤
      1 / (2 * a) * Ib := mul_le_mul_of_nonneg_left hI2 (by positivity)
  have h3 : a / 2 * pb + 1 / (2 * a) * Ib = s := by
    rw [ha]
    have hIb' : Ib = s ^ 2 / pb := by rw [hs2]; field_simp
    rw [hIb']
    field_simp
    ring
  have hW : WqN q c τ = ∫ ξ, (τ ^ 2 * (normSq (c + τ • ξ))⁻¹) ^ q ∂stdGauss (Fin n) := rfl
  rw [hW]
  have := hmono.trans_eq hint
  simp only [hFd] at this hsum ⊢
  linarith


/-! ## The numerical form at `n ≥ 45 000` -/

lemma exp_neg_quart {x : ℝ} (hx : 0 ≤ x) : exp (-x) ≤ 1 / (1 + x / 4 + (x / 4) ^ 2 / 2) ^ 4 := by
  have h := Real.quadratic_le_exp_of_nonneg (x := x / 4) (by positivity)
  have h4 : (1 + x / 4 + (x / 4) ^ 2 / 2) ^ 4 ≤ exp (x / 4) ^ 4 := pow_le_pow_left₀ (by positivity) h 4
  rw [← Real.exp_nat_mul] at h4
  have e : ((4 : ℕ) : ℝ) * (x / 4) = x := by push_cast; ring
  rw [e] at h4
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by positivity) h4

lemma exp_neg_quart' {x x0 : ℝ} (hx0 : 0 ≤ x0) (hx : x0 ≤ x) :
    exp (-x) ≤ 1 / (1 + x0 / 4 + (x0 / 4) ^ 2 / 2) ^ 4 :=
  (Real.exp_le_exp.mpr (by linarith)).trans (exp_neg_quart hx0)

/-- The levels `ε_k = 0.0031·min(k, 10)`. -/
noncomputable def eps45 (k : ℕ) : ℝ := 31 / 10000 * ((min k 10 : ℕ) : ℝ)

lemma eps45_mono (k : ℕ) : eps45 k ≤ eps45 (k + 1) := by
  unfold eps45
  have : ((min k 10 : ℕ) : ℝ) ≤ ((min (k + 1) 10 : ℕ) : ℝ) := by
    exact_mod_cast min_le_min_right 10 (Nat.le_succ k)
  linarith

lemma eps45_lt (k : ℕ) : eps45 k < 1 := by
  unfold eps45
  have : ((min k 10 : ℕ) : ℝ) ≤ 10 := by exact_mod_cast min_le_right k 10
  linarith

/-- `C(e) = ((1 − e)²)^{−20}`. -/
lemma fL_eq {τ Q e : ℝ} (hQ : 0 < Q) (he : e < 1) :
    fL 20 τ Q e = (τ ^ 2 / Q) ^ 20 * (1 / ((1 - e) ^ 2) ^ 20) := by
  unfold fL
  have h1 : 0 < 1 - e := by linarith
  have : (1 - e) ^ 2 ≠ 0 := by positivity
  rw [show (1 : ℝ) / ((1 - e) ^ 2) ^ 20 = (1 / (1 - e) ^ 2) ^ 20 by rw [div_pow, one_pow],
    ← mul_pow]
  congr 1
  field_simp


/-- `C(e) = ((1 − e)²)^{−20}`. -/
noncomputable def C45 (e : ℝ) : ℝ := 1 / ((1 - e) ^ 2) ^ 20

/-- The tail bound `P(e) = (1 + x/4 + (x/4)²/2)^{−4}` at `x = 42 613·e²`. -/
noncomputable def P45 (e : ℝ) : ℝ := 1 / (1 + e ^ 2 * 42613 / 4 + (e ^ 2 * 42613 / 4) ^ 2 / 2) ^ 4

lemma sum45_le : ∑ k ∈ Finset.range 10, (C45 (eps45 (k + 1)) - C45 (eps45 k)) * P45 (eps45 k) ≤
    27380 / 100000 := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, eps45, C45, P45]
  norm_num


open BstLean.Part150 (thetaC rhoC) in
/-- **`E[(τ²/|y|²)²⁰] ≤ (1.013·θ/n)²⁰`** for `n ≥ 45 000`, `0.46 ≤ θ ≤ 0.528` (the layered bound
with the ten levels `ε_k = 0.0031k`; Part 175 had `1.0622` at `n ≥ 48 000`). -/
theorem W20_le_45 (hn : 45000 ≤ n) (c : Fin n → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 528 / 1000) :
    WqN 20 c τ ≤ (1013 / 1000 * (thetaC c τ / n)) ^ 20 := by
  have hnR : (45000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h := WqN_le_layer (q := 20) (by omega) c hτ eps45 10 (by unfold eps45; norm_num)
    eps45_mono eps45_lt
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
  rw [show normSq c + (n : ℝ) * τ ^ 2 - τ ^ 2 = R - T by rw [hR, hT]] at h
  rw [← hT] at h
  have hT45 : 45000 * T ≤ 528 / 1000 * R := by nlinarith
  have hQ0 : 0 < R - T := by nlinarith
  set w := T / (R - T) with hw
  have hw0 : 0 < w := div_pos hT0 hQ0
  -- `Q/(2T) ≥ 42 613`
  have hlam : 42613 ≤ (R - T) / (2 * T) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  have hE : ∀ k, exp (-(eps45 k ^ 2 * (R - T)) / (2 * T)) ≤ P45 (eps45 k) := by
    intro k
    rw [neg_div]
    refine exp_neg_quart' (by positivity) ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hlam (sq_nonneg _)
  have hfL : ∀ k, fL 20 τ (R - T) (eps45 k) = w ^ 20 * C45 (eps45 k) := fun k => by
    rw [fL_eq hQ0 (eps45_lt k), C45, hw, ← hT]
  have hsum : ∑ k ∈ Finset.range 10, (fL 20 τ (R - T) (eps45 (k + 1)) - fL 20 τ (R - T) (eps45 k)) *
      exp (-(eps45 k ^ 2 * (R - T)) / (2 * T)) ≤ w ^ 20 * (27380 / 100000) := by
    calc _ ≤ ∑ k ∈ Finset.range 10, (fL 20 τ (R - T) (eps45 (k + 1)) - fL 20 τ (R - T) (eps45 k)) *
          P45 (eps45 k) := Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_left (hE k)
              (by linarith [fL_mono (q := 20) (τ := τ) hQ0 (eps45_mono k) (eps45_lt (k + 1))])
      _ = w ^ 20 * ∑ k ∈ Finset.range 10, (C45 (eps45 (k + 1)) - C45 (eps45 k)) * P45 (eps45 k) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hfL, hfL]; ring
      _ ≤ w ^ 20 * (27380 / 100000) := mul_le_mul_of_nonneg_left sum45_le (by positivity)
  have h0 : fL 20 τ (R - T) (eps45 0) = w ^ 20 := by
    rw [hfL]; unfold C45 eps45; norm_num
  -- the tail
  have he10 : eps45 10 = 31 / 1000 := by unfold eps45; norm_num
  have htl : √(exp (-(eps45 10 ^ 2 * (R - T)) / (2 * T))) ≤ (36788 / 100000) ^ 20 := by
    have h40 : exp (-(eps45 10 ^ 2 * (R - T)) / (2 * T)) ≤ exp (-1) ^ 40 := by
      rw [← Real.exp_nat_mul]
      apply Real.exp_le_exp.mpr
      rw [he10, neg_div, mul_div_assoc]
      have : (40 : ℝ) ≤ (31 / 1000) ^ 2 * ((R - T) / (2 * T)) := by nlinarith
      push_cast; linarith
    have h1 : exp (-1) ≤ 36788 / 100000 := by
      have := Real.exp_neg_one_lt_d9; norm_num at this ⊢; linarith
    have h2 : exp (-1) ^ 40 ≤ ((36788 / 100000 : ℝ) ^ 20) ^ 2 := by
      rw [← pow_mul]; exact pow_le_pow_left₀ (exp_pos _).le h1 _
    rw [← Real.sqrt_sq (show (0 : ℝ) ≤ (36788 / 100000) ^ 20 by positivity)]
    exact Real.sqrt_le_sqrt (h40.trans h2)
  have hd0 : (0 : ℝ) < (n : ℝ) - 1 - 4 * (20 : ℕ) := by push_cast; linarith
  have hinv : ((n : ℝ) - 1 - 4 * (20 : ℕ))⁻¹ ≤ 21779 / 10000 * w := by
    have hTR : 46 / 100 / (n : ℝ) ≤ w := by
      rw [hw, div_le_div_iff₀ hn0 hQ0]; nlinarith
    have h4 : ((n : ℝ) - 1 - 4 * (20 : ℕ))⁻¹ ≤ 21779 / 10000 * (46 / 100 / (n : ℝ)) := by
      rw [inv_eq_one_div, mul_div_assoc', div_le_div_iff₀ hd0 hn0]
      push_cast
      nlinarith
    exact h4.trans (mul_le_mul_of_nonneg_left hTR (by norm_num))
  have h2' := pow_le_pow_left₀ (inv_nonneg.mpr hd0.le) hinv 20
  have htail : √(exp (-(eps45 10 ^ 2 * (R - T)) / (2 * T))) * (((n : ℝ) - 1 - 4 * (20 : ℕ))⁻¹) ^ 20 ≤
      (36788 / 100000 : ℝ) ^ 20 * (21779 / 10000 * w) ^ 20 :=
    mul_le_mul htl h2' (by positivity) (by positivity)
  -- `w ≤ 1.0000118·T/R`
  have hwu : w ≤ 1000012 / 1000000 * (T / R) := by
    rw [hw, div_le_iff₀ hQ0]
    have e : 1000012 / 1000000 * (T / R) * (R - T) = T * (1000012 / 1000000 * (1 - T / R)) := by
      field_simp
    rw [e]
    have hTR : T / R ≤ 528 / 1000 / 45000 := by
      rw [div_le_iff₀ hR0]; nlinarith
    have : 1 ≤ 1000012 / 1000000 * (1 - T / R) := by nlinarith
    nlinarith
  have hfin : w ^ 20 + w ^ 20 * (27380 / 100000) + (36788 / 100000 : ℝ) ^ 20 * (21779 / 10000 * w) ^ 20 ≤
      w ^ 20 * (12858 / 10000) := by
    have e : (36788 / 100000 : ℝ) ^ 20 * (21779 / 10000 * w) ^ 20 =
        ((36788 / 100000 : ℝ) ^ 20 * (21779 / 10000) ^ 20) * w ^ 20 := by ring
    rw [e]
    have : (36788 / 100000 : ℝ) ^ 20 * (21779 / 10000) ^ 20 ≤ 119 / 10000 := by norm_num
    nlinarith [pow_pos hw0 20]
  have hwf : w ^ 20 * (12858 / 10000) ≤ (1013 / 1000 * ((n : ℝ) * T / R / n)) ^ 20 := by
    have e : (n : ℝ) * T / R / n = T / R := by field_simp
    rw [e]
    have h1 : w ^ 20 ≤ (1000012 / 1000000 * (T / R)) ^ 20 := pow_le_pow_left₀ hw0.le hwu 20
    have hu0 : 0 ≤ T / R := by positivity
    calc w ^ 20 * (12858 / 10000) ≤ (1000012 / 1000000 * (T / R)) ^ 20 * (12858 / 10000) :=
          mul_le_mul_of_nonneg_right h1 (by norm_num)
      _ = ((1000012 / 1000000) ^ 20 * (12858 / 10000)) * (T / R) ^ 20 := by ring
      _ ≤ (1013 / 1000) ^ 20 * (T / R) ^ 20 :=
          mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
      _ = (1013 / 1000 * (T / R)) ^ 20 := by ring
  rw [h0] at h
  push_cast at h htail
  linarith

end BstLean.Part176
