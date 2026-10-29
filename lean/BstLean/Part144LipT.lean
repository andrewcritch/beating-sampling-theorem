import BstLean.Part144Lip

/-!
# Part 144, a real inequality: the mean of the lower bound with no event on `τ`

Role: `delegations/statements/p144-spec.md`, item 2 (a tool for a sharper `sampleFails144`).
Pure real-number inequality; no measure theory.

* `lipMeanT_ge`: with `a = A − b`, `α = 2A(kk − 1)/kk`, `β = A³·kk/(4b²)`: if `Cm ≥ a`,
  `Cm ≥ 2A/kk`, `Cm > α`, `a(Cm − α) ≤ 2β·Cm·v0` and `β ≤ (Cm − α)(1 − v0)²` for some
  `0 ≤ v0 ≤ 1`, then `(A − b) − Cm·Q/c² ≤ max(0, L)`, `L` the mean of the lower bound of
  `Part144Lip`. No condition `|τ − c| ≤ η·c` is used; `τ > 0` only.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part144

/-- the mean of the lower bound against `(A − b) − Cm·Q/c²`, with no event on `τ` -/
theorem lipMeanT_ge {A b c τ f kk m2 x2 Q Cm v0 : ℝ} (hA : 0 < A) (hb : 0 < b) (hbA : b ≤ A)
    (hc : 0 < c) (hk : 2 ≤ kk) (hτ : 0 < τ)
    (hm : m2 = (τ - c) ^ 2 + 2 / kk * x2 + 2 * (kk - 1) / kk * f ^ 2) (hx2 : 0 ≤ x2)
    (hQ : (τ - c) ^ 2 + x2 + f ^ 2 ≤ Q)
    (_hC1 : A - b ≤ Cm) (hC2 : 2 * A / kk ≤ Cm) (hCα : 2 * A * (kk - 1) / kk < Cm)
    (hv0 : 0 ≤ v0) (hv1 : v0 ≤ 1)
    (hav : (A - b) * (Cm - 2 * A * (kk - 1) / kk) ≤ 2 * (A ^ 3 * kk / (4 * b ^ 2)) * Cm * v0)
    (hβ : A ^ 3 * kk / (4 * b ^ 2) ≤ (Cm - 2 * A * (kk - 1) / kk) * (1 - v0) ^ 2) :
    (A - b) - Cm * Q / c ^ 2 ≤
      max 0 ((A - b * τ / c) + b * τ / c ^ 2 * (τ - c) - A / c ^ 2 * m2
        - A ^ 3 * kk ^ 2 / (4 * (b * τ) ^ 2) * (f ^ 2 / kk)) := by
  have hk0 : 0 < kk := by linarith
  have hc2 : 0 < c ^ 2 := by positivity
  obtain ⟨s, hs⟩ : ∃ s : ℝ, τ = s * c := ⟨τ / c, by field_simp⟩
  obtain ⟨ξ2, h2⟩ : ∃ ξ2 : ℝ, x2 = ξ2 * c ^ 2 := ⟨x2 / c ^ 2, by field_simp⟩
  obtain ⟨ξ3, h3⟩ : ∃ ξ3 : ℝ, f ^ 2 = ξ3 * c ^ 2 := ⟨f ^ 2 / c ^ 2, by field_simp⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, Q = q * c ^ 2 := ⟨Q / c ^ 2, by field_simp⟩
  subst hs h2 hq
  have hs0 : 0 < s := by
    by_contra hcon
    have : s * c ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hcon) hc.le
    linarith
  have hξ2 : 0 ≤ ξ2 := by
    by_contra hcon
    have : ξ2 * c ^ 2 < 0 := mul_neg_of_neg_of_pos (not_le.mp hcon) hc2
    linarith
  have hξ3 : 0 ≤ ξ3 := by
    by_contra hcon
    have h1 : ξ3 * c ^ 2 < 0 := mul_neg_of_neg_of_pos (not_le.mp hcon) hc2
    have h2 : 0 ≤ f ^ 2 := sq_nonneg f
    linarith
  rw [h3] at hQ hm
  rw [h3, hm]
  set a : ℝ := A - b with ha
  set α : ℝ := 2 * A * (kk - 1) / kk with hα
  set β : ℝ := A ^ 3 * kk / (4 * b ^ 2) with hβd
  have ha0 : 0 ≤ a := by rw [ha]; linarith
  have hβ0 : 0 < β := by rw [hβd]; positivity
  have hαA : A ≤ α := by
    rw [hα, le_div_iff₀ hk0]
    have := mul_nonneg hA.le (by linarith : (0 : ℝ) ≤ kk - 2)
    linarith
  have hαa : a ≤ α := by rw [ha]; linarith
  have hCm0 : 0 < Cm := by linarith
  set ξ1 : ℝ := (s - 1) ^ 2 with hξ1
  have hξ10 : 0 ≤ ξ1 := sq_nonneg _
  have hqge : ξ1 + ξ2 + ξ3 ≤ q := by
    have e : (s * c - c) ^ 2 + ξ2 * c ^ 2 + ξ3 * c ^ 2 = (ξ1 + ξ2 + ξ3) * c ^ 2 := by
      rw [hξ1]; ring
    rw [e] at hQ
    exact le_of_mul_le_mul_right hQ hc2
  have hq2 : Cm * (q * c ^ 2) / c ^ 2 = Cm * q := by field_simp
  rw [hq2]
  -- the expression inside `max`, times `s²`
  set E : ℝ := (A - b * (s * c) / c) + b * (s * c) / c ^ 2 * (s * c - c) -
    A / c ^ 2 * ((s * c - c) ^ 2 + 2 / kk * (ξ2 * c ^ 2) + 2 * (kk - 1) / kk * (ξ3 * c ^ 2)) -
    A ^ 3 * kk ^ 2 / (4 * (b * (s * c)) ^ 2) * (ξ3 * c ^ 2 / kk) with hE
  have hEs : E * s ^ 2 = (a - a * ξ1 - 2 * A / kk * ξ2 - α * ξ3) * s ^ 2 - β * ξ3 := by
    rw [hE, ha, hα, hβd, hξ1]
    field_simp
    ring
  by_contra hcon
  have hlt := not_le.mp hcon
  have hpos : 0 < a - Cm * q := lt_of_le_of_lt (le_max_left _ _) hlt
  have hEl : E < a - Cm * q := lt_of_le_of_lt (le_max_right _ _) hlt
  have hs2 : 0 < s ^ 2 := by positivity
  have hCq : Cm * (ξ1 + ξ2 + ξ3) ≤ Cm * q := mul_le_mul_of_nonneg_left hqge hCm0.le
  -- (*)
  have hstar : Cm * ξ3 < a - Cm * ξ1 := by
    have : 0 ≤ Cm * ξ2 := mul_nonneg hCm0.le hξ2
    have e : Cm * (ξ1 + ξ2 + ξ3) = Cm * ξ1 + Cm * ξ2 + Cm * ξ3 := by ring
    linarith
  -- (**) times `s²`
  have h1 : E * s ^ 2 < (a - Cm * (ξ1 + ξ2 + ξ3)) * s ^ 2 :=
    mul_lt_mul_of_pos_right (by linarith) hs2
  rw [hEs] at h1
  set D : ℝ := β - (Cm - α) * s ^ 2 with hD
  have t1 : 0 ≤ (Cm - a) * ξ1 * s ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) hξ10) hs2.le
  have t2 : 0 ≤ (Cm - 2 * A / kk) * ξ2 * s ^ 2 :=
    mul_nonneg (mul_nonneg (by linarith) hξ2) hs2.le
  have h2' : (Cm - a) * ξ1 * s ^ 2 + (Cm - 2 * A / kk) * ξ2 * s ^ 2 < D * ξ3 := by
    have e : (a - Cm * (ξ1 + ξ2 + ξ3)) * s ^ 2 -
        ((a - a * ξ1 - 2 * A / kk * ξ2 - α * ξ3) * s ^ 2 - β * ξ3) =
        D * ξ3 - ((Cm - a) * ξ1 * s ^ 2 + (Cm - 2 * A / kk) * ξ2 * s ^ 2) := by
      rw [hD]; ring
    linarith
  have hDξ : 0 < D * ξ3 := by linarith
  have hDpos : 0 < D := by
    by_contra hc'
    have : D * ξ3 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hc') hξ3
    linarith
  -- (***)
  have h3' : Cm * ((Cm - a) * ξ1 * s ^ 2) < D * (a - Cm * ξ1) := by
    have e1 : Cm * ((Cm - a) * ξ1 * s ^ 2) < Cm * (D * ξ3) :=
      mul_lt_mul_of_pos_left (by linarith) hCm0
    have e2 : D * (Cm * ξ3) < D * (a - Cm * ξ1) := mul_lt_mul_of_pos_left hstar hDpos
    have e3 : Cm * (D * ξ3) = D * (Cm * ξ3) := by ring
    linarith
  have h4 : Cm * ξ1 * ((α - a) * s ^ 2 + β) < a * D := by
    have e : Cm * ξ1 * ((α - a) * s ^ 2 + β) =
        Cm * ((Cm - a) * ξ1 * s ^ 2) + D * (Cm * ξ1) := by rw [hD]; ring
    have e' : D * (a - Cm * ξ1) = a * D - D * (Cm * ξ1) := by ring
    linarith
  -- `s < 1 − v0`
  have hCα' : 0 < Cm - α := by linarith
  have hσ : s ^ 2 < (1 - v0) ^ 2 := by
    have h5 : (Cm - α) * s ^ 2 < (Cm - α) * (1 - v0) ^ 2 := by
      rw [hD] at hDpos; linarith
    exact lt_of_mul_lt_mul_left h5 hCα'.le
  have hsv : s < 1 - v0 := lt_of_pow_lt_pow_left₀ 2 (by linarith) hσ
  set v : ℝ := 1 - s with hv
  have hvv : v0 < v := by rw [hv]; linarith
  have hξv : ξ1 = v ^ 2 := by rw [hξ1, hv]; ring
  have hsv' : s = 1 - v := by rw [hv]; ring
  -- left side
  have hL : Cm * v ^ 2 * β ≤ Cm * ξ1 * ((α - a) * s ^ 2 + β) := by
    rw [hξv]
    have : 0 ≤ (α - a) * s ^ 2 := mul_nonneg (by linarith) hs2.le
    exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  -- right side
  have hDle : D ≤ (Cm - α) * (2 * (v - v0)) := by
    have e : (Cm - α) * (1 - v0) ^ 2 - (Cm - α) * (1 - v) ^ 2 =
        (Cm - α) * ((v - v0) * (2 - v - v0)) := by ring
    have h6 : D ≤ (Cm - α) * ((v - v0) * (2 - v - v0)) := by
      rw [← e, hD, hsv']; linarith
    have h7 : (v - v0) * (2 - v - v0) ≤ 2 * (v - v0) := by
      have h70 : 0 ≤ (v - v0) * (v + v0) := mul_nonneg (by linarith) (by linarith)
      have e7 : (v - v0) * (2 - v - v0) = 2 * (v - v0) - (v - v0) * (v + v0) := by ring
      linarith
    exact h6.trans (mul_le_mul_of_nonneg_left h7 hCα'.le)
  have hR : a * D ≤ 2 * β * Cm * v0 * (2 * (v - v0)) := by
    have h8 : a * D ≤ a * ((Cm - α) * (2 * (v - v0))) := mul_le_mul_of_nonneg_left hDle ha0
    have h9 : a * (Cm - α) * (2 * (v - v0)) ≤ 2 * β * Cm * v0 * (2 * (v - v0)) :=
      mul_le_mul_of_nonneg_right hav (by linarith)
    have e9 : a * ((Cm - α) * (2 * (v - v0))) = a * (Cm - α) * (2 * (v - v0)) := by ring
    linarith
  have hfin : Cm * β * v ^ 2 < Cm * β * (4 * v0 * (v - v0)) := by
    have e1 : Cm * β * v ^ 2 = Cm * v ^ 2 * β := by ring
    have e2 : Cm * β * (4 * v0 * (v - v0)) = 2 * β * Cm * v0 * (2 * (v - v0)) := by ring
    linarith
  have hCβ : 0 < Cm * β := mul_pos hCm0 hβ0
  have h10 : v ^ 2 < 4 * v0 * (v - v0) := lt_of_mul_lt_mul_left hfin hCβ.le
  have e11 : (v - 2 * v0) ^ 2 = v ^ 2 - 4 * v0 * (v - v0) := by ring
  have := sq_nonneg (v - 2 * v0)
  linarith

end BstLean.Part144

#print axioms BstLean.Part144.lipMeanT_ge
