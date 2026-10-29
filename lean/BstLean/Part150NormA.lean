import BstLean.Part150Norm2

/-!
# Part 150, item 5: the paper's oracle centre against the oracle centre of Part 149, fixed `A₁`

The paper's oracle centre is `bO/ρ` (Gaussian means of the unnormalized stand-in input, `1/ρ` at
the end). The oracle centre of Part 149 is `bMF` (means over the sphere-normalized input).

* `psiS_smul`: `ψ_{ls}(la) = l·ψ_s(a)` for `l ≥ 0`.
* `sqrt_sub_sq_le_div`: `(√a − √b)² ≤ (a − b)²/b` for `b > 0`.
* `arith_II`: the arithmetic of the comparison (real numbers only).
* `bO_sub_bMF_pt`: for every `A₂`:
  `|bO/ρ − bMF|² ≤ (m/π)·Δ²/s2 + 2|A₂ e₁|²`, with `s2 = (2/m)(N2 − |b1|²) > 0`,
  `Δ = |s2 − sO2/ρ²|`, `e₁ = b1 − hO/ρ`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part132 BstLean.Part137 BstLean.Part141
open BstLean.Part149 (a1 b1 N2 sMF bMF errD1 Qk)

lemma psiS_smul {l : ℝ} (hl : 0 ≤ l) (s a : ℝ) : psiS (l * s) (l * a) = l * psiS s a := by
  unfold psiS
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  show relu (l * a + l * s * z) = l * relu (a + s * z)
  rw [← relu_mul_of_nonneg hl]; congr 1; ring

lemma sqrt_sub_sq_le_div (a : ℝ) {b : ℝ} (hb : 0 < b) : (√a - √b) ^ 2 ≤ (a - b) ^ 2 / b := by
  have hsb : 0 < √b := Real.sqrt_pos.mpr hb
  have hb2 : √b ^ 2 = b := Real.sq_sqrt hb.le
  rw [le_div_iff₀ hb]
  rcases le_total 0 a with ha | ha
  · have hsa : 0 ≤ √a := Real.sqrt_nonneg a
    have ha2 : √a ^ 2 = a := Real.sq_sqrt ha
    have e : a - b = (√a - √b) * (√a + √b) := by
      have : (√a - √b) * (√a + √b) = √a ^ 2 - √b ^ 2 := by ring
      rw [this, ha2, hb2]
    rw [e, mul_pow]
    have h1 : b ≤ (√a + √b) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  · rw [Real.sqrt_eq_zero_of_nonpos ha, zero_sub, neg_sq, hb2]
    nlinarith

/-- The arithmetic of the comparison, first part. `ce = εQ + 2εD² + v6/2`. -/
lemma arith_II_pre {d εD εQ k V v6 E Q N aI e p lam ce : ℝ}
    (hd : 0 < d) (hεQ0 : 0 ≤ εQ) (hk1 : k ≤ 1)
    (hV0 : 0 ≤ V) (hV6 : V ≤ v6) (hE0 : 0 ≤ E) (hE : E ≤ (d * εD) ^ 2) (hQ0 : 0 ≤ Q)
    (hQ : Q ≤ (d * εQ) ^ 2) (hN0 : 0 ≤ N) (hN : N ≤ d * (1 + εD)) (haI : 0 ≤ aI)
    (hI : aI ^ 2 ≤ 2 * V * E / d + d * V ^ 2 / 2)
    (he : e ≤ V * √Q + k * aI ^ 2) (hp0 : 0 ≤ p)
    (hp : p ≤ √V * √Q + k * aI * √N) (hlam : 0 < lam)
    (hce : ce = εQ + 2 * εD ^ 2 + v6 / 2) :
    (√E * √V + 2 * p + e) ^ 2 ≤ 3 * (E * V + 4 * p ^ 2 + e ^ 2) ∧
    4 * p ^ 2 ≤ 8 * (V * Q) + E * V * (16 + 16 * εD) + 4 * (1 + εD) * (d ^ 2 * V ^ 2) ∧
    e ≤ d * V * ce ∧
    e ≤ Q / (2 * lam * d) + 2 * v6 * E / d + d * v6 ^ 2 * (lam + 1) / 2 := by
  have sQ0 : 0 ≤ √Q := Real.sqrt_nonneg _
  have sN0 : 0 ≤ √N := Real.sqrt_nonneg _
  have sQ2 : √Q ^ 2 = Q := Real.sq_sqrt hQ0
  have sV2 : √V ^ 2 = V := Real.sq_sqrt hV0
  have sE2 : √E ^ 2 = E := Real.sq_sqrt hE0
  have sN2 : √N ^ 2 = N := Real.sq_sqrt hN0
  have sQle : √Q ≤ d * εQ :=
    (le_abs_self _).trans (abs_le_of_sq_le_sq (sQ2.le.trans hQ) (mul_nonneg hd.le hεQ0))
  have hkI : k * aI ^ 2 ≤ aI ^ 2 := by
    have := mul_le_mul_of_nonneg_right hk1 (sq_nonneg aI); linarith only [this]
  have t2 : V ^ 2 ≤ v6 ^ 2 := pow_le_pow_left₀ hV0 hV6 2
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e0 : (√E * √V) ^ 2 = E * V := by rw [mul_pow, sE2, sV2]
    have h0 : (√E * √V + 2 * p + e) ^ 2 ≤ 3 * ((√E * √V) ^ 2 + (2 * p) ^ 2 + e ^ 2) := by
      nlinarith only [sq_nonneg (√E * √V - 2 * p), sq_nonneg (√E * √V - e),
        sq_nonneg (2 * p - e)]
    rw [e0] at h0
    calc (√E * √V + 2 * p + e) ^ 2 ≤ 3 * (E * V + (2 * p) ^ 2 + e ^ 2) := h0
      _ = 3 * (E * V + 4 * p ^ 2 + e ^ 2) := by ring
  · have hp' : p ≤ √V * √Q + aI * √N := by
      have : k * aI * √N ≤ 1 * (aI * √N) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_right hk1 (mul_nonneg haI sN0)
      linarith only [hp, this]
    have h := pow_le_pow_left₀ hp0 hp' 2
    have e1 : (√V * √Q) ^ 2 = V * Q := by rw [mul_pow, sV2, sQ2]
    have e2 : (aI * √N) ^ 2 = aI ^ 2 * N := by rw [mul_pow, sN2]
    have h0 : (√V * √Q + aI * √N) ^ 2 ≤ 2 * (√V * √Q) ^ 2 + 2 * (aI * √N) ^ 2 := by
      nlinarith only [sq_nonneg (√V * √Q - aI * √N)]
    rw [e1, e2] at h0
    have hB0 : 0 ≤ 2 * V * E / d + d * V ^ 2 / 2 := by positivity
    have h3 : aI ^ 2 * N ≤ (1 + εD) * (2 * (V * E) + d ^ 2 * V ^ 2 / 2) := by
      calc aI ^ 2 * N ≤ (2 * V * E / d + d * V ^ 2 / 2) * (d * (1 + εD)) :=
            mul_le_mul hI hN hN0 hB0
        _ = (1 + εD) * (2 * (V * E) + d ^ 2 * V ^ 2 / 2) := by field_simp
    have a2 : 8 * ((1 + εD) * (2 * (V * E) + d ^ 2 * V ^ 2 / 2)) =
        E * V * (16 + 16 * εD) + 4 * (1 + εD) * (d ^ 2 * V ^ 2) := by ring
    linarith only [h, h0, h3, a2]
  · have hEd : E / d ≤ d * εD ^ 2 := by
      rw [div_le_iff₀ hd]
      calc E ≤ (d * εD) ^ 2 := hE
        _ = d * εD ^ 2 * d := by ring
    have t1 : V * √Q ≤ V * (d * εQ) := mul_le_mul_of_nonneg_left sQle hV0
    have t2' : 2 * V * E / d ≤ 2 * V * (d * εD ^ 2) := by
      rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hEd (by positivity)
    have t3 : d * V ^ 2 / 2 ≤ d * V * (v6 / 2) := by
      have h := mul_le_mul_of_nonneg_left hV6 (mul_nonneg hd.le hV0)
      calc d * V ^ 2 / 2 = d * V * V / 2 := by ring
        _ ≤ d * V * v6 / 2 := by linarith only [h]
        _ = d * V * (v6 / 2) := by ring
    calc e ≤ V * √Q + k * aI ^ 2 := he
      _ ≤ V * (d * εQ) + (2 * V * (d * εD ^ 2) + d * V * (v6 / 2)) := by
          linarith only [t1, hkI, hI, t2', t3]
      _ = d * V * ce := by rw [hce]; ring
  · have t1 : V * √Q ≤ lam * d * V ^ 2 / 2 + Q / (2 * lam * d) := by
      have hld : 0 < lam * d := mul_pos hlam hd
      have e0 : lam * d * V ^ 2 / 2 + Q / (2 * lam * d) =
          ((lam * d * V) ^ 2 + Q) / (2 * (lam * d)) := by field_simp
      rw [e0, le_div_iff₀ (by positivity)]
      have h0 := sq_nonneg (lam * d * V - √Q)
      have e1 : (lam * d * V - √Q) ^ 2 =
          (lam * d * V) ^ 2 - 2 * (lam * d) * (V * √Q) + √Q ^ 2 := by ring
      rw [e1, sQ2] at h0
      linarith only [h0]
    have t1' : 2 * V * E / d ≤ 2 * v6 * E / d := by
      apply div_le_div_of_nonneg_right _ hd.le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV6 (by norm_num)) hE0
    have t3 : lam * d * V ^ 2 / 2 + d * V ^ 2 / 2 ≤ d * v6 ^ 2 * (lam + 1) / 2 := by
      have h := mul_le_mul_of_nonneg_left t2 (by positivity : 0 ≤ d * (lam + 1) / 2)
      calc lam * d * V ^ 2 / 2 + d * V ^ 2 / 2 = d * (lam + 1) / 2 * V ^ 2 := by ring
        _ ≤ d * (lam + 1) / 2 * v6 ^ 2 := h
        _ = d * v6 ^ 2 * (lam + 1) / 2 := by ring
    linarith only [he, hkI, hI, t1, t1', t3]

/-- The arithmetic of the comparison. `ce = εQ + 2εD² + v6/2`, `ke = 4 + 24·v6·ce/Pc`. -/
lemma arith_II {d εD εQ k V v6 E Q N aI e p lam Pc ce ke : ℝ}
    (hd : 0 < d) (hεD0 : 0 ≤ εD) (hεQ0 : 0 ≤ εQ) (hk1 : k ≤ 1)
    (hV0 : 0 ≤ V) (hV6 : V ≤ v6) (hE0 : 0 ≤ E) (hE : E ≤ (d * εD) ^ 2) (hQ0 : 0 ≤ Q)
    (hQ : Q ≤ (d * εQ) ^ 2) (hN0 : 0 ≤ N) (hN : N ≤ d * (1 + εD)) (haI : 0 ≤ aI)
    (hI : aI ^ 2 ≤ 2 * V * E / d + d * V ^ 2 / 2)
    (he0 : 0 ≤ e) (he : e ≤ V * √Q + k * aI ^ 2) (hp0 : 0 ≤ p)
    (hp : p ≤ √V * √Q + k * aI * √N) (hlam : 0 < lam) (hPc : 0 < Pc)
    (hce : ce = εQ + 2 * εD ^ 2 + v6 / 2) (hke : ke = 4 + 24 * v6 * ce / Pc) :
    8 / (Pc * d) * (√E * √V + 2 * p + e) ^ 2 + 4 * e ≤
      (192 * v6 / Pc + ke / (2 * lam)) * (Q / d) +
      (24 * v6 * (17 + 16 * εD) / Pc + 2 * v6 * ke) * (E / d) +
      d * (96 * (1 + εD) * v6 ^ 2 / Pc + ke * v6 ^ 2 * (lam + 1) / 2) := by
  obtain ⟨h1, h2, h4, s5⟩ := arith_II_pre hd hεQ0 hk1 hV0 hV6 hE0 hE hQ0 hQ hN0 hN haI hI he
    hp0 hp hlam hce
  have hv60 : 0 ≤ v6 := hV0.trans hV6
  have hce0 : 0 ≤ ce := by rw [hce]; positivity
  have hke0 : 0 ≤ ke := by rw [hke]; positivity
  have h6 : e ^ 2 ≤ (d * V * ce) * e := by
    have := mul_le_mul_of_nonneg_right h4 he0
    calc e ^ 2 = e * e := by ring
      _ ≤ d * V * ce * e := this
  have hu8 : 8 / (Pc * d) = 8 * (1 / (Pc * d)) := by ring
  have inner1 : E * V + 4 * p ^ 2 + e ^ 2 ≤
      E * V * (17 + 16 * εD) + 8 * (V * Q) + 4 * (1 + εD) * (d ^ 2 * V ^ 2) + d * V * ce * e := by
    linarith only [h2, h6]
  have t2 : V ^ 2 ≤ v6 ^ 2 := pow_le_pow_left₀ hV0 hV6 2
  have inner2 : E * V * (17 + 16 * εD) + 8 * (V * Q) + 4 * (1 + εD) * (d ^ 2 * V ^ 2) ≤
      E * v6 * (17 + 16 * εD) + 8 * (v6 * Q) + 4 * (1 + εD) * (d ^ 2 * v6 ^ 2) := by
    have a1 : E * V * (17 + 16 * εD) ≤ E * v6 * (17 + 16 * εD) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV6 hE0) (by positivity)
    have a2 : V * Q ≤ v6 * Q := mul_le_mul_of_nonneg_right hV6 hQ0
    have a3 : 4 * (1 + εD) * (d ^ 2 * V ^ 2) ≤ 4 * (1 + εD) * (d ^ 2 * v6 ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left t2 (by positivity)) (by positivity)
    linarith only [a1, a2, a3]
  have hcoef : 24 * (1 / (Pc * d)) * (d * V * ce) + 4 ≤ ke := by
    have e1 : 24 * (1 / (Pc * d)) * (d * V * ce) = 24 * V * ce / Pc := by field_simp
    rw [e1, hke]
    have : 24 * V * ce / Pc ≤ 24 * v6 * ce / Pc := by
      apply div_le_div_of_nonneg_right _ hPc.le
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV6 (by norm_num)) hce0
    linarith only [this]
  have hpos24 : (0 : ℝ) ≤ 24 * (1 / (Pc * d)) := by positivity
  calc 8 / (Pc * d) * (√E * √V + 2 * p + e) ^ 2 + 4 * e
      ≤ 8 * (1 / (Pc * d)) * (3 * (E * V + 4 * p ^ 2 + e ^ 2)) + 4 * e := by
        rw [hu8]
        have := mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 8 * (1 / (Pc * d)))
        linarith only [this]
    _ = 24 * (1 / (Pc * d)) * (E * V + 4 * p ^ 2 + e ^ 2) + 4 * e := by ring
    _ ≤ 24 * (1 / (Pc * d)) * (E * V * (17 + 16 * εD) + 8 * (V * Q) +
          4 * (1 + εD) * (d ^ 2 * V ^ 2) + d * V * ce * e) + 4 * e := by
        have := mul_le_mul_of_nonneg_left inner1 hpos24
        linarith only [this]
    _ = 24 * (1 / (Pc * d)) * (E * V * (17 + 16 * εD) + 8 * (V * Q) +
          4 * (1 + εD) * (d ^ 2 * V ^ 2)) + (24 * (1 / (Pc * d)) * (d * V * ce) + 4) * e := by ring
    _ ≤ 24 * (1 / (Pc * d)) * (E * v6 * (17 + 16 * εD) + 8 * (v6 * Q) +
          4 * (1 + εD) * (d ^ 2 * v6 ^ 2)) +
        ke * (Q / (2 * lam * d) + 2 * v6 * E / d + d * v6 ^ 2 * (lam + 1) / 2) := by
        have a1 := mul_le_mul_of_nonneg_left inner2 hpos24
        have a2 := mul_le_mul_of_nonneg_right hcoef he0
        have a3 := mul_le_mul_of_nonneg_left s5 hke0
        linarith only [a1, a2, a3]
    _ = (192 * v6 / Pc + ke / (2 * lam)) * (Q / d) +
        (24 * v6 * (17 + 16 * εD) / Pc + 2 * v6 * ke) * (E / d) +
        d * (96 * (1 + εD) * v6 ^ 2 / Pc + ke * v6 ^ 2 * (lam + 1) / 2) := by
        field_simp; ring

end BstLean.Part150
