import BstLean.Part150Final

/-!
# Part 150: Proposition P45 (iii) of `onW45-opus-prover.md` §3, the arithmetic (real numbers)

* `sqrt_cs`: `√(px) + √(qy) ≤ √((p + q)(x + y))` (the Cauchy–Schwarz step in `θ` of the paper).
* `abs_sqrt_sub_le`: `|√a − √b| ≤ |a − b|/√b`.
* `p45_T1`, `p45_Tb`, `p45_Ta`: the three terms in the unit `ρ·√(γ/n)`.
* `p45_arith`: the assembly.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open Real

lemma sqrt_cs {p q x y : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    √(p * x) + √(q * y) ≤ √((p + q) * (x + y)) := by
  have hpx : 0 ≤ p * x := mul_nonneg hp hx
  have hqy : 0 ≤ q * y := mul_nonneg hq hy
  have sq1 : √(p * x) ^ 2 = p * x := Real.sq_sqrt hpx
  have sq2 : √(q * y) ^ 2 = q * y := Real.sq_sqrt hqy
  have h12 : √(p * x) * √(q * y) ≤ (p * y + q * x) / 2 := by
    rw [← Real.sqrt_mul hpx, Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    nlinarith only [sq_nonneg (p * y - q * x)]
  have h : (√(p * x) + √(q * y)) ^ 2 ≤ (p + q) * (x + y) := by
    have e : (√(p * x) + √(q * y)) ^ 2 =
        √(p * x) ^ 2 + 2 * (√(p * x) * √(q * y)) + √(q * y) ^ 2 := by ring
    rw [e, sq1, sq2]
    linarith only [h12]
  calc √(p * x) + √(q * y) = √((√(p * x) + √(q * y)) ^ 2) :=
        (Real.sqrt_sq (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).symm
    _ ≤ √((p + q) * (x + y)) := Real.sqrt_le_sqrt h

lemma csqrt {c : ℝ} (hc : 0 ≤ c) (x : ℝ) : c * √x = √(c ^ 2 * x) := by
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

lemma abs_sqrt_sub_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) : |√a - √b| ≤ |a - b| / √b := by
  have hsb : 0 < √b := Real.sqrt_pos.mpr hb
  rw [le_div_iff₀ hsb]
  have h : a - b = (√a - √b) * (√a + √b) := by
    have : (√a - √b) * (√a + √b) = √a ^ 2 - √b ^ 2 := by ring
    rw [this, Real.sq_sqrt ha, Real.sq_sqrt hb.le]
  rw [h, abs_mul, abs_of_nonneg (add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b))]
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.sqrt_nonneg a)) (abs_nonneg _)

/-- The first term (second-layer atoms). -/
lemma p45_T1 {ρ nR a₂ Xc sT2 : ℝ} (hρ : 0 < ρ) (hn : 0 < nR) (ha₂ : 0 ≤ a₂) (hX0 : 0 ≤ Xc)
    (h1 : sT2 ≤ Xc * (2 / nR) * ρ ^ 2) :
    √2 * (a₂ * √sT2) ≤ a₂ * √(2 * Xc * nR) * (ρ * √(2 / nR / nR)) := by
  have e1 : √2 * √sT2 = √(2 * sT2) := (Real.sqrt_mul (by norm_num) _).symm
  have h0 : 0 ≤ 2 * Xc * nR := mul_nonneg (mul_nonneg (by norm_num) hX0) hn.le
  have e2 : √(2 * Xc * nR) * (ρ * √(2 / nR / nR)) =
      √(2 * Xc * nR * (ρ ^ 2 * (2 / nR / nR))) := by
    rw [csqrt hρ.le, ← Real.sqrt_mul h0]
  have e3 : 2 * Xc * nR * (ρ ^ 2 * (2 / nR / nR)) = 2 * (Xc * (2 / nR) * ρ ^ 2) := by
    field_simp
  have h : 2 * sT2 ≤ 2 * Xc * nR * (ρ ^ 2 * (2 / nR / nR)) := by
    rw [e3]; linarith only [h1]
  calc √2 * (a₂ * √sT2) = a₂ * (√2 * √sT2) := by ring
    _ = a₂ * √(2 * sT2) := by rw [e1]
    _ ≤ a₂ * √(2 * Xc * nR * (ρ ^ 2 * (2 / nR / nR))) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h) ha₂
    _ = a₂ * √(2 * Xc * nR) * (ρ * √(2 / nR / nR)) := by rw [← e2]; ring

/-- The unit: `√2·τ/√cs ≤ √(n/cs)·ρ√(γ/n)` (`θ ≤ 1`). -/
lemma p45_Tb {ρ nR cs τ : ℝ} (hρ : 0 < ρ) (hn : 0 < nR) (hcs : 0 < cs) (hτ : 0 < τ)
    (hnτ : nR * τ ^ 2 ≤ ρ ^ 2) :
    √2 * τ / √cs ≤ √(nR / cs) * (ρ * √(2 / nR / nR)) := by
  have e1 : √2 * τ / √cs = √(2 * τ ^ 2 / cs) := by
    rw [Real.sqrt_div' _ hcs.le, Real.sqrt_mul (by norm_num), Real.sqrt_sq hτ.le]
  have e2 : √(nR / cs) * (ρ * √(2 / nR / nR)) = √(nR / cs * (ρ ^ 2 * (2 / nR / nR))) := by
    rw [csqrt hρ.le, ← Real.sqrt_mul (by positivity)]
  have e3 : nR / cs * (ρ ^ 2 * (2 / nR / nR)) = 2 * (ρ ^ 2 / nR) / cs := by field_simp
  have h0 : τ ^ 2 ≤ ρ ^ 2 / nR := by
    rw [le_div_iff₀ hn]; linarith only [hnτ]
  rw [e1, e2, e3]
  exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by linarith only [h0]) hcs.le)

/-- The Cauchy–Schwarz step in `θ`. -/
lemma p45_Ta {ρ nR cs τ w δe δχ : ℝ} (hρ : 0 < ρ) (hn : 0 < nR) (hcs : 0 < cs) (hw : 0 < w)
    (hδe : 0 ≤ δe) (hδχ : 0 ≤ δχ) (hK : cs * τ ^ 2 ≤ (1 + δe) * (2 / nR) * ρ ^ 2) :
    √(2 * (1 + δχ) * w * τ ^ 2) +
        √(4 / π * (w * ((1 + δe) * (2 / nR) * ρ ^ 2 - cs * τ ^ 2) / cs)) ≤
      √(2 * (1 + δe) * w * nR * (1 + δχ + 2 / π) / cs) * (ρ * √(2 / nR / nR)) := by
  have hpi := Real.pi_pos
  have e1 : 2 * (1 + δχ) * w * τ ^ 2 = (1 + δχ) * (2 * w / cs * (cs * τ ^ 2)) := by
    field_simp
  have e2 : 4 / π * (w * ((1 + δe) * (2 / nR) * ρ ^ 2 - cs * τ ^ 2) / cs) =
      2 / π * (2 * w / cs * ((1 + δe) * (2 / nR) * ρ ^ 2 - cs * τ ^ 2)) := by
    field_simp; ring
  have e3 : √(2 * (1 + δe) * w * nR * (1 + δχ + 2 / π) / cs) * (ρ * √(2 / nR / nR)) =
      √(2 * (1 + δe) * w * nR * (1 + δχ + 2 / π) / cs * (ρ ^ 2 * (2 / nR / nR))) := by
    rw [csqrt hρ.le, ← Real.sqrt_mul (by positivity)]
  have e4 : 2 * (1 + δe) * w * nR * (1 + δχ + 2 / π) / cs * (ρ ^ 2 * (2 / nR / nR)) =
      (1 + δχ + 2 / π) * (2 * w / cs * (cs * τ ^ 2) +
        2 * w / cs * ((1 + δe) * (2 / nR) * ρ ^ 2 - cs * τ ^ 2)) := by
    field_simp; ring
  rw [e1, e2, e3, e4]
  have hc0 : 0 ≤ 2 * w / cs := by positivity
  exact sqrt_cs (by positivity) (by positivity) (mul_nonneg hc0 (by positivity))
    (mul_nonneg hc0 (by linarith only [hK]))

lemma phi_id {Y cs : ℝ} (hcs : 0 < cs) :
    √2 * (1 / √(2 * π)) * (2 * (√Y / √cs)) = √(4 / π * (Y / cs)) := by
  have hpi := Real.pi_pos
  have h4 : √(4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hs2 : 0 < √(2 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsp : 0 < √π := Real.sqrt_pos.mpr hpi
  have hsc : 0 < √cs := Real.sqrt_pos.mpr hcs
  have eR : √(4 / π * (Y / cs)) = 2 / √π * (√Y / √cs) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_div' _ hpi.le, h4, Real.sqrt_div' _ hcs.le]
  have eL : √(2 * π) = √2 * √π := Real.sqrt_mul (by norm_num) _
  rw [eR, eL]
  field_simp

/-- **The arithmetic of Proposition P45 (iii).** -/
lemma p45_arith {ρ τ nR a₁ a₂ q₁ w cs δe δχ sT2 sO2 NA Xv : ℝ}
    (hρ : 0 < ρ) (hn : 0 < nR) (hcs : 0 < cs) (hτ : 0 < τ) (hw : 0 < w) (hδe : 0 ≤ δe)
    (hδχ : 0 ≤ δχ) (ha₁ : 0 ≤ a₁) (ha₂ : 0 ≤ a₂) (hq₁ : 0 ≤ q₁)
    (hnτ : nR * τ ^ 2 ≤ ρ ^ 2) (hsT0 : 0 ≤ sT2)
    (h1 : sT2 ≤ (1 + δe) * (1 + 2 * w * q₁) * (2 / nR) * ρ ^ 2)
    (h2 : cs * τ ^ 2 ≤ sO2) (hK : cs * τ ^ 2 ≤ (1 + δe) * (2 / nR) * ρ ^ 2)
    (h3 : |sT2 - sO2| ≤ 4 * w * q₁ * τ ^ 2 +
      4 * a₁ * τ * √(w * ((1 + δe) * (2 / nR) * ρ ^ 2 - cs * τ ^ 2)) + 4 * w * a₁ ^ 2 * τ ^ 2)
    (h4 : NA ≤ 8 * (1 + δχ) * w * a₁ ^ 2 * τ ^ 2)
    (hX : Xv ≤ √2 * (a₂ * √sT2 + 1 / √(2 * π) * |√sT2 - √sO2|) + √NA) :
    Xv ≤ (a₂ * √(2 * (1 + δe) * (1 + 2 * w * q₁) * nR) +
        2 * a₁ * √(2 * (1 + δe) * w * nR * (1 + δχ + 2 / π) / cs) +
        4 * (1 / √(2 * π)) * w * √(nR / cs) * (q₁ + a₁ ^ 2)) * (ρ * √(2 / nR / nR)) := by
  have hpi := Real.pi_pos
  have hsc : 0 < √cs := Real.sqrt_pos.mpr hcs
  have T1 := p45_T1 hρ hn ha₂ (Xc := (1 + δe) * (1 + 2 * w * q₁)) (by positivity) h1
  rw [show 2 * ((1 + δe) * (1 + 2 * w * q₁)) * nR = 2 * (1 + δe) * (1 + 2 * w * q₁) * nR by ring]
    at T1
  have Tb := p45_Tb hρ hn hcs hτ hnτ
  have Ta := p45_Ta (τ := τ) (w := w) (δχ := δχ) hρ hn hcs hw hδe hδχ hK
  have hsO2 : 0 < sO2 := lt_of_lt_of_le (by positivity) h2
  have hsO : √cs * τ ≤ √sO2 := by
    have : √(cs * τ ^ 2) = √cs * τ := by rw [Real.sqrt_mul hcs.le, Real.sqrt_sq hτ.le]
    rw [← this]; exact Real.sqrt_le_sqrt h2
  have hB : 0 ≤ 4 * w * q₁ * τ ^ 2 +
      4 * a₁ * τ * √(w * ((1 + δe) * (2 / nR) * ρ ^ 2 - cs * τ ^ 2)) + 4 * w * a₁ ^ 2 * τ ^ 2 :=
    (abs_nonneg _).trans h3
  have hD : |√sT2 - √sO2| ≤ 4 * w * (q₁ + a₁ ^ 2) * τ / √cs +
      2 * a₁ * (2 * (√(w * ((1 + δe) * (2 / nR) * ρ ^ 2 - cs * τ ^ 2)) / √cs)) := by
    have d1 := abs_sqrt_sub_le hsT0 hsO2
    have d2 : |sT2 - sO2| / √sO2 ≤ (4 * w * q₁ * τ ^ 2 +
        4 * a₁ * τ * √(w * ((1 + δe) * (2 / nR) * ρ ^ 2 - cs * τ ^ 2)) +
        4 * w * a₁ ^ 2 * τ ^ 2) / √sO2 :=
      div_le_div_of_nonneg_right h3 (Real.sqrt_nonneg _)
    have d3 : (4 * w * q₁ * τ ^ 2 +
        4 * a₁ * τ * √(w * ((1 + δe) * (2 / nR) * ρ ^ 2 - cs * τ ^ 2)) +
        4 * w * a₁ ^ 2 * τ ^ 2) / √sO2 ≤ (4 * w * q₁ * τ ^ 2 +
        4 * a₁ * τ * √(w * ((1 + δe) * (2 / nR) * ρ ^ 2 - cs * τ ^ 2)) +
        4 * w * a₁ ^ 2 * τ ^ 2) / (√cs * τ) :=
      div_le_div_of_nonneg_left hB (by positivity) hsO
    have e : (4 * w * q₁ * τ ^ 2 +
        4 * a₁ * τ * √(w * ((1 + δe) * (2 / nR) * ρ ^ 2 - cs * τ ^ 2)) +
        4 * w * a₁ ^ 2 * τ ^ 2) / (√cs * τ) = 4 * w * (q₁ + a₁ ^ 2) * τ / √cs +
      2 * a₁ * (2 * (√(w * ((1 + δe) * (2 / nR) * ρ ^ 2 - cs * τ ^ 2)) / √cs)) := by
      field_simp; ring
    rw [← e]
    exact d1.trans (d2.trans d3)
  have hc0 : 0 ≤ √2 * (1 / √(2 * π)) := by positivity
  have hD' := mul_le_mul_of_nonneg_left hD hc0
  have ephi : √2 * (1 / √(2 * π)) * (2 * a₁ *
      (2 * (√(w * ((1 + δe) * (2 / nR) * ρ ^ 2 - cs * τ ^ 2)) / √cs))) =
      2 * a₁ * √(4 / π * (w * ((1 + δe) * (2 / nR) * ρ ^ 2 - cs * τ ^ 2) / cs)) := by
    rw [← phi_id hcs]; ring
  have hNA : √NA ≤ 2 * a₁ * √(2 * (1 + δχ) * w * τ ^ 2) := by
    rw [csqrt (by positivity)]
    refine Real.sqrt_le_sqrt (h4.trans (le_of_eq ?_))
    ring
  have F4 := mul_le_mul_of_nonneg_left Ta (by positivity : (0 : ℝ) ≤ 2 * a₁)
  have F5 := mul_le_mul_of_nonneg_left Tb
    (by positivity : (0 : ℝ) ≤ 4 * (1 / √(2 * π)) * w * (q₁ + a₁ ^ 2))
  calc Xv ≤ √2 * (a₂ * √sT2 + 1 / √(2 * π) * |√sT2 - √sO2|) + √NA := hX
    _ = √2 * (a₂ * √sT2) + √2 * (1 / √(2 * π)) * |√sT2 - √sO2| + √NA := by ring
    _ ≤ a₂ * √(2 * (1 + δe) * (1 + 2 * w * q₁) * nR) * (ρ * √(2 / nR / nR)) +
        √2 * (1 / √(2 * π)) * (4 * w * (q₁ + a₁ ^ 2) * τ / √cs +
          2 * a₁ * (2 * (√(w * ((1 + δe) * (2 / nR) * ρ ^ 2 - cs * τ ^ 2)) / √cs))) +
        2 * a₁ * √(2 * (1 + δχ) * w * τ ^ 2) := add_le_add (add_le_add T1 hD') hNA
    _ = a₂ * √(2 * (1 + δe) * (1 + 2 * w * q₁) * nR) * (ρ * √(2 / nR / nR)) +
        4 * (1 / √(2 * π)) * w * (q₁ + a₁ ^ 2) * (√2 * τ / √cs) +
        2 * a₁ * (√(2 * (1 + δχ) * w * τ ^ 2) +
          √(4 / π * (w * ((1 + δe) * (2 / nR) * ρ ^ 2 - cs * τ ^ 2) / cs))) := by
        linear_combination ephi
    _ ≤ a₂ * √(2 * (1 + δe) * (1 + 2 * w * q₁) * nR) * (ρ * √(2 / nR / nR)) +
        4 * (1 / √(2 * π)) * w * (q₁ + a₁ ^ 2) * (√(nR / cs) * (ρ * √(2 / nR / nR))) +
        2 * a₁ * (√(2 * (1 + δe) * w * nR * (1 + δχ + 2 / π) / cs) * (ρ * √(2 / nR / nR))) :=
        add_le_add (add_le_add le_rfl F5) F4
    _ = _ := by ring

end BstLean.Part150
