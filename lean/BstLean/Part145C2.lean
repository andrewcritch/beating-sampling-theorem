import BstLean.Part143World
import BstLean.Part145C1

/-!
# Part 145, helper `C2`: the cosine link with a second-order term near `4.5/n`

This file repeats `lin_cos_unit_L2b` and `lin_cos_L2b` of `Part133CosB` with the constant
`jCosC n` in the place of `(15/2)·√(12 + 48/n)/n` (about `26/n`).

Notation: `x = a² − 1`, `y = b² − 1`, `u = (x + y)/2`, `m = max(|x|, |y|)`, `p = a·b`,
`q = 1 − p`, `D = (a − b)²/2`, `V = (x − y)²/8`, `E = c − τ(a² + b²)/2`, `T = c/p`.
Exact identities: `q = D − u`, `D = V − D·u + D²/2` and
`T − τ = (E + τD)(1 + q + q²) + (T − τ)q³`. They give
`T − τ = E + τV − E·u + E·D − 2τ·D·u + (3/2)τ·D² + (E + τD)q² + (T − τ)q³`.

* `half_sq_sub_le_sq`: `D ≤ m²`.
* `cos_ptC`: `|T − τ| ≤ |E| + |τ|(x² + y²)/4 + |E||u| + (5/2)|E|m² + m³/4 + 12m⁴`.
* `l2_abs_mul_of_sq` (Cauchy–Schwarz for a product), `l2_max_pow`, `cos_L2_core`.
* `jCosC n = (17/16)·K + (5/2)·√(K·√2·Q) + (1/4)·√(√2·K·√2·Q) + 12·√2·Q`, `K = K4 n/n`,
  `Q = qCos n`; **`lin_cos_unit_L2c`**, **`lin_cos_L2c`** (every `n ≥ 1`);
  **`jCosC_le`**: `jCosC n ≤ 4.475/n` for `n ≥ 4096`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Set
open BstLean.Part130 BstLean.Part131 BstLean.Part132 BstLean.Part133
open BstLean.Part143 (l2_mul_integrable l2_abs_integral_mul_le)

/-! ## The pointwise bound -/

lemma half_sq_sub_le_sq_aux {a b m : ℝ} (hb : 0 ≤ b) (hba : b ≤ a) (hu : |a ^ 2 - 1| ≤ m)
    (hw : |b ^ 2 - 1| ≤ m) : (a - b) ^ 2 / 2 ≤ m ^ 2 := by
  have hu' := abs_le.mp hu
  have hw' := abs_le.mp hw
  have hm0 : 0 ≤ m := (abs_nonneg _).trans hu
  obtain ⟨r, hr0, hr2⟩ : ∃ r : ℝ, 0 < r ∧ r ^ 2 = 2 :=
    ⟨√2, by positivity, Real.sq_sqrt (by norm_num)⟩
  rcases le_or_gt r (a + b) with h | h
  · have h1 : 2 ≤ (a + b) ^ 2 := by nlinarith
    have h2 : (a ^ 2 - b ^ 2) ^ 2 ≤ (2 * m) ^ 2 := sq_le_sq' (by linarith) (by linarith)
    have h3 : (a - b) ^ 2 * (a + b) ^ 2 = (a ^ 2 - b ^ 2) ^ 2 := by ring
    nlinarith [sq_nonneg (a - b)]
  · have hb2 : 2 * b < r := by linarith
    have hrb : r * b < 1 := by nlinarith
    have h0 : 0 ≤ b * (2 - r * b) := mul_nonneg hb (by linarith)
    have h1 : a - b ≤ r * (1 - b ^ 2) := by nlinarith
    have h2 : 0 ≤ 1 - b ^ 2 := by nlinarith [mul_pos (sub_pos.2 hb2) (by linarith : 0 < r + 2 * b)]
    have h3 : r * (1 - b ^ 2) ≤ r * m := mul_le_mul_of_nonneg_left (by linarith) hr0.le
    have h4 : (a - b) ^ 2 ≤ (r * m) ^ 2 := pow_le_pow_left₀ (by linarith) (h1.trans h3) 2
    rw [mul_pow, hr2] at h4
    linarith

/-- `(a − b)²/2 ≤ m²` if `|a² − 1| ≤ m` and `|b² − 1| ≤ m` (`a, b ≥ 0`). -/
lemma half_sq_sub_le_sq {a b m : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : |a ^ 2 - 1| ≤ m)
    (hw : |b ^ 2 - 1| ≤ m) : (a - b) ^ 2 / 2 ≤ m ^ 2 := by
  rcases le_total b a with h | h
  · exact half_sq_sub_le_sq_aux hb h hu hw
  · have := half_sq_sub_le_sq_aux ha h hw hu
    rwa [show (b - a) ^ 2 = (a - b) ^ 2 by ring] at this

/-- `V·|u| ≤ m³/8`, `V = (x − y)²/8`, `u = (x + y)/2`. -/
lemma ptC_Vu {x y m : ℝ} (hu : |x| ≤ m) (hw : |y| ≤ m) :
    (x - y) ^ 2 / 8 * |(x + y) / 2| ≤ m ^ 3 / 8 := by
  have hu' := abs_le.mp hu
  have hw' := abs_le.mp hw
  have hm0 : 0 ≤ m := (abs_nonneg _).trans hu
  have hx2 : x ^ 2 ≤ m ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have hy2 : y ^ 2 ≤ m ^ 2 := sq_le_sq' (by linarith) (by linarith)
  have e1 : (x - y) ^ 2 * |x + y| = |x - y| * |x ^ 2 - y ^ 2| := by
    rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul, ← sq_abs (x - y)]
    ring
  have e2 : |(x + y) / 2| = |x + y| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h1 : |x - y| ≤ 2 * m := by
    rw [abs_le]; constructor <;> linarith
  have h2 : |x ^ 2 - y ^ 2| ≤ m ^ 2 := by
    rw [abs_le]; constructor <;> linarith [sq_nonneg x, sq_nonneg y]
  have h3 : |x - y| * |x ^ 2 - y ^ 2| ≤ 2 * m * m ^ 2 :=
    mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
  have e3 : (x - y) ^ 2 / 8 * (|x + y| / 2) = (x - y) ^ 2 * |x + y| / 16 := by ring
  rw [e2, e3, e1]
  linarith

/-- `D·|u| ≤ m³/8 + (3/2)·m⁴` from the identity `D = V − D·u + D²/2`. -/
lemma ptC_Du {D V u m : ℝ} (hD0 : 0 ≤ D) (hm0 : 0 ≤ m) (hDm : D ≤ m) (hDm2 : D ≤ m ^ 2)
    (hum : |u| ≤ m) (hDid : D = V - D * u + D ^ 2 / 2) (hVu : V * |u| ≤ m ^ 3 / 8) :
    D * |u| ≤ m ^ 3 / 8 + 3 / 2 * m ^ 4 := by
  have hDV : D ≤ V + 3 / 2 * (D * m) := by
    have h1 : D * (-u) ≤ D * m :=
      mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp hum).1]) hD0
    have h2 : D * D ≤ D * m := mul_le_mul_of_nonneg_left hDm hD0
    linarith
  have h1 : D * |u| ≤ (V + 3 / 2 * (D * m)) * |u| :=
    mul_le_mul_of_nonneg_right hDV (abs_nonneg u)
  have h2 : D * m * |u| ≤ m ^ 2 * m * m :=
    mul_le_mul (mul_le_mul hDm2 le_rfl hm0 (sq_nonneg m)) hum (abs_nonneg _) (by positivity)
  have e1 : (V + 3 / 2 * (D * m)) * |u| = V * |u| + 3 / 2 * (D * m * |u|) := by ring
  have e2 : m ^ 2 * m * m = m ^ 4 := by ring
  linarith

/-- The last term of the identity: `t·|q|³ ≤ (1/2)·e·q² + 6q⁴` if `t ≤ 2` and
`t·(1 − q) ≤ e`. -/
lemma ptC_Tq {t q e : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2) (he : 0 ≤ e) (h : t * (1 - q) ≤ e) :
    t * |q| ^ 3 ≤ 1 / 2 * (e * q ^ 2) + 6 * q ^ 4 := by
  have hq3 : |q| ^ 3 = |q| * q ^ 2 := by rw [← sq_abs q]; ring
  have hq4 : |q| ^ 4 = q ^ 4 := by
    calc |q| ^ 4 = (|q| ^ 2) ^ 2 := by ring
      _ = (q ^ 2) ^ 2 := by rw [sq_abs]
      _ = q ^ 4 := by ring
  rcases le_or_gt |q| (1 / 3) with hq | hq
  · have hp23 : 2 / 3 ≤ 1 - q := by linarith [(abs_le.mp hq).2]
    have h1 : t ≤ 3 / 2 * e := by
      have := mul_le_mul_of_nonneg_left hp23 ht0
      linarith
    have h2 : t * |q| ≤ 3 / 2 * e * (1 / 3) := mul_le_mul h1 hq (abs_nonneg _) (by positivity)
    have h3 : t * |q| * q ^ 2 ≤ 3 / 2 * e * (1 / 3) * q ^ 2 :=
      mul_le_mul_of_nonneg_right h2 (sq_nonneg q)
    have h4 : 0 ≤ q ^ 4 := by positivity
    rw [hq3]
    linarith
  · have h1 : t * |q| ^ 3 ≤ 2 * |q| ^ 3 := mul_le_mul_of_nonneg_right ht2 (by positivity)
    have h2 : |q| ^ 3 * (1 / 3) ≤ |q| ^ 3 * |q| :=
      mul_le_mul_of_nonneg_left hq.le (by positivity)
    have h3 : 0 ≤ e * q ^ 2 := by positivity
    rw [← hq4]
    linarith

/-- The sum of the eight terms of the identity. -/
lemma ptC_fin {Tt E τ V u D q m X2 : ℝ} (hτ : |τ| ≤ 1) (hD0 : 0 ≤ D)
    (hDm2 : D ≤ m ^ 2) (hV0 : 0 ≤ V) (hVx : V ≤ X2) (hqm : |q| ≤ m)
    (hDu : D * |u| ≤ m ^ 3 / 8 + 3 / 2 * m ^ 4)
    (hTq : |Tt| * |q| ^ 3 ≤ 1 / 2 * ((|E| + D) * q ^ 2) + 6 * q ^ 4)
    (main : Tt = E + τ * V - E * u + E * D - 2 * τ * D * u + 3 / 2 * τ * D ^ 2 +
        (E + τ * D) * q ^ 2 + Tt * q ^ 3) :
    |Tt| ≤ |E| + |τ| * X2 + |E| * |u| + 5 / 2 * (|E| * m ^ 2) + 1 / 4 * m ^ 3 +
      12 * m ^ 4 := by
  have hE0 := abs_nonneg E
  have hτ0 := abs_nonneg τ
  have hq2 : q ^ 2 ≤ m ^ 2 := by
    rw [← sq_abs q]
    exact pow_le_pow_left₀ (abs_nonneg _) hqm 2
  have hq4 : |q| ^ 4 = q ^ 4 := by
    calc |q| ^ 4 = (|q| ^ 2) ^ 2 := by ring
      _ = (q ^ 2) ^ 2 := by rw [sq_abs]
      _ = q ^ 4 := by ring
  have hq4m : q ^ 4 ≤ m ^ 4 := by
    rw [← hq4]
    exact pow_le_pow_left₀ (abs_nonneg _) hqm 4
  have hDD : D ^ 2 ≤ m ^ 4 := by
    have := mul_le_mul hDm2 hDm2 hD0 (sq_nonneg m)
    have e : m ^ 2 * m ^ 2 = m ^ 4 := by ring
    have e' : D * D = D ^ 2 := by ring
    linarith
  have hcτ : |E + τ * D| ≤ |E| + D := by
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hD0]
    have := mul_le_of_le_one_left hD0 hτ
    linarith
  have b2 : |τ * V| ≤ |τ| * X2 := by
    rw [abs_mul, abs_of_nonneg hV0]
    exact mul_le_mul_of_nonneg_left hVx hτ0
  have b3 : |E * u| ≤ |E| * |u| := (abs_mul _ _).le
  have b4 : |E * D| ≤ |E| * m ^ 2 := by
    rw [abs_mul, abs_of_nonneg hD0]
    exact mul_le_mul_of_nonneg_left hDm2 hE0
  have b5 : |2 * τ * D * u| ≤ m ^ 3 / 4 + 3 * m ^ 4 := by
    have e : |2 * τ * D * u| = 2 * (|τ| * (D * |u|)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
        abs_of_nonneg hD0]
      ring
    have := mul_le_of_le_one_left (mul_nonneg hD0 (abs_nonneg u)) hτ
    rw [e]
    linarith
  have b6 : |3 / 2 * τ * D ^ 2| ≤ 3 / 2 * m ^ 4 := by
    have e : |3 / 2 * τ * D ^ 2| = 3 / 2 * (|τ| * D ^ 2) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg D),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 2)]
      ring
    have := mul_le_of_le_one_left (sq_nonneg D) hτ
    rw [e]
    linarith
  have hEm : (|E| + D) * q ^ 2 ≤ (|E| + m ^ 2) * m ^ 2 :=
    mul_le_mul (by linarith) hq2 (sq_nonneg q) (add_nonneg hE0 (sq_nonneg m))
  have eEm : (|E| + m ^ 2) * m ^ 2 = |E| * m ^ 2 + m ^ 4 := by ring
  have b7 : |(E + τ * D) * q ^ 2| ≤ |E| * m ^ 2 + m ^ 4 := by
    rw [abs_mul, abs_of_nonneg (sq_nonneg q)]
    have h1 : |E + τ * D| * q ^ 2 ≤ (|E| + D) * q ^ 2 :=
      mul_le_mul_of_nonneg_right hcτ (sq_nonneg q)
    linarith
  have b8 : |Tt * q ^ 3| ≤ 1 / 2 * (|E| * m ^ 2) + 13 / 2 * m ^ 4 := by
    rw [abs_mul, abs_pow]
    linarith
  obtain ⟨l2, u2⟩ := abs_le.mp b2
  obtain ⟨l3, u3⟩ := abs_le.mp b3
  obtain ⟨l4, u4⟩ := abs_le.mp b4
  obtain ⟨l5, u5⟩ := abs_le.mp b5
  obtain ⟨l6, u6⟩ := abs_le.mp b6
  obtain ⟨l7, u7⟩ := abs_le.mp b7
  obtain ⟨l8, u8⟩ := abs_le.mp b8
  obtain ⟨l1, u1⟩ := abs_le.mp (le_refl |E|)
  rw [abs_le]
  constructor
  · rw [main]; linarith
  · rw [main]; linarith

/-- The pointwise bound of a cosine with a second-order term of the weights `1/4` and `1`. -/
lemma cos_ptC {a b c τ T : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hτ : |τ| ≤ 1)
    (hT : |T| ≤ 1) (hTeq : 0 < a * b → T = c / (a * b)) :
    |T - τ| ≤ |c - τ * ((a ^ 2 + b ^ 2) / 2)| +
      |τ| * (((a ^ 2 - 1) ^ 2 + (b ^ 2 - 1) ^ 2) / 4) +
      |c - τ * ((a ^ 2 + b ^ 2) / 2)| * |((a ^ 2 - 1) + (b ^ 2 - 1)) / 2| +
      5 / 2 * (|c - τ * ((a ^ 2 + b ^ 2) / 2)| * max |a ^ 2 - 1| |b ^ 2 - 1| ^ 2) +
      1 / 4 * max |a ^ 2 - 1| |b ^ 2 - 1| ^ 3 + 12 * max |a ^ 2 - 1| |b ^ 2 - 1| ^ 4 := by
  obtain ⟨E, hE⟩ : ∃ E, E = c - τ * ((a ^ 2 + b ^ 2) / 2) := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x, x = a ^ 2 - 1 := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = b ^ 2 - 1 := ⟨_, rfl⟩
  rw [← hE, ← hx, ← hy]
  obtain ⟨m, hm⟩ : ∃ m, m = max |x| |y| := ⟨_, rfl⟩
  rw [← hm]
  have hT2 : |T - τ| ≤ 2 := (abs_sub _ _).trans (by linarith)
  have hu : |x| ≤ m := hm ▸ le_max_left _ _
  have hw : |y| ≤ m := hm ▸ le_max_right _ _
  have hu' := abs_le.mp hu
  have hw' := abs_le.mp hw
  have hm0 : 0 ≤ m := (abs_nonneg _).trans hu
  have hE0 := abs_nonneg E
  have hτ0 := abs_nonneg τ
  rcases (mul_nonneg ha hb).eq_or_lt with h0 | hp
  · have n2 : 0 ≤ |τ| * ((x ^ 2 + y ^ 2) / 4) := by positivity
    have n3 : 0 ≤ |E| * |(x + y) / 2| := by positivity
    have n4 : 0 ≤ |E| * m ^ 2 := by positivity
    have n5 : 0 ≤ m ^ 3 := by positivity
    have hm1 : 1 ≤ m := by
      rcases mul_eq_zero.mp h0.symm with h | h
      · have e : x = -1 := by rw [hx, h]; norm_num
        rw [e] at hu'
        linarith [hu'.1]
      · have e : y = -1 := by rw [hy, h]; norm_num
        rw [e] at hw'
        linarith [hw'.1]
    have h4 : 1 ≤ m ^ 4 := one_le_pow₀ hm1
    linarith
  · obtain ⟨p, hpdef⟩ : ∃ p, p = a * b := ⟨_, rfl⟩
    rw [← hpdef] at hp hTeq
    have hp0 : p ≠ 0 := hp.ne'
    obtain ⟨q, hqdef⟩ : ∃ q, q = 1 - p := ⟨_, rfl⟩
    obtain ⟨D, hD⟩ : ∃ D, D = (a - b) ^ 2 / 2 := ⟨_, rfl⟩
    have hTp0 : (T - τ) * p = c - τ * p := by
      rw [hTeq hp]; field_simp
    have hTp : (T - τ) * (1 - q) = E + τ * D := by
      rw [hqdef, show 1 - (1 - p) = p by ring, hTp0, hE, hD, hpdef]; ring
    have hq : q = D - (x + y) / 2 := by rw [hqdef, hD, hx, hy, hpdef]; ring
    have hDid : D = (x - y) ^ 2 / 8 - D * ((x + y) / 2) + D ^ 2 / 2 := by
      rw [hD, hx, hy]; ring
    have key3 : T - τ = (E + τ * D) * (1 + q + q ^ 2) + (T - τ) * q ^ 3 := by
      linear_combination (1 + q + q ^ 2) * hTp
    have main : T - τ = E + τ * ((x - y) ^ 2 / 8) - E * ((x + y) / 2) + E * D -
        2 * τ * D * ((x + y) / 2) + 3 / 2 * τ * D ^ 2 + (E + τ * D) * q ^ 2 +
        (T - τ) * q ^ 3 := by
      linear_combination key3 + (E + τ * D) * hq + τ * hDid
    have hua : |a ^ 2 - 1| ≤ m := hx ▸ hu
    have hwb : |b ^ 2 - 1| ≤ m := hy ▸ hw
    have hqm : |q| ≤ m := by
      have := one_sub_mul_le ha hb hua hwb
      rwa [← hpdef, ← hqdef] at this
    have hum : |(x + y) / 2| ≤ m := by
      rw [abs_le]
      constructor <;> linarith
    have hD0 : 0 ≤ D := by rw [hD]; positivity
    have hDm : D ≤ m := hD ▸ half_sq_sub_le ha hb hua hwb
    have hDm2 : D ≤ m ^ 2 := hD ▸ half_sq_sub_le_sq ha hb hua hwb
    have hV0 : 0 ≤ (x - y) ^ 2 / 8 := by positivity
    have hVx : (x - y) ^ 2 / 8 ≤ (x ^ 2 + y ^ 2) / 4 := by linarith [sq_nonneg (x + y)]
    have hDu := ptC_Du hD0 hm0 hDm hDm2 hum hDid (ptC_Vu hu hw)
    have hcτ : |E + τ * D| ≤ |E| + D := by
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_of_nonneg hD0]
      have := mul_le_of_le_one_left hD0 hτ
      linarith
    have hTq : |T - τ| * |q| ^ 3 ≤ 1 / 2 * ((|E| + D) * q ^ 2) + 6 * q ^ 4 := by
      refine ptC_Tq (abs_nonneg _) hT2 (by linarith) ?_
      rcases le_or_gt 0 (1 - q) with h | h
      · have e1 : |T - τ| * (1 - q) = |E + τ * D| := by
          rw [← hTp, abs_mul, abs_of_nonneg h]
        linarith
      · have := mul_nonpos_of_nonneg_of_nonpos (abs_nonneg (T - τ)) h.le
        linarith
    exact ptC_fin hτ hD0 hDm2 hV0 hVx hqm hDu hTq main

/-! ## Generic facts on `L2le` -/

section Generic

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Cauchy–Schwarz for a product**: `‖f·g‖₂ ≤ √(‖f²‖₂·‖g²‖₂)`. -/
lemma l2_abs_mul_of_sq {f g : Ω → ℝ} {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hfm : AEStronglyMeasurable f μ) (hgm : AEStronglyMeasurable g μ)
    (hf : L2le μ (fun ω => f ω ^ 2) A) (hg : L2le μ (fun ω => g ω ^ 2) B) :
    L2le μ (fun ω => |f ω| * |g ω|) (√(A * B)) := by
  have e : ∀ ω, (|f ω| * |g ω|) ^ 2 = f ω ^ 2 * g ω ^ 2 := fun ω => by
    rw [mul_pow, sq_abs, sq_abs]
  refine L2le.mk' ((continuous_abs.comp_aestronglyMeasurable hfm).mul
    (continuous_abs.comp_aestronglyMeasurable hgm)) ?_ ?_
  · simp only [e]
    exact l2_mul_integrable hf hg
  · simp only [e]
    rw [Real.sq_sqrt (mul_nonneg hA hB)]
    exact (le_abs_self _).trans (l2_abs_integral_mul_le hA hB hf hg)

/-- A power of the maximum of two absolute values. -/
lemma l2_max_pow {f g : Ω → ℝ} {A : ℝ} (k : ℕ) (hfm : AEStronglyMeasurable f μ)
    (hgm : AEStronglyMeasurable g μ) (hf : L2le μ (fun ω => f ω ^ k) A)
    (hg : L2le μ (fun ω => g ω ^ k) A) :
    L2le μ (fun ω => max |f ω| |g ω| ^ k) (√2 * A) := by
  have e : ∀ t : ℝ, (|t| ^ k) ^ 2 = (t ^ k) ^ 2 := fun t => by
    rw [← pow_mul, ← pow_mul, mul_comm k 2, pow_mul, pow_mul, sq_abs]
  refine L2le.of_sq_le (((continuous_abs.comp_aestronglyMeasurable hfm).sup
    (continuous_abs.comp_aestronglyMeasurable hgm)).pow k) (hf.int_sq.add hg.int_sq)
    (fun ω => ?_) ?_
  · simp only [Pi.add_apply]
    rcases max_cases |f ω| |g ω| with hc | hc
    · rw [hc.1, e]
      linarith [sq_nonneg (g ω ^ k)]
    · rw [hc.1, e]
      linarith [sq_nonneg (f ω ^ k)]
  · simp only [Pi.add_apply]
    rw [integral_add hf.int_sq hg.int_sq, mul_pow, Real.sq_sqrt (by norm_num)]
    linarith [hf.le, hg.le]

/-- **The `L²` norm of a function with the pointwise bound of `cos_ptC`.** -/
lemma cos_L2_core {Ef X Y Df : Ω → ℝ} {τ c e K Q : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (he : 0 ≤ e) (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hXm : AEStronglyMeasurable X μ) (hYm : AEStronglyMeasurable Y μ)
    (hDm : AEStronglyMeasurable Df μ)
    (hE : L2le μ Ef e) (hE2 : L2le μ (fun ω => Ef ω ^ 2) (c ^ 2 * K))
    (hX2 : L2le μ (fun ω => X ω ^ 2) K) (hY2 : L2le μ (fun ω => Y ω ^ 2) K)
    (hX4 : L2le μ (fun ω => X ω ^ 4) Q) (hY4 : L2le μ (fun ω => Y ω ^ 4) Q)
    (hpt : ∀ ω, |Df ω| ≤ |Ef ω| + |τ| * ((X ω ^ 2 + Y ω ^ 2) / 4) +
      |Ef ω| * |(X ω + Y ω) / 2| + 5 / 2 * (|Ef ω| * max |X ω| |Y ω| ^ 2) +
      1 / 4 * max |X ω| |Y ω| ^ 3 + 12 * max |X ω| |Y ω| ^ 4) :
    L2le μ Df (e + |τ| * (K / 2) + c * K + 5 / 2 * √(K * (√2 * Q)) +
      1 / 4 * √(√2 * K * (√2 * Q)) + 12 * (√2 * Q)) := by
  have hs2 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have hτ0 := abs_nonneg τ
  have hmm : AEStronglyMeasurable (fun ω => max |X ω| |Y ω|) μ :=
    (continuous_abs.comp_aestronglyMeasurable hXm).sup
      (continuous_abs.comp_aestronglyMeasurable hYm)
  have hM2 := l2_max_pow 2 hXm hYm hX2 hY2
  have hM4 := l2_max_pow 4 hXm hYm hX4 hY4
  have hM4' : L2le μ (fun ω => (max |X ω| |Y ω| ^ 2) ^ 2) (√2 * Q) :=
    hM4.congr_fun fun ω => by ring
  have hXY := hX2.add' hY2 hK hK
  have hUm : AEStronglyMeasurable (fun ω => (X ω + Y ω) / 2) μ := by
    have := (hXm.add hYm).const_mul (1 / 2 : ℝ)
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  have hm2m : AEStronglyMeasurable (fun ω => max |X ω| |Y ω| ^ 2) μ := hmm.pow 2
  have t1 := hE.abs
  have t2 := hXY.const_mul_nonneg (c := |τ| / 4) (by positivity)
  have hU2 : L2le μ (fun ω => ((X ω + Y ω) / 2) ^ 2) K := by
    have h0 := hXY.const_mul_nonneg (c := 1 / 2) (by norm_num)
    refine (L2le.of_abs_le (hUm.pow 2) h0 (fun ω => ?_)).congr_bound
      (by ring)
    change |((X ω + Y ω) / 2) ^ 2| ≤ |1 / 2 * (X ω ^ 2 + Y ω ^ 2)|
    rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (by positivity)]
    linarith [sq_nonneg (X ω - Y ω)]
  have t3 := l2_abs_mul_of_sq (mul_nonneg (sq_nonneg c) hK) hK hE.aesm hUm hE2 hU2
  have hE2' : L2le μ (fun ω => Ef ω ^ 2) K := by
    refine hE2.mono (mul_nonneg (sq_nonneg c) hK) ?_
    have : c ^ 2 ≤ 1 := by nlinarith
    nlinarith
  have t4 := (l2_abs_mul_of_sq hK (mul_nonneg hs2 hQ) hE.aesm hm2m hE2' hM4').const_mul_nonneg
    (c := 5 / 2) (by norm_num)
  have t5 := (l2_abs_mul_of_sq (mul_nonneg hs2 hK) (mul_nonneg hs2 hQ) hmm hm2m hM2
    hM4').const_mul_nonneg (c := 1 / 4) (by norm_num)
  have t6 := hM4.const_mul_nonneg (c := 12) (by norm_num)
  have htot := ((((t1.add' t2 he (by positivity)).add' t3 (by positivity) (by positivity)).add' t4
    (by positivity) (by positivity)).add' t5 (by positivity) (by positivity)).add' t6
    (by positivity) (by positivity)
  have hsq : √(c ^ 2 * K * K) = c * K := by
    rw [show c ^ 2 * K * K = (c * K) ^ 2 by ring]
    exact Real.sqrt_sq (mul_nonneg hc0 hK)
  refine (L2le.of_abs_le hDm htot (fun ω => ?_)).congr_bound (by rw [hsq]; ring)
  have hm0 : 0 ≤ max |X ω| |Y ω| := le_max_of_le_left (abs_nonneg _)
  refine (hpt ω).trans ((le_of_eq ?_).trans (le_abs_self _))
  rw [abs_of_nonneg (pow_nonneg hm0 2), abs_of_nonneg hm0]
  ring

end Generic

/-! ## The constant -/

/-- **The second-order term of the cosine link**, with the eighth moment:
`(17/16)·K + (5/2)·√(K·√2·Q) + (1/4)·√(√2·K·√2·Q) + 12·√2·Q`, `K = √(12 + 48/n)/n` and
`Q = √(1680 + 76160/n + 467712/n² + 645120/n³)/n²`. -/
noncomputable def jCosC (n : ℕ) : ℝ :=
  17 / 16 * (K4 n / (n : ℝ)) + 5 / 2 * √(K4 n / (n : ℝ) * (√2 * qCos n)) +
    1 / 4 * √(√2 * (K4 n / (n : ℝ)) * (√2 * qCos n)) + 12 * (√2 * qCos n)

lemma jCosC_nonneg (n : ℕ) : 0 ≤ jCosC n := by
  have := K4_nonneg n
  have := qCos_nonneg n
  unfold jCosC
  positivity

/-! ## The unit case -/

variable {n k : ℕ}

theorem lin_cos_unit_L2c {v : ℝ} (hv : 0 < v) (hn : 1 ≤ n) {h h' : Fin k → ℝ}
    (hh : normSq h = 1) (hh' : normSq h' = 1) :
    L2le (gaussMat n k v)
      (fun M : Matrix (Fin n) (Fin k) ℝ =>
        dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - dotp h h')
      ((1 - dotp h h' ^ 2) / √(n : ℝ) + jCosC n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set τ := dotp h h' with hτdef
  set s := (n : ℝ) * v with hs
  have hs0 : 0 < s := mul_pos hn0 hv
  set K := √(12 + 48 / (n : ℝ)) / (n : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  have hQ0 := qCos_nonneg n
  have hτ : |τ| ≤ 1 := by
    have := abs_dotp_le_nrm h h'
    rwa [nrm_of_normSq_one hh, nrm_of_normSq_one hh', mul_one] at this
  have hτ' := abs_le.mp hτ
  have hτ2 : 0 ≤ 1 - τ ^ 2 := by nlinarith
  have hτ3 : 1 - τ ^ 2 ≤ 1 := by nlinarith [sq_nonneg τ]
  have ha1 : 0 ≤ (1 - τ ^ 2) / √(n : ℝ) := by positivity
  -- the first function
  have hE : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      dotp (M.mulVec h) (M.mulVec h') / s -
        τ * ((normSq (M.mulVec h) / s + normSq (M.mulVec h') / s) / 2))
      ((1 - τ ^ 2) / √(n : ℝ)) :=
    (ctp_L2 hv hn hh hh').congr_fun fun M => by
      rw [← hs, ← hτdef]
      field_simp
  -- the square of the first function
  have nP : normSq (h + h') = 2 + 2 * τ := by rw [normSq_add_eq, hh, hh']; ring
  have nM : normSq (h - h') = 2 - 2 * τ := by rw [normSq_sub_eq, hh, hh']; ring
  have hP : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (normSq (M.mulVec (h + h')) / s - (2 + 2 * τ)) ^ 2) ((2 + 2 * τ) ^ 2 * K) := by
    have := dev_sq_L2 hv hn (h + h')
    rw [nP, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; rw [hs]; field_simp
  have hMi : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (normSq (M.mulVec (h - h')) / s - (2 - 2 * τ)) ^ 2) ((2 - 2 * τ) ^ 2 * K) := by
    have := dev_sq_L2 hv hn (h - h')
    rw [nM, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; rw [hs]; field_simp
  have hg := (hP.const_mul_nonneg (c := (1 - τ) ^ 2 / 8) (by positivity)).add'
    (hMi.const_mul_nonneg (c := (1 + τ) ^ 2 / 8) (by positivity)) (by positivity) (by positivity)
  have hE2 : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (dotp (M.mulVec h) (M.mulVec h') / s -
        τ * ((normSq (M.mulVec h) / s + normSq (M.mulVec h') / s) / 2)) ^ 2)
      ((1 - τ ^ 2) ^ 2 * K) := by
    have hE2' := L2le.of_abs_le (hE.aesm.pow 2) hg (fun M => ?_)
    · refine hE2'.congr_bound ?_
      ring
    · obtain ⟨x, hx⟩ : ∃ x, x = normSq (M.mulVec (h + h')) / s - (2 + 2 * τ) := ⟨_, rfl⟩
      obtain ⟨y, hy⟩ : ∃ y, y = normSq (M.mulVec (h - h')) / s - (2 - 2 * τ) := ⟨_, rfl⟩
      have e : dotp (M.mulVec h) (M.mulVec h') / s -
          τ * ((normSq (M.mulVec h) / s + normSq (M.mulVec h') / s) / 2) =
          ((1 - τ) * x - (1 + τ) * y) / 4 := by
        rw [hx, hy, Matrix.mulVec_add, Matrix.mulVec_sub, normSq_add_eq, normSq_sub_eq]
        field_simp
        ring
      change |(dotp (M.mulVec h) (M.mulVec h') / s -
          τ * ((normSq (M.mulVec h) / s + normSq (M.mulVec h') / s) / 2)) ^ 2| ≤
        |(1 - τ) ^ 2 / 8 * (normSq (M.mulVec (h + h')) / s - (2 + 2 * τ)) ^ 2 +
          (1 + τ) ^ 2 / 8 * (normSq (M.mulVec (h - h')) / s - (2 - 2 * τ)) ^ 2|
      rw [abs_of_nonneg (sq_nonneg _), e, ← hx, ← hy]
      refine le_trans ?_ (le_abs_self _)
      have e2 : (1 - τ) ^ 2 / 8 * x ^ 2 + (1 + τ) ^ 2 / 8 * y ^ 2 -
          (((1 - τ) * x - (1 + τ) * y) / 4) ^ 2 = (((1 - τ) * x + (1 + τ) * y) / 4) ^ 2 := by
        ring
      have := sq_nonneg (((1 - τ) * x + (1 + τ) * y) / 4)
      linarith
  -- the deviations of the two norms
  have hA : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (normSq (M.mulVec h) / s - 1) ^ 2) K := by
    have := dev_sq_L2 hv hn h
    rw [hh, one_pow, one_mul, mul_one, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; field_simp
  have hB : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (normSq (M.mulVec h') / s - 1) ^ 2) K := by
    have := dev_sq_L2 hv hn h'
    rw [hh', one_pow, one_mul, mul_one, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; field_simp
  have hA4 : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (normSq (M.mulVec h) / s - 1) ^ 4) (qCos n) := by
    have := dev_four_L2 hv hn h
    rw [hh, one_pow, one_mul, mul_one, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; field_simp
  have hB4 : L2le (gaussMat n k v) (fun M : Matrix (Fin n) (Fin k) ℝ =>
      (normSq (M.mulVec h') / s - 1) ^ 4) (qCos n) := by
    have := dev_four_L2 hv hn h'
    rw [hh', one_pow, one_mul, mul_one, ← hs] at this
    refine this.congr_fun fun M => ?_
    congr 1; field_simp
  have hXm : AEStronglyMeasurable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      normSq (M.mulVec h) / s - 1) (gaussMat n k v) :=
    (((measurable_normSq_mulVec h).div_const _).sub_const _).aestronglyMeasurable
  have hYm : AEStronglyMeasurable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      normSq (M.mulVec h') / s - 1) (gaussMat n k v) :=
    (((measurable_normSq_mulVec h').div_const _).sub_const _).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable (fun M : Matrix (Fin n) (Fin k) ℝ =>
      dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - τ) (gaussMat n k v) :=
    ((measurable_dotp_sphPt h h').sub_const _).aestronglyMeasurable
  have hcore := cos_L2_core (τ := τ) hτ2 hτ3 ha1 hK0 hQ0 hXm hYm hmeas hE hE2 hA hB hA4 hB4
    (fun M => ?_)
  · refine hcore.mono (by positivity) ?_
    have ht : τ ^ 2 = |τ| ^ 2 := (sq_abs τ).symm
    have h17 : |τ| * (K / 2) + (1 - τ ^ 2) * K ≤ 17 / 16 * K := by
      rw [ht]
      nlinarith [mul_nonneg (sq_nonneg (|τ| - 1 / 4)) hK0]
    unfold jCosC K4
    rw [← hK]
    linarith
  -- the pointwise bound
  have hX0 : 0 ≤ normSq (M.mulVec h) := normSq_nonneg _
  have hY0 : 0 ≤ normSq (M.mulVec h') := normSq_nonneg _
  have hsqpos : 0 < √s := Real.sqrt_pos.mpr hs0
  have hab : √(normSq (M.mulVec h) / s) * √(normSq (M.mulVec h') / s) =
      nrm (M.mulVec h) * nrm (M.mulVec h') / s := by
    rw [Real.sqrt_div hX0, Real.sqrt_div hY0]
    unfold nrm
    field_simp
    rw [Real.sq_sqrt hs0.le]; ring
  have hT : |dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h'))| ≤ 1 :=
    abs_le.2 ⟨dotp_sphPt_ge hn _ _, dotp_sphPt_le hn _ _⟩
  have hTeq : 0 < √(normSq (M.mulVec h) / s) * √(normSq (M.mulVec h') / s) →
      dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) = dotp (M.mulVec h) (M.mulVec h') / s /
        (√(normSq (M.mulVec h) / s) * √(normSq (M.mulVec h') / s)) := by
    intro hpos
    have hx : normSq (M.mulVec h) ≠ 0 := by
      intro h0
      rw [h0, zero_div, Real.sqrt_zero, zero_mul] at hpos
      exact lt_irrefl _ hpos
    have hy : normSq (M.mulVec h') ≠ 0 := by
      intro h0
      rw [h0, zero_div, Real.sqrt_zero, mul_zero] at hpos
      exact lt_irrefl _ hpos
    rw [dotp_sphPt _ _ hx hy, hab]
    have := (nrm_pos_of_ne hx).ne'
    have := (nrm_pos_of_ne hy).ne'
    field_simp
  have hpt := cos_ptC (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hτ hT hTeq
  rw [Real.sq_sqrt (div_nonneg hX0 hs0.le), Real.sq_sqrt (div_nonneg hY0 hs0.le)] at hpt
  exact hpt

/-- **Link `W₃` in `L²`, with the eighth moment.** For nonzero `h, h'`, an `n × k` Gaussian
matrix `M` with entry variance `v > 0`:
`‖⟨sphPt (M h), sphPt (M h')⟩ − cos(h, h')‖₂ ≤ (1 − cos²)/√n + jCosC n`. -/
theorem lin_cos_L2c {n k : ℕ} {v : ℝ} (hv : 0 < v) (hn : 1 ≤ n) (h h' : Fin k → ℝ)
    (hh : normSq h ≠ 0) (hh' : normSq h' ≠ 0) :
    L2le (gaussMat n k v)
      (fun M : Matrix (Fin n) (Fin k) ℝ =>
        dotp (sphPt (M.mulVec h)) (sphPt (M.mulVec h')) - cosv h h')
      ((1 - cosv h h' ^ 2) / √(n : ℝ) + jCosC n) := by
  have hp := nrm_pos_of_ne hh
  have hp' := nrm_pos_of_ne hh'
  set g : Fin k → ℝ := (1 / nrm h) • h with hg
  set g' : Fin k → ℝ := (1 / nrm h') • h' with hg'
  have hg1 : normSq g = 1 := by
    rw [hg, normSq_smul, ← nrm_sq h]; field_simp
  have hg1' : normSq g' = 1 := by
    rw [hg', normSq_smul, ← nrm_sq h']; field_simp
  have hcos : dotp g g' = cosv h h' := by
    rw [hg, hg', dotp_smul_smul]; unfold cosv; field_simp
  have e : h = nrm h • g := by
    rw [hg, smul_smul]; field_simp; simp
  have e' : h' = nrm h' • g' := by
    rw [hg', smul_smul]; field_simp; simp
  have key := lin_cos_unit_L2c (n := n) hv hn hg1 hg1'
  rw [hcos] at key
  refine key.congr_fun fun M => ?_
  have e1 : M.mulVec h = nrm h • M.mulVec g := by
    conv_lhs => rw [e]
    rw [Matrix.mulVec_smul]
  have e2 : M.mulVec h' = nrm h' • M.mulVec g' := by
    conv_lhs => rw [e']
    rw [Matrix.mulVec_smul]
  rw [e1, e2, sphPt_smul hp, sphPt_smul hp']

/-! ## The number for `n ≥ 4096` -/

/-- **`jCosC n ≤ 4.475/n`** for `n ≥ 4096` (`jCos n ≥ 25.98/n`). -/
theorem jCosC_le {n : ℕ} (hn : 4096 ≤ n) : jCosC n ≤ 4475 / 1000 / (n : ℝ) := by
  have hx : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : (0 : ℝ) < n := by linarith
  have hs : (64 : ℝ) ≤ √(n : ℝ) := Real.le_sqrt_of_sq_le (by linarith)
  have hs0 : (0 : ℝ) < √(n : ℝ) := by linarith
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = 1 / (n : ℝ) := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = 1 / √(n : ℝ) := ⟨_, rfl⟩
  have hy0 : 0 < y := by rw [hy]; positivity
  have hz0 : 0 < z := by rw [hz]; positivity
  have hz1 : z ≤ 1 / 64 := by rw [hz]; exact one_div_le_one_div_of_le (by norm_num) hs
  have hy1 : y ≤ 1 / 4096 := by rw [hy]; exact one_div_le_one_div_of_le (by norm_num) hx
  have hyz : y = z * z := by
    rw [hy, hz, div_mul_div_comm, one_mul, Real.mul_self_sqrt hx0.le]
  have h2 := sqrt2_le
  have h20 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have hK0 := K4_nonneg n
  have hK : K4 n ≤ 17329 / 5000 := by
    unfold K4
    refine sqrt_le_of_sq (by norm_num) ?_
    have : 48 / (n : ℝ) ≤ 48 / 4096 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
    norm_num at this ⊢
    linarith
  have hQ0 := qCos_nonneg n
  have hQ : qCos n ≤ 25759 / 625 * y ^ 2 := by
    have e : qCos n = √(1680 + 76160 * y + 467712 * y ^ 2 + 645120 * y ^ 3) * y ^ 2 := by
      have e1 : 1680 + 76160 / (n : ℝ) + 467712 / (n : ℝ) ^ 2 + 645120 / (n : ℝ) ^ 3 =
          1680 + 76160 * y + 467712 * y ^ 2 + 645120 * y ^ 3 := by rw [hy]; ring
      unfold qCos
      rw [e1, hy]
      ring
    rw [e]
    refine mul_le_mul_of_nonneg_right (sqrt_le_of_sq (by norm_num) ?_) (by positivity)
    have a1 : y ^ 2 ≤ (1 / 4096) ^ 2 := pow_le_pow_left₀ hy0.le hy1 2
    have a2 : y ^ 3 ≤ (1 / 4096) ^ 3 := pow_le_pow_left₀ hy0.le hy1 3
    norm_num at a1 a2 ⊢
    linarith
  have eK : K4 n / (n : ℝ) = K4 n * y := by rw [hy]; ring
  unfold jCosC
  rw [eK]
  have hKy : K4 n * y ≤ 17329 / 5000 * y := mul_le_mul_of_nonneg_right hK hy0.le
  have hKy0 : 0 ≤ K4 n * y := by positivity
  have hsQ : √2 * qCos n ≤ 141422 / 100000 * (25759 / 625 * y ^ 2) :=
    mul_le_mul h2 hQ hQ0 (by norm_num)
  have hsQ0 : 0 ≤ √2 * qCos n := by positivity
  have hsK : √2 * (K4 n * y) ≤ 141422 / 100000 * (17329 / 5000 * y) :=
    mul_le_mul h2 hKy hKy0 (by norm_num)
  have hsK0 : 0 ≤ √2 * (K4 n * y) := by positivity
  have hy3 : y ^ 3 = (y * z) ^ 2 := by rw [hyz]; ring
  have t3 : √(K4 n * y * (√2 * qCos n)) ≤ 14213 / 1000 * (y * z) := by
    refine sqrt_le_of_sq (by positivity) ?_
    have := mul_le_mul hKy hsQ hsQ0 (by positivity)
    refine this.trans ?_
    have e : 17329 / 5000 * y * (141422 / 100000 * (25759 / 625 * y ^ 2)) =
        17329 / 5000 * (141422 / 100000) * (25759 / 625) * y ^ 3 := by ring
    rw [e, mul_pow, ← hy3]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have t4 : √(√2 * (K4 n * y) * (√2 * qCos n)) ≤ 16903 / 1000 * (y * z) := by
    refine sqrt_le_of_sq (by positivity) ?_
    have := mul_le_mul hsK hsQ hsQ0 (by positivity)
    refine this.trans ?_
    have e : 141422 / 100000 * (17329 / 5000 * y) * (141422 / 100000 * (25759 / 625 * y ^ 2)) =
        141422 / 100000 * (17329 / 5000) * (141422 / 100000) * (25759 / 625) * y ^ 3 := by ring
    rw [e, mul_pow, ← hy3]
    exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hyz' : y * z ≤ y * (1 / 64) := mul_le_mul_of_nonneg_left hz1 hy0.le
  have hy2 : y ^ 2 ≤ y * (1 / 4096) := by
    rw [sq]; exact mul_le_mul_of_nonneg_left hy1 hy0.le
  refine le_trans (?_ : _ ≤ 4475 / 1000 * y) (le_of_eq (by rw [hy]; ring))
  linarith

end BstLean.Part145

open BstLean.Part145 in
#print axioms cos_ptC
open BstLean.Part145 in
#print axioms lin_cos_L2c
open BstLean.Part145 in
#print axioms jCosC_le
