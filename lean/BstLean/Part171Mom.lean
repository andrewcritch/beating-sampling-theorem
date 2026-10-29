import BstLean.Part171Zeta

/-!
# Part 171 (file `Mom`): the bias moments from the node statistics

No proof is left open; no `native_decide` or `axiom` is used.

Paper: `theorem7-08-bias.tex`, `t7:p08:biasmom`: "`|Σ_j b_j bias_j|/|b| ≤ (Σ_j bias_j²)^{1/2}` and
`((1/m)Σ_j bias_j²)⁴ ≤ (1/m)Σ_j bias_j⁸`. The factors are `n^{3/2}` for location and `m` for
energy."

* `TF_le`, `TW_le`: the row bounds are at most `A₀ + A₁ρ + A₂ρ²`, `ρ = |ζ_j|`, with the
  coefficients `AF0`, `AF1`, `AF2` (location) and `AW0`, `AW1`, `AW2` (energy).
* `pow8_three`: `(x + y + z)⁸ ≤ (α + β + γ)⁷(x⁸/α⁷ + y⁸/β⁷ + z⁸/γ⁷)` (Minkowski in `L⁸`).
* `zeta_poly`: `E(A₀ + A₁|ζ_j| + A₂|ζ_j|²)⁸ ≤ (A₀ + A₁z₁ + A₂z₂)⁸` if `z₁⁸ ≥ 384`,
  `z₂⁸ ≥ 10 321 920`.
* **`node_biasF`**, **`node_biasW`**: `biasF⁸ ≤ n⁴m³Σ_j P_F(ρ_j)⁸`, `biasW⁸ ≤ m⁷Σ_j P_W(ρ_j)⁸`.
-/

namespace BstLean.Part171

open MeasureTheory ProbabilityTheory Real Set Filter Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part169
open BstLean.Part153 (phiG phiG_pos)
open BstLean.Part170 (biasF biasW hB tA aLat bOfY measurable_aLat aLat_normSq_le vmean_aLat G2)
open BstLean.Part137 (psiS)

variable {n : ℕ}

/-! ## The row bounds as polynomials in `ρ = |ζ_j|` -/

/-- `A₀` of the location row bound. -/
noncomputable def AF0 (sm Γm Hm Vm Pm : ℝ) : ℝ :=
  phiG 0 / (2 * sm) * Hm + 1 / 2 * (phiG 0 / (√2 * sm ^ 3) * Vm) + Pm * (3 / 2 * phiG 0 / sm * Γm)

/-- `A₁` of the location row bound. -/
noncomputable def AF1 (sm Dm Vm Pm C : ℝ) : ℝ :=
  1 / 2 * (2 * phiG 1 / sm ^ 2 * (√Dm * √Vm)) + Pm * (2 * (2 * √2 * C))

/-- `A₂` of the location row bound. -/
noncomputable def AF2 (sm Dm : ℝ) : ℝ := 1 / 2 * (√2 * phiG 0 / sm * Dm)

/-- `A₀` of the energy row bound. -/
noncomputable def AW0 (sm Γm Hm Vm Pm : ℝ) : ℝ := Hm + phiG 1 / (2 * sm ^ 2) * Vm + Pm * (4 * Γm)

/-- `A₁` of the energy row bound. -/
noncomputable def AW1 (sm sp Dm Vm Pm C : ℝ) : ℝ :=
  √2 * phiG 0 / sm * (√Dm * √Vm) + Pm * (4 * √2 * C * sp)

/-- `A₂` of the energy row bound. -/
noncomputable def AW2 (Dm Pm C : ℝ) : ℝ := Dm + Pm * (28 * C ^ 2)

lemma sqrt_le_mul_sqrt {D ρ Dm : ℝ} (hρ : 0 ≤ ρ) (hD : D ≤ ρ ^ 2 * Dm) : √D ≤ ρ * √Dm := by
  calc √D ≤ √(ρ ^ 2 * Dm) := Real.sqrt_le_sqrt hD
    _ = ρ * √Dm := by
      rw [Real.sqrt_mul (sq_nonneg ρ), Real.sqrt_sq hρ]

theorem TF_le {s sm Δ Γ D h V pg Γm Dm Hm Vm Pm C ρ : ℝ} (hsm : 0 < sm) (hs : sm ≤ s)
    (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (hΔ0 : 0 ≤ Δ) (hΔ : Δ ≤ 2 * √2 * C * ρ) (hΓ0 : 0 ≤ Γ)
    (hΓ : Γ ≤ Γm) (hD0 : 0 ≤ D) (hD : D ≤ ρ ^ 2 * Dm) (h0 : 0 ≤ h) (hh : h ≤ Hm)
    (hV0 : 0 ≤ V) (hV : V ≤ Vm) (hp0 : 0 ≤ pg) (hp : pg ≤ Pm) :
    TF s Δ Γ D h V pg ≤ AF0 sm Γm Hm Vm Pm + AF1 sm Dm Vm Pm C * ρ + AF2 sm Dm * ρ ^ 2 := by
  have hs0 : 0 < s := hsm.trans_le hs
  have hφ0 := phiG_pos 0
  have hφ1 := phiG_pos 1
  have hr : (0 : ℝ) < √2 := by positivity
  have t1 : phiG 0 / (2 * s) * h ≤ phiG 0 / (2 * sm) * Hm := by gcongr
  have t2 : √2 * phiG 0 / s * D ≤ √2 * phiG 0 / sm * (ρ ^ 2 * Dm) := by gcongr
  have hsD := sqrt_le_mul_sqrt hρ hD
  have t3 : 2 * phiG 1 / s ^ 2 * (√D * √V) ≤ 2 * phiG 1 / sm ^ 2 * ((ρ * √Dm) * √Vm) := by
    gcongr
  have t4 : phiG 0 / (√2 * s ^ 3) * V ≤ phiG 0 / (√2 * sm ^ 3) * Vm := by gcongr
  have t5 : pg * (2 * Δ + 3 / 2 * phiG 0 / s * Γ) ≤
      Pm * (2 * (2 * √2 * C * ρ) + 3 / 2 * phiG 0 / sm * Γm) := by
    have hΓm : 0 ≤ Γm := hΓ0.trans hΓ
    have hPm : 0 ≤ Pm := hp0.trans hp
    gcongr
  unfold TF AF0 AF1 AF2
  have e : 1 / 2 * (2 * phiG 1 / sm ^ 2 * (√Dm * √Vm)) * ρ =
      1 / 2 * (2 * phiG 1 / sm ^ 2 * ((ρ * √Dm) * √Vm)) := by ring
  nlinarith [t1, t2, t3, t4, t5, e]

theorem TW_le {a s sm sp Δ Γ D h V pg Γm Dm Hm Vm Pm C ρ : ℝ} (hsm : 0 < sm) (hs : sm ≤ s)
    (hsp : s ≤ sp) (hρ : 0 ≤ ρ) (hC : 0 ≤ C) (ha : |a| ≤ √2 * C * ρ) (hΔ0 : 0 ≤ Δ)
    (hΔ : Δ ≤ 2 * √2 * C * ρ) (hΓ0 : 0 ≤ Γ)
    (hΓ : Γ ≤ Γm) (hD0 : 0 ≤ D) (hD : D ≤ ρ ^ 2 * Dm) (h0 : 0 ≤ h) (hh : h ≤ Hm)
    (hV0 : 0 ≤ V) (hV : V ≤ Vm) (hp0 : 0 ≤ pg) (hp : pg ≤ Pm) :
    TW a s Δ Γ D h V pg ≤ AW0 sm Γm Hm Vm Pm + AW1 sm sp Dm Vm Pm C * ρ + AW2 Dm Pm C * ρ ^ 2 := by
  have hs0 : 0 < s := hsm.trans_le hs
  have hφ0 := phiG_pos 0
  have hφ1 := phiG_pos 1
  have hr2 : √2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr : (0 : ℝ) < √2 := by positivity
  have hsD := sqrt_le_mul_sqrt hρ hD
  have hPm : 0 ≤ Pm := hp0.trans hp
  have hsp0 : 0 ≤ sp := hs0.le.trans hsp
  have t2 : √2 * phiG 0 / s * (√D * √V) ≤ √2 * phiG 0 / sm * ((ρ * √Dm) * √Vm) := by gcongr
  have t3 : phiG 1 / (2 * s ^ 2) * V ≤ phiG 1 / (2 * sm ^ 2) * Vm := by gcongr
  have hpol : (|a| + Δ) ^ 2 + a ^ 2 + 2 * (|a| + s) * Δ + 4 * Γ ≤
      28 * C ^ 2 * ρ ^ 2 + 4 * √2 * C * sp * ρ + 4 * Γm := by
    have hA0 := abs_nonneg a
    have q1 : (|a| + Δ) ^ 2 ≤ (3 * √2 * C * ρ) ^ 2 := by
      have : |a| + Δ ≤ 3 * √2 * C * ρ := by linarith
      exact pow_le_pow_left₀ (by positivity) this 2
    have q2 : a ^ 2 ≤ (√2 * C * ρ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ hA0 ha 2
    have q3 : 2 * (|a| + s) * Δ ≤ 2 * (√2 * C * ρ + sp) * (2 * √2 * C * ρ) := by
      have : |a| + s ≤ √2 * C * ρ + sp := by linarith
      gcongr
    have e1 : (3 * √2 * C * ρ) ^ 2 = 18 * C ^ 2 * ρ ^ 2 := by
      rw [show (3 * √2 * C * ρ) ^ 2 = 9 * √2 ^ 2 * C ^ 2 * ρ ^ 2 by ring, hr2]; ring
    have e2 : (√2 * C * ρ) ^ 2 = 2 * C ^ 2 * ρ ^ 2 := by
      rw [show (√2 * C * ρ) ^ 2 = √2 ^ 2 * C ^ 2 * ρ ^ 2 by ring, hr2]
    have e3 : 2 * (√2 * C * ρ + sp) * (2 * √2 * C * ρ) = 8 * C ^ 2 * ρ ^ 2 + 4 * √2 * C * sp * ρ := by
      rw [show 2 * (√2 * C * ρ + sp) * (2 * √2 * C * ρ) =
        4 * √2 ^ 2 * C ^ 2 * ρ ^ 2 + 4 * √2 * C * sp * ρ by ring, hr2]; ring
    linarith
  have t4 : pg * ((|a| + Δ) ^ 2 + a ^ 2 + 2 * (|a| + s) * Δ + 4 * Γ) ≤
      Pm * (28 * C ^ 2 * ρ ^ 2 + 4 * √2 * C * sp * ρ + 4 * Γm) := by
    have : 0 ≤ (|a| + Δ) ^ 2 + a ^ 2 + 2 * (|a| + s) * Δ + 4 * Γ := by positivity
    calc _ ≤ Pm * ((|a| + Δ) ^ 2 + a ^ 2 + 2 * (|a| + s) * Δ + 4 * Γ) := by gcongr
      _ ≤ _ := by gcongr
  unfold TW AW0 AW1 AW2
  have hD2 : D ≤ ρ ^ 2 * Dm := hD
  nlinarith [t2, t3, t4, hD2]

/-! ## Minkowski in `L⁸` for three terms -/

lemma pow8_three {x y z α β γ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) (hα : 0 < α)
    (hβ : 0 < β) (hγ : 0 < γ) :
    (x + y + z) ^ 8 ≤ (α + β + γ) ^ 7 * (x ^ 8 / α ^ 7 + y ^ 8 / β ^ 7 + z ^ 8 / γ ^ 7) := by
  have h1 := BstLean.Part170.pow8_split x (y + z) hα (add_pos hβ hγ)
  have h2 := BstLean.Part170.pow8_split y z hβ hγ
  rw [abs_of_nonneg hx, abs_of_nonneg (add_nonneg hy hz)] at h1
  rw [abs_of_nonneg hy, abs_of_nonneg hz] at h2
  have hβγ : 0 < β + γ := add_pos hβ hγ
  have hc : 0 ≤ (α + (β + γ)) ^ 7 / (β + γ) ^ 7 := by positivity
  have h3 := mul_le_mul_of_nonneg_left h2 hc
  have e : (α + (β + γ)) ^ 7 / (β + γ) ^ 7 * ((β + γ) ^ 7 / β ^ 7 * y ^ 8 + (β + γ) ^ 7 / γ ^ 7 * z ^ 8) =
      (α + (β + γ)) ^ 7 * (y ^ 8 / β ^ 7 + z ^ 8 / γ ^ 7) := by
    field_simp
  rw [e] at h3
  have e2 : (α + β + γ) ^ 7 * (x ^ 8 / α ^ 7 + y ^ 8 / β ^ 7 + z ^ 8 / γ ^ 7) =
      (α + (β + γ)) ^ 7 / α ^ 7 * x ^ 8 + (α + (β + γ)) ^ 7 * (y ^ 8 / β ^ 7 + z ^ 8 / γ ^ 7) := by
    rw [show α + β + γ = α + (β + γ) by ring]; field_simp; ring
  rw [show x + y + z = x + (y + z) by ring, e2]
  linarith

/-- The pointwise step: `(A₀ + A₁ρ + A₂ρ²)⁸ ≤ W(A₀ + A₁q⁴/z₁⁷ + A₂q⁸/z₂⁷)`, `q = ρ²`,
`W = (A₀ + A₁z₁ + A₂z₂)⁷`. -/
lemma poly8_pt {A₀ A₁ A₂ z₁ z₂ ρ : ℝ} (h0 : 0 < A₀) (h1 : 0 < A₁) (h2 : 0 < A₂) (hz1 : 0 < z₁)
    (hz2 : 0 < z₂) (hρ : 0 ≤ ρ) :
    (A₀ + A₁ * ρ + A₂ * ρ ^ 2) ^ 8 ≤
      (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₀ + (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₁ / z₁ ^ 7 * (ρ ^ 2) ^ 4 +
        (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₂ / z₂ ^ 7 * (ρ ^ 2) ^ 8 := by
  have key := pow8_three h0.le (mul_nonneg h1.le hρ) (mul_nonneg h2.le (sq_nonneg ρ))
    h0 (mul_pos h1 hz1) (mul_pos h2 hz2)
  have e : (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * (A₀ ^ 8 / A₀ ^ 7 + (A₁ * ρ) ^ 8 / (A₁ * z₁) ^ 7 +
      (A₂ * ρ ^ 2) ^ 8 / (A₂ * z₂) ^ 7) =
      (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₀ + (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₁ / z₁ ^ 7 * (ρ ^ 2) ^ 4 +
        (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₂ / z₂ ^ 7 * (ρ ^ 2) ^ 8 := by
    field_simp
  rw [← e]; exact key

lemma poly8_const {A₀ A₁ A₂ z₁ z₂ : ℝ} (h0 : 0 < A₀) (h1 : 0 < A₁) (h2 : 0 < A₂) (hz1 : 0 < z₁)
    (hz2 : 0 < z₂) (hz1' : 384 ≤ z₁ ^ 8) (hz2' : 10321920 ≤ z₂ ^ 8) :
    (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₀ + (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₁ / z₁ ^ 7 * 384 +
        (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₂ / z₂ ^ 7 * 10321920 ≤ (A₀ + A₁ * z₁ + A₂ * z₂) ^ 8 := by
  have hW : 0 ≤ (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 := by positivity
  have b1 : A₁ / z₁ ^ 7 * 384 ≤ A₁ * z₁ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have e : A₁ * z₁ * z₁ ^ 7 = A₁ * z₁ ^ 8 := by ring
    rw [e]; exact mul_le_mul_of_nonneg_left hz1' h1.le
  have b2 : A₂ / z₂ ^ 7 * 10321920 ≤ A₂ * z₂ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have e : A₂ * z₂ * z₂ ^ 7 = A₂ * z₂ ^ 8 := by ring
    rw [e]; exact mul_le_mul_of_nonneg_left hz2' h2.le
  have c1 := mul_le_mul_of_nonneg_left b1 hW
  have c2 := mul_le_mul_of_nonneg_left b2 hW
  have e : (A₀ + A₁ * z₁ + A₂ * z₂) ^ 8 = (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₀ +
      (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * (A₁ * z₁) + (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * (A₂ * z₂) := by ring
  rw [e]
  have e1 : (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₁ / z₁ ^ 7 * 384 =
      (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * (A₁ / z₁ ^ 7 * 384) := by ring
  have e2 : (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₂ / z₂ ^ 7 * 10321920 =
      (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * (A₂ / z₂ ^ 7 * 10321920) := by ring
  rw [e1, e2]; linarith

/-- `∫⁻∫⁻ (c₀ + c₁q⁴ + c₂q⁸) = c₀ + 384c₁ + 10 321 920c₂`, `q = ξ₁_j² + ξ₂_j²`. -/
lemma lint_three {m : ℕ} (j : Fin m) {c₀ c₁ c₂ : ℝ} (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal (c₀ + c₁ * (ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 4 +
        c₂ * (ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 8) ∂stdGauss (Fin m) ∂stdGauss (Fin m) =
      ENNReal.ofReal (c₀ + c₁ * 384 + c₂ * 10321920) := by
  have hpt : ∀ ξ₁ ξ₂ : Fin m → ℝ, ENNReal.ofReal (c₀ + c₁ * (ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 4 +
      c₂ * (ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 8) =
      ENNReal.ofReal c₀ + ENNReal.ofReal c₁ * ENNReal.ofReal ((ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 4) +
        ENNReal.ofReal c₂ * ENNReal.ofReal ((ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 8) := by
    intro ξ₁ ξ₂
    rw [← ENNReal.ofReal_mul hc₁, ← ENNReal.ofReal_mul hc₂, ← ENNReal.ofReal_add hc₀ (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
  simp_rw [hpt]
  have hm4 : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      ENNReal.ofReal ((p.1 j ^ 2 + p.2 j ^ 2) ^ 4)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hm8 : Measurable (fun p : (Fin m → ℝ) × (Fin m → ℝ) =>
      ENNReal.ofReal ((p.1 j ^ 2 + p.2 j ^ 2) ^ 8)) :=
    ENNReal.measurable_ofReal.comp (by fun_prop)
  have hin : ∀ ξ₁ : Fin m → ℝ, ∫⁻ ξ₂, (ENNReal.ofReal c₀ +
      ENNReal.ofReal c₁ * ENNReal.ofReal ((ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 4) +
        ENNReal.ofReal c₂ * ENNReal.ofReal ((ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 8)) ∂stdGauss (Fin m) =
      ENNReal.ofReal c₀ + ENNReal.ofReal c₁ * ∫⁻ ξ₂, ENNReal.ofReal ((ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 4)
          ∂stdGauss (Fin m) +
        ENNReal.ofReal c₂ * ∫⁻ ξ₂, ENNReal.ofReal ((ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 8) ∂stdGauss (Fin m) := by
    intro ξ₁
    have m4 : Measurable (fun ξ₂ : Fin m → ℝ => ENNReal.ofReal ((ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 4)) :=
      ENNReal.measurable_ofReal.comp (by fun_prop)
    have m8 : Measurable (fun ξ₂ : Fin m → ℝ => ENNReal.ofReal ((ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 8)) :=
      ENNReal.measurable_ofReal.comp (by fun_prop)
    rw [lintegral_add_right _ (m8.const_mul _), lintegral_add_left measurable_const,
      lintegral_const, measure_univ, mul_one, lintegral_const_mul _ m4, lintegral_const_mul _ m8]
  simp_rw [hin]
  have i4 : Measurable (fun ξ₁ : Fin m → ℝ =>
      ∫⁻ ξ₂, ENNReal.ofReal ((ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 4) ∂stdGauss (Fin m)) :=
    hm4.lintegral_prod_right'
  have i8 : Measurable (fun ξ₁ : Fin m → ℝ =>
      ∫⁻ ξ₂, ENNReal.ofReal ((ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 8) ∂stdGauss (Fin m)) :=
    hm8.lintegral_prod_right'
  rw [lintegral_add_right _ (i8.const_mul _), lintegral_add_left measurable_const,
    lintegral_const, measure_univ, mul_one, lintegral_const_mul _ i4,
    lintegral_const_mul _ i8, zeta_mom4, zeta_mom8, ← ENNReal.ofReal_mul hc₁,
    ← ENNReal.ofReal_mul hc₂, ← ENNReal.ofReal_add hc₀ (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]

/-- **`E(A₀ + A₁|ζ_j| + A₂|ζ_j|²)⁸ ≤ (A₀ + A₁z₁ + A₂z₂)⁸`.** -/
theorem zeta_poly {m : ℕ} (j : Fin m) {A₀ A₁ A₂ z₁ z₂ : ℝ} (h0 : 0 < A₀) (h1 : 0 < A₁)
    (h2 : 0 < A₂) (hz1 : 0 < z₁) (hz2 : 0 < z₂) (hz1' : 384 ≤ z₁ ^ 8)
    (hz2' : 10321920 ≤ z₂ ^ 8) :
    ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((A₀ + A₁ * √(ξ₁ j ^ 2 + ξ₂ j ^ 2) +
        A₂ * √(ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 2) ^ 8) ∂stdGauss (Fin m) ∂stdGauss (Fin m) ≤
      ENNReal.ofReal ((A₀ + A₁ * z₁ + A₂ * z₂) ^ 8) := by
  have hW : 0 ≤ (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 := by positivity
  have hc₀ : 0 ≤ (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₀ := by positivity
  have hc₁ : 0 ≤ (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₁ / z₁ ^ 7 := by positivity
  have hc₂ : 0 ≤ (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₂ / z₂ ^ 7 := by positivity
  calc _ ≤ ∫⁻ ξ₁, ∫⁻ ξ₂, ENNReal.ofReal ((A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₀ +
          (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₁ / z₁ ^ 7 * (ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 4 +
          (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₂ / z₂ ^ 7 * (ξ₁ j ^ 2 + ξ₂ j ^ 2) ^ 8)
          ∂stdGauss (Fin m) ∂stdGauss (Fin m) := by
        refine lintegral_mono fun ξ₁ => lintegral_mono fun ξ₂ => ENNReal.ofReal_le_ofReal ?_
        have h := poly8_pt h0 h1 h2 hz1 hz2 (Real.sqrt_nonneg (ξ₁ j ^ 2 + ξ₂ j ^ 2))
        rw [Real.sq_sqrt (by positivity)] at h ⊢; exact h
    _ = ENNReal.ofReal ((A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₀ +
          (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₁ / z₁ ^ 7 * 384 +
          (A₀ + A₁ * z₁ + A₂ * z₂) ^ 7 * A₂ / z₂ ^ 7 * 10321920) := lint_three j hc₀ hc₁ hc₂
    _ ≤ _ := ENNReal.ofReal_le_ofReal (poly8_const h0 h1 h2 hz1 hz2 hz1' hz2')

end BstLean.Part171
