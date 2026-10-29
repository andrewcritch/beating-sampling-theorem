import BstLean.Part182EvW
import BstLean.Part182Geo
import BstLean.Part182Cov

/-!
# Part 182 (file `GeoT`): the window geometry `GeoT n` for every `n ≥ 22 000`

No proof is left open; no `native_decide` or `axiom` is used.

**`geoT_holds`**: for `n ≥ 22 000`, `τ > 0`, `0.46 ≤ θ ≤ 0.528` and every `(ξ, ξ') ∈ Γ(5, 14, 8)`:
`0.386 ≤ x·x' ≤ 0.638` (`x = sphPt (c + τξ)`). From `gamma_dot` (file `Geo`) and the arithmetic core
`gt_core` in the variables `u = 1/√n`, `R₁ = √(θ(1−θ)/n) ≤ u/2`, `R₂ = √(14/n) ≤ 3.7417u`,
`g₊ ≤ √n + 3.79`. Margins: upper `≈ 0.0016` (at `θ = 0.46`), lower `≈ 1.3·10⁻⁴` (at `θ = 0.528`,
`n = 22 000`).
-/

namespace BstLean.Part182

open MeasureTheory Real
open BstLean.Part130 BstLean.Part150

variable {n : ℕ}

/-- The arithmetic core: upper and lower window bounds in the variables
`θ`, `u = 1/√n`, `R1 = √(θ(1−θ)/n)`, `R2 = √(14/n)`, `B = √(θ/((1−θ)n))`, `g = g₊`. -/
lemma gt_core {θ u R1 R2 B g N : ℝ} (hθ0 : 46 / 100 ≤ θ) (hθ1 : θ ≤ 528 / 1000)
    (hu0 : 0 < u) (hu : u ≤ 6742 / 10 ^ 6) (hN : N = u ^ 2)
    (hR1 : R1 ≤ u / 2) (_hR10 : 0 ≤ R1) (hR2 : R2 ≤ 37417 / 10000 * u) (_hR20 : 0 ≤ R2)
    (hB1 : (1 - θ) * B = R1) (hB2 : (1 - θ) * B ^ 2 = θ * N)
    (hg : θ * N * 8 * g ≤ 8 * θ * (u + 379 / 100 * u ^ 2)) :
    ((1 - θ) * (1 + 5 * B) ^ 2 + θ * N * 8 * g) ≤
        638 / 1000 * (1 - (2 * 5 * R1 + 2 * θ * R2)) ∧
      386 / 1000 * (1 + (2 * 5 * R1 + 2 * θ * R2 + 2 * θ * 14 * N)) ≤
        (1 - θ) * (1 - 5 * B) ^ 2 - θ * N * 8 * g := by
  have e1 : (1 - θ) * (1 + 5 * B) ^ 2 = (1 - θ) + 10 * ((1 - θ) * B) + 25 * ((1 - θ) * B ^ 2) := by
    ring
  have e2 : (1 - θ) * (1 - 5 * B) ^ 2 = (1 - θ) - 10 * ((1 - θ) * B) + 25 * ((1 - θ) * B ^ 2) := by
    ring
  rw [hB1, hB2] at e1 e2
  rw [e1, e2]
  have hθ0' : 0 ≤ θ := by linarith
  have hθu : θ * u ≤ θ * (6742 / 10 ^ 6) := mul_le_mul_of_nonneg_left hu hθ0'
  have hu2 : u ^ 2 ≤ (6742 / 10 ^ 6) ^ 2 := pow_le_pow_left₀ hu0.le hu 2
  have hθu2 : θ * u ^ 2 ≤ θ * (6742 / 10 ^ 6) ^ 2 := mul_le_mul_of_nonneg_left hu2 hθ0'
  have hθR2 : θ * R2 ≤ θ * (37417 / 10000 * u) := mul_le_mul_of_nonneg_left hR2 hθ0'
  have hθu20 : 0 ≤ θ * u ^ 2 := mul_nonneg hθ0' (sq_nonneg u)
  subst hN
  constructor
  · nlinarith
  · nlinarith

lemma gt_u_le (hn : 22000 ≤ n) : (√(n : ℝ))⁻¹ ≤ 6742 / 10 ^ 6 := by
  have hnR : (22000 : ℝ) ≤ n := by exact_mod_cast hn
  have hs : (10 ^ 6 / 6742 : ℝ) ≤ √(n : ℝ) := by
    apply Real.le_sqrt_of_sq_le; nlinarith
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  refine le_trans ?_ hs
  norm_num

/-- **The window geometry**: for `n ≥ 22 000`, every pair of `Γ(5, 14, 8)` in the window
`0.46 ≤ θ ≤ 0.528` has `0.386 ≤ x·x' ≤ 0.638`. -/
theorem geoT_holds (hn : 22000 ≤ n) : GeoT n := by
  intro c τ hτ hw p hp
  obtain ⟨hθ0, hθ1⟩ := hw
  have hn0 : 0 < n := by omega
  have hnR : (22000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnp : (0 : ℝ) < n := by linarith
  set θ := thetaC c τ with hθd
  have hθlt : θ < 1 := by linarith
  have hc : c ≠ 0 := ne_zero_of_thetaC_lt hn0 hτ hθlt
  have h1θ : 0 < 1 - θ := by linarith
  -- the variables
  set u := (√(n : ℝ))⁻¹ with hud
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hnp
  have hu0 : 0 < u := inv_pos.mpr hs0
  have hu := gt_u_le hn
  have hu2 : u ^ 2 = 1 / (n : ℝ) := by
    rw [hud, inv_pow, Real.sq_sqrt hnp.le, one_div]
  have hsu : √(n : ℝ) = 1 / u := by rw [hud, one_div, inv_inv]
  set R1 := √(θ * (1 - θ) / n) with hR1d
  set R2 := √((14 : ℝ) / n) with hR2d
  set B := √(θ / ((1 - θ) * n)) with hBd
  set g := gPlus n 14 with hgd
  have hR10 : 0 ≤ R1 := Real.sqrt_nonneg _
  have hR20 : 0 ≤ R2 := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hR1 : R1 ≤ u / 2 := by
    refine sqrt_le_of_sq' (by positivity) ?_
    have e : θ * (1 - θ) / n = θ * (1 - θ) * u ^ 2 := by rw [hu2]; ring
    rw [e]
    have hq : θ * (1 - θ) ≤ 1 / 4 := by nlinarith [sq_nonneg (θ - 1 / 2)]
    nlinarith [sq_nonneg u]
  have hR2 : R2 ≤ 37417 / 10000 * u := by
    refine sqrt_le_of_sq' (by positivity) ?_
    have e : (14 : ℝ) / n = 14 * u ^ 2 := by rw [hu2]; ring
    rw [e]
    nlinarith [sq_nonneg u]
  have hBsq : B ^ 2 = θ / ((1 - θ) * n) := Real.sq_sqrt (by positivity)
  have hR1sq : R1 ^ 2 = θ * (1 - θ) / n := Real.sq_sqrt (by
    have : 0 ≤ θ * (1 - θ) := mul_nonneg (by linarith) h1θ.le
    positivity)
  have hB2 : (1 - θ) * B ^ 2 = θ * u ^ 2 := by
    rw [hBsq, hu2]; field_simp
  have hB1 : (1 - θ) * B = R1 := by
    have hsq : ((1 - θ) * B) ^ 2 = R1 ^ 2 := by
      rw [mul_pow, hBsq, hR1sq]; field_simp
    exact (pow_left_inj₀ (mul_nonneg h1θ.le hB0) hR10 two_ne_zero).1 hsq
  have h14 : √(14 : ℝ) ≤ 37417 / 10000 := sqrt_le_of_sq' (by norm_num) (by norm_num)
  have hgle : g ≤ √(n : ℝ) + 379 / 100 := by
    refine sqrt_le_of_sq' (by positivity) ?_
    have e : √((n : ℝ) * 14) = √(n : ℝ) * √14 := Real.sqrt_mul hnp.le 14
    rw [e]
    have hs148 : (148 : ℝ) ≤ √(n : ℝ) := by
      apply Real.le_sqrt_of_sq_le; nlinarith
    have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hnp.le
    nlinarith [mul_le_mul_of_nonneg_left h14 hs0.le]
  have hg : θ * u ^ 2 * 8 * g ≤ 8 * θ * (u + 379 / 100 * u ^ 2) := by
    have hθ0' : 0 ≤ θ := by linarith
    have h1 : θ * u ^ 2 * 8 * g ≤ θ * u ^ 2 * 8 * (1 / u + 379 / 100) := by
      rw [← hsu]
      exact mul_le_mul_of_nonneg_left hgle (by positivity)
    refine h1.trans (le_of_eq ?_)
    field_simp
  obtain ⟨hup, hlo⟩ := gt_core hθ0 hθ1 hu0 hu rfl hR1 hR10 hR2 hR20 hB1 hB2 hg
  -- gamma_dot
  have hb : 5 * B < 1 := by
    by_contra hcon
    have : (1 - θ) * 1 ≤ (1 - θ) * (5 * B) := mul_le_mul_of_nonneg_left (not_lt.mp hcon) h1θ.le
    nlinarith
  have hr := rminus_lt hn (by linarith : (0 : ℝ) ≤ θ) hθ1
  have hG := gamma_dot hn0 hc hτ (t0 := 5) (z0 := 14) (t1 := 8) (by norm_num) (by norm_num)
    (by norm_num) hθlt (ξ := p.1) (ξ' := p.2) hp hb hr
  have eθn : θ / (n : ℝ) = θ * u ^ 2 := by rw [hu2]; ring
  have e14 : 2 * θ * 14 / (n : ℝ) = 2 * θ * 14 * u ^ 2 := by rw [hu2]; ring
  rw [eθn, e14] at hG
  obtain ⟨hG1, hG2⟩ := hG
  have hden : 0 < 1 - (2 * 5 * R1 + 2 * θ * R2) := by linarith
  have hθ0' : 0 ≤ θ := by linarith
  have hrp : 0 < 1 + (2 * 5 * R1 + 2 * θ * R2 + 2 * θ * 14 * u ^ 2) := by positivity
  constructor
  · have hL0 : 0 ≤ (1 - θ) * (1 - 5 * B) ^ 2 - θ * u ^ 2 * 8 * g := by
      have : 0 ≤ 386 / 1000 * (1 + (2 * 5 * R1 + 2 * θ * R2 + 2 * θ * 14 * u ^ 2)) := by positivity
      linarith
    refine le_trans ?_ (hG2 hL0)
    rw [le_div_iff₀ hrp]
    exact hlo
  · refine hG1.trans ?_
    rw [div_le_iff₀ hden]
    exact hup

end BstLean.Part182

open BstLean.Part182 in
#print axioms geoT_holds
