import BstLean.Part185All

/-!
# Part 186 (file `GeoC`): the window of `x·x'` on a core pair set, for one θ-piece

No proof is left open; no `native_decide` or `axiom` is used.

* **`geo_core`**: for `n ≥ n₀` (`1/√n ≤ u_M`) and `θ_l ≤ θ ≤ θ_h`, every pair of `Γ(t₀, z₀, t₁)` has
  `c_l ≤ x·x' ≤ c_h`, under two scalar conditions (`hup`, `hlo`) that are linear in the data.
  (Part 182's `gamma_dot` with the bounds `R₁ ≤ u/2`, `√(z₀/n) ≤ a₂u`, `g₊ ≤ 1/u + a_g`.)
-/

namespace BstLean.Part186

open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150 BstLean.Part152 BstLean.Part157 BstLean.Part160
open BstLean.Part182

variable {n : ℕ}

/-- **The window of the core pairs.** -/
theorem geo_core (hn0 : 0 < n) {t0 z0 t1 θl θh cl ch uM a2 ag : ℝ} (ht0 : 0 ≤ t0) (hz0 : 0 ≤ z0)
    (ht1 : 0 ≤ t1) (hθl : 0 ≤ θl) (hθh1 : θh < 1) (hcl : 0 ≤ cl) (hch : 0 ≤ ch)
    (huM : (√(n : ℝ))⁻¹ ≤ uM) (ha2 : √z0 ≤ a2) (hag0 : 0 ≤ ag) (hag1 : √z0 ≤ ag)
    (hag2 : 2 * z0 ≤ ag ^ 2)
    (hrr : t0 * uM + 2 * θh * a2 * uM < 1)
    (hb : t0 ^ 2 * θh * uM ^ 2 < 1 - θh)
    (hup : (1 - θl) + uM * (t0 + t1 * θh + ch * (t0 + 2 * θh * a2)) +
      uM ^ 2 * (t0 ^ 2 * θh + t1 * ag * θh) ≤ ch)
    (hlo : cl * (1 + uM * (t0 + 2 * θh * a2) + uM ^ 2 * (2 * θh * z0)) ≤
      (1 - θh) - uM * (t0 + t1 * θh) - uM ^ 2 * (t1 * ag * θh))
    {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ) (hθ0 : θl ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ θh)
    {p : (Fin n → ℝ) × (Fin n → ℝ)} (hp : p ∈ GammaS c t0 z0 t1) :
    cl ≤ sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ∧
      sphPt (c + τ • p.1) ⬝ᵥ sphPt (c + τ • p.2) ≤ ch := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  set θ := thetaC c τ with hθd
  have hθlt : θ < 1 := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have hθ0' : 0 ≤ θ := by linarith
  have hc : c ≠ 0 := ne_zero_of_thetaC_lt hn0 hτ hθlt
  set u := (√(n : ℝ))⁻¹ with hud
  have hs0 : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hnR
  have hu0 : 0 < u := inv_pos.mpr hs0
  have hu2 : u ^ 2 = 1 / (n : ℝ) := by
    rw [hud, inv_pow, Real.sq_sqrt hnR.le, one_div]
  have hsu : √(n : ℝ) = 1 / u := by rw [hud, one_div, inv_inv]
  have huM0 : 0 ≤ uM := hu0.le.trans huM
  set R1 := √(θ * (1 - θ) / n) with hR1d
  set R2 := √(z0 / n) with hR2d
  set B := √(θ / ((1 - θ) * n)) with hBd
  set g := gPlus n z0 with hgd
  have hR10 : 0 ≤ R1 := Real.sqrt_nonneg _
  have hR20 : 0 ≤ R2 := Real.sqrt_nonneg _
  have hB0 : 0 ≤ B := Real.sqrt_nonneg _
  have hR1 : R1 ≤ u / 2 := by
    refine sqrt_le_of_sq' (by positivity) ?_
    have e : θ * (1 - θ) / n = θ * (1 - θ) * u ^ 2 := by rw [hu2]; ring
    rw [e]
    have hq : θ * (1 - θ) ≤ 1 / 4 := by nlinarith [sq_nonneg (θ - 1 / 2)]
    nlinarith [sq_nonneg u]
  have hR2 : R2 ≤ a2 * u := by
    have e : R2 = √z0 * u := by
      rw [hR2d, Real.sqrt_div' _ hnR.le, hud, div_eq_mul_inv]
    rw [e]
    exact mul_le_mul_of_nonneg_right ha2 hu0.le
  have hBsq : B ^ 2 = θ / ((1 - θ) * n) := Real.sq_sqrt (by positivity)
  have hR1sq : R1 ^ 2 = θ * (1 - θ) / n := Real.sq_sqrt (by
    have : 0 ≤ θ * (1 - θ) := mul_nonneg hθ0' h1θ.le
    positivity)
  have hB2 : (1 - θ) * B ^ 2 = θ * u ^ 2 := by
    rw [hBsq, hu2]; field_simp
  have hB1 : (1 - θ) * B = R1 := by
    have hsq : ((1 - θ) * B) ^ 2 = R1 ^ 2 := by
      rw [mul_pow, hBsq, hR1sq]; field_simp
    exact (pow_left_inj₀ (mul_nonneg h1θ.le hB0) hR10 two_ne_zero).1 hsq
  have hgle : g ≤ 1 / u + ag := by
    rw [← hsu]
    refine sqrt_le_of_sq' (by positivity) ?_
    have e : √((n : ℝ) * z0) = √(n : ℝ) * √z0 := Real.sqrt_mul hnR.le z0
    rw [e]
    have hsq : √(n : ℝ) ^ 2 = n := Real.sq_sqrt hnR.le
    have h1 : √(n : ℝ) * √z0 ≤ √(n : ℝ) * ag := mul_le_mul_of_nonneg_left hag1 hs0.le
    have e2 : (√(n : ℝ) + ag) ^ 2 = √(n : ℝ) ^ 2 + 2 * (√(n : ℝ) * ag) + ag ^ 2 := by ring
    rw [e2, hsq]
    linarith
  have hg : θ * u ^ 2 * t1 * g ≤ t1 * θ * (u + ag * u ^ 2) := by
    have h1 : θ * u ^ 2 * t1 * g ≤ θ * u ^ 2 * t1 * (1 / u + ag) :=
      mul_le_mul_of_nonneg_left hgle (by positivity)
    refine h1.trans (le_of_eq ?_)
    field_simp
  -- u ≤ uM
  have huu : u ≤ uM := huM
  have hu2M : u ^ 2 ≤ uM ^ 2 := pow_le_pow_left₀ hu0.le huu 2
  -- the radius condition
  have hrc : 2 * t0 * R1 + 2 * θ * R2 ≤ t0 * uM + 2 * θh * a2 * uM := by
    have a1 : 2 * t0 * R1 ≤ t0 * uM := by
      have h2 : 2 * R1 ≤ uM := by linarith
      calc 2 * t0 * R1 = t0 * (2 * R1) := by ring
        _ ≤ t0 * uM := mul_le_mul_of_nonneg_left h2 ht0
    have a2' : 2 * θ * R2 ≤ 2 * θh * (a2 * uM) := by
      have : R2 ≤ a2 * uM := hR2.trans (mul_le_mul_of_nonneg_left huu (ha2.trans' (Real.sqrt_nonneg _)))
      have h3 : θ * R2 ≤ θh * (a2 * uM) := mul_le_mul hθ1 this hR20 (by linarith)
      linarith only [h3]
    have e : 2 * θh * (a2 * uM) = 2 * θh * a2 * uM := by ring
    linarith only [a1, a2', e]
  have hr : 2 * t0 * R1 + 2 * θ * R2 < 1 := lt_of_le_of_lt hrc hrr
  have hbB : t0 * B < 1 := by
    have k1 : θ * u ^ 2 ≤ θh * uM ^ 2 := mul_le_mul hθ1 hu2M (sq_nonneg _) (by linarith)
    have k2 : (1 - θh) * B ^ 2 ≤ (1 - θ) * B ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    have k3 : (1 - θh) * (t0 * B) ^ 2 ≤ t0 ^ 2 * θh * uM ^ 2 := by
      have e : (1 - θh) * (t0 * B) ^ 2 = t0 ^ 2 * ((1 - θh) * B ^ 2) := by ring
      rw [e]
      calc t0 ^ 2 * ((1 - θh) * B ^ 2) ≤ t0 ^ 2 * ((1 - θ) * B ^ 2) :=
            mul_le_mul_of_nonneg_left k2 (sq_nonneg _)
        _ = t0 ^ 2 * (θ * u ^ 2) := by rw [hB2]
        _ ≤ t0 ^ 2 * (θh * uM ^ 2) := mul_le_mul_of_nonneg_left k1 (sq_nonneg _)
        _ = t0 ^ 2 * θh * uM ^ 2 := by ring
    have k4 : (t0 * B) ^ 2 < 1 := by
      have h1 : 0 < 1 - θh := by linarith
      by_contra hcon
      have : (1 - θh) * 1 ≤ (1 - θh) * (t0 * B) ^ 2 :=
        mul_le_mul_of_nonneg_left (not_lt.mp hcon) h1.le
      linarith
    have hnn : 0 ≤ t0 * B := mul_nonneg ht0 hB0
    by_contra hcon
    have h1 : 1 ≤ t0 * B := not_lt.mp hcon
    have h2 : 1 * 1 ≤ (t0 * B) * (t0 * B) := mul_le_mul h1 h1 zero_le_one hnn
    have e : (t0 * B) ^ 2 = (t0 * B) * (t0 * B) := by ring
    linarith only [h2, e, k4]
  have hG := gamma_dot hn0 hc hτ (t0 := t0) (z0 := z0) (t1 := t1) ht0 hz0 ht1 hθlt hp hbB hr
  obtain ⟨hG1, hG2⟩ := hG
  have eθn : θ / (n : ℝ) = θ * u ^ 2 := by rw [hu2]; ring
  have ez : 2 * θ * z0 / (n : ℝ) = 2 * θ * z0 * u ^ 2 := by rw [hu2]; ring
  rw [eθn] at hG1 hG2
  rw [ez] at hG2
  have e1 : (1 - θ) * (1 + t0 * B) ^ 2 = (1 - θ) + 2 * t0 * ((1 - θ) * B) + t0 ^ 2 * ((1 - θ) * B ^ 2) := by
    ring
  have e2 : (1 - θ) * (1 - t0 * B) ^ 2 = (1 - θ) - 2 * t0 * ((1 - θ) * B) + t0 ^ 2 * ((1 - θ) * B ^ 2) := by
    ring
  rw [hB1, hB2] at e1 e2
  have hden : 0 < 1 - (2 * t0 * R1 + 2 * θ * R2) := by linarith
  -- upper
  have hU : (1 - θ) * (1 + t0 * B) ^ 2 + θ * u ^ 2 * t1 * g ≤ ch * (1 - (2 * t0 * R1 + 2 * θ * R2)) := by
    rw [e1]
    have k1 : t0 ^ 2 * (θ * u ^ 2) ≤ t0 ^ 2 * θh * uM ^ 2 := by
      have : θ * u ^ 2 ≤ θh * uM ^ 2 := mul_le_mul hθ1 hu2M (sq_nonneg _) (by linarith)
      calc t0 ^ 2 * (θ * u ^ 2) ≤ t0 ^ 2 * (θh * uM ^ 2) := mul_le_mul_of_nonneg_left this (sq_nonneg _)
        _ = t0 ^ 2 * θh * uM ^ 2 := by ring
    have k2 : t1 * θ * (u + ag * u ^ 2) ≤ t1 * θh * uM + t1 * ag * θh * uM ^ 2 := by
      have a : θ * u ≤ θh * uM := mul_le_mul hθ1 huu hu0.le (by linarith)
      have b : θ * u ^ 2 ≤ θh * uM ^ 2 := mul_le_mul hθ1 hu2M (sq_nonneg _) (by linarith)
      have : t1 * θ * (u + ag * u ^ 2) = t1 * (θ * u) + t1 * ag * (θ * u ^ 2) := by ring
      rw [this]
      have h1 := mul_le_mul_of_nonneg_left a ht1
      have h2 := mul_le_mul_of_nonneg_left b (mul_nonneg ht1 hag0)
      have e3 : t1 * (θh * uM) + t1 * ag * (θh * uM ^ 2) = t1 * θh * uM + t1 * ag * θh * uM ^ 2 := by ring
      linarith only [h1, h2, e3]
    have k3 : ch * (2 * t0 * R1 + 2 * θ * R2) ≤ ch * (t0 * uM + 2 * θh * a2 * uM) :=
      mul_le_mul_of_nonneg_left hrc hch
    have k4 : 2 * t0 * R1 ≤ t0 * uM := by
      have h2 : 2 * R1 ≤ uM := by linarith
      calc 2 * t0 * R1 = t0 * (2 * R1) := by ring
        _ ≤ t0 * uM := mul_le_mul_of_nonneg_left h2 ht0
    have hgk := hg.trans k2
    have hup' := hup
    ring_nf at hup' k3 ⊢
    ring_nf at hgk k1 k4
    linarith only [hup', k3, hgk, k1, k4, hθ0]
  -- lower
  have hL : cl * (1 + (2 * t0 * R1 + 2 * θ * R2 + 2 * θ * z0 * u ^ 2)) ≤
      (1 - θ) * (1 - t0 * B) ^ 2 - θ * u ^ 2 * t1 * g := by
    rw [e2]
    have k2 : t1 * θ * (u + ag * u ^ 2) ≤ t1 * θh * uM + t1 * ag * θh * uM ^ 2 := by
      have a : θ * u ≤ θh * uM := mul_le_mul hθ1 huu hu0.le (by linarith)
      have b : θ * u ^ 2 ≤ θh * uM ^ 2 := mul_le_mul hθ1 hu2M (sq_nonneg _) (by linarith)
      have : t1 * θ * (u + ag * u ^ 2) = t1 * (θ * u) + t1 * ag * (θ * u ^ 2) := by ring
      rw [this]
      have h1 := mul_le_mul_of_nonneg_left a ht1
      have h2 := mul_le_mul_of_nonneg_left b (mul_nonneg ht1 hag0)
      have e3 : t1 * (θh * uM) + t1 * ag * (θh * uM ^ 2) = t1 * θh * uM + t1 * ag * θh * uM ^ 2 := by ring
      linarith only [h1, h2, e3]
    have k5 : 2 * θ * z0 * u ^ 2 ≤ 2 * θh * z0 * uM ^ 2 := by
      have b : θ * u ^ 2 ≤ θh * uM ^ 2 := mul_le_mul hθ1 hu2M (sq_nonneg _) (by linarith)
      have h5 := mul_le_mul_of_nonneg_left b (by positivity : (0 : ℝ) ≤ 2 * z0)
      have e5 : 2 * z0 * (θ * u ^ 2) = 2 * θ * z0 * u ^ 2 := by ring
      have e6 : 2 * z0 * (θh * uM ^ 2) = 2 * θh * z0 * uM ^ 2 := by ring
      linarith only [h5, e5, e6]
    have k6 : cl * (2 * t0 * R1 + 2 * θ * R2 + 2 * θ * z0 * u ^ 2) ≤
        cl * (t0 * uM + 2 * θh * a2 * uM + 2 * θh * z0 * uM ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hcl
    have k4 : 2 * t0 * R1 ≤ t0 * uM := by
      have h2 : 2 * R1 ≤ uM := by linarith
      calc 2 * t0 * R1 = t0 * (2 * R1) := by ring
        _ ≤ t0 * uM := mul_le_mul_of_nonneg_left h2 ht0
    have k7 : 0 ≤ t0 ^ 2 * (θ * u ^ 2) := by positivity
    have hgk := hg.trans k2
    have hlo' := hlo
    ring_nf at hlo' k6 ⊢
    ring_nf at hgk k4 k7
    linarith only [hlo', k6, hgk, k4, k7, hθ1]
  have hrp : 0 < 1 + (2 * t0 * R1 + 2 * θ * R2 + 2 * θ * z0 * u ^ 2) := by positivity
  constructor
  · have hL0 : 0 ≤ (1 - θ) * (1 - t0 * B) ^ 2 - θ * u ^ 2 * t1 * g := by
      have : 0 ≤ cl * (1 + (2 * t0 * R1 + 2 * θ * R2 + 2 * θ * z0 * u ^ 2)) := by positivity
      linarith
    refine le_trans ?_ (hG2 hL0)
    rw [le_div_iff₀ hrp]
    exact hL
  · refine hG1.trans ?_
    rw [div_le_iff₀ hden]
    exact hU

end BstLean.Part186
