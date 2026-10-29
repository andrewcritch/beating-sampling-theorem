import BstLean.Part165Num

/-!
# Part 165 (file `Root`): the root sum at fixed constants (`n ≥ 23 000`)

No proof is left open; no `native_decide` or `axiom` is used.

* `tK_mono`, `priceC_mono`: monotonicity of the prices of Part 162.
* `priceC_scale`: the price at arguments `L g, A g⁴, D g², …` is `g⁴` times an explicit bracket.
* `rootE`: the explicit body of `rootFL` (Part 162), with the interface fields as arguments.
* `rc_*`: bounds of the pieces (`w_s/σ_l`, `ε₀`, `κ`, `L`, the exponent, `ι`, `c₂`, `c₃`, `A`,
  `D`, `e_k`, `d_k`, the price, `B`, the removal root, the displacement root).
* **`root_core`**: `rootE ≤ 0.002159` from field bounds of order `g^k`, `g = √(2/n)`,
  `g² ≤ 2/23000`, floor `σ_l = g·s` with `s ≥ 0.43`, `β_low ≤ 3·10⁻¹⁴`.
-/

namespace BstLean.Part165

open Real
open BstLean.Part162 (tK tK_nonneg priceC Bpap Dpap eps0 cVw cEw iotaP c2η c3η)

lemma tK_mono {κ κ' n n' L L' x x' y y' : ℝ} (h0κ : 0 ≤ κ) (h0n : 0 ≤ n) (h0L : 0 ≤ L)
    (h0x : 0 ≤ x) (h0y : 0 ≤ y) (hκ : κ ≤ κ') (hn : n ≤ n') (hL : L ≤ L') (hx : x ≤ x')
    (hy : y ≤ y') : tK κ n L x y ≤ tK κ' n' L' x' y' := by
  unfold tK
  have : 0 ≤ κ' := h0κ.trans hκ
  have : 0 ≤ n' := h0n.trans hn
  have : 0 ≤ L' := h0L.trans hL
  have : 0 ≤ x' := h0x.trans hx
  have : 0 ≤ y' := h0y.trans hy
  gcongr

lemma priceC_mono {κ κ' n L L' ε ε' E E' A A' D D' e4 e4' d4 d4' e6 e6' d6 d6' : ℝ}
    (h0κ : 0 ≤ κ) (h0n : 0 ≤ n) (h0L : 0 ≤ L) (h0ε : 0 ≤ ε) (h0E : 0 ≤ E) (h0A : 0 ≤ A)
    (h0D : 0 ≤ D) (h0e4 : 0 ≤ e4) (h0d4 : 0 ≤ d4) (h0e6 : 0 ≤ e6) (h0d6 : 0 ≤ d6)
    (hκ : κ ≤ κ') (hL : L ≤ L') (hε : ε ≤ ε') (hE : E ≤ E') (hA : A ≤ A') (hD : D ≤ D')
    (he4 : e4 ≤ e4') (hd4 : d4 ≤ d4') (he6 : e6 ≤ e6') (hd6 : d6 ≤ d6') :
    priceC κ n L ε E A D e4 d4 e6 d6 ≤ priceC κ' n L' ε' E' A' D' e4' d4' e6' d6' := by
  have : 0 ≤ κ' := h0κ.trans hκ
  have : 0 ≤ L' := h0L.trans hL
  have : 0 ≤ ε' := h0ε.trans hε
  have : 0 ≤ E' := h0E.trans hE
  have : 0 ≤ A' := h0A.trans hA
  have : 0 ≤ D' := h0D.trans hD
  have : 0 ≤ e4' := h0e4.trans he4
  have : 0 ≤ d4' := h0d4.trans hd4
  have : 0 ≤ e6' := h0e6.trans he6
  have : 0 ≤ d6' := h0d6.trans hd6
  have t4 := tK_mono h0κ h0n h0L h0e4 h0d4 hκ le_rfl hL he4 hd4
  have t6 := tK_mono h0κ h0n h0L h0e6 h0d6 hκ le_rfl hL he6 hd6
  have t40 := tK_nonneg h0κ h0n h0L h0e4 h0d4
  have t60 := tK_nonneg h0κ h0n h0L h0e6 h0d6
  have hT2 : κ * (n * A / 2 + D + L * √(A * D)) ≤ κ' * (n * A' / 2 + D' + L' * √(A' * D')) := by
    gcongr
  have hT20 : 0 ≤ κ * (n * A / 2 + D + L * √(A * D)) := by positivity
  unfold priceC
  gcongr


lemma priceC_scale {κ n L ε E A D x4 y4 x6 y6 g : ℝ} (hg : 0 < g)
    (hn : n * g ^ 2 = 2) (hA : 0 ≤ A) (hD : 0 ≤ D) :
    priceC κ n (L * g) ε E (A * (g ^ 2) ^ 2) (D * g ^ 2) (x4 * g ^ 2) (y4 * g) (x6 * g ^ 2) (y6 * g) =
      (g ^ 2) ^ 2 * (κ * g ^ 2 * (A ^ 2 / 2 + (1 + ε) * A * D) +
        (κ * (A + D + L * √(A * D) * g ^ 2)) ^ 2 / 2 +
        g ^ 2 * (κ * (A + D + L * √(A * D) * g ^ 2)) * (κ * (x4 ^ 2 + y4 ^ 2 + L * y4 * x4 * g ^ 2)) ^ 2 / 6 +
        (g ^ 2) ^ 2 * (κ * (x4 ^ 2 + y4 ^ 2 + L * y4 * x4 * g ^ 2)) ^ 4 / 24 +
        (g ^ 2) ^ 3 * (κ * (x4 ^ 2 + y4 ^ 2 + L * y4 * x4 * g ^ 2)) ^ 2 *
          (κ * (x6 ^ 2 + y6 ^ 2 + L * y6 * x6 * g ^ 2)) ^ 3 / 120 +
        E * (g ^ 2) ^ 4 * (κ * (x6 ^ 2 + y6 ^ 2 + L * y6 * x6 * g ^ 2)) ^ 6 / 720) := by
  have hs : √(A * (g ^ 2) ^ 2 * (D * g ^ 2)) = √(A * D) * (g ^ 2 * g) := by
    rw [show A * (g ^ 2) ^ 2 * (D * g ^ 2) = (A * D) * (g ^ 2 * g) ^ 2 by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hn' : n = 2 / g ^ 2 := by field_simp; linarith
  unfold priceC tK
  rw [hs, hn']
  field_simp
  ring

/-- The explicit body of `rootFL` (Part 162), with the fields of the interface as arguments. -/
noncomputable def rootE (n : ℕ) (wl ws η CA σl Vs Vl VS ts8 ts12 tl8 tl12 tlq tsq βl : ℝ) : ℝ :=
  √(2 * (1 + η⁻¹) * Bpap wl ws tlq tsq βl (2 * 12)) +
    √(priceC (1 - eps0 ws σl ^ 2)⁻¹ n (√CA * (2 * wl) / σl)
      (eps0 ws σl) (exp ((1 - eps0 ws σl ^ 2)⁻¹ * (n * eps0 ws σl ^ 2 / 2 +
        (√CA * (2 * wl) / σl) ^ 2 * (1 + eps0 ws σl))))
      (cVw ws σl * ((1 - η)⁻¹ * Vs)) (CA / σl ^ 2 * ((1 - η)⁻¹ * Vl))
      (cEw ws σl * ((iotaP η 8 + c2η η + c3η η ws σl) * ts8))
      (√CA / σl * ((iotaP η 8 + c2η η) * tl8))
      (cEw ws σl * ((iotaP η 12 + c2η η + c3η η ws σl) * ts12))
      (√CA / σl * ((iotaP η 12 + c2η η) * tl12))) +
    √(Dpap n (Bpap wl ws tlq tsq βl (2 * 12)) CA Vl VS η σl)

lemma sqrt_le_of_sq {x y : ℝ} (hy : 0 ≤ y) (h : x ≤ y ^ 2) : √x ≤ y :=
  (Real.sqrt_le_sqrt h).trans (le_of_eq (Real.sqrt_sq hy))


section core

variable {g s : ℝ}

/-- `w_s/σ_l ≤ (1750/43)·g²` for `σ_l = g s`, `s ≥ 0.43`. -/
lemma rc_rho (hg : 0 < g) (hs : 43 / 100 ≤ s) :
    35 / 2 * (g ^ 2 * g) / (g * s) = 35 / 2 / s * g ^ 2 ∧ 0 ≤ 35 / 2 / s * g ^ 2 ∧
    35 / 2 / s * g ^ 2 ≤ 1750 / 43 * g ^ 2 := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  refine ⟨by field_simp, by positivity, ?_⟩
  have : 35 / 2 / s ≤ 1750 / 43 := by
    rw [div_le_iff₀ hs0]; nlinarith
  exact mul_le_mul_of_nonneg_right this (sq_nonneg g)

lemma rc_eps (hg : 0 < g) (hg0 : g ^ 2 ≤ 2 / 23000) (hs : 43 / 100 ≤ s) :
    eps0 (35 / 2 * (g ^ 2 * g)) (g * s) = (1 + 2 * (35 / 2 / s * g ^ 2)) ^ 2 - 1 ∧
    0 ≤ eps0 (35 / 2 * (g ^ 2 * g)) (g * s) ∧
    eps0 (35 / 2 * (g ^ 2 * g)) (g * s) ≤ 1421 / 100000 := by
  obtain ⟨hρ, hρ0, hρ1⟩ := rc_rho hg hs
  have hε : eps0 (35 / 2 * (g ^ 2 * g)) (g * s) = (1 + 2 * (35 / 2 / s * g ^ 2)) ^ 2 - 1 := by
    unfold eps0; rw [mul_div_assoc, hρ]
  rw [hε]
  have hx : 35 / 2 / s * g ^ 2 ≤ 1750 / 43 * (2 / 23000) := hρ1.trans (by gcongr)
  refine ⟨rfl, by nlinarith, by nlinarith⟩

lemma rc_neps {n : ℕ} (hg : 0 < g) (hgn : (n : ℝ) * g ^ 2 = 2) (hg0 : g ^ 2 ≤ 2 / 23000)
    (hs : 43 / 100 ≤ s) :
    (n : ℝ) * eps0 (35 / 2 * (g ^ 2 * g)) (g * s) ^ 2 / 2 ≤ 2321 / 1000 := by
  have hn' : (n : ℝ) = 2 / g ^ 2 := by field_simp; linarith
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  rw [(rc_eps hg hg0 hs).1, hn']
  have e : 2 / g ^ 2 * ((1 + 2 * (35 / 2 / s * g ^ 2)) ^ 2 - 1) ^ 2 / 2 =
      (35 / s) ^ 2 * g ^ 2 * (2 + 35 / s * g ^ 2) ^ 2 := by field_simp; ring
  rw [e]
  have h1 : 35 / s ≤ 3500 / 43 := by rw [div_le_iff₀ hs0]; nlinarith
  have h0 : 0 ≤ 35 / s := by positivity
  calc (35 / s) ^ 2 * g ^ 2 * (2 + 35 / s * g ^ 2) ^ 2
      ≤ (3500 / 43 : ℝ) ^ 2 * (2 / 23000) * (2 + 3500 / 43 * (2 / 23000)) ^ 2 := by gcongr
    _ ≤ 2321 / 1000 := by norm_num

lemma rc_kappa {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1421 / 100000) :
    0 < 1 - ε ^ 2 ∧ (1 - ε ^ 2)⁻¹ ≤ 1000203 / 1000000 := by
  have hεsq : ε ^ 2 ≤ (1421 / 100000) ^ 2 := pow_le_pow_left₀ hε0 hε1 2
  have hκd : 0 < 1 - ε ^ 2 := by nlinarith
  refine ⟨hκd, ?_⟩
  rw [inv_le_comm₀ hκd (by norm_num)]
  have : (1000203 / 1000000 : ℝ)⁻¹ ≤ 1 - (1421 / 100000) ^ 2 := by norm_num
  linarith

lemma rc_L {CA : ℝ} (hg : 0 < g) (hs : 43 / 100 ≤ s) (h0CA : 0 ≤ CA) (hCA : CA ≤ 1532 / 1000) :
    0 ≤ √CA * (2 * (22 * g ^ 2)) / (g * s) ∧
    √CA * (2 * (22 * g ^ 2)) / (g * s) ≤ 12666 / 100 * g := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hsCA : √CA ≤ 12378 / 10000 :=
    (Real.sqrt_le_sqrt hCA).trans (sqrt_le_of_sq (by norm_num) (by norm_num))
  have hLe : √CA * (2 * (22 * g ^ 2)) / (g * s) = √CA * (44 / s) * g := by
    field_simp; ring
  rw [hLe]
  refine ⟨by positivity, ?_⟩
  have h1 : 44 / s ≤ 4400 / 43 := by rw [div_le_iff₀ hs0]; nlinarith
  have : √CA * (44 / s) ≤ 12666 / 100 := by
    calc √CA * (44 / s) ≤ 12378 / 10000 * (4400 / 43) := by gcongr
      _ ≤ 12666 / 100 := by norm_num
  exact mul_le_mul_of_nonneg_right this hg.le

lemma rc_EE {n : ℕ} {κ ε L : ℝ} (hg : 0 < g) (hg0 : g ^ 2 ≤ 2 / 23000) (hκ0 : 0 ≤ κ)
    (hκ1 : κ ≤ 1000203 / 1000000) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1421 / 100000)
    (hnε : (n : ℝ) * ε ^ 2 / 2 ≤ 2321 / 1000) (hL0 : 0 ≤ L) (hL1 : L ≤ 12666 / 100 * g) :
    exp (κ * ((n : ℝ) * ε ^ 2 / 2 + L ^ 2 * (1 + ε))) ≤ 55 := by
  have hL2 : L ^ 2 * (1 + ε) ≤ 14149 / 10000 := by
    have h1 : L ^ 2 ≤ (12666 / 100) ^ 2 * (2 / 23000) := by
      calc L ^ 2 ≤ (12666 / 100 * g) ^ 2 := pow_le_pow_left₀ hL0 hL1 2
        _ = (12666 / 100) ^ 2 * g ^ 2 := by ring
        _ ≤ (12666 / 100) ^ 2 * (2 / 23000) := by gcongr
    calc L ^ 2 * (1 + ε) ≤ (12666 / 100) ^ 2 * (2 / 23000) * (1 + 1421 / 100000) := by gcongr
      _ ≤ 14149 / 10000 := by norm_num
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hexpo : κ * ((n : ℝ) * ε ^ 2 / 2 + L ^ 2 * (1 + ε)) ≤ 4 := by
    calc κ * ((n : ℝ) * ε ^ 2 / 2 + L ^ 2 * (1 + ε)) ≤
          1000203 / 1000000 * (2321 / 1000 + 14149 / 10000) := by gcongr
      _ ≤ 4 := by norm_num
  calc exp (κ * ((n : ℝ) * ε ^ 2 / 2 + L ^ 2 * (1 + ε))) ≤ exp 4 := exp_le_exp.mpr hexpo
    _ = exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    _ ≤ (2.7182818286 : ℝ) ^ 4 := pow_le_pow_left₀ (exp_pos _).le Real.exp_one_lt_d9.le 4
    _ ≤ 55 := by norm_num

lemma rc_iota (p : ℕ) (hp : 1 ≤ p) : 0 ≤ iotaP (1 / 10000) p ∧ iotaP (1 / 10000) p ≤ 10002 / 10000 := by
  refine ⟨by unfold iotaP; positivity, ?_⟩
  unfold iotaP
  have h1 : (1 : ℝ) ≤ (1 - 1 / 10000)⁻¹ := by norm_num
  have hp' : ((p : ℕ) : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hp)
  calc ((1 - 1 / 10000 : ℝ)⁻¹) ^ (((p : ℕ) : ℝ)⁻¹) ≤ ((1 - 1 / 10000 : ℝ)⁻¹) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 hp'
    _ ≤ 10002 / 10000 := by rw [Real.rpow_one]; norm_num

lemma rc_c2 : 0 ≤ c2η (1 / 10000) ∧ c2η (1 / 10000) ≤ 10001 / 1000000 := by
  refine ⟨by unfold c2η; positivity, ?_⟩
  unfold c2η; exact sqrt_le_of_sq (by norm_num) (by norm_num)

lemma rc_sη : (99994 / 100000 : ℝ) ≤ √(1 - 1 / 10000) := by
  rw [show (99994 / 100000 : ℝ) = √((99994 / 100000) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

lemma rc_c3 (hg : 0 < g) (hg0 : g ^ 2 ≤ 2 / 23000) (hs : 43 / 100 ≤ s) :
    0 ≤ c3η (1 / 10000) (35 / 2 * (g ^ 2 * g)) (g * s) ∧
    c3η (1 / 10000) (35 / 2 * (g ^ 2 * g)) (g * s) ≤ 17698 / 10000000 := by
  have hsη := rc_sη
  have hsη0 : 0 < √(1 - 1 / 10000 : ℝ) := lt_of_lt_of_le (by norm_num) hsη
  obtain ⟨hρ, hρ0, hρ1⟩ := rc_rho hg hs
  have hc3e : c3η (1 / 10000) (35 / 2 * (g ^ 2 * g)) (g * s) =
      35 / 2 / s * g ^ 2 / (2 * √(1 - 1 / 10000)) := by
    unfold c3η; rw [← hρ]; field_simp
  rw [hc3e]
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (by positivity)]
  calc 35 / 2 / s * g ^ 2 ≤ 1750 / 43 * (2 / 23000) := hρ1.trans (by gcongr)
    _ ≤ 17698 / 10000000 * (2 * (99994 / 100000)) := by norm_num
    _ ≤ 17698 / 10000000 * (2 * √(1 - 1 / 10000)) := by gcongr

lemma rc_A {Vs : ℝ} (hg : 0 < g) (hg0 : g ^ 2 ≤ 2 / 23000) (hs : 43 / 100 ≤ s) (h0Vs : 0 ≤ Vs)
    (hVs : Vs ≤ 81508 / 100000 * (g ^ 2) ^ 3) :
    0 ≤ cVw (35 / 2 * (g ^ 2 * g)) (g * s) * ((1 - 1 / 10000)⁻¹ * Vs) ∧
    cVw (35 / 2 * (g ^ 2 * g)) (g * s) * ((1 - 1 / 10000)⁻¹ * Vs) ≤
      1776 / 100 * (g ^ 2) ^ 2 := by
  obtain ⟨hρ, hρ0, hρ1⟩ := rc_rho hg hs
  have hAe : cVw (35 / 2 * (g ^ 2 * g)) (g * s) * ((1 - 1 / 10000)⁻¹ * Vs) =
      4 * (1 + 35 / 2 / s * g ^ 2) ^ 2 / (g * s) ^ 2 * (10000 / 9999 * Vs) := by
    unfold cVw; rw [hρ]; norm_num
  rw [hAe]
  refine ⟨by positivity, ?_⟩
  have hx : 35 / 2 / s * g ^ 2 ≤ 1750 / 43 * (2 / 23000) := hρ1.trans (by gcongr)
  set x := 35 / 2 / s * g ^ 2 with hxdef
  calc 4 * (1 + x) ^ 2 / (g * s) ^ 2 * (10000 / 9999 * Vs)
      ≤ 4 * (1 + 1750 / 43 * (2 / 23000)) ^ 2 / (g * (43 / 100)) ^ 2 *
        (10000 / 9999 * (81508 / 100000 * (g ^ 2) ^ 3)) := by
        gcongr
    _ = 4 * (1 + 1750 / 43 * (2 / 23000)) ^ 2 / (43 / 100) ^ 2 * (10000 / 9999) *
        (81508 / 100000) * (g ^ 2) ^ 2 := by field_simp
    _ ≤ 1776 / 100 * (g ^ 2) ^ 2 := by gcongr; norm_num

lemma rc_D {CA Vl : ℝ} (hg : 0 < g) (hs : 43 / 100 ≤ s) (h0CA : 0 ≤ CA) (hCA : CA ≤ 1532 / 1000)
    (h0Vl : 0 ≤ Vl) (hVl : Vl ≤ 127512 / 100000 * (g ^ 2) ^ 2) :
    0 ≤ CA / (g * s) ^ 2 * ((1 - 1 / 10000)⁻¹ * Vl) ∧
    CA / (g * s) ^ 2 * ((1 - 1 / 10000)⁻¹ * Vl) ≤ 10567 / 1000 * g ^ 2 := by
  have hηi : (1 - 1 / 10000 : ℝ)⁻¹ = 10000 / 9999 := by norm_num
  rw [hηi]
  refine ⟨by positivity, ?_⟩
  calc CA / (g * s) ^ 2 * (10000 / 9999 * Vl)
      ≤ 1532 / 1000 / (g * (43 / 100)) ^ 2 * (10000 / 9999 * (127512 / 100000 * (g ^ 2) ^ 2)) := by
        gcongr
    _ = 1532 / 1000 / (43 / 100) ^ 2 * (10000 / 9999) * (127512 / 100000) * g ^ 2 := by
        field_simp
    _ ≤ 10567 / 1000 * g ^ 2 := by gcongr; norm_num

lemma rc_e {p : ℕ} {t K : ℝ} (hg : 0 < g) (hg0 : g ^ 2 ≤ 2 / 23000) (hs : 43 / 100 ≤ s)
    (hp : 1 ≤ p) (ht : 0 ≤ t) (hK : t ≤ K * (g ^ 2 * g)) :
    0 ≤ cEw (35 / 2 * (g ^ 2 * g)) (g * s) *
        ((iotaP (1 / 10000) p + c2η (1 / 10000) + c3η (1 / 10000) (35 / 2 * (g ^ 2 * g))
          (g * s)) * t) ∧
    cEw (35 / 2 * (g ^ 2 * g)) (g * s) *
        ((iotaP (1 / 10000) p + c2η (1 / 10000) + c3η (1 / 10000) (35 / 2 * (g ^ 2 * g))
          (g * s)) * t) ≤
      2 * (43 / 100 + 35 / 2 * (2 / 23000)) / (43 / 100) ^ 2 *
        ((10002 / 10000 + 10001 / 1000000 + 17698 / 10000000) * K) * g ^ 2 := by
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hK0 : 0 ≤ K := by
    by_contra hc
    have : K * (g ^ 2 * g) < 0 := mul_neg_of_neg_of_pos (not_le.mp hc) (by positivity)
    linarith
  obtain ⟨hι0, hι1⟩ := rc_iota p hp
  obtain ⟨hc20, hc21⟩ := rc_c2
  obtain ⟨hc30, hc31⟩ := rc_c3 hg hg0 hs
  have hcEw : cEw (35 / 2 * (g ^ 2 * g)) (g * s) = 2 * (1 / s + 35 / 2 / s ^ 2 * g ^ 2) / g := by
    unfold cEw; field_simp
  have hq : 2 * (1 / s + 35 / 2 / s ^ 2 * g ^ 2) ≤ 2 * (43 / 100 + 35 / 2 * (2 / 23000)) / (43 / 100) ^ 2 := by
    have h1 : 1 / s ≤ 100 / 43 := by rw [div_le_iff₀ hs0]; nlinarith
    have h2 : 35 / 2 / s ^ 2 ≤ 35 / 2 / (43 / 100) ^ 2 := by gcongr
    have h3 : 35 / 2 / s ^ 2 * g ^ 2 ≤ 35 / 2 / (43 / 100) ^ 2 * (2 / 23000) := by gcongr
    have e : 2 * (43 / 100 + 35 / 2 * (2 / 23000)) / (43 / 100 : ℝ) ^ 2 =
        2 * (100 / 43 + 35 / 2 / (43 / 100) ^ 2 * (2 / 23000)) := by norm_num
    rw [e]; linarith
  rw [hcEw]
  refine ⟨by positivity, ?_⟩
  calc 2 * (1 / s + 35 / 2 / s ^ 2 * g ^ 2) / g *
        ((iotaP (1 / 10000) p + c2η (1 / 10000) + c3η (1 / 10000) (35 / 2 * (g ^ 2 * g))
          (g * s)) * t)
      ≤ 2 * (43 / 100 + 35 / 2 * (2 / 23000)) / (43 / 100) ^ 2 / g *
        ((10002 / 10000 + 10001 / 1000000 + 17698 / 10000000) * (K * (g ^ 2 * g))) := by
        gcongr
    _ = _ := by field_simp

lemma rc_d {p : ℕ} {CA t K : ℝ} (hg : 0 < g) (hs : 43 / 100 ≤ s) (h0CA : 0 ≤ CA)
    (hCA : CA ≤ 1532 / 1000) (hp : 1 ≤ p) (ht : 0 ≤ t) (hK : t ≤ K * g ^ 2) :
    0 ≤ √CA / (g * s) * ((iotaP (1 / 10000) p + c2η (1 / 10000)) * t) ∧
    √CA / (g * s) * ((iotaP (1 / 10000) p + c2η (1 / 10000)) * t) ≤
      12378 / 10000 / (43 / 100) * ((10002 / 10000 + 10001 / 1000000) * K) * g := by
  have hK0 : 0 ≤ K := by
    by_contra hc
    have : K * g ^ 2 < 0 := mul_neg_of_neg_of_pos (not_le.mp hc) (by positivity)
    linarith
  obtain ⟨hι0, hι1⟩ := rc_iota p hp
  obtain ⟨hc20, hc21⟩ := rc_c2
  have hsCA : √CA ≤ 12378 / 10000 :=
    (Real.sqrt_le_sqrt hCA).trans (sqrt_le_of_sq (by norm_num) (by norm_num))
  refine ⟨by positivity, ?_⟩
  calc √CA / (g * s) * ((iotaP (1 / 10000) p + c2η (1 / 10000)) * t)
      ≤ 12378 / 10000 / (g * (43 / 100)) * ((10002 / 10000 + 10001 / 1000000) * (K * g ^ 2)) := by
        gcongr
    _ = 12378 / 10000 / (43 / 100) * ((10002 / 10000 + 10001 / 1000000) * K) * g := by
        field_simp

end core

section core2

variable {g s : ℝ}

lemma rc_price {n : ℕ} {κ L ε E A D e4 d4 e6 d6 : ℝ} (hg : 0 < g) (hgn : (n : ℝ) * g ^ 2 = 2)
    (hg0 : g ^ 2 ≤ 2 / 23000) (h0κ : 0 ≤ κ) (h0L : 0 ≤ L) (h0ε : 0 ≤ ε) (h0E : 0 ≤ E)
    (h0A : 0 ≤ A) (h0D : 0 ≤ D) (h0e4 : 0 ≤ e4) (h0d4 : 0 ≤ d4) (h0e6 : 0 ≤ e6) (h0d6 : 0 ≤ d6)
    (hκ : κ ≤ 1000203 / 1000000) (hL : L ≤ 12666 / 100 * g) (hε : ε ≤ 1421 / 100000)
    (hE : E ≤ 55) (hA : A ≤ 1776 / 100 * (g ^ 2) ^ 2) (hD : D ≤ 10567 / 1000 * g ^ 2)
    (he4 : e4 ≤ 1199 / 100 * g ^ 2) (hd4 : d4 ≤ 924 / 100 * g) (he6 : e6 ≤ 1449 / 100 * g ^ 2)
    (hd6 : d6 ≤ 1116 / 100 * g) :
    √(priceC κ n L ε E A D e4 d4 e6 d6) ≤ 1850 / 10 ^ 6 := by
  have h1 := priceC_mono h0κ (Nat.cast_nonneg n) h0L h0ε h0E h0A h0D h0e4 h0d4 h0e6 h0d6 hκ hL hε
    hE hA hD he4 hd4 he6 hd6
  rw [priceC_scale hg hgn (by norm_num) (by norm_num)] at h1
  have hs : √((1776 / 100 : ℝ) * (10567 / 1000)) ≤ 1370 / 100 :=
    sqrt_le_of_sq (by norm_num) (by norm_num)
  have hs0 : 0 ≤ √((1776 / 100 : ℝ) * (10567 / 1000)) := Real.sqrt_nonneg _
  have hu : 0 ≤ g ^ 2 := sq_nonneg g
  have hF : (1000203 / 1000000 : ℝ) * g ^ 2 * ((1776 / 100) ^ 2 / 2 + (1 + 1421 / 100000) *
        (1776 / 100) * (10567 / 1000)) +
      (1000203 / 1000000 * (1776 / 100 + 10567 / 1000 + 12666 / 100 *
        √((1776 / 100 : ℝ) * (10567 / 1000)) * g ^ 2)) ^ 2 / 2 +
      g ^ 2 * (1000203 / 1000000 * (1776 / 100 + 10567 / 1000 + 12666 / 100 *
        √((1776 / 100 : ℝ) * (10567 / 1000)) * g ^ 2)) *
        (1000203 / 1000000 * ((1199 / 100) ^ 2 + (924 / 100) ^ 2 + 12666 / 100 * (924 / 100) *
          (1199 / 100) * g ^ 2)) ^ 2 / 6 +
      (g ^ 2) ^ 2 * (1000203 / 1000000 * ((1199 / 100) ^ 2 + (924 / 100) ^ 2 + 12666 / 100 *
        (924 / 100) * (1199 / 100) * g ^ 2)) ^ 4 / 24 +
      (g ^ 2) ^ 3 * (1000203 / 1000000 * ((1199 / 100) ^ 2 + (924 / 100) ^ 2 + 12666 / 100 *
        (924 / 100) * (1199 / 100) * g ^ 2)) ^ 2 *
        (1000203 / 1000000 * ((1449 / 100) ^ 2 + (1116 / 100) ^ 2 + 12666 / 100 * (1116 / 100) *
          (1449 / 100) * g ^ 2)) ^ 3 / 120 +
      55 * (g ^ 2) ^ 4 * (1000203 / 1000000 * ((1449 / 100) ^ 2 + (1116 / 100) ^ 2 +
        12666 / 100 * (1116 / 100) * (1449 / 100) * g ^ 2)) ^ 6 / 720 ≤ 452 := by
    calc _ ≤ (1000203 / 1000000 : ℝ) * (2 / 23000) * ((1776 / 100) ^ 2 / 2 + (1 + 1421 / 100000) *
            (1776 / 100) * (10567 / 1000)) +
          (1000203 / 1000000 * (1776 / 100 + 10567 / 1000 + 12666 / 100 * (1370 / 100) *
            (2 / 23000))) ^ 2 / 2 +
          (2 / 23000) * (1000203 / 1000000 * (1776 / 100 + 10567 / 1000 + 12666 / 100 *
            (1370 / 100) * (2 / 23000))) *
            (1000203 / 1000000 * ((1199 / 100) ^ 2 + (924 / 100) ^ 2 + 12666 / 100 * (924 / 100) *
              (1199 / 100) * (2 / 23000))) ^ 2 / 6 +
          (2 / 23000) ^ 2 * (1000203 / 1000000 * ((1199 / 100) ^ 2 + (924 / 100) ^ 2 +
            12666 / 100 * (924 / 100) * (1199 / 100) * (2 / 23000))) ^ 4 / 24 +
          (2 / 23000) ^ 3 * (1000203 / 1000000 * ((1199 / 100) ^ 2 + (924 / 100) ^ 2 +
            12666 / 100 * (924 / 100) * (1199 / 100) * (2 / 23000))) ^ 2 *
            (1000203 / 1000000 * ((1449 / 100) ^ 2 + (1116 / 100) ^ 2 + 12666 / 100 *
              (1116 / 100) * (1449 / 100) * (2 / 23000))) ^ 3 / 120 +
          55 * (2 / 23000) ^ 4 * (1000203 / 1000000 * ((1449 / 100) ^ 2 + (1116 / 100) ^ 2 +
            12666 / 100 * (1116 / 100) * (1449 / 100) * (2 / 23000))) ^ 6 / 720 := by
          gcongr
      _ ≤ 452 := by norm_num
  have h2 : priceC κ n L ε E A D e4 d4 e6 d6 ≤ (g ^ 2) ^ 2 * 452 :=
    h1.trans (mul_le_mul_of_nonneg_left hF (by positivity))
  calc √(priceC κ n L ε E A D e4 d4 e6 d6) ≤ √((g ^ 2) ^ 2 * 452) := Real.sqrt_le_sqrt h2
    _ = g ^ 2 * √452 := by rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hu]
    _ ≤ (2 / 23000) * (2127 / 100) := by
        gcongr
        exact sqrt_le_of_sq (by norm_num) (by norm_num)
    _ ≤ 1850 / 10 ^ 6 := by norm_num

lemma rc_B {tlq tsq βl : ℝ} (hg : 0 < g) (h0tlq : 0 ≤ tlq) (htlq : tlq ≤ 53493 / 10000 * g ^ 2)
    (h0tsq : 0 ≤ tsq) (htsq : tsq ≤ 42768 / 10000 * (g ^ 2 * g)) (h0β : 0 ≤ βl)
    (hβ : βl ≤ 3 / 10 ^ 14) :
    0 ≤ Bpap (22 * g ^ 2) (35 / 2 * (g ^ 2 * g)) tlq tsq βl (2 * 12) ∧
    Bpap (22 * g ^ 2) (35 / 2 * (g ^ 2 * g)) tlq tsq βl (2 * 12) ≤ 34 / 10 ^ 15 := by
  unfold Bpap
  have hu : 0 < g ^ 2 := by positivity
  have h1 : tlq / (22 * g ^ 2) ≤ 53493 / 10000 / 22 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  have h2 : tsq / (35 / 2 * (g ^ 2 * g)) ≤ 42768 / 10000 / (35 / 2) := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith [mul_pos hu hg]
  have h10 : 0 ≤ tlq / (22 * g ^ 2) := by positivity
  have h20 : 0 ≤ tsq / (35 / 2 * (g ^ 2 * g)) := by positivity
  refine ⟨by positivity, ?_⟩
  calc (tlq / (22 * g ^ 2)) ^ (2 * 12) + (tsq / (35 / 2 * (g ^ 2 * g))) ^ (2 * 12) + βl
      ≤ (53493 / 10000 / 22) ^ (2 * 12) + (42768 / 10000 / (35 / 2)) ^ (2 * 12) + 3 / 10 ^ 14 := by
        gcongr
    _ ≤ 34 / 10 ^ 15 := by norm_num

lemma rc_R1 {B : ℝ} (h0B : 0 ≤ B) (hB : B ≤ 34 / 10 ^ 15) :
    √(2 * (1 + (1 / 10000 : ℝ)⁻¹) * B) ≤ 27 / 10 ^ 6 := by
  apply sqrt_le_of_sq (by norm_num)
  calc 2 * (1 + (1 / 10000 : ℝ)⁻¹) * B ≤ 2 * (1 + (1 / 10000 : ℝ)⁻¹) * (34 / 10 ^ 15) := by gcongr
    _ ≤ (27 / 10 ^ 6) ^ 2 := by norm_num

lemma rc_Dp {n : ℕ} {B CA Vl VS : ℝ} (hg : 0 < g) (hgn : (n : ℝ) * g ^ 2 = 2)
    (hg0 : g ^ 2 ≤ 2 / 23000) (hs : 43 / 100 ≤ s) (h0B : 0 ≤ B) (hB : B ≤ 34 / 10 ^ 15)
    (h0CA : 0 ≤ CA) (hCA : CA ≤ 1532 / 1000) (h0Vl : 0 ≤ Vl)
    (hVl : Vl ≤ 127512 / 100000 * (g ^ 2) ^ 2)
    (h0VS : 0 ≤ VS) (hVS : VS ≤ 4247 / 10 * (g ^ 2) ^ 4) :
    √(Dpap n B CA Vl VS (1 / 10000) (g * s)) ≤ 225 / 10 ^ 6 := by
  unfold Dpap
  have hn' : (n : ℝ) = 2 / g ^ 2 := by field_simp; linarith
  have hsB : √B ≤ 1845 / 10 ^ 10 := (Real.sqrt_le_sqrt hB).trans
    (sqrt_le_of_sq (by norm_num) (by norm_num))
  have hsB0 : 0 ≤ √B := Real.sqrt_nonneg _
  have hu : 0 < g ^ 2 := by positivity
  have hT1 : CA * Vl / (2 * (1 - 1 / 10000) * (g * s) ^ 2) ≤
      1532 / 1000 * (127512 / 100000) / (2 * (1 - 1 / 10000) * (43 / 100) ^ 2) * g ^ 2 := by
    calc CA * Vl / (2 * (1 - 1 / 10000) * (g * s) ^ 2)
        ≤ 1532 / 1000 * (127512 / 100000 * (g ^ 2) ^ 2) /
          (2 * (1 - 1 / 10000) * (g * (43 / 100)) ^ 2) := by gcongr
      _ = _ := by field_simp
  have hT2 : (n : ℝ) * VS / (8 * (1 - 1 / 10000) ^ 2 * (g * s) ^ 4) ≤
      2 * (4247 / 10) / (8 * (1 - 1 / 10000) ^ 2 * (43 / 100) ^ 4) * g ^ 2 := by
    rw [hn']
    calc 2 / g ^ 2 * VS / (8 * (1 - 1 / 10000) ^ 2 * (g * s) ^ 4)
        ≤ 2 / g ^ 2 * (4247 / 10 * (g ^ 2) ^ 4) /
          (8 * (1 - 1 / 10000) ^ 2 * (g * (43 / 100)) ^ 4) := by gcongr
      _ = _ := by field_simp
  have hsum : CA * Vl / (2 * (1 - 1 / 10000) * (g * s) ^ 2) +
      (n : ℝ) * VS / (8 * (1 - 1 / 10000) ^ 2 * (g * s) ^ 4) ≤ 3112 * g ^ 2 := by
    have e : 1532 / 1000 * (127512 / 100000) / (2 * (1 - 1 / 10000) * (43 / 100) ^ 2) +
        2 * (4247 / 10) / (8 * (1 - 1 / 10000) ^ 2 * (43 / 100) ^ 4) ≤ (3112 : ℝ) := by norm_num
    nlinarith
  have hs0 : 0 < s := lt_of_lt_of_le (by norm_num) hs
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hS0 : 0 ≤ CA * Vl / (2 * (1 - 1 / 10000) * (g * s) ^ 2) +
      (n : ℝ) * VS / (8 * (1 - 1 / 10000) ^ 2 * (g * s) ^ 4) := by positivity
  apply sqrt_le_of_sq (by norm_num)
  calc √B * (CA * Vl / (2 * (1 - 1 / 10000) * (g * s) ^ 2) +
        (n : ℝ) * VS / (8 * (1 - 1 / 10000) ^ 2 * (g * s) ^ 4))
      ≤ 1845 / 10 ^ 10 * (3112 * (2 / 23000)) := by
        gcongr
        exact hsum.trans (by gcongr)
    _ ≤ (225 / 10 ^ 6) ^ 2 := by norm_num

/-- **The root sum at fixed constants.** For `g > 0` with `n g² = 2`, `g² ≤ 2/23000`, a floor
`σ_l = g·s` with `s ≥ 0.43`, `w_l = 22g²`, `w_s = 17.5g³`, `η = 10⁻⁴`, `C_A ≤ 1.532`,
`β_low ≤ 3·10⁻¹⁴` and the field bounds of the interface: `rootE ≤ 0.002159`. -/
theorem root_core {n : ℕ} (hg : 0 < g) (hgn : (n : ℝ) * g ^ 2 = 2) (hg0 : g ^ 2 ≤ 2 / 23000)
    (hs : 43 / 100 ≤ s) {CA Vs Vl VS ts8 ts12 tl8 tl12 tlq tsq βl : ℝ}
    (h0CA : 0 ≤ CA) (hCA : CA ≤ 1532 / 1000)
    (h0Vs : 0 ≤ Vs) (hVs : Vs ≤ 81508 / 100000 * (g ^ 2) ^ 3)
    (h0Vl : 0 ≤ Vl) (hVl : Vl ≤ 127512 / 100000 * (g ^ 2) ^ 2)
    (h0VS : 0 ≤ VS) (hVS : VS ≤ 4247 / 10 * (g ^ 2) ^ 4)
    (h0ts8 : 0 ≤ ts8) (hts8 : ts8 ≤ 25379 / 10000 * (g ^ 2 * g))
    (h0tl8 : 0 ≤ tl8) (htl8 : tl8 ≤ 31743 / 10000 * g ^ 2)
    (h0ts12 : 0 ≤ ts12) (hts12 : ts12 ≤ 30661 / 10000 * (g ^ 2 * g))
    (h0tl12 : 0 ≤ tl12) (htl12 : tl12 ≤ 38350 / 10000 * g ^ 2)
    (h0tlq : 0 ≤ tlq) (htlq : tlq ≤ 53493 / 10000 * g ^ 2)
    (h0tsq : 0 ≤ tsq) (htsq : tsq ≤ 42768 / 10000 * (g ^ 2 * g))
    (h0β : 0 ≤ βl) (hβ : βl ≤ 3 / 10 ^ 14) :
    rootE n (22 * g ^ 2) (35 / 2 * (g ^ 2 * g)) (1 / 10000) CA (g * s)
      Vs Vl VS ts8 ts12 tl8 tl12 tlq tsq βl ≤ 2159 / 10 ^ 6 := by
  obtain ⟨-, hε0, hε1⟩ := rc_eps hg hg0 hs
  obtain ⟨hκd, hκ1⟩ := rc_kappa hε0 hε1
  have hκ0 := (inv_pos.2 hκd).le
  obtain ⟨hL0, hL1⟩ := rc_L hg hs h0CA hCA
  have hnε := rc_neps (n := n) hg hgn hg0 hs
  have hEE := rc_EE hg hg0 hκ0 hκ1 hε0 hε1 hnε hL0 hL1
  obtain ⟨hA0, hA⟩ := rc_A hg hg0 hs h0Vs hVs
  obtain ⟨hD0, hD⟩ := rc_D hg hs h0CA hCA h0Vl hVl
  obtain ⟨he40, he4⟩ := rc_e (p := 8) hg hg0 hs (by norm_num) h0ts8 hts8
  obtain ⟨he60, he6⟩ := rc_e (p := 12) hg hg0 hs (by norm_num) h0ts12 hts12
  obtain ⟨hd40, hd4⟩ := rc_d (p := 8) hg hs h0CA hCA (by norm_num) h0tl8 htl8
  obtain ⟨hd60, hd6⟩ := rc_d (p := 12) hg hs h0CA hCA (by norm_num) h0tl12 htl12
  have hP := rc_price (n := n) hg hgn hg0 hκ0 hL0 hε0 (exp_pos _).le hA0 hD0 he40 hd40 he60 hd60
    hκ1 hL1 hε1 hEE hA hD (he4.trans (by gcongr; norm_num)) (hd4.trans (by gcongr; norm_num))
    (he6.trans (by gcongr; norm_num)) (hd6.trans (by gcongr; norm_num))
  obtain ⟨hB0, hB⟩ := rc_B hg h0tlq htlq h0tsq htsq h0β hβ
  have hR1 := rc_R1 hB0 hB
  have hR3 := rc_Dp (n := n) hg hgn hg0 hs hB0 hB h0CA hCA h0Vl hVl h0VS hVS
  unfold rootE
  linarith

end core2

end BstLean.Part165
