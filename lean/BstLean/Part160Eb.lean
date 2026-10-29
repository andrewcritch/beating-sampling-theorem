import BstLean.Part160Defs

/-!
# Part 160 (file `Eb`): a sharper upper bound of the centre energy

Do not use `sorry`, `native_decide` or `axiom`.

Part 154 has `e_b = t_A|b|²/γ_A ≤ 0.82` on the event `GoodC16` (through the chord
`κ(r) ≤ 1/π + (1 − 1/π) r`). This file uses a quadratic upper bound of `κ`.

* `kappa_quad`: `κ(r) ≤ 1/π + r/2 + (1/2 − 1/π) r²` on `[0, 1]`.
* `rb_quad`: `E 𝖯_b² ≤ Γ − (3/2 − 2/π) s_h² + (1/2 − 1/π) s_h⁴/Γ`.
* `ebO16`: on `GoodC16`, `θ_in ≥ 0.46`, `n ≥ 16384`: `e_b° ≤ 0.771` for the oracle centre.
* `eb16`: `t_A|b|² ≤ γ_A·0.772` for the computed centre `b = bT n n/ρ`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150
open BstLean.Part153 (nrm Pb GoodAs GoodAs16)
open BstLean.Part154 (GoodC16 csC)

/-! ## The quadratic bound of `κ` -/

lemma arcsin_convexOn : ConvexOn ℝ (Icc (0 : ℝ) 1) Real.arcsin := by
  refine MonotoneOn.convexOn_of_deriv (convex_Icc _ _) Real.continuous_arcsin.continuousOn ?_ ?_
  · rw [interior_Icc]
    intro x hx
    exact (Real.hasDerivAt_arcsin (ne_of_gt (by linarith [hx.1])) (ne_of_lt hx.2)
      ).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx y hy hxy
    rw [(Real.hasDerivAt_arcsin (ne_of_gt (by linarith [hx.1])) (ne_of_lt hx.2)).deriv,
      (Real.hasDerivAt_arcsin (ne_of_gt (by linarith [hy.1])) (ne_of_lt hy.2)).deriv]
    have h1 : 1 - y ^ 2 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hy.1]
    have h2 : 0 < 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
    exact one_div_le_one_div_of_le (Real.sqrt_pos.mpr h2) (Real.sqrt_le_sqrt h1)

/-- The difference `q − κ`, `q(x) = 1/π + x/2 + (1/2 − 1/π) x²`. -/
private noncomputable def qk (x : ℝ) : ℝ := (1 / π + x / 2 + (1 / 2 - 1 / π) * x ^ 2) - kappa x

private lemma qk_deriv {x : ℝ} (h0 : 0 < x) (h1 : x < 1) :
    HasDerivAt qk (((π - 2) * x - Real.arcsin x) / π) x := by
  have hp := Real.pi_pos
  have d1 : HasDerivAt (fun x : ℝ => 1 / π + x / 2 + (1 / 2 - 1 / π) * x ^ 2)
      (1 / 2 + (1 / 2 - 1 / π) * (2 * x)) x := by
    have a := (hasDerivAt_id x).div_const 2
    have b := ((hasDerivAt_pow 2 x).const_mul (1 / 2 - 1 / π))
    have c := (a.const_add (1 / π)).add b
    convert c using 1
    · funext y
      simp
    · norm_num
  have d2 := d1.sub (hasDerivAt_kappa (by linarith) h1)
  have e : 1 / 2 + (1 / 2 - 1 / π) * (2 * x) - (π - Real.arccos x) / π =
      ((π - 2) * x - Real.arcsin x) / π := by
    rw [BstLean.Part132.kappa_deriv_eq]
    field_simp
    ring
  rw [e] at d2
  exact d2

private lemma qk_cont : Continuous qk := by
  unfold qk
  have := continuous_kappa
  fun_prop

/-- **A quadratic upper bound of `κ`**: `κ(r) ≤ 1/π + r/2 + (1/2 − 1/π) r²` on `[0, 1]`
(equality at `0` and at `1`; it is below the chord `1/π + (1 − 1/π) r`). -/
theorem kappa_quad {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) :
    kappa r ≤ 1 / π + r / 2 + (1 / 2 - 1 / π) * r ^ 2 := by
  have hp := Real.pi_pos
  suffices h : 0 ≤ qk r by unfold qk at h; linarith
  have hq0 : qk 0 = 0 := by unfold qk; rw [kappa_zero]; ring
  have hq1 : qk 1 = 0 := by unfold qk; rw [kappa_one]; ring
  have hcv := arcsin_convexOn
  have hz : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_refl _, by norm_num⟩
  by_cases hG : Real.arcsin r ≤ (π - 2) * r
  · -- `q − κ` is nondecreasing on `[0, r]`
    have hm : MonotoneOn qk (Icc 0 r) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) qk_cont.continuousOn ?_ ?_
      · rw [interior_Icc]
        exact fun x hx =>
          (qk_deriv hx.1 (by linarith [hx.2])).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro x hx
        have hx1 : x < 1 := by linarith [hx.2]
        rw [(qk_deriv hx.1 hx1).deriv]
        have hr0 : 0 < r := by linarith [hx.1, hx.2]
        have hc := hcv.2 hz (show r ∈ Icc (0 : ℝ) 1 from ⟨h0, h1⟩)
          (show 0 ≤ 1 - x / r by rw [sub_nonneg, div_le_one hr0]; exact hx.2.le)
          (div_nonneg hx.1.le hr0.le) (by ring)
        simp only [smul_eq_mul, mul_zero, zero_add, Real.arcsin_zero] at hc
        rw [div_mul_cancel₀ _ hr0.ne'] at hc
        have h2 : x / r * Real.arcsin r ≤ x / r * ((π - 2) * r) :=
          mul_le_mul_of_nonneg_left hG (div_nonneg hx.1.le hr0.le)
        have h3 : x / r * ((π - 2) * r) = (π - 2) * x := by field_simp
        exact div_nonneg (by linarith) hp.le
    have := hm ⟨le_refl _, h0⟩ ⟨h0, le_refl _⟩ h0
    rwa [hq0] at this
  · -- `q − κ` is nonincreasing on `[r, 1]`
    have hG' : (π - 2) * r < Real.arcsin r := not_le.mp hG
    have hr0 : 0 < r := by
      rcases h0.eq_or_lt with h | h
      · rw [← h] at hG'; simp at hG'
      · exact h
    have hm : AntitoneOn qk (Icc r 1) := by
      refine antitoneOn_of_deriv_nonpos (convex_Icc _ _) qk_cont.continuousOn ?_ ?_
      · rw [interior_Icc]
        exact fun x hx =>
          (qk_deriv (by linarith [hx.1]) hx.2).differentiableAt.differentiableWithinAt
      · rw [interior_Icc]
        intro x hx
        have hx0 : 0 < x := by linarith [hx.1]
        rw [(qk_deriv hx0 hx.2).deriv]
        have hc := hcv.2 hz (show x ∈ Icc (0 : ℝ) 1 from ⟨hx0.le, hx.2.le⟩)
          (show 0 ≤ 1 - r / x by rw [sub_nonneg, div_le_one hx0]; exact hx.1.le)
          (show 0 ≤ r / x by positivity) (by ring)
        simp only [smul_eq_mul, mul_zero, zero_add, Real.arcsin_zero] at hc
        rw [div_mul_cancel₀ _ hx0.ne'] at hc
        -- `arcsin r ≤ (r/x) arcsin x`
        have h2 : (π - 2) * r < r / x * Real.arcsin x := lt_of_lt_of_le hG' hc
        have h3 : (π - 2) * x < Real.arcsin x := by
          have h4 : (π - 2) * r * (x / r) < r / x * Real.arcsin x * (x / r) :=
            mul_lt_mul_of_pos_right h2 (by positivity)
          have e1 : (π - 2) * r * (x / r) = (π - 2) * x := by field_simp
          have e2 : r / x * Real.arcsin x * (x / r) = Real.arcsin x := by field_simp
          rwa [e1, e2] at h4
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) hp.le
    have := hm ⟨le_refl _, h1⟩ ⟨h1, le_refl _⟩ h1
    rwa [hq1] at this

/-! ## The mean of the oracle energy with the quadratic bound -/

section rb

variable {n m : ℕ}

/-- **The mean of the energy with the quadratic bound of `κ`**:
`E 𝖯_b² ≤ Γ − (3/2 − 2/π)·s_h² + (1/2 − 1/π)·s_h⁴/Γ` (Part 153 has
`E 𝖯_b² ≤ Γ − (1 − 1/π)·s_h²` from the chord). -/
theorem rb_quad (hm : 1 ≤ m) (A₁ : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (τ : ℝ) :
    ∫ A₂, Pb A₁ c τ A₂ ^ 2 ∂gaussMat m m (2 / (m : ℝ)) ≤
      gO A₁ c τ - (3 / 2 - 2 / π) * sO2 A₁ c τ + (1 / 2 - 1 / π) * sO2 A₁ c τ ^ 2 / gO A₁ c τ := by
  obtain ⟨-, he⟩ := BstLean.Part153.rb_eq hm A₁ c τ
  rw [he]
  have hGb0 := BstLean.Part153.GamBar_nonneg A₁ c τ
  have hGb := BstLean.Part153.GamBar_le A₁ c τ
  have hs : sO2 A₁ c τ = gO A₁ c τ - 2 / (m : ℝ) * normSq (hO A₁ c τ) := rfl
  rw [hs]
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℝ, Γ = gO A₁ c τ := ⟨_, rfl⟩
  obtain ⟨Gb, hGbd⟩ : ∃ Gb : ℝ, Gb = 2 / (m : ℝ) * normSq (hO A₁ c τ) := ⟨_, rfl⟩
  rw [← hGbd] at hGb0 hGb ⊢
  rw [← hΓ] at hGb ⊢
  have hp := Real.pi_pos
  rcases (hGb0.trans hGb).eq_or_lt with h0 | hpos
  · have hG : Gb = 0 := le_antisymm (by rw [h0]; exact hGb) hGb0
    rw [← h0, hG]
    simp
  · have hr0 : 0 ≤ Gb / Γ := div_nonneg hGb0 hpos.le
    have hr1 : Gb / Γ ≤ 1 := (div_le_one hpos).mpr hGb
    have k := kappa_quad hr0 hr1
    calc Γ * kappa (Gb / Γ) ≤ Γ * (1 / π + Gb / Γ / 2 + (1 / 2 - 1 / π) * (Gb / Γ) ^ 2) :=
          mul_le_mul_of_nonneg_left k hpos.le
      _ = Γ - (3 / 2 - 2 / π) * (Γ - Gb) + (1 / 2 - 1 / π) * (Γ - Gb) ^ 2 / Γ := by
          field_simp
          ring

/-- The algebra of `eb_le_quad` (real numbers only). -/
private lemma eb_alg {P I R2 Γ S G0 δ w a σ₀ : ℝ} (hP0 : 0 ≤ P) (hw : 0 ≤ w)
    (hbe : P ≤ I + √Γ * w) (hJ : I ^ 2 ≤ R2) (hR2Γ : R2 ≤ Γ)
    (hquad : R2 ≤ Γ - (1 / 2 + 2 * a) * S + a * S ^ 2 / Γ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hσ : 0 < σ₀) (hS : σ₀ * G0 ≤ S) (hSΓ : S ≤ Γ) (hδ : 0 ≤ δ) (hΓle : Γ ≤ (1 + δ) * G0)
    (hG0pos : 0 < G0) :
    P ^ 2 ≤ ((1 + δ) * (1 + (2 * w + w ^ 2)) - (1 / 2 + 2 * a) * σ₀ +
      a * σ₀ ^ 2 / (1 + δ)) * G0 := by
  obtain ⟨S0, hS0⟩ : ∃ S0 : ℝ, S0 = σ₀ * G0 := ⟨_, rfl⟩
  rw [← hS0] at hS
  have hS0pos : 0 < S0 := by rw [hS0]; positivity
  have hΓpos : 0 < Γ := lt_of_lt_of_le (lt_of_lt_of_le hS0pos hS) hSΓ
  obtain ⟨G1, hG1⟩ : ∃ G1 : ℝ, G1 = (1 + δ) * G0 := ⟨_, rfl⟩
  rw [← hG1] at hΓle
  have hG1pos : 0 < G1 := lt_of_lt_of_le hΓpos hΓle
  have hsΓ : √Γ ^ 2 = Γ := Real.sq_sqrt hΓpos.le
  have hIΓ : I ≤ √Γ := Real.le_sqrt_of_sq_le (hJ.trans hR2Γ)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = √Γ := ⟨_, rfl⟩
  rw [← hr] at hsΓ hIΓ hbe
  have hr0 : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg _
  have hPsq : P ^ 2 ≤ R2 + Γ * (2 * w + w ^ 2) := by
    have h1 : P ^ 2 ≤ (I + r * w) ^ 2 := pow_le_pow_left₀ hP0 hbe 2
    have h2 : I * (r * w) ≤ r * (r * w) := mul_le_mul_of_nonneg_right hIΓ (mul_nonneg hr0 hw)
    have h3 : (I + r * w) ^ 2 = I ^ 2 + 2 * (I * (r * w)) + r ^ 2 * w ^ 2 := by ring
    have h4 : r * (r * w) = r ^ 2 * w := by ring
    rw [h4, hsΓ] at h2
    rw [h3, hsΓ] at h1
    have h5 : Γ * (2 * w + w ^ 2) = 2 * (Γ * w) + Γ * w ^ 2 := by ring
    linarith
  have st2 : a * S ^ 2 / Γ - (1 / 2 + 2 * a) * S ≤ a * S0 ^ 2 / Γ - (1 / 2 + 2 * a) * S0 := by
    have h1 : S ^ 2 - S0 ^ 2 ≤ 2 * Γ * (S - S0) := by nlinarith
    have h2 : (S ^ 2 - S0 ^ 2) / Γ ≤ 2 * (S - S0) := by
      rw [div_le_iff₀ hΓpos]; linarith
    have h3 : a * S ^ 2 / Γ - a * S0 ^ 2 / Γ = a * ((S ^ 2 - S0 ^ 2) / Γ) := by ring
    have h4 : a * ((S ^ 2 - S0 ^ 2) / Γ) ≤ a * (2 * (S - S0)) :=
      mul_le_mul_of_nonneg_left h2 ha0
    linarith
  have st3 : Γ + a * S0 ^ 2 / Γ ≤ G1 + a * S0 ^ 2 / G1 := by
    have h1 : a * S0 ^ 2 / Γ - a * S0 ^ 2 / G1 = a * S0 ^ 2 * (G1 - Γ) / (Γ * G1) := by
      field_simp
    have h2 : a * S0 ^ 2 * (G1 - Γ) / (Γ * G1) ≤ G1 - Γ := by
      rw [div_le_iff₀ (by positivity)]
      have h3 : S0 ^ 2 ≤ Γ * G1 := by nlinarith
      have h4 : a * S0 ^ 2 ≤ 1 * S0 ^ 2 := mul_le_mul_of_nonneg_right ha1 (sq_nonneg _)
      have h5 : a * S0 ^ 2 * (G1 - Γ) ≤ Γ * G1 * (G1 - Γ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      linarith
    linarith
  have hq0 : 0 ≤ 2 * w + w ^ 2 := by positivity
  have hΓq : Γ * (2 * w + w ^ 2) ≤ G1 * (2 * w + w ^ 2) := mul_le_mul_of_nonneg_right hΓle hq0
  have hfin : G1 + a * S0 ^ 2 / G1 - (1 / 2 + 2 * a) * S0 + G1 * (2 * w + w ^ 2) =
      ((1 + δ) * (1 + (2 * w + w ^ 2)) - (1 / 2 + 2 * a) * σ₀ + a * σ₀ ^ 2 / (1 + δ)) * G0 := by
    rw [hG1, hS0]
    have : (1 : ℝ) + δ ≠ 0 := by positivity
    field_simp
    ring
  linarith

/-- **The oracle centre energy, deterministic form** (Lemma EN (iii) with the quadratic bound of
`κ`): on `E_e` (`hE`), `E_sc` (`hsc`), `E_be` (`hbe`), with `θ_in ≥ θ_lo` (`hθ`),
`σ₀ = c_s θ_lo/2`, `q = 4√L_c/n + 4L_c/n²`:
`e_b° ≤ (1 + δ)(1 + q) − (3/2 − 2/π)σ₀ + (1/2 − 1/π)σ₀²/(1 + δ)`. -/
theorem eb_le_quad {n : ℕ} (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ) {Lc δ cs θlo : ℝ}
    (hρ : 0 < normSq c + (n : ℝ) * τ ^ 2) (hLc : 0 ≤ Lc) (hδ : 0 ≤ δ)
    (hE : |gO A₁ c τ - 2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)| ≤
      δ * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)))
    (hcs : 0 < cs) (hθl : 0 < θlo) (hsc : cs * τ ^ 2 ≤ sO2 A₁ c τ)
    (hθ : θlo ≤ (n : ℝ) * τ ^ 2 / (normSq c + (n : ℝ) * τ ^ 2))
    (hbe : Pb A₁ c τ A₂ ≤ ∫ A₂, Pb A₁ c τ A₂ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) +
      √(2 * Lc * (2 / ((mA n : ℕ) : ℝ)) * gO A₁ c τ)) :
    2 / ((mA n : ℕ) : ℝ) * normSq (bO A₁ A₂ c τ) / (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) ≤
      (1 + δ) * (1 + (4 * √Lc / (n : ℝ) + 4 * Lc / (n : ℝ) ^ 2)) -
        (3 / 2 - 2 / π) * (cs * θlo / 2) + (1 / 2 - 1 / π) * (cs * θlo / 2) ^ 2 / (1 + δ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ hn
  have hcast : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  obtain ⟨hi, -, hup⟩ := BstLean.Part153.rb_bounds hmA A₁ c τ
  have hquad := rb_quad hmA A₁ c τ
  have hJ := BstLean.Part133.sq_integral_le hi
  have hP0 := BstLean.Part153.Pb_nonneg A₁ c τ A₂
  have hΓ0 := BstLean.Part153.gO_nonneg' A₁ c τ
  have hs0 := BstLean.Part153.sO2_nonneg A₁ c τ
  have hSΓ : sO2 A₁ c τ ≤ gO A₁ c τ := by
    have h := BstLean.Part153.GamBar_nonneg A₁ c τ
    have e : sO2 A₁ c τ = gO A₁ c τ - 2 / ((mA n : ℕ) : ℝ) * normSq (hO A₁ c τ) := rfl
    linarith
  have hp := Real.pi_pos
  have hp3 := Real.pi_gt_three
  have hpi : 0 ≤ 1 - 1 / π := by
    have : 1 / π ≤ 1 := by rw [div_le_one hp]; linarith
    linarith
  have hR2Γ : ∫ A₂, Pb A₁ c τ A₂ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤
      gO A₁ c τ := by
    have := mul_nonneg hpi hs0
    linarith
  have hsL : √Lc ^ 2 = Lc := Real.sq_sqrt hLc
  have hsΓ : √(gO A₁ c τ) ^ 2 = gO A₁ c τ := Real.sq_sqrt hΓ0
  have hD : √(2 * Lc * (2 / ((mA n : ℕ) : ℝ)) * gO A₁ c τ) =
      √(gO A₁ c τ) * (2 * √Lc / (n : ℝ)) := by
    have e : 2 * Lc * (2 / ((mA n : ℕ) : ℝ)) * gO A₁ c τ =
        (√(gO A₁ c τ) * (2 * √Lc / (n : ℝ))) ^ 2 := by
      rw [hcast, mul_pow, div_pow, mul_pow, hsΓ, hsL]
      field_simp
    rw [e]
    exact Real.sqrt_sq (by positivity)
  rw [hD] at hbe
  have hτ : cs * θlo / 2 * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) ≤ cs * τ ^ 2 := by
    have h1 : θlo * (normSq c + (n : ℝ) * τ ^ 2) ≤ (n : ℝ) * τ ^ 2 := (le_div_iff₀ hρ).mp hθ
    have h2 : cs * θlo / 2 * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) =
        cs * (θlo * (normSq c + (n : ℝ) * τ ^ 2) / (n : ℝ)) := by
      field_simp
    rw [h2]
    refine mul_le_mul_of_nonneg_left ?_ hcs.le
    rw [div_le_iff₀ hnR]
    linarith
  have ha0 : (0 : ℝ) ≤ 1 / 2 - 1 / π := by
    have : 1 / π ≤ 1 / 2 := by rw [div_le_div_iff₀ hp (by norm_num)]; linarith
    linarith
  have ha1 : (1 : ℝ) / 2 - 1 / π ≤ 1 := by
    have : 0 ≤ 1 / π := by positivity
    linarith
  have hk : (3 : ℝ) / 2 - 2 / π = 1 / 2 + 2 * (1 / 2 - 1 / π) := by ring
  rw [hk] at hquad ⊢
  have hΓle : gO A₁ c τ ≤ (1 + δ) * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) := by
    have := (abs_le.mp hE).2
    linarith
  have key := eb_alg hP0 (show (0 : ℝ) ≤ 2 * √Lc / (n : ℝ) by positivity) hbe hJ hR2Γ hquad
    ha0 ha1 (show (0 : ℝ) < cs * θlo / 2 by positivity) (hτ.trans hsc) hSΓ hδ hΓle
    (by positivity)
  rw [← BstLean.Part153.Pb_sq, div_le_iff₀ (by positivity)]
  have e : 2 * (2 * √Lc / (n : ℝ)) + (2 * √Lc / (n : ℝ)) ^ 2 =
      4 * √Lc / (n : ℝ) + 4 * Lc / (n : ℝ) ^ 2 := by
    rw [div_pow, mul_pow, hsL]; ring
  rw [e] at key
  exact key

end rb

/-! ## The numbers for `n ≥ 16384`, `θ_in ≥ 0.46` -/

/-- The number of `eb_le_quad` at `δ = 11/1000`, `c_s = 0.95·2(1 − 1/π)`, `θ_lo = 0.46`,
`L_c = 12`, `n ≥ 16384` is at most `0.771`. -/
lemma ebO_num {n : ℕ} (hn : 16384 ≤ n) :
    (1 + 11 / 1000 : ℝ) * (1 + (4 * √12 / (n : ℝ) + 4 * 12 / (n : ℝ) ^ 2)) -
        (3 / 2 - 2 / π) * (csC * (46 / 100) / 2) +
        (1 / 2 - 1 / π) * (csC * (46 / 100) / 2) ^ 2 / (1 + 11 / 1000) ≤ 771 / 1000 := by
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have h12 : √(12 : ℝ) ≤ 4 := by
    rw [show (4 : ℝ) = √16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hq1 : 4 * √(12 : ℝ) / n ≤ 16 / 16384 := by
    rw [div_le_div_iff₀ hn0 (by norm_num)]
    nlinarith
  have hq2 : 4 * (12 : ℝ) / (n : ℝ) ^ 2 ≤ 48 / 16384 ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 1 / π := ⟨_, rfl⟩
  have hp1 : (31830 : ℝ) / 100000 ≤ p := by
    rw [hp, div_le_div_iff₀ (by norm_num) Real.pi_pos]
    nlinarith [Real.pi_lt_d4]
  have hp2 : p ≤ 31832 / 100000 := by
    rw [hp, div_le_div_iff₀ Real.pi_pos (by norm_num)]
    nlinarith [Real.pi_gt_d4]
  have hcs : csC = 95 / 100 * 2 * (1 - p) := by unfold csC; rw [hp]; norm_num
  have e2 : (2 : ℝ) / π = 2 * p := by rw [hp]; ring
  rw [hcs, e2, ← hp]
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 95 / 100 * 2 * (1 - p) * (46 / 100) / 2 := ⟨_, rfl⟩
  rw [← hs]
  have hs1 : (29789 : ℝ) / 100000 ≤ s := by rw [hs]; linarith
  have hs2 : s ≤ 29791 / 100000 := by rw [hs]; linarith
  have hks : (25718 : ℝ) / 100000 ≤ (3 / 2 - 2 * p) * s := by nlinarith
  have has : (1 / 2 - p) * s ^ 2 ≤ 16127 / 1000000 := by
    have h1 : s ^ 2 ≤ (29791 / 100000) ^ 2 := pow_le_pow_left₀ (by linarith) hs2 2
    have h2 : (0 : ℝ) ≤ s ^ 2 := sq_nonneg s
    nlinarith
  have has' : (1 / 2 - p) * s ^ 2 / (1 + 11 / 1000) ≤ 15952 / 1000000 := by
    rw [div_le_iff₀ (by norm_num)]
    linarith
  linarith

variable {n : ℕ}

/-- **The oracle centre energy on `GoodC16`** (`n ≥ 16384`, `θ_in ≥ 0.46`):
`e_b° = t_A|b′°|²/(γ_Aρ²) ≤ 0.771` (Part 154: `0.819`). -/
theorem ebO16 (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ}
    {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ} (h : (A₁, A₂) ∈ GoodC16 n n c τ) :
    2 / ((mA n : ℕ) : ℝ) * normSq (bO A₁ A₂ c τ) / (2 / (n : ℝ) * rhoC c τ ^ 2) ≤ 771 / 1000 := by
  have hn8 : 8192 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hm := BstLean.Part130.one_le_mA hn1
  have hAs : (A₁, A₂) ∈ GoodAs n c τ := h.1.1
  have hρ2 := rhoC_sqP c τ
  have hρ : 0 < normSq c + (n : ℝ) * τ ^ 2 := by
    have := rhoC_posP hn1 c hτ
    rw [← hρ2]; positivity
  have hE := BstLean.Part153.GoodA_energy hn8 hAs
  rw [BstLean.Part153.GamS_eq_gO hm] at hE
  have hsc0 := (BstLean.Part153.AStage_bounds hn8 hAs).2.2.2
  have hsc : csC * τ ^ 2 ≤ sO2 A₁ c τ := hsc0
  have hcs : 0 < csC := by
    have h1 : 1 / π < 1 := by
      rw [div_lt_one Real.pi_pos]
      linarith [Real.pi_gt_three]
    unfold csC
    exact mul_pos (by norm_num) (by linarith)
  have hθ : (46 / 100 : ℝ) ≤ (n : ℝ) * τ ^ 2 / (normSq c + (n : ℝ) * τ ^ 2) := by
    rw [← hρ2]; exact hθ0
  have hbe := BstLean.Part153.GoodA_be hAs
  have key := eb_le_quad hn1 A₁ A₂ c τ (Lc := 12) (δ := 11 / 1000) hρ (by norm_num)
    (by norm_num) hE hcs (by norm_num) hsc hθ hbe
  rw [hρ2]
  exact key.trans (ebO_num hn)

/-- **The energy of the computed centre on `GoodC16`** (`n ≥ 16384`, `0.46 ≤ θ_in ≤ 0.55`,
`b = bT n n/ρ`): `t_A|b|² ≤ γ_A·0.772` (Part 154, `centreVOK`: `0.82`). -/
theorem eb16 (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤ 2 / (n : ℝ) * (772 / 1000) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hρ := rhoC_posP hn1 c hτ
  obtain ⟨-, -, -, g4, -, -, -, -⟩ := BstLean.Part154.GoodC16_centre hn hn1 hτ h
    (BstLean.Part154.rhoBar_lt16 hn) (BstLean.Part154.eMP_le16 hn hθ0 hθ1) (θlo := 46 / 100) hθ0
  obtain ⟨hε0, hε⟩ := BstLean.Part154.epsJ_le16 hn
  have hO := ebO16 hn hτ hθ0 h
  have hrn : (128 : ℝ) ≤ √(n : ℝ) := by
    rw [show (128 : ℝ) = √(128 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num; linarith)
  have hrn0 : 0 < √(n : ℝ) := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = √(2 / ((mA n : ℕ) : ℝ)) := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := by rw [hs]; exact Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 2 / ((mA n : ℕ) : ℝ) := by rw [hs]; exact Real.sq_sqrt (by positivity)
  obtain ⟨g, hg⟩ : ∃ g : ℝ, g = √(2 / (n : ℝ)) := ⟨_, rfl⟩
  have hg0 : 0 < g := by rw [hg]; exact Real.sqrt_pos.mpr (by positivity)
  have hg2 : g ^ 2 = 2 / (n : ℝ) := by rw [hg]; exact Real.sq_sqrt (by positivity)
  have hX : √(2 / (n : ℝ) / n) = g / √(n : ℝ) := by
    rw [hg, Real.sqrt_div (by positivity)]
  rw [← hs, hX] at g4
  obtain ⟨bo, hbo⟩ : ∃ bo, bo = bO A₁ A₂ c τ := ⟨_, rfl⟩
  obtain ⟨bt, hbt⟩ : ∃ bt, bt = bT n n A₁ A₂ c τ := ⟨_, rfl⟩
  obtain ⟨ρ, hρd⟩ : ∃ ρ : ℝ, ρ = rhoC c τ := ⟨_, rfl⟩
  rw [← hbo, ← hbt, ← hρd] at g4
  rw [← hbo, ← hρd] at hO
  rw [← hbt, ← hρd]
  rw [← hρd] at hρ
  have hρi : 0 < 1 / ρ := by positivity
  -- the oracle part
  have h1 : s * nrm ((1 / ρ) • bo) ≤ g * (87808 / 100000) := by
    have h0 : 0 ≤ s * nrm ((1 / ρ) • bo) := mul_nonneg hs0 (BstLean.Part153.nrm_nonneg _)
    refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
    rw [mul_pow, hs2, BstLean.Part153.nrm_sq, mul_pow, hg2]
    have e : normSq ((1 / ρ) • bo) = normSq bo / ρ ^ 2 := by
      unfold normSq
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      field_simp
    rw [e]
    have h2 : 2 / ((mA n : ℕ) : ℝ) * normSq bo ≤ 771 / 1000 * (2 / (n : ℝ) * ρ ^ 2) :=
      (div_le_iff₀ (by positivity)).mp hO
    have h3 : 2 / ((mA n : ℕ) : ℝ) * (normSq bo / ρ ^ 2) =
        2 / ((mA n : ℕ) : ℝ) * normSq bo / ρ ^ 2 := by ring
    rw [h3, div_le_iff₀ (by positivity)]
    have h4 : (0 : ℝ) ≤ 2 / (n : ℝ) * ρ ^ 2 := by positivity
    nlinarith
  -- the difference
  have h2 : s * nrm ((1 / ρ) • bt - (1 / ρ) • bo) ≤ g * (6 / 100000) := by
    have e : (1 / ρ) • bt - (1 / ρ) • bo = (1 / ρ) • (bt - bo) := by rw [smul_sub]
    rw [e, BstLean.Part153.nrm_smul, abs_of_pos hρi]
    have e2 : s * (1 / ρ * nrm (bt - bo)) = s * nrm (bt - bo) / ρ := by ring
    rw [e2]
    refine g4.trans ?_
    have h3 : BstLean.Part150.epsJ n n n (BstLean.Part153.wn n) csC (11 / 1000)
        (BstLean.Part154.deltaChi n 12) * (g / √(n : ℝ)) ≤ 75 / 10000 * (g / √(n : ℝ)) :=
      mul_le_mul_of_nonneg_right hε (by positivity)
    refine h3.trans ?_
    rw [show (75 : ℝ) / 10000 * (g / √(n : ℝ)) = g * (75 / 10000 / √(n : ℝ)) by ring]
    refine mul_le_mul_of_nonneg_left ?_ hg0.le
    rw [div_le_iff₀ hrn0]
    linarith
  have h3 : s * nrm ((1 / ρ) • bt) ≤ g * (87814 / 100000) := by
    have e : (1 / ρ) • bt = (1 / ρ) • bo + ((1 / ρ) • bt - (1 / ρ) • bo) := by abel
    have h4 := BstLean.Part153.nrm_add_le ((1 / ρ) • bo) ((1 / ρ) • bt - (1 / ρ) • bo)
    rw [← e] at h4
    have h5 := mul_le_mul_of_nonneg_left h4 hs0
    linarith
  have h4 := pow_le_pow_left₀ (mul_nonneg hs0 (BstLean.Part153.nrm_nonneg _)) h3 2
  rw [mul_pow, hs2, BstLean.Part153.nrm_sq, mul_pow, hg2] at h4
  have h5 : (0 : ℝ) ≤ 2 / (n : ℝ) := by positivity
  have hcast : ((mA n : ℕ) : ℝ) = (mA n : ℝ) := rfl
  nlinarith

end BstLean.Part160

open BstLean.Part160 in
#print axioms kappa_quad
open BstLean.Part160 in
#print axioms rb_quad
open BstLean.Part160 in
#print axioms eb_le_quad
open BstLean.Part160 in
#print axioms ebO16
open BstLean.Part160 in
#print axioms eb16
