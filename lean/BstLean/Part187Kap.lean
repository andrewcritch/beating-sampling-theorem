import BstLean.Part160ScTab
import BstLean.Part159Kap

/-!
# Part 187 (file `Kap`): the centre energy `e_b` with the exact arc-cosine kernel at one point

No proof is left open; no `native_decide` or `axiom` is used.

Part 160 (`eb_le_quad`) bounds `e_b°` through the quadratic surrogate
`κ(r) ≤ 1/π + r/2 + (1/2 − 1/π) r²`. Here the exact identity `E 𝖯_b² = Γ κ(Γ̄/Γ)` (Part 153,
`rb_eq`) is used with the monotonicity of `κ` only:

* `arcsin_le_pi6_add`: `arcsin r ≤ π/6 + d` when `r ≤ (1/2)(1 − d²/2) + (√3/2)(d − d³/6)`
  (`sin(π/6 + d)` bounded below by `cos d ≥ 1 − d²/2` and `sin d ≥ d − d³/6`).
* `kappa_le_pi6`: then `κ(r) ≤ √(1 − r²)/π + r(2/3 + d/π)`.
* `eb_le_kap`: on the events of `eb_le_quad`, `e_b° ≤ (1 + δ)(K + q)` for every `K ≥ κ(1 − σ₀/(1 + δ))`,
  `σ₀ = c_s θ_lo/2`, `q = 4√L_c/n + 4L_c/n²`.
* `eb16K_gen`: the computed-centre bound `t_A|b|² ≤ γ_A·Eb` on `GoodC16 ∩ SSc` for
  `θ_lo ≤ θ_in ≤ 0.55`, `n ≥ 16 384`, with free numbers (the analogue of `eb16_sharp_gen`).
-/

namespace BstLean.Part187

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part150
open BstLean.Part153 (nrm Pb GoodAs)
open BstLean.Part154 (GoodC16)

/-- **An upper bound of `arcsin`** near `1/2`. -/
theorem arcsin_le_pi6_add {r d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hr : r ≤ 1 / 2 * (1 - d ^ 2 / 2) + √3 / 2 * (d - d ^ 3 / 6)) :
    arcsin r ≤ π / 6 + d := by
  have hp := Real.pi_gt_three
  have hs : 1 / 2 * (1 - d ^ 2 / 2) + √3 / 2 * (d - d ^ 3 / 6) ≤ Real.sin (π / 6 + d) := by
    rw [Real.sin_add, Real.sin_pi_div_six, Real.cos_pi_div_six]
    have h1 := Real.one_sub_sq_div_two_le_cos (x := d)
    have h2 := (Real.sin_gt_sub_cube hd0).le
    have h3 : (0 : ℝ) ≤ √3 / 2 := by positivity
    have h4 := mul_le_mul_of_nonneg_left h2 h3
    nlinarith
  calc arcsin r ≤ arcsin (Real.sin (π / 6 + d)) := Real.arcsin_le_arcsin (hr.trans hs)
    _ = π / 6 + d := Real.arcsin_sin (by linarith) (by linarith)

/-- **An upper bound of `κ`** at one point: `κ(r) ≤ √(1 − r²)/π + r(2/3 + d/π)`. -/
theorem kappa_le_pi6 {r d : ℝ} (hr0 : 0 ≤ r) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hr : r ≤ 1 / 2 * (1 - d ^ 2 / 2) + √3 / 2 * (d - d ^ 3 / 6)) :
    kappa r ≤ √(1 - r ^ 2) / π + r * (2 / 3 + d / π) := by
  have hp := Real.pi_pos
  have ha := arcsin_le_pi6_add hd0 hd1 hr
  rw [BstLean.Part159.kappa_arcsin]
  have h1 : r * (π / 2 + arcsin r) ≤ r * (π / 2 + (π / 6 + d)) :=
    mul_le_mul_of_nonneg_left (by linarith) hr0
  have e : √(1 - r ^ 2) / π + r * (2 / 3 + d / π) =
      (√(1 - r ^ 2) + r * (π / 2 + (π / 6 + d))) / π := by
    field_simp
    ring
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith) hp.le

section rb

variable {n m : ℕ}

/-- **The oracle centre energy with the exact kernel** (deterministic form; the events and the
hypotheses of `BstLean.Part160.eb_le_quad`): `e_b° ≤ (1 + δ)(K + q)` for every
`K ≥ κ(1 − σ₀/(1 + δ))`, `σ₀ = c_s θ_lo/2`, `q = 4√L_c/n + 4L_c/n²`. -/
theorem eb_le_kap (hn : 1 ≤ n) (A₁ : Matrix (Fin (mA n)) (Fin n) ℝ)
    (A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ) (c : Fin n → ℝ) (τ : ℝ) {Lc δ cs θlo K : ℝ}
    (hρ : 0 < normSq c + (n : ℝ) * τ ^ 2) (hLc : 0 ≤ Lc) (hδ : 0 ≤ δ)
    (hE : |gO A₁ c τ - 2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)| ≤
      δ * (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)))
    (hcs : 0 < cs) (hθl : 0 < θlo) (hsc : cs * τ ^ 2 ≤ sO2 A₁ c τ)
    (hθ : θlo ≤ (n : ℝ) * τ ^ 2 / (normSq c + (n : ℝ) * τ ^ 2))
    (hbe : Pb A₁ c τ A₂ ≤ ∫ A₂, Pb A₁ c τ A₂ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) +
      √(2 * Lc * (2 / ((mA n : ℕ) : ℝ)) * gO A₁ c τ))
    (hσ1 : cs * θlo / 2 ≤ 1 + δ)
    (hK : kappa (1 - cs * θlo / 2 / (1 + δ)) ≤ K) :
    2 / ((mA n : ℕ) : ℝ) * normSq (bO A₁ A₂ c τ) / (2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2)) ≤
      (1 + δ) * (K + (4 * √Lc / (n : ℝ) + 4 * Lc / (n : ℝ) ^ 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ hn
  have hcast : ((mA n : ℕ) : ℝ) = (n : ℝ) ^ 2 := by unfold mA; push_cast; ring
  obtain ⟨hi, he⟩ := BstLean.Part153.rb_eq hmA A₁ c τ
  have hJ := BstLean.Part133.sq_integral_le hi
  have hP0 := BstLean.Part153.Pb_nonneg A₁ c τ A₂
  have hGb0 := BstLean.Part153.GamBar_nonneg A₁ c τ
  have hGb := BstLean.Part153.GamBar_le A₁ c τ
  have hs0 := BstLean.Part153.sO2_nonneg A₁ c τ
  have hS : sO2 A₁ c τ = gO A₁ c τ - 2 / ((mA n : ℕ) : ℝ) * normSq (hO A₁ c τ) := rfl
  have hsL : √Lc ^ 2 = Lc := Real.sq_sqrt hLc
  -- names
  obtain ⟨G0, hG0⟩ : ∃ G0 : ℝ, G0 = 2 / (n : ℝ) * (normSq c + (n : ℝ) * τ ^ 2) := ⟨_, rfl⟩
  have hG0pos : 0 < G0 := by rw [hG0]; positivity
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : ℝ, σ₀ = cs * θlo / 2 := ⟨_, rfl⟩
  have hσpos : 0 < σ₀ := by rw [hσ₀]; positivity
  rw [← hσ₀] at hσ1 hK
  rw [← hG0] at hE
  -- `s_h² ≥ σ₀ G0`
  have hτ : σ₀ * G0 ≤ cs * τ ^ 2 := by
    have h1 : θlo * (normSq c + (n : ℝ) * τ ^ 2) ≤ (n : ℝ) * τ ^ 2 := (le_div_iff₀ hρ).mp hθ
    have h2 : σ₀ * G0 = cs * (θlo * (normSq c + (n : ℝ) * τ ^ 2) / (n : ℝ)) := by
      rw [hσ₀, hG0]; field_simp
    rw [h2]
    refine mul_le_mul_of_nonneg_left ?_ hcs.le
    rw [div_le_iff₀ hnR]
    linarith
  have hSlo : σ₀ * G0 ≤ sO2 A₁ c τ := hτ.trans hsc
  have hΓle : gO A₁ c τ ≤ (1 + δ) * G0 := by
    have := (abs_le.mp hE).2
    linarith
  obtain ⟨Γ, hΓ⟩ : ∃ Γ : ℝ, Γ = gO A₁ c τ := ⟨_, rfl⟩
  obtain ⟨Gb, hGbd⟩ : ∃ Gb : ℝ, Gb = 2 / ((mA n : ℕ) : ℝ) * normSq (hO A₁ c τ) := ⟨_, rfl⟩
  rw [← hΓ, ← hGbd] at hS
  rw [← hΓ] at hΓle he hbe
  rw [← hGbd] at he hGb0 hGb
  rw [← hΓ] at hGb
  have hΓpos : 0 < Γ := by
    have : 0 < σ₀ * G0 := by positivity
    have h2 : sO2 A₁ c τ ≤ Γ := by rw [hS]; linarith
    linarith
  -- the kernel argument: `Γ̄/Γ ≤ 1 − σ₀/(1 + δ)`
  have hr0 : 0 ≤ Gb / Γ := div_nonneg hGb0 hΓpos.le
  have hr1 : Gb / Γ ≤ 1 - σ₀ / (1 + δ) := by
    have h1 : Gb / Γ = 1 - sO2 A₁ c τ / Γ := by
      rw [hS, sub_div, div_self hΓpos.ne']; ring
    rw [h1]
    have h2 : σ₀ / (1 + δ) ≤ sO2 A₁ c τ / Γ := by
      rw [div_le_div_iff₀ (by positivity) hΓpos]
      have h3 : σ₀ * Γ ≤ σ₀ * ((1 + δ) * G0) := mul_le_mul_of_nonneg_left hΓle hσpos.le
      nlinarith
    linarith
  have hrm1 : 1 - σ₀ / (1 + δ) ≤ 1 := by
    have : 0 ≤ σ₀ / (1 + δ) := by positivity
    linarith
  have hrm0 : -1 ≤ 1 - σ₀ / (1 + δ) := by
    have : σ₀ / (1 + δ) ≤ 1 := (div_le_one (by positivity)).mpr hσ1
    linarith
  have hkm : kappa (Gb / Γ) ≤ kappa (1 - σ₀ / (1 + δ)) :=
    kappa_monotoneOn ⟨by linarith, hr1.trans hrm1⟩ ⟨hrm0, hrm1⟩ hr1
  have hK0 : 0 ≤ K := ((kappa_mem (by linarith) (hr1.trans hrm1)).1.trans hkm).trans hK
  have hR2 : ∫ A₂, Pb A₁ c τ A₂ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤
      (1 + δ) * G0 * K := by
    rw [he]
    calc Γ * kappa (Gb / Γ) ≤ Γ * K := mul_le_mul_of_nonneg_left (hkm.trans hK) hΓpos.le
      _ ≤ (1 + δ) * G0 * K := mul_le_mul_of_nonneg_right hΓle hK0
  have hR2Γ : ∫ A₂, Pb A₁ c τ A₂ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) ≤ Γ := by
    rw [he]
    have := (kappa_mem (by linarith) (hr1.trans hrm1)).2
    nlinarith
  -- the deviation
  have hsΓ : √Γ ^ 2 = Γ := Real.sq_sqrt hΓpos.le
  have hD : √(2 * Lc * (2 / ((mA n : ℕ) : ℝ)) * Γ) = √Γ * (2 * √Lc / (n : ℝ)) := by
    have e : 2 * Lc * (2 / ((mA n : ℕ) : ℝ)) * Γ = (√Γ * (2 * √Lc / (n : ℝ))) ^ 2 := by
      rw [hcast, mul_pow, div_pow, mul_pow, hsΓ, hsL]
      field_simp
    rw [e]
    exact Real.sqrt_sq (by positivity)
  rw [hD] at hbe
  obtain ⟨I, hI⟩ : ∃ I : ℝ, I = ∫ A₂, Pb A₁ c τ A₂ ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) :=
    ⟨_, rfl⟩
  obtain ⟨R2, hR2d⟩ : ∃ R2 : ℝ,
      R2 = ∫ A₂, Pb A₁ c τ A₂ ^ 2 ∂gaussMat (mA n) (mA n) (2 / ((mA n : ℕ) : ℝ)) := ⟨_, rfl⟩
  rw [← hI] at hbe hJ
  rw [← hR2d] at hJ hR2 hR2Γ
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = 2 * √Lc / (n : ℝ) := ⟨_, rfl⟩
  rw [← hw] at hbe
  have hw0 : 0 ≤ w := by rw [hw]; positivity
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = √Γ := ⟨_, rfl⟩
  rw [← hr] at hsΓ hbe
  have hr00 : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg _
  have hIΓ : I ≤ r := by rw [hr]; exact Real.le_sqrt_of_sq_le (hJ.trans hR2Γ)
  have hPsq : Pb A₁ c τ A₂ ^ 2 ≤ R2 + Γ * (2 * w + w ^ 2) := by
    have h1 : Pb A₁ c τ A₂ ^ 2 ≤ (I + r * w) ^ 2 := pow_le_pow_left₀ hP0 hbe 2
    have h2 : I * (r * w) ≤ r * (r * w) := mul_le_mul_of_nonneg_right hIΓ (mul_nonneg hr00 hw0)
    have h3 : (I + r * w) ^ 2 = I ^ 2 + 2 * (I * (r * w)) + r ^ 2 * w ^ 2 := by ring
    have h4 : r * (r * w) = r ^ 2 * w := by ring
    rw [h4, hsΓ] at h2
    rw [h3, hsΓ] at h1
    have h5 : Γ * (2 * w + w ^ 2) = 2 * (Γ * w) + Γ * w ^ 2 := by ring
    linarith
  have hq0 : 0 ≤ 2 * w + w ^ 2 := by positivity
  have hΓq : Γ * (2 * w + w ^ 2) ≤ (1 + δ) * G0 * (2 * w + w ^ 2) :=
    mul_le_mul_of_nonneg_right hΓle hq0
  rw [← BstLean.Part153.Pb_sq, ← hG0, div_le_iff₀ hG0pos]
  have e : 2 * w + w ^ 2 = 4 * √Lc / (n : ℝ) + 4 * Lc / (n : ℝ) ^ 2 := by
    rw [hw, div_pow, mul_pow, hsL]; ring
  rw [← e]
  have e2 : (1 + δ) * (K + (2 * w + w ^ 2)) * G0 =
      (1 + δ) * G0 * K + (1 + δ) * G0 * (2 * w + w ^ 2) := by ring
  rw [e2]
  linarith

end rb

/-- The numbers of `eb_le_kap` at `δ = 1/1000`, `L_c = 12`, `n ≥ 16 384`. -/
lemma ebK_num {n : ℕ} (hn : 16384 ≤ n) {K Eo : ℝ}
    (hE : (1001 / 1000 : ℝ) * (K + 16 / 16384 + 48 / 16384 ^ 2) ≤ Eo) :
    (1 + 1 / 1000 : ℝ) * (K + (4 * √12 / (n : ℝ) + 4 * 12 / (n : ℝ) ^ 2)) ≤ Eo := by
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
  nlinarith

/-- **The κ number at one point**: `κ(r) ≤ K` from `√3 ≥ 1.732`, `π ≥ 3.14159`, an upper bound
`S` of `√(1 − r²)` and the `arcsin` step `d`. -/
lemma kappa_le_num {r d S K : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hr : r ≤ 1 / 2 * (1 - d ^ 2 / 2) + 1732 / 1000 / 2 * (d - d ^ 3 / 6))
    (hS0 : 0 ≤ S) (hS : 1 - r ^ 2 ≤ S ^ 2)
    (hK : S / (314159 / 100000) + r * (2 / 3 + d / (314159 / 100000)) ≤ K) :
    kappa r ≤ K := by
  have hp := Real.pi_gt_d6
  have hp0 := Real.pi_pos
  have h3 : (1732 / 1000 : ℝ) ≤ √3 := by
    rw [show (1732 / 1000 : ℝ) = √((1732 / 1000) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hdd : 0 ≤ d - d ^ 3 / 6 := by nlinarith
  have hr' : r ≤ 1 / 2 * (1 - d ^ 2 / 2) + √3 / 2 * (d - d ^ 3 / 6) := by
    have : 1732 / 1000 / 2 * (d - d ^ 3 / 6) ≤ √3 / 2 * (d - d ^ 3 / 6) :=
      mul_le_mul_of_nonneg_right (by linarith) hdd
    linarith
  have hk := kappa_le_pi6 hr0 hd0 hd1 hr'
  have hsq : √(1 - r ^ 2) ≤ S := by
    rw [show S = √(S ^ 2) by rw [Real.sqrt_sq hS0]]
    exact Real.sqrt_le_sqrt hS
  have h1 : √(1 - r ^ 2) / π ≤ S / (314159 / 100000) := by
    calc √(1 - r ^ 2) / π ≤ S / π := div_le_div_of_nonneg_right hsq hp0.le
      _ ≤ S / (314159 / 100000) := div_le_div_of_nonneg_left hS0 (by norm_num) (by linarith)
  have h2 : r * (2 / 3 + d / π) ≤ r * (2 / 3 + d / (314159 / 100000)) := by
    refine mul_le_mul_of_nonneg_left ?_ hr0
    have : d / π ≤ d / (314159 / 100000) := div_le_div_of_nonneg_left hd0.le (by norm_num) (by linarith)
    linarith
  linarith

/-- **The computed-centre energy with the exact kernel** on `GoodC16` and `SSc` for
`θ_lo ≤ θ_in ≤ 0.55`, `n ≥ 16 384`, with free numbers (the analogue of
`BstLean.Part160.eb16_sharp_gen`; the quadratic surrogate is replaced by `κ(1 − X/1.001) ≤ K`). -/
theorem eb16K_gen {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    {θlo K' X d S K Eo e Eb : ℝ}
    (hlo : 46 / 100 ≤ θlo) (hlo1 : θlo ≤ 1) (hθ0 : θlo ≤ thetaC c τ)
    (hθ1 : thetaC c τ ≤ 55 / 100)
    (hK' : (1 - θlo) * (1 - θlo + 55 / 100 / 16384) / ((1 - 3 / 100) ^ 2 * (99996 / 100000)) +
      (1 - θlo) * (1504 / 10 ^ 6) ^ 2 + 55 / 100 / 16384 ≤ K')
    (hX0 : 0 < X)
    (hX : X ≤ 95 / 100 * (1 - 31832 / 100000 - (1 - θlo) / 2 - (1 / 2 - 3183 / 10000) * K'))
    (hX1 : X ≤ 1001 / 1000)
    (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hr : 1 - X / (1001 / 1000) ≤ 1 / 2 * (1 - d ^ 2 / 2) + 1732 / 1000 / 2 * (d - d ^ 3 / 6))
    (hS0 : 0 ≤ S) (hS : 1 - (1 - X / (1001 / 1000)) ^ 2 ≤ S ^ 2)
    (hK : S / (314159 / 100000) + (1 - X / (1001 / 1000)) * (2 / 3 + d / (314159 / 100000)) ≤ K)
    (hEo : (1001 / 1000 : ℝ) * (K + 16 / 16384 + 48 / 16384 ^ 2) ≤ Eo)
    (he : 0 ≤ e) (hEe : Eo ≤ e ^ 2) (hEb : (e + 6 / 100000) ^ 2 ≤ Eb)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS' : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤ 2 / (n : ℝ) * Eb := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hAs : (A₁, A₂) ∈ GoodAs n c τ := h.1.1
  have hρ2 := rhoC_sqP c τ
  have hρ : 0 < normSq c + (n : ℝ) * τ ^ 2 := by
    have := rhoC_posP hn1 c hτ
    rw [← hρ2]; positivity
  have hE := BstLean.Part160.energy16 hn hAs
  have hs := BstLean.Part160.sO2_ge_gen hn hτ hlo hlo1 hθ0 hθ1 hK' hX hS'
  have hbe := BstLean.Part153.GoodA_be hAs
  have hrr0 : 0 ≤ 1 - X / (1001 / 1000) := by
    have : X / (1001 / 1000) ≤ 1 := by rw [div_le_one (by norm_num)]; exact hX1
    linarith
  have hrr1 : 1 - X / (1001 / 1000) ≤ 1 := by
    have : 0 ≤ X / (1001 / 1000) := by positivity
    linarith
  have hKk := kappa_le_num hrr0 hrr1 hd0 hd1 hr hS0 hS hK
  have hO : 2 / ((mA n : ℕ) : ℝ) * normSq (bO A₁ A₂ c τ) / (2 / (n : ℝ) * rhoC c τ ^ 2) ≤ Eo := by
    obtain ⟨R, hR⟩ : ∃ R : ℝ, R = normSq c + (n : ℝ) * τ ^ 2 := ⟨_, rfl⟩
    have hτ2 : 0 < τ ^ 2 := by positivity
    rw [hρ2, ← hR]
    rw [← hR] at hρ hE hs
    obtain ⟨θ, hθd⟩ : ∃ θ : ℝ, θ = (n : ℝ) * τ ^ 2 / R := ⟨_, rfl⟩
    have hθpos : 0 < θ := by rw [hθd]; positivity
    have hsc : 2 * X / θ * τ ^ 2 ≤ sO2 A₁ c τ := by
      refine le_trans (le_of_eq ?_) hs
      rw [hθd]; field_simp
    have ex : 2 * X / θ * θ / 2 = X := by field_simp
    have key := eb_le_kap hn1 A₁ A₂ c τ (Lc := 12) (δ := 1 / 1000) (cs := 2 * X / θ)
      (θlo := θ) (K := K) (by rw [← hR]; exact hρ) (by norm_num) (by norm_num)
      (by rw [← hR]; exact hE) (by positivity) hθpos hsc (by rw [← hR, hθd]) hbe
      (by rw [ex]; linarith) (by rw [ex]; norm_num; norm_num at hKk; exact hKk)
    rw [← hR] at key
    exact key.trans (ebK_num hn hEo)
  have h1 := BstLean.Part160.eb_transfer hn hτ (hlo.trans hθ0) hθ1 h hO he hEe
  exact h1.trans (mul_le_mul_of_nonneg_left hEb (by positivity))

/-! ## The table for `n ≥ 16 384` (numbers chosen outside Lean; Lean checks them) -/

/-- `t_A|b|² ≤ 0.72441·γ_A` on `GoodC16` and `SSc` for `46/100 ≤ θ_in ≤ 0.55` (exact kernel;
Part 160 `eb16_sharp_46` has the quadratic surrogate). -/
theorem eb16K_46 {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 46 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (72441 / 100000) :=
  eb16K_gen hn hτ (θlo := 46 / 100) (K' := 309983 / 1000000) (X := 84397 / 250000) (d := 201 / 1000)
    (S := 374421 / 500000) (K := 3613 / 5000) (Eo := 724301 / 1000000) (e := 851059 / 1000000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

/-- `t_A|b|² ≤ 0.71952·γ_A` on `GoodC16` and `SSc` for `47/100 ≤ θ_in ≤ 0.55` (exact kernel;
Part 160 `eb16_sharp_47` has the quadratic surrogate). -/
theorem eb16K_47 {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 47 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (4497 / 6250) :=
  eb16K_gen hn hτ (θlo := 47 / 100) (K' := 29861 / 100000) (X := 344301 / 1000000) (d := 1921 / 10000)
    (S := 188681 / 250000) (K := 358857 / 500000) (Eo := 71941 / 100000) (e := 848181 / 1000000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

/-- `t_A|b|² ≤ 0.71467·γ_A` on `GoodC16` and `SSc` for `48/100 ≤ θ_in ≤ 0.55` (exact kernel;
Part 160 `eb16_sharp_48` has the quadratic surrogate). -/
theorem eb16K_48 {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 48 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (71467 / 100000) :=
  eb16K_gen hn hτ (θlo := 48 / 100) (K' := 5749 / 20000) (X := 350977 / 1000000) (d := 1833 / 10000)
    (S := 76047 / 100000) (K := 71287 / 100000) (Eo := 714561 / 1000000) (e := 422659 / 500000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

/-- `t_A|b|² ≤ 0.70986·γ_A` on `GoodC16` and `SSc` for `49/100 ≤ θ_in ≤ 0.55` (exact kernel;
Part 160 `eb16_sharp_49` has the quadratic surrogate). -/
theorem eb16K_49 {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 49 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (35493 / 50000) :=
  eb16K_gen hn hτ (θlo := 49 / 100) (K' := 138251 / 500000) (X := 357617 / 1000000) (d := 873 / 5000)
    (S := 153217 / 200000) (K := 177017 / 250000) (Eo := 354877 / 500000) (e := 842469 / 1000000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

/-- `t_A|b|² ≤ 0.70510·γ_A` on `GoodC16` and `SSc` for `50/100 ≤ θ_in ≤ 0.55` (exact kernel;
Part 160 `eb16_sharp_50` has the quadratic surrogate). -/
theorem eb16K_50 {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 50 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (7051 / 10000) :=
  eb16K_gen hn hτ (θlo := 50 / 100) (K' := 265767 / 1000000) (X := 18211 / 50000) (d := 83 / 500)
    (S := 771571 / 1000000) (K := 703309 / 1000000) (Eo := 704991 / 1000000) (e := 419819 / 500000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

/-- `t_A|b|² ≤ 0.70037·γ_A` on `GoodC16` and `SSc` for `51/100 ≤ θ_in ≤ 0.55` (exact kernel;
Part 160 `eb16_sharp_51` has the quadratic surrogate). -/
theorem eb16K_51 {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 51 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (70037 / 100000) :=
  eb16K_gen hn hτ (θlo := 51 / 100) (K' := 63811 / 250000) (X := 370787 / 1000000) (d := 63 / 400)
    (S := 776933 / 1000000) (K := 21831 / 31250) (Eo := 700269 / 1000000) (e := 836821 / 1000000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

/-- `t_A|b|² ≤ 0.69570·γ_A` on `GoodC16` and `SSc` for `52/100 ≤ θ_in ≤ 0.55` (exact kernel;
Part 160 `eb16_sharp_52` has the quadratic surrogate). -/
theorem eb16K_52 {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 52 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (6957 / 10000) :=
  eb16K_gen hn hτ (θlo := 52 / 100) (K' := 122467 / 500000) (X := 94329 / 250000) (d := 1491 / 10000)
    (S := 391087 / 500000) (K := 693919 / 1000000) (Eo := 695591 / 1000000) (e := 834021 / 1000000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

/-- `t_A|b|² ≤ 0.69108·γ_A` on `GoodC16` and `SSc` for `53/100 ≤ θ_in ≤ 0.55` (exact kernel;
Part 160 `eb16_sharp_53` has the quadratic surrogate). -/
theorem eb16K_53 {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 53 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (17277 / 25000) :=
  eb16K_gen hn hτ (θlo := 53 / 100) (K' := 234837 / 1000000) (X := 383809 / 1000000) (d := 1409 / 10000)
    (S := 787297 / 1000000) (K := 172327 / 250000) (Eo := 21593 / 31250) (e := 133 / 160)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

/-- `t_A|b|² ≤ 0.68649·γ_A` on `GoodC16` and `SSc` for `54/100 ≤ θ_in ≤ 0.55` (exact kernel;
Part 160 `eb16_sharp_54` has the quadratic surrogate). -/
theorem eb16K_54 {n : ℕ} (hn : 16384 ≤ n) {c : Fin n → ℝ} {τ : ℝ} (hτ : 0 < τ)
    (hθ0 : 54 / 100 ≤ thetaC c τ) (hθ1 : thetaC c τ ≤ 55 / 100)
    {A₁ : Matrix (Fin (mA n)) (Fin n) ℝ} {A₂ : Matrix (Fin (mA n)) (Fin (mA n)) ℝ}
    (h : (A₁, A₂) ∈ GoodC16 n n c τ) (hS : ((c, τ), (A₁, A₂)) ∈ BstLean.Part160.SSc n) :
    2 / (mA n : ℝ) * normSq ((1 / rhoC c τ) • bT n n A₁ A₂ c τ) ≤
      2 / (n : ℝ) * (68649 / 100000) :=
  eb16K_gen hn hτ (θlo := 54 / 100) (K' := 28119 / 125000) (X := 78053 / 200000) (d := 1327 / 10000)
    (S := 396153 / 500000) (K := 684721 / 1000000) (Eo := 42899 / 62500) (e := 828483 / 1000000)
    (by norm_num) (by norm_num) hθ0 hθ1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) h hS

end BstLean.Part187

#print axioms BstLean.Part187.eb16K_46
#print axioms BstLean.Part187.eb_le_kap
