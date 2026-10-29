import BstLean.Part138Mix

/-!
# Part 138, item 3: the cheap stand-in of the World network, for fixed `(M₁, M₂)`

Role: `delegations/statements/p138-spec.md`. Paper sources: `onW16c-cx.md` §§4–5,
`onW5-opus-prover.md` §4.5. The centre is the exact mean hidden vector `h̄` of Parts 134, 136
(NOT the arithmetic centre of the programs).

`N = 2n`, `m = mW n`, `t = 2/m`, `θ = (M₁, M₂)`, `h̄ = hbarW θ`, `w`, `w̄`, `G_ζ` of Part 137.

* `tau0 N m θ = √(t|h̄|²·w̄(θ))`: **the constant scalar `τ₀` of the cheap stand-in**.
* `wLow = 1/0.494 − 1`: the lower bound of `w̄` on `good136 n`.
* `zetaP ζ = ζ(3 + ζ)/(0.4936(1 − ζ)²)`: the paper's `ζ′`; `rLow ζ = max 0 (1 − ζ′/wLow)`:
  the paper's `r_low` for the constant `w₀ = w̄`; `cRho ζ = (1 + √r_low)²(1 + r_low)`.
* `Kfun n ζ (u, θ)`: `n(w − w̄)²/(wLow²·cRho ζ)` on `G_ζ`, and `1` off `G_ζ`.
* `Hbar n ζ θ = E_u Kfun n ζ (u, θ)`: the bound of the mean squared Hellinger distance of the
  exact and the cheap stand-in at `θ` (it does not depend on `M₃`).
* `good_pt`: on `good136 n` and `G_ζ`: `λ(u) > 0` and
  `hellG n (σ(u)/λ(u)) τ₀ ≤ n(w − w̄)²/(wLow²·cRho ζ)`.
* **`cheapMean138`**: `θ ∈ good136 n`, every `c`, every real `a`:
  `(E_{ν_c} φ − E_{ν′_c} φ)² ≤ 2·Hbar·(E_{ν_c}(φ − a)² + E_{ν′_c}(φ − a)²)`.
* **`cheapStandIn138`**: `θ ∈ good136 n`:
  `E_{M₃}(E_{μ_W} φ − E_{ν′} φ)² ≤ 2·(0.99/n)·E_c Var_{ν_c} φ
     + 4·Hbar·E_c(E_{ν_c}(φ − a)² + E_{ν′_c}(φ − a)²)`.
* `cheapStandIn138_bdd`: for `|φ| ≤ B` the second term is at most `8B²·Hbar`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part138

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137

/-- The comparison of two standard deviations through their squares: if `τ² ≥ ρ·τ₀²`, then
`(τ − τ₀)²/(τ² + τ₀²) ≤ (τ² − τ₀²)²/(τ₀⁴(1 + √ρ)²(1 + ρ))`. -/
lemma hell_ratio {τ τ₀ ρ : ℝ} (hτ : 0 ≤ τ) (hτ₀ : 0 < τ₀) (hρ : 0 ≤ ρ)
    (h : ρ * τ₀ ^ 2 ≤ τ ^ 2) :
    (τ - τ₀) ^ 2 / (τ ^ 2 + τ₀ ^ 2) ≤
      (τ ^ 2 - τ₀ ^ 2) ^ 2 / (τ₀ ^ 4 * ((1 + √ρ) ^ 2 * (1 + ρ))) := by
  have h1 : √ρ * τ₀ ≤ τ := by
    have := Real.sqrt_le_sqrt h
    rwa [Real.sqrt_mul hρ, Real.sqrt_sq hτ₀.le, Real.sqrt_sq hτ] at this
  have hs0 := Real.sqrt_nonneg ρ
  have hA : τ₀ ^ 2 * (1 + √ρ) ^ 2 ≤ (τ + τ₀) ^ 2 := by
    have h2 : τ₀ * (1 + √ρ) ≤ τ + τ₀ := by nlinarith
    have h3 := pow_le_pow_left₀ (by positivity) h2 2
    rwa [mul_pow] at h3
  have hB : τ₀ ^ 2 * (1 + ρ) ≤ τ ^ 2 + τ₀ ^ 2 := by nlinarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h4 := mul_le_mul hA hB (by positivity) (by positivity)
  have h5 := mul_le_mul_of_nonneg_left h4 (sq_nonneg (τ - τ₀))
  calc (τ - τ₀) ^ 2 * (τ₀ ^ 4 * ((1 + √ρ) ^ 2 * (1 + ρ)))
      = (τ - τ₀) ^ 2 * (τ₀ ^ 2 * (1 + √ρ) ^ 2 * (τ₀ ^ 2 * (1 + ρ))) := by ring
    _ ≤ (τ - τ₀) ^ 2 * ((τ + τ₀) ^ 2 * (τ ^ 2 + τ₀ ^ 2)) := h5
    _ = (τ ^ 2 - τ₀ ^ 2) ^ 2 * (τ ^ 2 + τ₀ ^ 2) := by ring

/-! ## The constants -/

/-- **The constant scalar of the cheap stand-in**: `τ₀ = √(t|h̄|²·w̄)`. -/
noncomputable def tau0 (N m : ℕ) (θ : HidParam N m) : ℝ :=
  √(2 / (m : ℝ) * normSq (hbarW θ) * wbar N m θ)

/-- The lower bound of `w̄` on `good136 n`. -/
noncomputable def wLow : ℝ := 1 / (494 / 1000) - 1

/-- The paper's `ζ′`: the bound of `|w − w̄|` on the good set of inputs. -/
noncomputable def zetaP (ζ : ℝ) : ℝ := ζ * (3 + ζ) / (4936 / 10000 * (1 - ζ) ^ 2)

/-- The paper's `r_low` for the constant `w₀ = w̄`. -/
noncomputable def rLow (ζ : ℝ) : ℝ := max 0 (1 - zetaP ζ / wLow)

/-- `(1 + √r_low)²(1 + r_low)`: between `1` and `8`. -/
noncomputable def cRho (ζ : ℝ) : ℝ := (1 + √(rLow ζ)) ^ 2 * (1 + rLow ζ)

lemma wLow_pos : 0 < wLow := by unfold wLow; norm_num

lemma zetaP_nonneg {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) : 0 ≤ zetaP ζ := by
  unfold zetaP
  have : 0 < 1 - ζ := by linarith
  positivity

lemma rLow_nonneg (ζ : ℝ) : 0 ≤ rLow ζ := le_max_left _ _

lemma cRho_ge_one (ζ : ℝ) : 1 ≤ cRho ζ := by
  unfold cRho
  have h1 := rLow_nonneg ζ
  have h2 := Real.sqrt_nonneg (rLow ζ)
  nlinarith [mul_nonneg h2 h2, mul_nonneg (mul_nonneg h2 h2) h1, mul_nonneg h2 h1]

lemma cRho_pos (ζ : ℝ) : 0 < cRho ζ := lt_of_lt_of_le one_pos (cRho_ge_one ζ)

/-- `Kfun n ζ (u, θ)`: `n(w − w̄)²/(wLow²·cRho ζ)` on the good set of inputs, `1` off it. -/
noncomputable def Kfun (n : ℕ) (ζ : ℝ) (p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) : ℝ :=
  (goodU (2 * n) (mW n) ζ).indicator
      (fun p => (n : ℝ) / (wLow ^ 2 * cRho ζ) *
        (wn (2 * n) (mW n) p.1 p.2 - wbar (2 * n) (mW n) p.2) ^ 2) p +
    (goodU (2 * n) (mW n) ζ)ᶜ.indicator (fun _ => (1 : ℝ)) p

/-- **`Hbar n ζ θ = E_u Kfun n ζ (u, θ)`**: the bound of the mean squared Hellinger distance of
the exact and the cheap stand-in at `θ = (M₁, M₂)`. -/
noncomputable def Hbar (n : ℕ) (ζ : ℝ) (θ : HidParam (2 * n) (mW n)) : ℝ :=
  ∫ u, Kfun n ζ (u, θ) ∂uniformSphere (2 * n)

lemma Kfun_of_mem {n : ℕ} {ζ : ℝ} {p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)}
    (hp : p ∈ goodU (2 * n) (mW n) ζ) :
    Kfun n ζ p = (n : ℝ) / (wLow ^ 2 * cRho ζ) *
      (wn (2 * n) (mW n) p.1 p.2 - wbar (2 * n) (mW n) p.2) ^ 2 := by
  unfold Kfun
  rw [Set.indicator_of_mem hp, Set.indicator_of_notMem (by simpa using hp), add_zero]

lemma Kfun_of_notMem {n : ℕ} {ζ : ℝ} {p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)}
    (hp : p ∉ goodU (2 * n) (mW n) ζ) : Kfun n ζ p = 1 := by
  unfold Kfun
  rw [Set.indicator_of_notMem hp, Set.indicator_of_mem (by simpa using hp), zero_add]

lemma Kfun_nonneg (n : ℕ) (ζ : ℝ) (p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) :
    0 ≤ Kfun n ζ p := by
  by_cases hp : p ∈ goodU (2 * n) (mW n) ζ
  · rw [Kfun_of_mem hp]
    have := cRho_pos ζ
    have := wLow_pos
    positivity
  · rw [Kfun_of_notMem hp]; exact zero_le_one

lemma measurable_Kfun {n : ℕ} (hn : 1 ≤ n) (ζ : ℝ) : Measurable (Kfun n ζ) := by
  have hN : 1 ≤ 2 * n := by omega
  unfold Kfun
  exact ((((measurable_wn hN).sub ((measurable_wbar hN).comp measurable_snd)).pow_const
    2).const_mul _).indicator (goodU_meas hN ζ) |>.add
    (measurable_const.indicator (goodU_meas hN ζ).compl)

lemma Hbar_nonneg (n : ℕ) (ζ : ℝ) (θ : HidParam (2 * n) (mW n)) : 0 ≤ Hbar n ζ θ :=
  integral_nonneg fun u => Kfun_nonneg n ζ (u, θ)

/-! ## The facts on the good event -/

section good

variable {n : ℕ} (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ good136 n)

include hn hθ

lemma hbarW_ne : normSq (hbarW θ) ≠ 0 := normSq_ne_zero (lamOne136 hn hθ).1

lemma wbar_window : wLow ≤ wbar (2 * n) (mW n) θ ∧
    wbar (2 * n) (mW n) θ ≤ 1 / (4936 / 10000) - 1 := by
  obtain ⟨hB1, hB2⟩ := Bn136 hn hθ
  have hB0 : 0 < Bn (2 * n) (mW n) θ := by linarith
  unfold wbar wLow
  have h1 := one_div_le_one_div_of_le hB0 hB2
  have h2 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4936 / 10000) hB1
  constructor <;> linarith

lemma Kth_pos : 0 < 2 / (mW n : ℝ) * normSq (hbarW θ) := by
  have hm : (0 : ℝ) < mW n := by
    have := mW_ge_million hn
    exact_mod_cast (by omega : 0 < mW n)
  have h1 : 0 < normSq (hbarW θ) :=
    lt_of_le_of_ne (normSq_nonneg _) (Ne.symm (hbarW_ne hn hθ))
  positivity

lemma tau0_sq : tau0 (2 * n) (mW n) θ ^ 2 =
    2 / (mW n : ℝ) * normSq (hbarW θ) * wbar (2 * n) (mW n) θ := by
  unfold tau0
  have h1 := (wbar_window hn hθ).1
  have h2 := wLow_pos
  exact Real.sq_sqrt (mul_nonneg (Kth_pos hn hθ).le (by linarith))

lemma tau0_pos : 0 < tau0 (2 * n) (mW n) θ := by
  unfold tau0
  have h1 := (wbar_window hn hθ).1
  have h2 := wLow_pos
  exact Real.sqrt_pos.mpr (mul_pos (Kth_pos hn hθ) (by linarith))

/-- **The good inputs**: for `θ ∈ good136 n` and `u ∈ G_ζ`: `λ(u) > 0`, and the squared Hellinger
distance of `N(c, (σ(u)/λ(u))²I)` and `N(c, τ₀²I)` is at most `n(w − w̄)²/(wLow²·cRho ζ)`. -/
theorem good_pt {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) {u : Fin (2 * n) → ℝ}
    (hu : (u, θ) ∈ goodU (2 * n) (mW n) ζ) :
    0 < lam (hbarW θ) (hid2 θ.1 θ.2 u) ∧
      hellG n (sig (2 / (mW n : ℝ)) (hbarW θ) (hid2 θ.1 θ.2 u) /
          lam (hbarW θ) (hid2 θ.1 θ.2 u)) (tau0 (2 * n) (mW n) θ) ≤
        (n : ℝ) / (wLow ^ 2 * cRho ζ) *
          (wn (2 * n) (mW n) u θ - wbar (2 * n) (mW n) θ) ^ 2 := by
  have hN : 1 ≤ 2 * n := by omega
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have hnpos : (0 : ℝ) < n := by
    have : (4096 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hul := hu.2
  have hlam : lamn (2 * n) (mW n) u θ = lam (hbarW θ) (hid2 θ.1 θ.2 u) := rfl
  simp only at hul
  rw [hlam] at hul
  set l := lam (hbarW θ) (hid2 θ.1 θ.2 u) with hl
  set s := sig (2 / (mW n : ℝ)) (hbarW θ) (hid2 θ.1 θ.2 u) with hs
  have hl0 : 0 < l := by
    have := abs_le.mp hul
    linarith
  refine ⟨hl0, ?_⟩
  have hs0 : 0 ≤ s := by rw [hs]; unfold sig; positivity
  set τ := s / l with hτ
  have hτ0 : 0 ≤ τ := div_nonneg hs0 hl0.le
  set K := 2 / (mW n : ℝ) * normSq (hbarW θ) with hK
  have hKpos : 0 < K := Kth_pos hn hθ
  set w := wn (2 * n) (mW n) u θ with hw
  set wb := wbar (2 * n) (mW n) θ with hwb
  have hτ2 : τ ^ 2 = K * w := by
    rw [hτ, div_pow]
    exact tau_sq_eq hN hm u (hbarW_ne hn hθ) (by rw [hlam]; exact hl0.ne')
  have hτ02 : tau0 (2 * n) (mW n) θ ^ 2 = K * wb := tau0_sq hn hθ
  have hτ0pos := tau0_pos hn hθ
  obtain ⟨hwb1, -⟩ := wbar_window hn hθ
  have hwLow := wLow_pos
  have hwb0 : 0 < wb := by linarith
  have hw0 : 0 ≤ w := by
    have : 0 ≤ K * w := by rw [← hτ2]; positivity
    exact nonneg_of_mul_nonneg_right this hKpos
  have hclose : |w - wb| ≤ zetaP ζ :=
    (wClose137 hn hζ1 (p := (u, θ)) ⟨hθ, hu⟩).1
  -- the ratio
  have hr : rLow ζ * wb ≤ w := by
    have hz := zetaP_nonneg hζ0 hζ1
    unfold rLow
    rcases le_total (1 - zetaP ζ / wLow) 0 with h0 | h0
    · rw [max_eq_left h0, zero_mul]; exact hw0
    · rw [max_eq_right h0]
      have h1 : zetaP ζ ≤ zetaP ζ / wLow * wb := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hwLow]
        exact mul_le_mul_of_nonneg_left hwb1 hz
      have h2 := (abs_le.mp hclose).1
      nlinarith
  have hr2 : rLow ζ * tau0 (2 * n) (mW n) θ ^ 2 ≤ τ ^ 2 := by
    rw [hτ2, hτ02]
    have := mul_le_mul_of_nonneg_left hr hKpos.le
    linarith
  have h1 := hellG_le (by omega : 2 ≤ n) hτ0 hτ0pos
  have h2 := hell_ratio hτ0 hτ0pos (rLow_nonneg ζ) hr2
  have e4 : tau0 (2 * n) (mW n) θ ^ 4 = (K * wb) ^ 2 := by
    rw [← hτ02]; ring
  have h3 : (τ ^ 2 - tau0 (2 * n) (mW n) θ ^ 2) ^ 2 /
      (tau0 (2 * n) (mW n) θ ^ 4 * ((1 + √(rLow ζ)) ^ 2 * (1 + rLow ζ))) =
      (w - wb) ^ 2 / (wb ^ 2 * cRho ζ) := by
    rw [e4, hτ2, hτ02]
    unfold cRho
    have hc := cRho_pos ζ
    unfold cRho at hc
    field_simp
  have h4 : (w - wb) ^ 2 / (wb ^ 2 * cRho ζ) ≤ (w - wb) ^ 2 / (wLow ^ 2 * cRho ζ) := by
    refine div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos (by positivity) (cRho_pos ζ)) ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hwLow.le hwb1 2) (cRho_pos ζ).le
  calc hellG n τ (tau0 (2 * n) (mW n) θ)
      ≤ (n : ℝ) * (τ - tau0 (2 * n) (mW n) θ) ^ 2 / (τ ^ 2 + tau0 (2 * n) (mW n) θ ^ 2) := h1
    _ = (n : ℝ) * ((τ - tau0 (2 * n) (mW n) θ) ^ 2 / (τ ^ 2 + tau0 (2 * n) (mW n) θ ^ 2)) := by
      rw [mul_div_assoc]
    _ ≤ (n : ℝ) * ((w - wb) ^ 2 / (wLow ^ 2 * cRho ζ)) :=
      mul_le_mul_of_nonneg_left ((h2.trans (le_of_eq h3)).trans h4) hnpos.le
    _ = _ := by ring

/-- On the good event `Kfun n ζ (·, θ)` is bounded. -/
lemma Kfun_le {ζ : ℝ} (hζ1 : ζ < 1) (u : Fin (2 * n) → ℝ) :
    Kfun n ζ (u, θ) ≤ (n : ℝ) / (wLow ^ 2 * cRho ζ) * zetaP ζ ^ 2 + 1 := by
  have hc := cRho_pos ζ
  have hwl := wLow_pos
  have hC : 0 ≤ (n : ℝ) / (wLow ^ 2 * cRho ζ) := by positivity
  by_cases hp : (u, θ) ∈ goodU (2 * n) (mW n) ζ
  · rw [Kfun_of_mem hp]
    have hclose := (wClose137 hn hζ1 (p := (u, θ)) ⟨hθ, hp⟩).1
    have hsq : (wn (2 * n) (mW n) u θ - wbar (2 * n) (mW n) θ) ^ 2 ≤ zetaP ζ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hclose 2
    have := mul_le_mul_of_nonneg_left hsq hC
    linarith
  · rw [Kfun_of_notMem hp]
    have : 0 ≤ (n : ℝ) / (wLow ^ 2 * cRho ζ) * zetaP ζ ^ 2 := by positivity
    linarith

lemma Kfun_integrable {ζ : ℝ} (hζ1 : ζ < 1) :
    Integrable (fun u => Kfun n ζ (u, θ)) (uniformSphere (2 * n)) := by
  have := uniformSphere_isProbability (2 * n) (by omega)
  refine Integrable.of_bound ((measurable_Kfun (by omega) ζ).comp
    measurable_prodMk_right).aestronglyMeasurable
    ((n : ℝ) / (wLow ^ 2 * cRho ζ) * zetaP ζ ^ 2 + 1) (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Kfun_nonneg n ζ (u, θ))]
  exact Kfun_le hn hθ hζ1 u

/-- **The cheap stand-in against the exact stand-in, at one `c`.** For `n ≥ 4096`,
`θ ∈ good136 n`, `0 ≤ ζ < 1`, every `c ∈ ℝⁿ`, every bounded measurable `φ` and every real `a`:
`(E_{ν_c} φ − E_{ν′_c} φ)² ≤ 2·Hbar n ζ θ·(E_{ν_c}(φ − a)² + E_{ν′_c}(φ − a)²)`. -/
theorem cheapMean138 {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) (c : Fin n → ℝ)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) (a : ℝ) :
    (∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (hbarW θ) c -
        ∫ x, φ x ∂cheapIn c (tau0 (2 * n) (mW n) θ)) ^ 2 ≤
      2 * Hbar n ζ θ *
        (∫ x, (φ x - a) ^ 2
            ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (hbarW θ) c +
          ∫ x, (φ x - a) ^ 2 ∂cheapIn c (tau0 (2 * n) (mW n) θ)) := by
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  have hh : Measurable (hid2 θ.1 θ.2) := (continuous_hid2 θ.1 θ.2).measurable
  have p1 := standIn_prob (n := n) (uniformSphere (2 * n)) hh (2 / (mW n : ℝ)) (hbarW θ) c
  have p2 := cheapIn_prob c (tau0 (2 * n) (mW n) θ)
  have hψ : BM (fun x => φ x - a) := hφ.sub (BM.const a)
  have hK : ∀ u : Fin (2 * n) → ℝ,
      (0 < lam (hbarW θ) (hid2 θ.1 θ.2 u) ∧
        hellG n (sig (2 / (mW n : ℝ)) (hbarW θ) (hid2 θ.1 θ.2 u) /
          lam (hbarW θ) (hid2 θ.1 θ.2 u)) (tau0 (2 * n) (mW n) θ) ≤ Kfun n ζ (u, θ)) ∨
      1 ≤ Kfun n ζ (u, θ) := by
    intro u
    by_cases hp : (u, θ) ∈ goodU (2 * n) (mW n) ζ
    · left
      rw [Kfun_of_mem hp]
      exact good_pt hn hθ hζ0 hζ1 hp
    · right
      rw [Kfun_of_notMem hp]
  have h := cheap_mix (uniformSphere (2 * n)) (by omega : 2 ≤ n) (2 / (mW n : ℝ)) (hbarW θ) c hh
    (tau0_pos hn hθ) ((measurable_Kfun (by omega) ζ).comp measurable_prodMk_right)
    (Kfun_integrable hn hθ hζ1) hK hψ
  have e1 : ∫ x, (φ x - a)
      ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (hbarW θ) c =
      ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (hbarW θ) c -
        a := by
    rw [integral_sub (hφ.integrable _) (integrable_const _)]
    simp
  have e2 : ∫ x, (φ x - a) ∂cheapIn c (tau0 (2 * n) (mW n) θ) =
      ∫ x, φ x ∂cheapIn c (tau0 (2 * n) (mW n) θ) - a := by
    rw [integral_sub (hφ.integrable _) (integrable_const _)]
    simp
  rw [e1, e2] at h
  have e3 : (∫ x, φ x
        ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (hbarW θ) c - a -
      (∫ x, φ x ∂cheapIn c (tau0 (2 * n) (mW n) θ) - a)) =
      ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (hbarW θ) c -
        ∫ x, φ x ∂cheapIn c (tau0 (2 * n) (mW n) θ) := by ring
  rw [e3] at h
  exact h

/-- **The cheap stand-in theorem for fixed `(M₁, M₂)` (item 3).** For `n ≥ 4096`,
`θ = (M₁, M₂) ∈ good136 n`, `0 ≤ ζ < 1`, bounded measurable `φ` and every real `a`, with the
expectation over `M₃`:
`E(E_{μ_W} φ − E_{ν′} φ)² ≤ 2·(0.99/n)·E_c Var_{ν_c} φ
   + 4·Hbar n ζ θ·E_c(E_{ν_c}(φ − a)² + E_{ν′_c}(φ − a)²)`.
`ν′ = cheapIn (M₃h̄) τ₀` is the cheap stand-in with the constant `τ₀² = t|h̄|²·w̄(θ)`. -/
theorem cheapStandIn138 {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ)
    (a : ℝ) :
    ∫ M₃, ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂cheapIn (M₃.mulVec (hbarW θ)) (tau0 (2 * n) (mW n) θ)) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)) ≤
      2 * (99 / 100 / (n : ℝ) *
        ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
          (hbarW θ) c] ∂cDist n (2 / (mW n : ℝ)) (hbarW θ)) +
      4 * Hbar n ζ θ *
        ∫ c, (∫ x, (φ x - a) ^ 2
              ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (hbarW θ) c +
            ∫ x, (φ x - a) ^ 2 ∂cheapIn c (tau0 (2 * n) (mW n) θ))
          ∂cDist n (2 / (mW n : ℝ)) (hbarW θ) := by
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  have hh : Measurable (hid2 θ.1 θ.2) := (continuous_hid2 θ.1 θ.2).measurable
  set P := gaussMat n (mW n) (2 / (mW n : ℝ)) with hP
  set b := hbarW θ with hb
  set τ₀ := tau0 (2 * n) (mW n) θ with hτ₀
  have hψ : BM (fun x => (φ x - a) ^ 2) := (hφ.sub (BM.const a)).sq
  -- the three means as functions of `M₃`
  have bX : BM (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      ∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) :=
    (bm_muW hN hφ).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have bYc : BM (fun c : Fin n → ℝ =>
      ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b c) :=
    bm_standIn (n := n) (uniformSphere (2 * n)) (2 / (mW n : ℝ)) b hh hφ
  have bZc : BM (fun c : Fin n → ℝ => ∫ x, φ x ∂cheapIn c τ₀) :=
    bm_cheapIn measurable_id measurable_const hφ
  have bSc : BM (fun c : Fin n → ℝ =>
      ∫ x, (φ x - a) ^ 2
          ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b c +
        ∫ x, (φ x - a) ^ 2 ∂cheapIn c τ₀) :=
    (bm_standIn (n := n) (uniformSphere (2 * n)) (2 / (mW n : ℝ)) b hh hψ).add
      (bm_cheapIn measurable_id measurable_const hψ)
  have mb : Measurable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ => M₃.mulVec b) :=
    measurable_mulVec_right b
  have bY := bYc.comp mb
  have bZ := bZc.comp mb
  have bS := bSc.comp mb
  -- pointwise in `M₃`
  have hpt : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
      ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂cheapIn (M₃.mulVec b) τ₀) ^ 2 ≤
      2 * ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2 +
      4 * Hbar n ζ θ *
        (∫ x, (φ x - a) ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
            (M₃.mulVec b) +
          ∫ x, (φ x - a) ^ 2 ∂cheapIn (M₃.mulVec b) τ₀) := by
    intro M₃
    have h1 := cheapMean138 hn hθ hζ0 hζ1 (M₃.mulVec b) hφ a
    nlinarith [sq_nonneg ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
      2 * ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b) + ∫ x, φ x ∂cheapIn (M₃.mulVec b) τ₀)]
  have i1 : Integrable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      2 * ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2) P := ((BM.const 2).mul (bX.sub bY).sq).integrable P
  have i2 : Integrable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      4 * Hbar n ζ θ *
        (∫ x, (φ x - a) ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
            (M₃.mulVec b) +
          ∫ x, (φ x - a) ^ 2 ∂cheapIn (M₃.mulVec b) τ₀)) P :=
    ((BM.const (4 * Hbar n ζ θ)).mul bS).integrable P
  have i12 : Integrable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      2 * ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2 +
      4 * Hbar n ζ θ *
        (∫ x, (φ x - a) ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
            (M₃.mulVec b) +
          ∫ x, (φ x - a) ^ 2 ∂cheapIn (M₃.mulVec b) τ₀)) P := i1.add i2
  have hmono := integral_mono ((bX.sub bZ).sq.integrable P) i12 hpt
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul] at hmono
  have h136 := standIn136 hn hθ hφ
  have ecd : ∫ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
      (∫ x, (φ x - a) ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
            (M₃.mulVec b) +
          ∫ x, (φ x - a) ^ 2 ∂cheapIn (M₃.mulVec b) τ₀) ∂P =
      ∫ c, (∫ x, (φ x - a) ^ 2
              ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b c +
            ∫ x, (φ x - a) ^ 2 ∂cheapIn c τ₀) ∂cDist n (2 / (mW n : ℝ)) b := by
    rw [← cDist_eq, integral_map mb.aemeasurable bSc.meas.aestronglyMeasurable]
  rw [ecd] at hmono
  have h136' : ∫ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
      ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2 ∂P ≤
      99 / 100 / (n : ℝ) *
        ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b c]
          ∂cDist n (2 / (mW n : ℝ)) b := h136
  linarith

/-- **Item 3 for a bounded function**: for `|φ| ≤ B` the second term is at most
`8B²·Hbar n ζ θ`. -/
theorem cheapStandIn138_bdd {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) {φ : (Fin n → ℝ) → ℝ}
    (hφ : Measurable φ) {B : ℝ} (hB : ∀ x, |φ x| ≤ B) :
    ∫ M₃, ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂cheapIn (M₃.mulVec (hbarW θ)) (tau0 (2 * n) (mW n) θ)) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)) ≤
      2 * (99 / 100 / (n : ℝ) *
        ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
          (hbarW θ) c] ∂cDist n (2 / (mW n : ℝ)) (hbarW θ)) +
      8 * B ^ 2 * Hbar n ζ θ := by
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  have hh : Measurable (hid2 θ.1 θ.2) := (continuous_hid2 θ.1 θ.2).measurable
  have hφb : BM φ := ⟨hφ, B, hB⟩
  have h := cheapStandIn138 hn hθ hζ0 hζ1 hφb 0
  have hb2 : ∀ x, (φ x - 0) ^ 2 ≤ B ^ 2 := fun x => by
    rw [sub_zero, ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
  have hS : ∀ c : Fin n → ℝ,
      (∫ x, (φ x - 0) ^ 2
          ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (hbarW θ) c +
        ∫ x, (φ x - 0) ^ 2 ∂cheapIn c (tau0 (2 * n) (mW n) θ)) ≤ 2 * B ^ 2 := by
    intro c
    have p1 := standIn_prob (n := n) (uniformSphere (2 * n)) hh (2 / (mW n : ℝ)) (hbarW θ) c
    have p2 := cheapIn_prob c (tau0 (2 * n) (mW n) θ)
    have hψ : BM (fun x => (φ x - 0) ^ 2) := (hφb.sub (BM.const 0)).sq
    have h1 := integral_mono (hψ.integrable
      (standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (hbarW θ) c))
      (integrable_const (B ^ 2)) hb2
    have h2 := integral_mono (hψ.integrable (cheapIn c (tau0 (2 * n) (mW n) θ)))
      (integrable_const (B ^ 2)) hb2
    simp only [integral_const, probReal_univ, one_smul] at h1 h2
    linarith
  have hprob : IsProbabilityMeasure (cDist n (2 / (mW n : ℝ)) (hbarW θ)) := by
    rw [← cDist_eq]
    exact (Measure.isProbabilityMeasure_map_iff
      (measurable_mulVec_right (hbarW θ)).aemeasurable).2 inferInstance
  have hψ : BM (fun x => (φ x - 0) ^ 2) := (hφb.sub (BM.const 0)).sq
  have bSc : BM (fun c : Fin n → ℝ =>
      ∫ x, (φ x - 0) ^ 2
          ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (hbarW θ) c +
        ∫ x, (φ x - 0) ^ 2 ∂cheapIn c (tau0 (2 * n) (mW n) θ)) :=
    (bm_standIn (n := n) (uniformSphere (2 * n)) (2 / (mW n : ℝ)) (hbarW θ) hh hψ).add
      (bm_cheapIn measurable_id measurable_const hψ)
  have h3 := integral_mono (bSc.integrable (cDist n (2 / (mW n : ℝ)) (hbarW θ)))
    (integrable_const (2 * B ^ 2)) hS
  simp only [integral_const, probReal_univ, one_smul] at h3
  have h4 := mul_le_mul_of_nonneg_left h3
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (Hbar_nonneg n ζ θ))
  linarith

end good

end BstLean.Part138

open BstLean.Part138 in
#print axioms good_pt
open BstLean.Part138 in
#print axioms cheapMean138
open BstLean.Part138 in
#print axioms cheapStandIn138
open BstLean.Part138 in
#print axioms cheapStandIn138_bdd
