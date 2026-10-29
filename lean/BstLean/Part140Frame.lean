import BstLean.Part140Det
import BstLean.Part140Dist

/-!
# Part 140, item 2: the stand-in theorem with the computed centre `b̂ = ψ_s(M₂ h̄₁)`

Role: `delegations/statements/p140-spec.md` (item 2). Paper sources: `onW5c-cx.md` §4,
`onW5-opus-prover.md` §3 (c) and §4.3, `onW8c-cx.md` §4 (`λ̂₁ ≤ 3.52/n`).

`N = 2n`, `m = mW n`, `t = 2/m`, `γ = 2/N`, `θ = (M₁, M₂)`.

* `goodT n dT`: the event `n·E_u(T̂(u) − γκ(q₁))² ≤ γ²·dT`; `goodT_prob`.
* **`goodHat n`**: the good hidden event for the computed centre:
  `good136 n` (Part 136), `t|b̂ − h̄|² ≤ γ·(3/4)/N`, and `goodT n (1/400000)`.
  `goodHat_prob`: its probability is at least `1 − (0.002 + 70/n)`, every `n ≥ 4096`.
* **`lamHat140`**: on `goodHat n`, every `n ≥ 4096`: `b̂ ≠ 0`, the unit residual directions for
  the centre `b̂` have the frame bound `1.83/n` (the hypothesis `hL` of Part 134), and
  `lamOne … b̂ … ≤ 1.83/n`.
* **`standInHat140`**: `E_{M₃}(E_{μ_W} φ − E_{ν̂} φ)² ≤ (1.83/n)·E_c Var_{ν̂_c} φ`, with `ν̂` the exact
  stand-in of Part 134 built on `b̂` (`ĉ = M₃ b̂`). `standInVarHat140`: the conditional form.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part140

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part105 (BM sphere_cont_integrable)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137

/-! ## The events -/

/-- The event `n·E_u(T̂(u) − γκ(q₁))² ≤ γ²·dT`. -/
def goodT (n : ℕ) (dT : ℝ) : Set (HidParam (2 * n) (mW n)) :=
  {θ | (n : ℝ) * errT θ ≤ (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * dT}

lemma goodT_meas {n : ℕ} (hn : 1 ≤ n) (dT : ℝ) : MeasurableSet (goodT n dT) :=
  measurableSet_le ((measurable_errT (by omega)).const_mul _) measurable_const

/-- `Pr(goodT n dT fails) ≤ 8.03/(64·n²·dT)` for `n ≥ 4096`. -/
theorem goodT_prob {n : ℕ} (hn : 4096 ≤ n) {dT : ℝ} (hdT : 0 < dT) :
    (hidGauss (2 * n) (mW n)).real (goodT n dT)ᶜ ≤
      803 / 100 / (64 * (n : ℝ) ^ 2 * dT) := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hN : 1 ≤ 2 * n := by omega
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
    linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  set B : ℝ := (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * dT / (n : ℝ) with hB
  have hBpos : 0 < B := by rw [hB]; positivity
  have hsub : (goodT n dT)ᶜ ⊆ {θ | B < errT θ} := by
    intro θ hθ
    have h1 : ¬ (n : ℝ) * errT θ ≤ (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * dT := hθ
    rw [not_le] at h1
    change B < errT θ
    rw [hB, div_lt_iff₀ hnpos]
    linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (errT_bad (N := 2 * n) (m := mW n) hN hm hBpos).trans ?_
  have hc := cHat2_sq_le (N := 2 * n) (m := mW n) (by omega) hmM
  have b := nsq_div_mW_le hn
  have e : (2 / ((2 * n : ℕ) : ℝ) * cHat2 (2 * n) (mW n)) ^ 2 / B =
      (n : ℝ) * cHat2 (2 * n) (mW n) ^ 2 / dT := by
    rw [hB]
    field_simp
  rw [e]
  have h2 : (n : ℝ) * cHat2 (2 * n) (mW n) ^ 2 ≤ (n : ℝ) * (803 / 100 / (mW n : ℝ)) :=
    mul_le_mul_of_nonneg_left hc hnpos.le
  have h3 : (n : ℝ) * (803 / 100 / (mW n : ℝ)) = 803 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) /
      (n : ℝ) := by
    field_simp
  have h4 : 803 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (n : ℝ) ≤
      803 / 100 * (1 / (64 * (n : ℝ))) / (n : ℝ) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left b (by norm_num)) hnpos.le
  have h5 : (n : ℝ) * cHat2 (2 * n) (mW n) ^ 2 ≤ 803 / 100 / (64 * (n : ℝ) ^ 2) := by
    refine (h2.trans (le_of_eq h3)).trans (h4.trans (le_of_eq ?_))
    field_simp
  calc (n : ℝ) * cHat2 (2 * n) (mW n) ^ 2 / dT ≤ 803 / 100 / (64 * (n : ℝ) ^ 2) / dT :=
        div_le_div_of_nonneg_right h5 hdT.le
    _ = 803 / 100 / (64 * (n : ℝ) ^ 2 * dT) := by rw [div_div]

/-- **The good hidden event for the computed centre** `b̂`: the good event of Part 136, the
computed centre is near the exact centre (`t|b̂ − h̄|² ≤ γ·(3/4)/N`), and the integrated error of
`T̂ = t⟨h(u), b̂⟩` is small. It uses `(M₁, M₂)` only. -/
def goodHat (n : ℕ) : Set (HidParam (2 * n) (mW n)) :=
  good136 n ∩ goodDist n (3 / 4) ∩ goodT n (1 / 400000)

theorem goodHat_meas {n : ℕ} (hn : 1 ≤ n) : MeasurableSet (goodHat n) :=
  ((good136_meas hn).inter (goodDist_meas hn _)).inter (goodT_meas hn _)

lemma goodHat_sub136 {n : ℕ} {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ goodHat n) :
    θ ∈ good136 n := hθ.1.1

/-- **The probability of the good hidden event**: at least `1 − (0.002 + 70/n)`, `n ≥ 4096`. -/
theorem goodHat_prob {n : ℕ} (hn : 4096 ≤ n) :
    1 - (2 / 1000 + 70 / (n : ℝ)) ≤ (hidGauss (2 * n) (mW n)).real (goodHat n) := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hn1 : 1 ≤ n := by omega
  set P := hidGauss (2 * n) (mW n) with hP
  have h1 : P.real (good136 n)ᶜ ≤ 2 / 1000 := by
    rw [measureReal_compl (good136_meas hn1), probReal_univ]
    have := good136_prob hn
    linarith
  have h2 : P.real (goodDist n (3 / 4))ᶜ ≤ 57 / (n : ℝ) := by
    refine (goodDist_prob hn (by norm_num)).trans ?_
    rw [div_le_div_iff₀ (by positivity) hnpos]
    nlinarith
  have h3 : P.real (goodT n (1 / 400000))ᶜ ≤ 13 / (n : ℝ) := by
    refine (goodT_prob hn (by norm_num)).trans ?_
    rw [div_le_div_iff₀ (by positivity) hnpos]
    nlinarith [mul_pos hnpos hnpos]
  have hsub : (goodHat n)ᶜ ⊆
      ((good136 n)ᶜ ∪ (goodDist n (3 / 4))ᶜ) ∪ (goodT n (1 / 400000))ᶜ := by
    intro θ hθ
    simp only [goodHat, Set.mem_compl_iff, Set.mem_inter_iff, not_and_or] at hθ
    simpa only [Set.mem_union, Set.mem_compl_iff] using hθ
  have h4 : P.real (goodHat n)ᶜ ≤ 2 / 1000 + 57 / (n : ℝ) + 13 / (n : ℝ) :=
    (measureReal_mono hsub (measure_ne_top _ _)).trans
      ((measureReal_union_le _ _).trans (add_le_add
        ((measureReal_union_le _ _).trans (add_le_add h1 h2)) h3))
  rw [measureReal_compl (goodHat_meas hn1), probReal_univ] at h4
  have e : (70 : ℝ) / n = 57 / n + 13 / n := by ring
  linarith

/-- The window of `κ(q₁)`: `0.49372 ≤ κ(q₁) ≤ 0.4938` for `N = 2n ≥ 8192`. -/
lemma kap1_window {n : ℕ} (hn : 4096 ≤ n) : 49372 / 100000 ≤ kap1 (2 * n) ∧ kap1 (2 * n) ≤ 4938 / 10000 := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hN : 1 ≤ 2 * n := by omega
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have h1 := kap1_ge hN
  have h2 := kap1_le hN
  have h3 := qN_le hN
  have h4 := kappa2_zero_le
  have h5 := kappa2_zero_ge
  have h6 : (8 : ℝ) / 25 / ((2 * n : ℕ) : ℝ) ≤ 4 / 100000 := by
    rw [hNcast, div_le_iff₀ (by positivity)]
    linarith
  constructor <;> linarith

/-! ## The facts on the good event -/

section good

variable {n : ℕ} (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ goodHat n)

include hn hθ

/-- On `goodHat n`: `0.48·γ ≤ t|b̂|² ≤ 0.508·γ`. -/
lemma Bh_hat : 2 / ((2 * n : ℕ) : ℝ) * (48 / 100) ≤ Bh (2 * n) (mW n) θ ∧
    Bh (2 * n) (mW n) θ ≤ 2 / ((2 * n : ℕ) : ℝ) * (508 / 1000) :=
  Bh_window hn hθ.1.1 hθ.1.2

lemma Bh_pos : 0 < Bh (2 * n) (mW n) θ := by
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  have := (Bh_hat hn hθ).1
  nlinarith

lemma normSq_bhat_pos : 0 < normSq (bhat θ) := by
  have h := Bh_pos hn hθ
  unfold Bh at h
  have hm : (0 : ℝ) < mW n := by
    have := mW_ge_million hn
    exact_mod_cast (by omega : 0 < mW n)
  by_contra h0
  have : normSq (bhat θ) = 0 := le_antisymm (not_lt.mp h0) (normSq_nonneg _)
  rw [this, mul_zero] at h
  exact lt_irrefl _ h

lemma bhat_ne : bhat θ ≠ 0 := by
  intro h0
  have h := normSq_bhat_pos hn hθ
  rw [h0] at h
  simp [normSq] at h

/-- **The frame bound for the computed centre.** For every `n ≥ 4096` and `θ ∈ goodHat n`:
`E_u ⟨ê(u), w⟩² ≤ (1.83/n)·|w|²`, with `ê(u) = eDir b̂ (h(u))` the unit residual direction
orthogonal to `b̂`. -/
theorem frameHat140 (w : Fin (mW n) → ℝ) :
    ∫ u, (∑ j, eDir (bhat θ) (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n) ≤
      183 / 100 / (n : ℝ) * ∑ j, w j ^ 2 := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hN : 1 ≤ 2 * n := by omega
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
    linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have := uniformSphere_isProbability (2 * n) hN
  obtain ⟨hk1, hk2⟩ := kap1_window hn
  obtain ⟨hBl, -⟩ := Bh_hat hn hθ
  obtain ⟨b, hb0, hb1, hmodel⟩ := kk_three
  -- the three hypotheses on the centre
  have hξ : ∑ j, (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) j - bhat θ j) ^ 2 ≤
      (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * ((3 / 8) / (n : ℝ)) := by
    have hd : dist2 (2 * n) (mW n) θ ≤
        2 / ((2 * n : ℕ) : ℝ) * (3 / 4 / ((2 * n : ℕ) : ℝ)) := hθ.1.2
    have e : ∑ j, (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) j - bhat θ j) ^ 2 =
        normSq (bhat θ - hbarW θ) := by
      rw [normSq_sub_comm]
      rfl
    rw [e]
    unfold dist2 at hd
    rw [hNcast] at hd ⊢
    have h1 : normSq (bhat θ - hbarW θ) ≤
        (mW n : ℝ) / 2 * (2 / (2 * (n : ℝ)) * (3 / 4 / (2 * (n : ℝ)))) := by
      have := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ (mW n : ℝ) / 2)
      have e2 : (mW n : ℝ) / 2 * (2 / (mW n : ℝ) * normSq (bhat θ - hbarW θ)) =
          normSq (bhat θ - hbarW θ) := by field_simp
      linarith
    refine h1.trans (le_of_eq ?_)
    field_simp
    ring
  have hX : ∫ u, (∑ j, hid2 θ.1 θ.2 u j * bhat θ j -
        (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * kap1 (2 * n)) ^ 2 ∂uniformSphere (2 * n) ≤
      ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) ^ 2 * ((1 / 400000) / (n : ℝ)) := by
    have hT : (n : ℝ) * errT θ ≤ (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * (1 / 400000) := hθ.2
    have e : ∀ u : Fin (2 * n) → ℝ, (∑ j, hid2 θ.1 θ.2 u j * bhat θ j -
        (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * kap1 (2 * n)) ^ 2 =
        ((mW n : ℝ) / 2) ^ 2 *
          (That (2 * n) (mW n) u θ - 2 / ((2 * n : ℕ) : ℝ) * kap1 (2 * n)) ^ 2 := by
      intro u
      have e1 : That (2 * n) (mW n) u θ =
          2 / (mW n : ℝ) * ∑ j, hid2 θ.1 θ.2 u j * bhat θ j := rfl
      rw [e1]
      field_simp
    simp_rw [e]
    rw [integral_const_mul]
    change ((mW n : ℝ) / 2) ^ 2 * errT θ ≤ _
    have h1 : errT θ ≤ (2 / ((2 * n : ℕ) : ℝ)) ^ 2 * (1 / 400000) / (n : ℝ) := by
      rw [le_div_iff₀ hnpos]
      linarith
    refine (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)).trans (le_of_eq ?_)
    rw [hNcast]
    field_simp
  have hβb : (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * (48 / 100) ≤ normSq (bhat θ) := by
    unfold Bh at hBl
    rw [hNcast] at hBl ⊢
    have := mul_le_mul_of_nonneg_left hBl (by positivity : (0 : ℝ) ≤ (mW n : ℝ) / 2)
    have e2 : (mW n : ℝ) / 2 * (2 / (mW n : ℝ) * normSq (bhat θ)) = normSq (bhat θ) := by
      field_simp
    have e3 : (mW n : ℝ) / 2 * (2 / (2 * (n : ℝ)) * (48 / 100)) =
        (mW n : ℝ) / (2 * (n : ℝ)) * (48 / 100) := by field_simp
    linarith
  have hsle : (441 : ℝ) / 1000 ≤ 1 - 3 / 100 - (kap1 (2 * n) + 1 / 100) ^ 2 / (48 / 100) := by
    have h1 : (kap1 (2 * n) + 1 / 100) ^ 2 ≤ (4938 / 10000 + 1 / 100) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 2
    have h2 : (kap1 (2 * n) + 1 / 100) ^ 2 / (48 / 100) ≤
        (4938 / 10000 + 1 / 100) ^ 2 / (48 / 100) :=
      div_le_div_of_nonneg_right h1 (by norm_num)
    have h3 : (4938 / 10000 + 1 / 100 : ℝ) ^ 2 / (48 / 100) ≤ 529 / 1000 := by norm_num
    linarith
  exact frameB_num (n := n) (n0 := 4096) le_rfl hn (b := b) (c2 := 138 / 1000)
    (η := 1 / 1000) (K₃ := 2 / 5) (r0 := 1 / 262144) (k0 := 5771 / 625000)
    (k6 := 5349 / 250000) (sp := 4 / 100) (ε₁ := 3 / 100) (ε₂ := 1 / 100) (s := 441 / 1000)
    (p₂ := 4 / 10000) (D0 := 4805289 / 20000000) (C := 183 / 100) (ξ₀ := 3 / 8)
    (a := kap1 (2 * n)) (dT := 1 / 400000) (β := 48 / 100)
    hb0 hb1 (by norm_num) (by norm_num) (by norm_num) hmodel
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by linarith) (by norm_num) (by norm_num) hsle (by norm_num) hθ.1.1 hξ hX hβb w

/-- **`lamHat140`** (the stand-in factor for the computed centre). For every `n ≥ 4096`, on the
good hidden event `goodHat n`: `b̂ ≠ 0`, the hypothesis `hL` of Part 134 holds for the centre `b̂`
with `L = 1.83/n`, and `lamOne … b̂ … ≤ 1.83/n`. -/
theorem lamHat140 :
    bhat θ ≠ 0 ∧
    (∀ w : Fin (mW n) → ℝ,
      ∫ u, (∑ j, eDir (bhat θ) (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n) ≤
        183 / 100 / (n : ℝ) * ∑ j, w j ^ 2) ∧
    lamOne (uniformSphere (2 * n)) (bhat θ) (hid2 θ.1 θ.2) ≤ 183 / 100 / (n : ℝ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact ⟨bhat_ne hn hθ, frameHat140 hn hθ,
    lamOne_le _ _ _ (by positivity) (frameHat140 hn hθ)⟩

/-- **`standInHat140`** (item 2): the stand-in theorem with the computed centre. For every
`n ≥ 4096`, `θ = (M₁, M₂) ∈ goodHat n` and bounded measurable `φ`, with the expectation over `M₃`:
`E(E_{μ_W} φ − E_{ν̂} φ)² ≤ (1.83/n)·E_c Var_{ν̂_c} φ`, where `ν̂_c` is the exact stand-in built on
the centre `b̂` and `ĉ = M₃ b̂`. -/
theorem standInHat140 {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    ∫ M₃, ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
          (bhat θ) (M₃.mulVec (bhat θ))) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)) ≤
      183 / 100 / (n : ℝ) *
        ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
          (bhat θ) c] ∂cDist n (2 / (mW n : ℝ)) (bhat θ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact s1_mse_mlp (by omega) θ.1 θ.2 (bhat_ne hn hθ) hφ (by positivity) (frameHat140 hn hθ)

/-- The conditional form: for every `c`, `Var(E_{μ_W} φ | ĉ = c) ≤ (1.83/n)·Var_{ν̂_c} φ`. -/
theorem standInVarHat140 (c : Fin n → ℝ) {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) :
    Var[fun M' => ∫ x, φ x ∂muWn ((θ.1, θ.2,
          glue (bhat θ) c (M' * projPerp (bhat θ))) : MlpParam (2 * n) (mW n) n);
        gaussMat n (mW n) (2 / (mW n : ℝ))] ≤
      183 / 100 / (n : ℝ) *
        Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (bhat θ) c] := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  exact s1_var_mlp (by omega) θ.1 θ.2 (bhat θ) c hφ (by positivity) (frameHat140 hn hθ)

end good

end BstLean.Part140

open BstLean.Part140 in
#print axioms goodT_prob
open BstLean.Part140 in
#print axioms goodHat_prob
open BstLean.Part140 in
#print axioms frameHat140
open BstLean.Part140 in
#print axioms lamHat140
open BstLean.Part140 in
#print axioms standInHat140
open BstLean.Part140 in
#print axioms standInVarHat140
