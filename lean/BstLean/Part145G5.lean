import BstLean.Part145G4

/-!
# Part 145 (abstract good hidden event), file 5: a frame constant that depends on `θ`

* `GoodEv0 n G`: measurable and the window of `Bh`: the part of `GoodEv` without the frame
  bound. The lemmas of files 1 and 2 use only this part; this file makes them again with
  `GoodEv0` (names with `G0`). **`badAG0_prob_gen`**, **`zeroPtAG0_null`**.
* `GoodEvF n G Lf`: a good hidden event with a frame constant `Lf θ` that depends on `θ`.
* `XF ΛV n ζ η η′`, **`errSampleAF_lint`**: the error bound from a bound `ΛV` of the mean of
  `1_G(θ)·Lf θ·(DKV n θ + Lf θ/n)`.
* `DKV_le_two`, `measurable_DKV`, `DKV_sq_int`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open BstLean.Part143
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142

/-- Measurable and the window: the part of `GoodEv` without the frame bound. -/
structure GoodEv0 (n : ℕ) (G : Set (HidParam (2 * n) (mW n))) : Prop where
  meas : MeasurableSet G
  win : ∀ θ ∈ G, 2 / ((2 * n : ℕ) : ℝ) * (48 / 100) ≤ Bh (2 * n) (mW n) θ ∧
      Bh (2 * n) (mW n) θ ≤ 2 / ((2 * n : ℕ) : ℝ) * (508 / 1000)

/-- A good hidden event with a frame constant `Lf θ` that depends on `θ`. -/
structure GoodEvF (n : ℕ) (G : Set (HidParam (2 * n) (mW n)))
    (Lf : HidParam (2 * n) (mW n) → ℝ) : Prop where
  meas : MeasurableSet G
  win : ∀ θ ∈ G, 2 / ((2 * n : ℕ) : ℝ) * (48 / 100) ≤ Bh (2 * n) (mW n) θ ∧
      Bh (2 * n) (mW n) θ ≤ 2 / ((2 * n : ℕ) : ℝ) * (508 / 1000)
  Lmeas : Measurable Lf
  Lnn : ∀ θ ∈ G, 0 ≤ Lf θ
  frame : ∀ θ ∈ G, ∀ w : Fin (mW n) → ℝ,
      ∫ u, (∑ j, eDir (bhat θ) (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n) ≤
        Lf θ / (n : ℝ) * ∑ j, w j ^ 2

lemma GoodEv.to0 {n : ℕ} {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G) :
    GoodEv0 n G := ⟨hG.meas, hG.win⟩

lemma GoodEvF.to0 {n : ℕ} {G : Set (HidParam (2 * n) (mW n))}
    {Lf : HidParam (2 * n) (mW n) → ℝ} (hG : GoodEvF n G Lf) : GoodEv0 n G :=
  ⟨hG.meas, hG.win⟩

end BstLean.Part145

-- ===== from Part140Frame =====

namespace BstLean.Part145

open BstLean.Part140
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part105 (BM sphere_cont_integrable)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137

section good

variable {n : ℕ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 4096 ≤ n) {θ :
    HidParam (2 * n) (mW n)} (hθ : θ ∈ G)

include hG hn hθ

omit hn in
/-- On `G`: `0.48·γ ≤ t|b̂|² ≤ 0.508·γ`. -/
lemma BhG0_hat : 2 / ((2 * n : ℕ) : ℝ) * (48 / 100) ≤ Bh (2 * n) (mW n) θ ∧
    Bh (2 * n) (mW n) θ ≤ 2 / ((2 * n : ℕ) : ℝ) * (508 / 1000) :=
  hG.win θ hθ

lemma BhG0_pos : 0 < Bh (2 * n) (mW n) θ := by
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  have := (BhG0_hat hG hθ).1
  nlinarith

lemma normSqG0_bhat_pos : 0 < normSq (bhat θ) := by
  have h := BhG0_pos hG hn hθ
  unfold Bh at h
  have hm : (0 : ℝ) < mW n := by
    have := mW_ge_million hn
    exact_mod_cast (by omega : 0 < mW n)
  by_contra h0
  have : normSq (bhat θ) = 0 := le_antisymm (not_lt.mp h0) (normSq_nonneg _)
  rw [this, mul_zero] at h
  exact lt_irrefl _ h

lemma bhatG0_ne : bhat θ ≠ 0 := by
  intro h0
  have h := normSqG0_bhat_pos hG hn hθ
  rw [h0] at h
  simp [normSq] at h

end good

end BstLean.Part145

-- ===== from Part140Tau =====

namespace BstLean.Part145

open BstLean.Part140
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part105 (BM sphere_cont_integrable)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137

variable {N m : ℕ}

section good

variable {n : ℕ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 4096 ≤ n) {θ :
    HidParam (2 * n) (mW n)} (hθ : θ ∈ G)

include hG hn hθ

/-- On `G`: `0.4798 ≤ ℓ₀² ≤ 0.508`. -/
theorem B0G0_window : 4798 / 10000 ≤ B0 (2 * n) (mW n) θ ∧ B0 (2 * n) (mW n) θ ≤ 508 / 1000 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  obtain ⟨hk1, hk2⟩ := kap1_window hn
  obtain ⟨hB1, hB2⟩ := BhG0_hat hG hθ
  have hBpos := BhG0_pos hG hn hθ
  have hksq1 : (49372 / 100000 : ℝ) ^ 2 ≤ kap1 (2 * n) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hk1 2
  have hksq2 : kap1 (2 * n) ^ 2 ≤ (4938 / 10000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hk2 2
  unfold B0
  constructor
  · rw [le_div_iff₀ hBpos]
    have h1 : 4798 / 10000 * Bh (2 * n) (mW n) θ ≤
        4798 / 10000 * (2 / ((2 * n : ℕ) : ℝ) * (508 / 1000)) :=
      mul_le_mul_of_nonneg_left hB2 (by norm_num)
    have h2 : 2 / ((2 * n : ℕ) : ℝ) * (49372 / 100000 : ℝ) ^ 2 ≤
        2 / ((2 * n : ℕ) : ℝ) * kap1 (2 * n) ^ 2 := mul_le_mul_of_nonneg_left hksq1 hγ.le
    have h3 : 4798 / 10000 * (2 / ((2 * n : ℕ) : ℝ) * (508 / 1000)) ≤
        2 / ((2 * n : ℕ) : ℝ) * (49372 / 100000 : ℝ) ^ 2 := by
      have e : 4798 / 10000 * (2 / ((2 * n : ℕ) : ℝ) * (508 / 1000)) =
          2 / ((2 * n : ℕ) : ℝ) * (4798 / 10000 * (508 / 1000)) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (by norm_num) hγ.le
    linarith
  · rw [div_le_iff₀ hBpos]
    have h1 : 508 / 1000 * (2 / ((2 * n : ℕ) : ℝ) * (48 / 100)) ≤
        508 / 1000 * Bh (2 * n) (mW n) θ := mul_le_mul_of_nonneg_left hB1 (by norm_num)
    have h2 : 2 / ((2 * n : ℕ) : ℝ) * kap1 (2 * n) ^ 2 ≤
        2 / ((2 * n : ℕ) : ℝ) * (4938 / 10000 : ℝ) ^ 2 := mul_le_mul_of_nonneg_left hksq2 hγ.le
    have h3 : 2 / ((2 * n : ℕ) : ℝ) * (4938 / 10000 : ℝ) ^ 2 ≤
        508 / 1000 * (2 / ((2 * n : ℕ) : ℝ) * (48 / 100)) := by
      have e : 508 / 1000 * (2 / ((2 * n : ℕ) : ℝ) * (48 / 100)) =
          2 / ((2 * n : ℕ) : ℝ) * (508 / 1000 * (48 / 100)) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_left (by norm_num) hγ.le
    linarith

/-- On `G`: `wLowH ≤ ŵ₀ ≤ 1/0.4798 − 1`. -/
theorem w0HG0_window : wLowH ≤ w0H (2 * n) (mW n) θ ∧
    w0H (2 * n) (mW n) θ ≤ 1 / (4798 / 10000) - 1 := by
  obtain ⟨hB1, hB2⟩ := B0G0_window hG hn hθ
  have hB0 : 0 < B0 (2 * n) (mW n) θ := by linarith
  unfold w0H wLowH
  have h1 := one_div_le_one_div_of_le hB0 hB2
  have h2 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4798 / 10000) hB1
  constructor <;> linarith

theorem tauHatG0_sq : tauHat (2 * n) (mW n) θ ^ 2 =
    Bh (2 * n) (mW n) θ * w0H (2 * n) (mW n) θ := by
  have h1 := (w0HG0_window hG hn hθ).1
  have h2 := wLowH_pos
  have hB := BhG0_pos hG hn hθ
  unfold tauHat
  rw [← w0H_eq, max_eq_right (by linarith)]
  exact Real.sq_sqrt (mul_nonneg hB.le (by linarith))

theorem tauHatG0_pos : 0 < tauHat (2 * n) (mW n) θ := by
  have h1 := (w0HG0_window hG hn hθ).1
  have h2 := wLowH_pos
  have hB := BhG0_pos hG hn hθ
  unfold tauHat
  rw [← w0H_eq, max_eq_right (by linarith)]
  exact Real.sqrt_pos.mpr (mul_pos hB (by linarith))

end good

end BstLean.Part145

-- ===== from Part140Cheap =====

namespace BstLean.Part145

open BstLean.Part140
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138

section good

variable {n : ℕ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 4096 ≤ n) {θ :
    HidParam (2 * n) (mW n)} (hθ : θ ∈ G)

include hG hn hθ

/-- On `G` and the good inputs: `|ŵ − ŵ₀| ≤ ζ′`. -/
lemma wCloseHG0 {ζ : ℝ} (hζ1 : ζ < 1) {u : Fin (2 * n) → ℝ}
    (hu : (u, θ) ∈ goodUH (2 * n) (mW n) ζ) :
    |wH (2 * n) (mW n) u θ - w0H (2 * n) (mW n) θ| ≤ zetaPH ζ := by
  obtain ⟨hD, hl⟩ := hu
  have hζ0 : 0 ≤ ζ := (abs_nonneg _).trans hD
  have h1ζ : 0 < 1 - ζ := by linarith
  have hw := w_diff (by norm_num : (0 : ℝ) < 4798 / 10000) (B0G0_window hG hn hθ).1 hζ1 hD hl
  refine hw.trans ?_
  unfold zetaPH
  rw [one_div_mul_eq_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have : (2 + ζ) * |lamH (2 * n) (mW n) (u, θ).1 (u, θ).2 - 1| ≤ (2 + ζ) * ζ :=
    mul_le_mul_of_nonneg_left hl (by linarith)
  have hD' : |Dn (2 * n) (mW n) (u, θ).1 (u, θ).2 - 1| ≤ ζ := hD
  nlinarith

/-- **The good inputs**: for `θ ∈ G` and `u ∈ G_ζ`: `λ̂(u) > 0`, and the squared Hellinger
distance of `N(c, (σ̂(u)/λ̂(u))²I)` and `N(c, τ̂₀²I)` is at most `n(ŵ − ŵ₀)²/(wLowH²·cRhoH ζ)`. -/
theorem goodG0_ptH {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) {u : Fin (2 * n) → ℝ}
    (hu : (u, θ) ∈ goodUH (2 * n) (mW n) ζ) :
    0 < lam (bhat θ) (hid2 θ.1 θ.2 u) ∧
      hellG n (sig (2 / (mW n : ℝ)) (bhat θ) (hid2 θ.1 θ.2 u) /
          lam (bhat θ) (hid2 θ.1 θ.2 u)) (tauHat (2 * n) (mW n) θ) ≤
        (n : ℝ) / (wLowH ^ 2 * cRhoH ζ) *
          (wH (2 * n) (mW n) u θ - w0H (2 * n) (mW n) θ) ^ 2 := by
  have hN : 1 ≤ 2 * n := by omega
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hmpos : (0 : ℝ) < mW n := by exact_mod_cast (by omega : 0 < mW n)
  have hnpos : (0 : ℝ) < n := by
    have : (4096 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  obtain ⟨hk1, -⟩ := kap1_window hn
  have hkpos : 0 < kap1 (2 * n) := by linarith
  have hul : |lamH (2 * n) (mW n) u θ - 1| ≤ ζ := hu.2
  have hlH : 0 < lamH (2 * n) (mW n) u θ := by
    have := abs_le.mp hul
    linarith
  have hTpos : 0 < That (2 * n) (mW n) u θ := by
    have e : That (2 * n) (mW n) u θ =
        lamH (2 * n) (mW n) u θ * (2 / ((2 * n : ℕ) : ℝ) * kap1 (2 * n)) := by
      unfold lamH
      field_simp
    rw [e]
    positivity
  have hnb := normSqG0_bhat_pos hG hn hθ
  have hXpos : 0 < dotp (hid2 θ.1 θ.2 u) (bhat θ) := by
    have e : That (2 * n) (mW n) u θ = 2 / (mW n : ℝ) * dotp (hid2 θ.1 θ.2 u) (bhat θ) := rfl
    rw [e] at hTpos
    by_contra h0
    have : dotp (hid2 θ.1 θ.2 u) (bhat θ) ≤ 0 := not_lt.mp h0
    have : 2 / (mW n : ℝ) * dotp (hid2 θ.1 θ.2 u) (bhat θ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) this
    linarith
  set l := lam (bhat θ) (hid2 θ.1 θ.2 u) with hl
  set s := sig (2 / (mW n : ℝ)) (bhat θ) (hid2 θ.1 θ.2 u) with hs
  have hl0 : 0 < l := by
    have e : l = dotp (hid2 θ.1 θ.2 u) (bhat θ) / normSq (bhat θ) := rfl
    rw [e]
    positivity
  refine ⟨hl0, ?_⟩
  have hs0 : 0 ≤ s := by rw [hs]; unfold sig; positivity
  set τ := s / l with hτ
  have hτ0 : 0 ≤ τ := div_nonneg hs0 hl0.le
  set K := Bh (2 * n) (mW n) θ with hK
  have hKpos : 0 < K := BhG0_pos hG hn hθ
  set w := wH (2 * n) (mW n) u θ with hw
  set wb := w0H (2 * n) (mW n) θ with hwb
  have hτ2 : τ ^ 2 = K * w := by
    rw [hτ, div_pow]
    exact tauH_sq hN hm u hnb.ne' hkpos.ne' hTpos.ne'
  have hτ02 : tauHat (2 * n) (mW n) θ ^ 2 = K * wb := tauHatG0_sq hG hn hθ
  have hτ0pos := tauHatG0_pos hG hn hθ
  obtain ⟨hwb1, -⟩ := w0HG0_window hG hn hθ
  have hwLow := wLowH_pos
  have hwb0 : 0 < wb := by linarith
  have hw0 : 0 ≤ w := by
    have : 0 ≤ K * w := by rw [← hτ2]; positivity
    exact nonneg_of_mul_nonneg_right this hKpos
  have hclose : |w - wb| ≤ zetaPH ζ := wCloseHG0 hG hn hθ hζ1 hu
  -- the ratio
  have hr : rLowH ζ * wb ≤ w := by
    have hz := zetaPH_nonneg hζ0 hζ1
    unfold rLowH
    rcases le_total (1 - zetaPH ζ / wLowH) 0 with h0 | h0
    · rw [max_eq_left h0, zero_mul]; exact hw0
    · rw [max_eq_right h0]
      have h1 : zetaPH ζ ≤ zetaPH ζ / wLowH * wb := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hwLow]
        exact mul_le_mul_of_nonneg_left hwb1 hz
      have h2 := (abs_le.mp hclose).1
      nlinarith
  have hr2 : rLowH ζ * tauHat (2 * n) (mW n) θ ^ 2 ≤ τ ^ 2 := by
    rw [hτ2, hτ02]
    have := mul_le_mul_of_nonneg_left hr hKpos.le
    linarith
  have h1 := hellG_le (by omega : 2 ≤ n) hτ0 hτ0pos
  have h2 := hell_ratio hτ0 hτ0pos (rLowH_nonneg ζ) hr2
  have e4 : tauHat (2 * n) (mW n) θ ^ 4 = (K * wb) ^ 2 := by
    rw [← hτ02]; ring
  have h3 : (τ ^ 2 - tauHat (2 * n) (mW n) θ ^ 2) ^ 2 /
      (tauHat (2 * n) (mW n) θ ^ 4 * ((1 + √(rLowH ζ)) ^ 2 * (1 + rLowH ζ))) =
      (w - wb) ^ 2 / (wb ^ 2 * cRhoH ζ) := by
    rw [e4, hτ2, hτ02]
    unfold cRhoH
    have hc := cRhoH_pos ζ
    unfold cRhoH at hc
    field_simp
  have h4 : (w - wb) ^ 2 / (wb ^ 2 * cRhoH ζ) ≤ (w - wb) ^ 2 / (wLowH ^ 2 * cRhoH ζ) := by
    refine div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos (by positivity) (cRhoH_pos ζ)) ?_
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hwLow.le hwb1 2) (cRhoH_pos ζ).le
  calc hellG n τ (tauHat (2 * n) (mW n) θ)
      ≤ (n : ℝ) * (τ - tauHat (2 * n) (mW n) θ) ^ 2 /
          (τ ^ 2 + tauHat (2 * n) (mW n) θ ^ 2) := h1
    _ = (n : ℝ) * ((τ - tauHat (2 * n) (mW n) θ) ^ 2 /
          (τ ^ 2 + tauHat (2 * n) (mW n) θ ^ 2)) := by
      rw [mul_div_assoc]
    _ ≤ (n : ℝ) * ((w - wb) ^ 2 / (wLowH ^ 2 * cRhoH ζ)) :=
      mul_le_mul_of_nonneg_left ((h2.trans (le_of_eq h3)).trans h4) hnpos.le
    _ = _ := by ring

/-- On the good event `KfunH n ζ (·, θ)` is bounded. -/
lemma KfunHG0_le {ζ : ℝ} (hζ1 : ζ < 1) (u : Fin (2 * n) → ℝ) :
    KfunH n ζ (u, θ) ≤ (n : ℝ) / (wLowH ^ 2 * cRhoH ζ) * zetaPH ζ ^ 2 + 1 := by
  have hc := cRhoH_pos ζ
  have hwl := wLowH_pos
  have hC : 0 ≤ (n : ℝ) / (wLowH ^ 2 * cRhoH ζ) := by positivity
  by_cases hp : (u, θ) ∈ goodUH (2 * n) (mW n) ζ
  · rw [KfunH_of_mem hp]
    have hclose := wCloseHG0 hG hn hθ hζ1 hp
    have hsq : (wH (2 * n) (mW n) u θ - w0H (2 * n) (mW n) θ) ^ 2 ≤ zetaPH ζ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hclose 2
    have := mul_le_mul_of_nonneg_left hsq hC
    linarith
  · rw [KfunH_of_notMem hp]
    have : 0 ≤ (n : ℝ) / (wLowH ^ 2 * cRhoH ζ) * zetaPH ζ ^ 2 := by positivity
    linarith

lemma KfunHG0_integrable {ζ : ℝ} (hζ1 : ζ < 1) :
    Integrable (fun u => KfunH n ζ (u, θ)) (uniformSphere (2 * n)) := by
  have := uniformSphere_isProbability (2 * n) (by omega)
  refine Integrable.of_bound ((measurable_KfunH (by omega) ζ).comp
    measurable_prodMk_right).aestronglyMeasurable
    ((n : ℝ) / (wLowH ^ 2 * cRhoH ζ) * zetaPH ζ ^ 2 + 1) (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (KfunH_nonneg n ζ (u, θ))]
  exact KfunHG0_le hG hn hθ hζ1 u

/-- **The cheap stand-in against the exact stand-in with the computed centre, at one `c`.** For
`n ≥ 4096`, `θ ∈ G`, `0 ≤ ζ < 1`, every `c ∈ ℝⁿ`, bounded measurable `φ`, real `a`:
`(E_{ν̂_c} φ − E_{ν̂′_c} φ)² ≤ 2·HbarH n ζ θ·(E_{ν̂_c}(φ − a)² + E_{ν̂′_c}(φ − a)²)`. -/
theorem cheapMeanHatG0 {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) (c : Fin n → ℝ)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) (a : ℝ) :
    (∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (bhat θ) c -
        ∫ x, φ x ∂cheapIn c (tauHat (2 * n) (mW n) θ)) ^ 2 ≤
      2 * HbarH n ζ θ *
        (∫ x, (φ x - a) ^ 2
            ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (bhat θ) c +
          ∫ x, (φ x - a) ^ 2 ∂cheapIn c (tauHat (2 * n) (mW n) θ)) := by
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  have hh : Measurable (hid2 θ.1 θ.2) := (continuous_hid2 θ.1 θ.2).measurable
  have p1 := standIn_prob (n := n) (uniformSphere (2 * n)) hh (2 / (mW n : ℝ)) (bhat θ) c
  have p2 := cheapIn_prob c (tauHat (2 * n) (mW n) θ)
  have hψ : BM (fun x => φ x - a) := hφ.sub (BM.const a)
  have hK : ∀ u : Fin (2 * n) → ℝ,
      (0 < lam (bhat θ) (hid2 θ.1 θ.2 u) ∧
        hellG n (sig (2 / (mW n : ℝ)) (bhat θ) (hid2 θ.1 θ.2 u) /
          lam (bhat θ) (hid2 θ.1 θ.2 u)) (tauHat (2 * n) (mW n) θ) ≤ KfunH n ζ (u, θ)) ∨
      1 ≤ KfunH n ζ (u, θ) := by
    intro u
    by_cases hp : (u, θ) ∈ goodUH (2 * n) (mW n) ζ
    · left
      rw [KfunH_of_mem hp]
      exact goodG0_ptH hG hn hθ hζ0 hζ1 hp
    · right
      rw [KfunH_of_notMem hp]
  have h := cheap_mix (uniformSphere (2 * n)) (by omega : 2 ≤ n) (2 / (mW n : ℝ)) (bhat θ) c hh
    (tauHatG0_pos hG hn hθ) ((measurable_KfunH (by omega) ζ).comp measurable_prodMk_right)
    (KfunHG0_integrable hG hn hθ hζ1) hK hψ
  have e1 : ∫ x, (φ x - a)
      ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (bhat θ) c =
      ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (bhat θ) c -
        a := by
    rw [integral_sub (hφ.integrable _) (integrable_const _)]
    simp
  have e2 : ∫ x, (φ x - a) ∂cheapIn c (tauHat (2 * n) (mW n) θ) =
      ∫ x, φ x ∂cheapIn c (tauHat (2 * n) (mW n) θ) - a := by
    rw [integral_sub (hφ.integrable _) (integrable_const _)]
    simp
  rw [e1, e2] at h
  have e3 : (∫ x, φ x
        ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (bhat θ) c - a -
      (∫ x, φ x ∂cheapIn c (tauHat (2 * n) (mW n) θ) - a)) =
      ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (bhat θ) c -
        ∫ x, φ x ∂cheapIn c (tauHat (2 * n) (mW n) θ) := by ring
  rw [e3] at h
  exact h

end good

section mean

variable {n : ℕ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 4096 ≤ n) {ζ : ℝ}
    (hζ0 : 0 < ζ) (hζ1 : ζ < 1)

include hG hn hζ0 hζ1

/-- **The mean of `HbarH` on the good event.** `θ ↦ 1_goodHat(θ)·HbarH n ζ θ` is integrable, and
`E_θ[1_goodHat·HbarH n ζ θ] ≤ EHH n ζ`. -/
theorem HbarHG0_mean :
    Integrable (G.indicator (HbarH n ζ)) (hidGauss (2 * n) (mW n)) ∧
      ∫ θ, G.indicator (HbarH n ζ) θ ∂hidGauss (2 * n) (mW n) ≤ EHH n ζ := by
  have hN : 1 ≤ 2 * n := by omega
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have := uniformSphere_isProbability (2 * n) hN
  have mE := hG.meas
  obtain ⟨hk1, -⟩ := kap1_window hn
  have hkpos : 0 < kap1 (2 * n) := by linarith
  set μP := (uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n)) with hμP
  set C : ℝ := (n : ℝ) / (wLowH ^ 2 * cRhoH ζ) with hC
  have hC0 : 0 ≤ C := by
    have := cRhoH_pos ζ
    have := wLowH_pos
    rw [hC]; positivity
  set S := goodSH G ζ with hS
  set Bd : Set ((Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) :=
    {p | p.2 ∈ G ∧ p ∉ goodUH (2 * n) (mW n) ζ} with hBd
  have mS : MeasurableSet S := goodSH_meas hN mE ζ
  have mBd : MeasurableSet Bd := (measurable_snd mE).inter (goodUH_meas hN ζ).compl
  set F1 : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) → ℝ :=
    S.indicator (fun p => (wH (2 * n) (mW n) p.1 p.2 - w0H (2 * n) (mW n) p.2) ^ 2) with hF1
  set F2 : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) → ℝ :=
    Bd.indicator (fun _ => (1 : ℝ)) with hF2
  obtain ⟨iF1, hF1le⟩ := tauFluctH_gen_int (N := 2 * n) (m := mW n) hN hm hkpos mE
    (by norm_num : (0 : ℝ) < 4798 / 10000) hζ0.le hζ1
    (fun θ hθ => (B0G0_window hG hn hθ).1)
  have iF2 : Integrable F2 μP := (integrable_const (1 : ℝ)).indicator mBd
  have iF : Integrable (fun p => C * F1 p + F2 p) μP := (iF1.const_mul C).add iF2
  -- the pointwise identity
  have hpt : ∀ (θ : HidParam (2 * n) (mW n)) (u : Fin (2 * n) → ℝ),
      G.indicator (fun θ => KfunH n ζ (u, θ)) θ = C * F1 (u, θ) + F2 (u, θ) := by
    intro θ u
    by_cases hθ : θ ∈ G
    · rw [Set.indicator_of_mem hθ]
      by_cases hp : (u, θ) ∈ goodUH (2 * n) (mW n) ζ
      · have h1 : (u, θ) ∈ S := ⟨hθ, hp⟩
        have h2 : (u, θ) ∉ Bd := fun h => h.2 hp
        rw [KfunH_of_mem hp, hF1, hF2, Set.indicator_of_mem h1, Set.indicator_of_notMem h2,
          add_zero]
      · have h1 : (u, θ) ∉ S := fun h => hp h.2
        have h2 : (u, θ) ∈ Bd := ⟨hθ, hp⟩
        rw [KfunH_of_notMem hp, hF1, hF2, Set.indicator_of_notMem h1, Set.indicator_of_mem h2,
          mul_zero, zero_add]
    · have h1 : (u, θ) ∉ S := fun h => hθ h.1
      have h2 : (u, θ) ∉ Bd := fun h => hθ h.1
      rw [Set.indicator_of_notMem hθ, hF1, hF2, Set.indicator_of_notMem h1,
        Set.indicator_of_notMem h2, mul_zero, zero_add]
  have hfun : G.indicator (HbarH n ζ) =
      fun θ => ∫ u, (C * F1 (u, θ) + F2 (u, θ)) ∂uniformSphere (2 * n) := by
    funext θ
    simp_rw [← hpt θ]
    by_cases hθ : θ ∈ G
    · simp only [Set.indicator_of_mem hθ]; rfl
    · simp [Set.indicator_of_notMem hθ]
  have hint : Integrable (fun θ => ∫ u, (C * F1 (u, θ) + F2 (u, θ)) ∂uniformSphere (2 * n))
      (hidGauss (2 * n) (mW n)) := iF.integral_prod_right
  refine ⟨by rw [hfun]; exact hint, ?_⟩
  rw [hfun, ← integral_prod_symm _ iF, integral_add (iF1.const_mul C) iF2, integral_const_mul]
  have h1 : ∫ p, F1 p ∂μP ≤ OmegaH2 n ζ := hF1le
  have h2 : ∫ p, F2 p ∂μP ≤ BetaH n ζ := by
    have e : ∫ p, F2 p ∂μP = μP.real Bd := by
      rw [hF2, integral_indicator mBd, setIntegral_const, smul_eq_mul, mul_one]
    rw [e]
    have hsub : Bd ⊆ {p | p ∉ goodUH (2 * n) (mW n) ζ} := fun p hp => hp.2
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans
      (tauBadH_gen (N := 2 * n) (m := mW n) hN hm hkpos hζ0)
  unfold EHH
  have := mul_le_mul_of_nonneg_left h1 hC0
  linarith

end mean

end BstLean.Part145

-- ===== from Part140Err =====

namespace BstLean.Part145

open BstLean.Part140
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM

lemma goodWHG0_meas {n : ℕ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) : MeasurableSet
    (goodWHG G) :=
  (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) (hG.meas)

lemma measurable_errGHG0 {n : ℕ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤
    n) : Measurable (errGHG G) := by
  have hN : 1 ≤ 2 * n := by omega
  have e : errGHG G = ({t | t.1 ∈ goodWHG G} : Set (MlpParam (2 * n) (mW n) n ×
      MlpParam n (mA n) n × MlpParam n (mF n) 1)).indicator
      (fun t => (gHat t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2) ^ 2) := by
    funext t
    by_cases ht : t.1 ∈ goodWHG G
    · rw [Set.indicator_of_mem (show t ∈ {t : MlpParam (2 * n) (mW n) n ×
        MlpParam n (mA n) n × MlpParam n (mF n) 1 | t.1 ∈ goodWHG G} from ht)]
      unfold errGHG
      rw [Set.indicator_of_mem ht]
    · rw [Set.indicator_of_notMem (show t ∉ {t : MlpParam (2 * n) (mW n) n ×
        MlpParam n (mA n) n × MlpParam n (mF n) 1 | t.1 ∈ goodWHG G} from ht)]
      unfold errGHG
      rw [Set.indicator_of_notMem ht]
  rw [e]
  exact (((measurable_gHat hN).sub (BstLean.Part131.measurable_Bn hN)).pow_const 2).indicator
    (measurable_fst (goodWHG0_meas hG))

end BstLean.Part145

-- ===== from Part141Tau =====

namespace BstLean.Part145

open BstLean.Part141
open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 BstLean.Part138 BstLean.Part140

lemma goodAG0_meas {n : ℕ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤ n) :
    MeasurableSet (goodAG G) :=
  (hG.meas).inter (measurableSet_le (measurable_dA hn) measurable_const)

section good

variable {n : ℕ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 4096 ≤ n) {θ :
    HidParam (2 * n) (mW n)} (hθ : θ ∈ goodAG G)

include hG hn hθ

/-- On `goodAG n`, with `γ = 2/N`: `τ̂₀² ≥ 0.46·γ`, `τ̃₀² ≥ 0.458·γ` and
`(τ̃₀² − τ̂₀²)² ≤ γ²·(42·t|b̃ − b̂|²/γ + 3/(qA n)²)`. -/
theorem scalarAG0 :
    2 / ((2 * n : ℕ) : ℝ) * (46 / 100) ≤ tauHat (2 * n) (mW n) θ ^ 2 ∧
    2 / ((2 * n : ℕ) : ℝ) * (458 / 1000) ≤ tauA n θ ^ 2 ∧
    (tauA n θ ^ 2 - tauHat (2 * n) (mW n) θ ^ 2) ^ 2 ≤
      (2 / ((2 * n : ℕ) : ℝ)) ^ 2 *
        (42 * (Part141.dA n θ / (2 / ((2 * n : ℕ) : ℝ))) + 3 * (1 / (qA n : ℝ)) ^ 2) := by
  have hn1 : 1 ≤ n := by omega
  have hnR : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  set γ : ℝ := 2 / ((2 * n : ℕ) : ℝ) with hγd
  have hγ : 0 < γ := by rw [hγd, hNcast]; positivity
  have hγ1 : γ ≤ 1 := by
    rw [hγd, hNcast, div_le_one (by positivity)]
    linarith
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_million hn
    linarith
  have hq' : (0 : ℝ) < qA n := by exact_mod_cast qA_pos hn1
  have hqR : (40960000 : ℝ) ≤ qA n := by rw [qA_cast]; linarith
  obtain ⟨hB1, hB2⟩ := BhG0_hat hG hθ.1
  obtain ⟨hk1, hk2⟩ := kap1_window hn
  have hdle : Part141.dA n θ ≤ γ / 1000000 := hθ.2
  have hd0 := dA_nonneg n θ
  set B : ℝ := Bh (2 * n) (mW n) θ with hBd
  set B' : ℝ := 2 / (mW n : ℝ) * normSq (bA n θ) with hB'd
  set c : ℝ := c1Hat (2 * n) with hcd
  set c' : ℝ := ((c1A n : ℚ) : ℝ) with hc'd
  have hB'0 : 0 ≤ B' := mul_nonneg (by positivity) (normSq_nonneg _)
  -- the squares of the two scalars
  have eT : tauHat (2 * n) (mW n) θ ^ 2 = B * relu (B * c - 1) := by
    rw [← tauOf_bhat]
    unfold tauOf
    rw [Real.sq_sqrt (mul_nonneg (mul_nonneg (by positivity) (normSq_nonneg _))
      (relu_nonneg _))]
    rfl
  have eT' : tauA n θ ^ 2 = B' * relu (B' * c' - 1) := by
    unfold tauA tauOf
    rw [Real.sq_sqrt (mul_nonneg (mul_nonneg (by positivity) (normSq_nonneg _))
      (relu_nonneg _))]
  -- normalized units
  have hκ : γ * c = 1 / kap1 (2 * n) ^ 2 := by
    rw [hcd]
    unfold c1Hat
    rw [← hγd]
    field_simp
  have hksq1 : (49372 / 100000 : ℝ) ^ 2 ≤ kap1 (2 * n) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hk1 2
  have hksq2 : kap1 (2 * n) ^ 2 ≤ (4938 / 10000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by linarith) hk2 2
  have hkpos : (0 : ℝ) < kap1 (2 * n) ^ 2 := by nlinarith
  have hκ1 : 4101 / 1000 ≤ γ * c := by
    rw [hκ, le_div_iff₀ hkpos]
    nlinarith
  have hκ2 : γ * c ≤ 41025 / 10000 := by
    rw [hκ, div_le_iff₀ hkpos]
    nlinarith
  have hcerr : |γ * c' - γ * c| ≤ 1 / (qA n : ℝ) * (γ * c) := by
    rw [← mul_sub, abs_mul, abs_of_pos hγ]
    have h1 := c1A_err hn1
    have h2 : γ * |c' - c| ≤ 1 * (1 / (qA n : ℝ)) :=
      mul_le_mul hγ1 h1 (abs_nonneg _) (by norm_num)
    have h3 : (1 : ℝ) / (qA n : ℝ) * 1 ≤ 1 / (qA n : ℝ) * (γ * c) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hdiff : (B' - B) ^ 2 ≤ 2 * Part141.dA n θ * (B' + B) := by
    have h := normSq_diff_sq (bA n θ) (bhat θ)
    have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ (2 / (mW n : ℝ)) ^ 2)
    have e1 : (B' - B) ^ 2 = (2 / (mW n : ℝ)) ^ 2 * (normSq (bA n θ) - normSq (bhat θ)) ^ 2 := by
      rw [hB'd, hBd]; unfold Bh; ring
    have e2 : 2 * Part141.dA n θ * (B' + B) = (2 / (mW n : ℝ)) ^ 2 *
        (2 * normSq (bA n θ - bhat θ) * (normSq (bA n θ) + normSq (bhat θ))) := by
      rw [hB'd, hBd]; unfold Bh Part141.dA; ring
    rw [e1, e2]
    exact h2
  have hN := tauN (β := B / γ) (β' := B' / γ) (κ := γ * c) (κ' := γ * c') (ξ := Part141.dA n θ / γ)
    (e := 1 / (qA n : ℝ))
    (by rw [le_div_iff₀ hγ]; linarith) (by rw [div_le_iff₀ hγ]; linarith) (by positivity)
    (by positivity) (by rw [div_le_iff₀ hγ]; linarith)
    (by
      have e1 : (B' / γ - B / γ) ^ 2 = (B' - B) ^ 2 / γ ^ 2 := by field_simp
      have e2 : 2 * (Part141.dA n θ / γ) * (B' / γ + B / γ) = 2 * Part141.dA n θ * (B' + B) / γ ^ 2
          := by
        field_simp
      rw [e1, e2]
      exact div_le_div_of_nonneg_right hdiff (by positivity))
    hκ1 hκ2 hcerr (by positivity)
    (by rw [div_le_div_iff₀ hq' (by norm_num)]; linarith)
  have eN : B / γ * (γ * c) = B * c := by field_simp
  have eN' : B' / γ * (γ * c') = B' * c' := by field_simp
  rw [eN, eN'] at hN
  obtain ⟨hN1, hN2, hN3⟩ := hN
  rw [eT, eT']
  have ea : B * relu (B * c - 1) = γ * (B / γ * relu (B * c - 1)) := by field_simp
  have eb : B' * relu (B' * c' - 1) = γ * (B' / γ * relu (B' * c' - 1)) := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [ea]; exact mul_le_mul_of_nonneg_left hN1 hγ.le
  · rw [eb]; exact mul_le_mul_of_nonneg_left hN2 hγ.le
  · rw [ea, eb, ← mul_sub, mul_pow]
    exact mul_le_mul_of_nonneg_left hN3 (by positivity)

lemma tauAG0_pos : 0 < tauA n θ := by
  have h := (scalarAG0 hG hn hθ).2.1
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  have h0 : 0 ≤ tauA n θ := by unfold tauA tauOf; exact Real.sqrt_nonneg _
  have hsq : 0 < tauA n θ ^ 2 := by nlinarith
  exact lt_of_le_of_ne h0 (fun h => by rw [← h] at hsq; norm_num at hsq)

/-- **The Hellinger price of the arithmetic centre and scalar.** On `goodAG n`:
`8·hellG n τ̃₀ τ̂₀ + 2n·t|b̃ − b̂|²/τ̃₀² ≤ n·(404·t|b̃ − b̂|²/γ + 29/(qA n)²)`. -/
theorem KAG0_le :
    8 * hellG n (tauA n θ) (tauHat (2 * n) (mW n) θ) +
        2 * (n : ℝ) * Part141.dA n θ / tauA n θ ^ 2 ≤
      (n : ℝ) * (404 * (Part141.dA n θ / (2 / ((2 * n : ℕ) : ℝ))) + 29 * (1 / (qA n : ℝ)) ^ 2) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  set γ : ℝ := 2 / ((2 * n : ℕ) : ℝ) with hγd
  have hγ : 0 < γ := by rw [hγd, hNcast]; positivity
  obtain ⟨h1, h2, h3⟩ := scalarAG0 hG hn hθ
  rw [← hγd] at h1 h2 h3
  have ha := tauAG0_pos hG hn hθ
  have hb := tauHatG0_pos hG hn hθ.1
  have hd0 := dA_nonneg n θ
  set a : ℝ := tauA n θ with had
  set b : ℝ := tauHat (2 * n) (mW n) θ with hbd
  set T' : ℝ := a ^ 2 / γ with hT'
  set T : ℝ := b ^ 2 / γ with hT
  set ξ : ℝ := Part141.dA n θ / γ with hξ
  have hTl : 46 / 100 ≤ T := by rw [hT, le_div_iff₀ hγ]; linarith
  have hT'l : 458 / 1000 ≤ T' := by rw [hT', le_div_iff₀ hγ]; linarith
  have hξ0 : 0 ≤ ξ := by rw [hξ]; positivity
  have hD : (T' - T) ^ 2 ≤ 42 * ξ + 3 * (1 / (qA n : ℝ)) ^ 2 := by
    have e : (T' - T) ^ 2 = (a ^ 2 - b ^ 2) ^ 2 / γ ^ 2 := by rw [hT', hT]; field_simp
    rw [e, div_le_iff₀ (by positivity)]
    linarith
  have hK := K_num hTl hT'l hξ0 hD
  have hH := hellG_le (n := n) (by omega) ha.le hb
  have hF := hell_frac ha.le hb
  have e1 : (a ^ 2 - b ^ 2) ^ 2 / (a ^ 2 + b ^ 2) ^ 2 = (T' - T) ^ 2 / (T' + T) ^ 2 := by
    rw [hT', hT]; field_simp
  have e2 : 2 * (n : ℝ) * Part141.dA n θ / a ^ 2 = (n : ℝ) * (2 * ξ / T') := by
    rw [hT', hξ]; field_simp
  have hH2 : hellG n a b ≤ (n : ℝ) * ((T' - T) ^ 2 / (T' + T) ^ 2) := by
    rw [← e1]
    refine hH.trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hF hnpos.le
  rw [e2]
  have := mul_le_mul_of_nonneg_left hK hnpos.le
  nlinarith

end good

end BstLean.Part145

-- ===== from Part141Err =====

namespace BstLean.Part145

open BstLean.Part141
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140

section fixed

variable {n : ℕ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 4096 ≤ n) {θ :
    HidParam (2 * n) (mW n)} (hθ : θ ∈ goodAG G)

include hG hn hθ

/-- For fixed `(M₁, M₂) ∈ goodAG n` and fixed `M₃`: the mean over `(A, F)` of `(g̃ − ĝ)²`. -/
lemma diffFixedMG0 (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ) :
    ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal ((gA ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
        gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2)
      ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) ≤
    ENNReal.ofReal ((2 * (normSq (M₃.mulVec (bA n θ - bhat θ)) / tauA n θ ^ 2) +
      8 * hellG n (tauA n θ) (tauHat (2 * n) (mW n) θ)) * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have ha := tauAG0_pos hG hn hθ
  have hb := tauHatG0_pos hG hn hθ.1
  set a : ℝ := tauA n θ with had
  set b : ℝ := tauHat (2 * n) (mW n) θ with hbd
  set c : Fin n → ℝ := M₃.mulVec (bhat θ) with hc
  set c' : Fin n → ℝ := M₃.mulVec (bA n θ) with hc'
  have hcc : c' - c = M₃.mulVec (bA n θ - bhat θ) := by
    rw [hc, hc', Matrix.mulVec_sub]
  set w : ℝ := normSq (c' - c) / a ^ 2 with hw
  have hw0 : 0 ≤ w := div_nonneg (normSq_nonneg _) (sq_nonneg _)
  set H : ℝ := 4 * hellG n a b with hH
  have hH0 : 0 ≤ H := mul_nonneg (by norm_num) (hellG_nonneg _ _ _)
  set o1 : (Fin n → ℝ) → Fin n → ℝ := fun γ => c' + a • γ with ho1
  set o2 : (Fin n → ℝ) → Fin n → ℝ := fun γ => c + a • γ with ho2
  set o3 : (Fin n → ℝ) → Fin n → ℝ := fun γ => c + b • γ with ho3
  have mo1 : Measurable o1 := measurable_const.add (measurable_const_smul a)
  have mo2 : Measurable o2 := measurable_const.add (measurable_const_smul a)
  have mo3 : Measurable o3 := measurable_const.add (measurable_const_smul b)
  set P := stdGauss (Fin n) with hP
  have key : ∀ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal ((gA ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
        gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2) ≤
      ENNReal.ofReal w * (Lout P o1 p + Lout P o2 p) +
        ENNReal.ofReal H * (Lout P o2 p + Lout P o3 p) := by
    rintro ⟨A, F⟩
    have h := diff_pt hn1 c c' ha hb A F
    have i1 : 0 ≤ ∫ x, phiS A F x ^ 2 ∂cheapIn c' a := integral_nonneg fun _ => sq_nonneg _
    have i2 : 0 ≤ ∫ x, phiS A F x ^ 2 ∂cheapIn c a := integral_nonneg fun _ => sq_nonneg _
    have i3 : 0 ≤ ∫ x, phiS A F x ^ 2 ∂cheapIn c b := integral_nonneg fun _ => sq_nonneg _
    rw [← sqInt_cheapIn hn1 c' a A F, ← sqInt_cheapIn hn1 c a A F, ← sqInt_cheapIn hn1 c b A F,
      ← ENNReal.ofReal_add i1 i2, ← ENNReal.ofReal_add i2 i3,
      ← ENNReal.ofReal_mul hw0, ← ENNReal.ofReal_mul hH0,
      ← ENNReal.ofReal_add (mul_nonneg hw0 (add_nonneg i1 i2))
        (mul_nonneg hH0 (add_nonneg i2 i3))]
    refine ENNReal.ofReal_le_ofReal ?_
    exact h
  refine (lintegral_mono key).trans (le_of_eq ?_)
  have m1 := measurable_Lout (mA := mA n) (mF := mF n) P mo1
  have m2 := measurable_Lout (mA := mA n) (mF := mF n) P mo2
  have m3 := measurable_Lout (mA := mA n) (mF := mF n) P mo3
  have h4 : (0 : ℝ) ≤ 4 / (n : ℝ) := by positivity
  have m12 : Measurable (fun p : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      Lout P o1 p + Lout P o2 p) := m1.add m2
  have m23 : Measurable (fun p : MlpParam n (mA n) n × MlpParam n (mF n) 1 =>
      Lout P o2 p + Lout P o3 p) := m2.add m3
  have hA : ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1, (Lout P o1 p + Lout P o2 p)
      ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) =
      ENNReal.ofReal (4 / (n : ℝ)) + ENNReal.ofReal (4 / (n : ℝ)) := by
    rw [lintegral_add_left m1, lintegral_Lout P hn1 hmA hmF mo1,
      lintegral_Lout P hn1 hmA hmF mo2]
  have hB : ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1, (Lout P o2 p + Lout P o3 p)
      ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) =
      ENNReal.ofReal (4 / (n : ℝ)) + ENNReal.ofReal (4 / (n : ℝ)) := by
    rw [lintegral_add_left m2, lintegral_Lout P hn1 hmA hmF mo2,
      lintegral_Lout P hn1 hmA hmF mo3]
  rw [lintegral_add_left (m12.const_mul (ENNReal.ofReal w)), lintegral_const_mul _ m12,
    lintegral_const_mul _ m23, hA, hB]
  rw [← ENNReal.ofReal_add h4 h4, ← ENNReal.ofReal_mul hw0, ← ENNReal.ofReal_mul hH0,
    ← ENNReal.ofReal_add (mul_nonneg hw0 (add_nonneg h4 h4))
      (mul_nonneg hH0 (add_nonneg h4 h4))]
  congr 1
  rw [hw, hH, hcc]
  ring

/-- **For fixed `(M₁, M₂) ∈ goodAG n`**: `E_{M₃} E_{A,F} (g̃ − ĝ)² ≤
`n·(404·t|b̃ − b̂|²/γ + 29/q²)·(4/n)`. -/
theorem diffFixedAG0 :
    ∫⁻ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
      (∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
        ENNReal.ofReal ((gA ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
          gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2)
        ∂((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)))
      ∂gaussMat n (mW n) (2 / (mW n : ℝ)) ≤
    ENNReal.ofReal ((n : ℝ) * (404 * (Part141.dA n θ / (2 / ((2 * n : ℕ) : ℝ))) +
      29 * (1 / (qA n : ℝ)) ^ 2) * (4 / (n : ℝ))) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_million hn
    linarith
  have ha := tauAG0_pos hG hn hθ
  set a : ℝ := tauA n θ with had
  set Hh : ℝ := hellG n a (tauHat (2 * n) (mW n) θ) with hHh
  have hH0 : 0 ≤ Hh := hellG_nonneg _ _ _
  set d : Fin (mW n) → ℝ := bA n θ - bhat θ with hd
  obtain ⟨li, le⟩ := layer_sq (m := n) (k := mW n) (v := 2 / (mW n : ℝ)) (by positivity) d
  set f : Matrix (Fin n) (Fin (mW n)) ℝ → ℝ := fun M₃ =>
    (2 * (normSq (M₃.mulVec d) / a ^ 2) + 8 * Hh) * (4 / (n : ℝ)) with hf
  have hf0 : ∀ M₃, 0 ≤ f M₃ := fun M₃ => by
    have : 0 ≤ normSq (M₃.mulVec d) / a ^ 2 := div_nonneg (normSq_nonneg _) (sq_nonneg _)
    rw [hf]; positivity
  have hfi : Integrable f (gaussMat n (mW n) (2 / (mW n : ℝ))) := by
    rw [hf]
    exact ((((li.div_const _).const_mul 2).add (integrable_const _)).mul_const _)
  have hfint : ∫ M₃, f M₃ ∂gaussMat n (mW n) (2 / (mW n : ℝ)) =
      (8 * Hh + 2 * (n : ℝ) * Part141.dA n θ / a ^ 2) * (4 / (n : ℝ)) := by
    rw [hf, integral_mul_const, integral_add ((li.div_const _).const_mul 2)
      (integrable_const _), integral_const_mul, integral_div, le]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    unfold Part141.dA
    rw [← hd]
    ring
  calc _ ≤ ∫⁻ M₃, ENNReal.ofReal (f M₃) ∂gaussMat n (mW n) (2 / (mW n : ℝ)) :=
        lintegral_mono fun M₃ => diffFixedMG0 hG hn hθ M₃
    _ = ENNReal.ofReal (∫ M₃, f M₃ ∂gaussMat n (mW n) (2 / (mW n : ℝ))) :=
        (ofReal_integral_eq_lintegral_ofReal hfi (Filter.Eventually.of_forall hf0)).symm
    _ ≤ _ := by
        rw [hfint]
        refine ENNReal.ofReal_le_ofReal ?_
        exact mul_le_mul_of_nonneg_right (KAG0_le hG hn hθ) (by positivity)

end fixed

lemma goodWAG0_meas {n : ℕ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤ n) :
    MeasurableSet (goodWAG G) :=
  (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) (goodAG0_meas hG hn)

lemma measurable_dGAG0 {n : ℕ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤ n)
    : Measurable (dGAG G) := by
  have hN : 1 ≤ 2 * n := by omega
  have e : dGAG G = ({t | t.1 ∈ goodWAG G} : Set (MlpParam (2 * n) (mW n) n ×
      MlpParam n (mA n) n × MlpParam n (mF n) 1)).indicator
      (fun t => (gA t.1 t.2.1 t.2.2 - gHat t.1 t.2.1 t.2.2) ^ 2) := by
    funext t
    exact ind_fst_eq (goodWAG G) (fun W p => (gA W p.1 p.2 - gHat W p.1 p.2) ^ 2) t
  rw [e]
  exact ((measurable_gA.sub (measurable_gHat hN)).pow_const 2).indicator
    (measurable_fst (goodWAG0_meas hG hn))

lemma measurable_errGAG0 {n : ℕ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤
    n) : Measurable (errGAG G) := by
  have hN : 1 ≤ 2 * n := by omega
  have e : errGAG G = ({t | t.1 ∈ goodWAG G} : Set (MlpParam (2 * n) (mW n) n ×
      MlpParam n (mA n) n × MlpParam n (mF n) 1)).indicator
      (fun t => (gA t.1 t.2.1 t.2.2 - Part130.Bn t.1 t.2.1 t.2.2) ^ 2) := by
    funext t
    exact ind_fst_eq (goodWAG G) (fun W p => (gA W p.1 p.2 - Part130.Bn W p.1 p.2) ^ 2) t
  rw [e]
  exact ((measurable_gA.sub (BstLean.Part131.measurable_Bn hN)).pow_const 2).indicator
    (measurable_fst (goodWAG0_meas hG hn))

/-- **The distance of the two estimates, joint over `(W, A, F)`.** For `n ≥ 4096`:
`E_{W,A,F}[1_good(W)·(g̃ − ĝ)²] ≤ pertA n·(4/n)`. -/
theorem diffVecAG0_lint {n : ℕ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 4096 ≤
    n) :
    ∫⁻ t, ENNReal.ofReal (dGAG G t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (pertA n * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  have hq' : (0 : ℝ) < qA n := by exact_mod_cast qA_pos hn1
  have mE := goodAG0_meas hG (n := n) hn1
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  set gM := gaussMat n (mW n) (2 / (mW n : ℝ)) with hgM
  set f : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => ENNReal.ofReal (dGAG G t) with hf
  have mf : Measurable f := ENNReal.measurable_ofReal.comp (measurable_dGAG0 hG hn1)
  set Gf : MlpParam (2 * n) (mW n) n → ℝ≥0∞ := fun W => ∫⁻ p, f (W, p) ∂PAF with hGf
  have mGf : Measurable Gf := mf.lintegral_prod_right'
  have e : mlpGauss (2 * n) (mW n) n =
      ((hidGauss (2 * n) (mW n)).prod gM).map MeasurableEquiv.prodAssoc := by
    unfold mlpGauss hidGauss
    rw [Measure.prodAssoc_prod]
  have step1 : ∫⁻ t, f t ∂mlpTriple 2 n =
      ∫⁻ θ, (∫⁻ M₃, Gf (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n) := by
    have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod PAF := rfl
    rw [e0, lintegral_prod _ mf.aemeasurable]
    change ∫⁻ W, Gf W ∂mlpGauss (2 * n) (mW n) n = _
    rw [e, lintegral_map mGf MeasurableEquiv.prodAssoc.measurable]
    exact lintegral_prod (fun a => Gf (MeasurableEquiv.prodAssoc a))
      (mGf.comp MeasurableEquiv.prodAssoc.measurable).aemeasurable
  set k : HidParam (2 * n) (mW n) → ℝ := fun θ =>
    (n : ℝ) * (404 * (Part141.dA n θ / (2 / ((2 * n : ℕ) : ℝ))) + 29 * (1 / (qA n : ℝ)) ^ 2) *
      (4 / (n : ℝ)) with hk
  have hk0 : ∀ θ, 0 ≤ k θ := by
    intro θ
    have := dA_nonneg n θ
    rw [hk]
    positivity
  have step2 : ∀ θ : HidParam (2 * n) (mW n),
      ∫⁻ M₃, Gf (θ.1, θ.2, M₃) ∂gM ≤ ENNReal.ofReal (k θ) := by
    intro θ
    by_cases hθ : θ ∈ goodAG G
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∈ goodWAG G := fun M₃ => hθ
      have hin : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ, Gf (θ.1, θ.2, M₃) =
          ∫⁻ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
            ENNReal.ofReal ((gA ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2 -
              gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2) ∂PAF := by
        intro M₃
        refine lintegral_congr fun p => ?_
        simp only [hf, dGAG, Set.indicator_of_mem (hW M₃)]
      simp_rw [hin]
      exact diffFixedAG0 hG hn hθ
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∉ goodWAG G := fun M₃ => hθ
      have hz : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ, Gf (θ.1, θ.2, M₃) = 0 := by
        intro M₃
        simp only [hGf, hf, dGAG, Set.indicator_of_notMem (hW M₃), ENNReal.ofReal_zero,
          lintegral_zero]
      simp_rw [hz]
      simp
  obtain ⟨hdi, hdb⟩ := centreArith141 hn
  have ik : Integrable k (hidGauss (2 * n) (mW n)) := by
    rw [hk]
    exact ((((hdi.div_const _).const_mul 404).add (integrable_const _)).const_mul _).mul_const _
  rw [step1]
  calc ∫⁻ θ, (∫⁻ M₃, Gf (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n)
      ≤ ∫⁻ θ, ENNReal.ofReal (k θ) ∂hidGauss (2 * n) (mW n) := lintegral_mono step2
    _ = ENNReal.ofReal (∫ θ, k θ ∂hidGauss (2 * n) (mW n)) :=
        (ofReal_integral_eq_lintegral_ofReal ik (Filter.Eventually.of_forall hk0)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hk, integral_mul_const, integral_const_mul,
          integral_add ((hdi.div_const _).const_mul 404) (integrable_const _),
          integral_const_mul, integral_div]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
        have h1 : (∫ θ, Part141.dA n θ ∂hidGauss (2 * n) (mW n)) / (2 / ((2 * n : ℕ) : ℝ)) ≤
            68 / (qA n : ℝ) ^ 2 := by
          rw [div_le_iff₀ hγ]
          linarith
        have h2 : (n : ℝ) * (404 * ((∫ θ, Part141.dA n θ ∂hidGauss (2 * n) (mW n)) /
            (2 / ((2 * n : ℕ) : ℝ))) + 29 * (1 / (qA n : ℝ)) ^ 2) ≤ pertA n := by
          unfold pertA
          have e1 : 27501 * (n : ℝ) / (qA n : ℝ) ^ 2 =
              (n : ℝ) * (404 * (68 / (qA n : ℝ) ^ 2) + 29 * (1 / (qA n : ℝ)) ^ 2) := by
            field_simp
            ring
          rw [e1]
          exact mul_le_mul_of_nonneg_left (by linarith) hnpos.le
        exact mul_le_mul_of_nonneg_right h2 (by positivity)

end BstLean.Part145

-- ===== from Part141Final =====

namespace BstLean.Part145

open BstLean.Part141
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140

/-- The probability that `W` is not in the good hidden event, as an event of `(W, A, F)`, from a
bound for `G`. -/
lemma badAG0_prob_gen {n : ℕ} (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n
    G) {p : ℝ}
    (h1 : (hidGauss (2 * n) (mW n)).real Gᶜ ≤ p) :
    (mlpTriple 2 n).real {t | t.1 ∉ goodWAG G} ≤ p + 68000000 / (qA n : ℝ) ^ 2 := by
  have hn1 : 1 ≤ n := by omega
  have mG := goodWAG0_meas hG (n := n) hn1
  have hmS := goodAG0_meas hG (n := n) hn1
  have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod
      ((mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1)) := rfl
  have e1 : {t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 |
      t.1 ∉ goodWAG G} = (goodWAG G)ᶜ ×ˢ (Set.univ : Set (MlpParam n (mA n) n ×
        MlpParam n (mF n) 1)) := by
    ext t; simp
  rw [e0, e1, measureReal_def, Measure.prod_prod, measure_univ, mul_one, ← measureReal_def]
  have e : (goodWAG G)ᶜ =
      (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) ⁻¹' (goodAG G)ᶜ := rfl
  have hmap : (mlpGauss (2 * n) (mW n) n).map
      (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) = hidGauss (2 * n) (mW n) := by
    unfold mlpGauss hidGauss
    have h1 : (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) =
        Prod.map id Prod.fst := by
      funext W; rfl
    rw [h1, ← Measure.map_prod_map _ _ measurable_id measurable_fst, Measure.map_id,
      Measure.map_fst_prod]
    simp
  have hf : Measurable (fun W : MlpParam (2 * n) (mW n) n => (W.1, W.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  rw [e, ← map_measureReal_apply hf hmS.compl, hmap]
  exact goodAG_prob_gen hn h1

end BstLean.Part145

-- ===== from Part141Sample =====

namespace BstLean.Part145

open BstLean.Part141
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140

lemma measurable_errSAG0 {n : ℕ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G) (hn : 1 ≤
    n) (k : ℕ) : Measurable (errSAG G k) := by
  have hN : 1 ≤ 2 * n := by omega
  have e : errSAG G k = ({p | p.1.1 ∈ goodWAG G} : Set ((MlpParam (2 * n) (mW n) n ×
      MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ))).indicator
      (fun p => (gSampleA k p.1.1 p.1.2.1 p.1.2.2 p.2 -
        Part130.Bn p.1.1 p.1.2.1 p.1.2.2) ^ 2) := by
    funext p
    by_cases hp : p.1.1 ∈ goodWAG G
    · rw [Set.indicator_of_mem (show p ∈ {p : (MlpParam (2 * n) (mW n) n ×
        MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
        p.1.1 ∈ goodWAG G} from hp)]
      unfold errSAG
      rw [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem (show p ∉ {p : (MlpParam (2 * n) (mW n) n ×
        MlpParam n (mA n) n × MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
        p.1.1 ∈ goodWAG G} from hp)]
      unfold errSAG
      rw [Set.indicator_of_notMem hp]
  rw [e]
  exact (((measurable_gSampleA k).sub
    ((BstLean.Part131.measurable_Bn hN).comp measurable_fst)).pow_const 2).indicator
    ((measurable_fst.comp measurable_fst) (goodWAG0_meas hG hn))

end BstLean.Part145

-- ===== from Part141Prog =====

namespace BstLean.Part145

open BstLean.Part141
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open BstLean.Cost
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140

/-- The event "`W` is good and a point is zero before the normalization" has probability `0`. -/
lemma zeroPtAG0_null {n : ℕ} (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv0 n G)
    (k : ℕ) :
    ((mlpTriple 2 n).prod (gamK k n))
      {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
        (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWAG G ∧ ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} = 0 := by
  have hn1 : 1 ≤ n := by omega
  set Z : Set ((MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) ×
      (Fin k → Fin n → ℝ)) :=
    {p | p.1.1 ∈ goodWAG G ∧ ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} with hZ
  have mZ : MeasurableSet Z := by
    have m1 : MeasurableSet {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) | p.1.1 ∈ goodWAG G} :=
      (measurable_fst.comp measurable_fst) (goodWAG0_meas hG hn1)
    have m2 : MeasurableSet {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
        ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} := by
      have e : {p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) |
          ∃ i, normSq (preA p.1.1 (p.2 i)) = 0} =
          ⋃ i : Fin k, {p | normSq (preA p.1.1 (p.2 i)) = 0} := by
        ext p; simp
      rw [e]
      refine MeasurableSet.iUnion fun i => ?_
      have hm : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
          MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => normSq (preA p.1.1 (p.2 i))) :=
        measurable_normSq.comp (measurable_preA.comp
          ((measurable_fst.comp measurable_fst).prodMk
            ((measurable_pi_apply i).comp measurable_snd)))
      exact hm (measurableSet_singleton 0)
    exact m1.inter m2
  rw [Measure.measure_prod_null mZ]
  refine Filter.Eventually.of_forall fun t => ?_
  change gamK k n (Prod.mk t ⁻¹' Z) = 0
  by_cases hg : t.1 ∈ goodWAG G
  · have hτ : tauWA t.1 ≠ 0 := (tauAG0_pos hG hn hg).ne'
    refine measure_mono_null ?_ (preA_null hn1 k t.1 hτ)
    rintro γ ⟨-, h⟩
    exact h
  · have e : Prod.mk t ⁻¹' Z = ∅ := by
      ext γ
      simp only [Set.mem_preimage, hZ, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
        not_and]
      intro h
      exact absurd h hg
    rw [e]
    simp

end BstLean.Part145

-- ===== the frame constant that depends on `θ` =====

namespace BstLean.Part145

open BstLean.Part143
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138
open BstLean.Part139 hiding BM
open BstLean.Part140 BstLean.Part141 BstLean.Part142

/-! ## The bound of `DKV` -/

/-- `DKV n θ ≤ 2`: from `(φ − φ′)²/2 ≤ φ² + φ′²` and `E_{A,F} φ(x)² = 4/n` for unit `x`. -/
lemma DKV_le_two {n : ℕ} (hn : 4096 ≤ n) (θ : HidParam (2 * n) (mW n)) : DKV n θ ≤ 2 := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have := lawU2_prob hN
  set Pd := (gaussMat n (mW n) (2 / (mW n : ℝ))).prod (lawU2 (2 * n)) with hPd
  have key : ∀ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
      LoutD Pd (oD1 θ) (oD2 θ) p ≤ Lout Pd (oD1 θ) p + Lout Pd (oD2 θ) p := by
    intro p
    unfold LoutD Lout
    rw [← lintegral_add_left (f := fun ω => ENNReal.ofReal (phiS p.1 p.2 (oD1 θ ω) ^ 2))
      (ENNReal.measurable_ofReal.comp
        (((bm_phiS hn1 p.1 p.2).comp (measurable_oD1 θ)).meas.pow_const 2))]
    refine lintegral_mono fun ω => ?_
    rw [← ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    nlinarith [sq_nonneg (phiS p.1 p.2 (oD1 θ ω) + phiS p.1 p.2 (oD2 θ ω))]
  have h1 : LDV n θ ≤ ENNReal.ofReal (4 / (n : ℝ)) + ENNReal.ofReal (4 / (n : ℝ)) := by
    unfold LDV
    refine (lintegral_mono key).trans (le_of_eq ?_)
    rw [lintegral_add_left (measurable_Lout (mA := mA n) (mF := mF n) Pd (measurable_oD1 θ)),
      lintegral_Lout (mA := mA n) (mF := mF n) Pd hn1 hmA hmF (measurable_oD1 θ),
      lintegral_Lout (mA := mA n) (mF := mF n) Pd hn1 hmA hmF (measurable_oD2 θ)]
  have h4 : (0 : ℝ) ≤ 4 / (n : ℝ) := by positivity
  rw [← ENNReal.ofReal_add h4 h4] at h1
  have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
  rw [ENNReal.toReal_ofReal (add_nonneg h4 h4)] at h2
  unfold DKV
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (n : ℝ) / 4)
  have e : (n : ℝ) / 4 * (4 / (n : ℝ) + 4 / (n : ℝ)) = 2 := by field_simp; norm_num
  linarith

lemma measurable_DKV {n : ℕ} (hn : 1 ≤ n) : Measurable (DKV n) :=
  (measurable_LDV hn).ennreal_toReal.const_mul _

lemma DKV_sq_int {n : ℕ} (hn : 4096 ≤ n) :
    Integrable (fun θ => DKV n θ ^ 2) (hidGauss (2 * n) (mW n)) := by
  refine Integrable.mono' (integrable_const (4 : ℝ))
    ((measurable_DKV (by omega)).pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun θ => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  nlinarith [DKV_nonneg n θ, DKV_le_two hn θ]

/-! ## The numbers -/

/-- `XALV` with `ΛV` in the place of `Lc·(1 − κ^{∘6}(0) + e + Lc/n)`. -/
noncomputable def XF (ΛV : ℝ) (n : ℕ) (ζ η η' : ℝ) : ℝ :=
  (1 + η') * ((1 + η) * (ΛV / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ) + (1 + 1 / η') * pertA n

lemma XF_nonneg {n : ℕ} (hn : 4096 ≤ n) {ΛV : ℝ} (hΛ0 : 0 ≤ ΛV) (ζ : ℝ) {η : ℝ} (hη : 0 < η)
    {η' : ℝ} (hη' : 0 < η') : 0 ≤ XF ΛV n ζ η η' := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hEH := EHH_nonneg hn ζ
  have hp := pertA_nonneg n
  unfold XF
  positivity

/-! ## The chain -/

/-- **`errVecHatGV_lint` with a frame constant that depends on `θ`.** -/
theorem errVecHatF_lint {n : ℕ} {G : Set (HidParam (2 * n) (mW n))}
    {Lf : HidParam (2 * n) (mW n) → ℝ} (hG : GoodEvF n G Lf)
    (hn : 4096 ≤ n) {ΛV : ℝ}
    (hΛi : Integrable (G.indicator fun θ => Lf θ * (DKV n θ + Lf θ / (n : ℝ)))
      (hidGauss (2 * n) (mW n)))
    (hΛ : ∫ θ, G.indicator (fun θ => Lf θ * (DKV n θ + Lf θ / (n : ℝ))) θ
      ∂hidGauss (2 * n) (mW n) ≤ ΛV)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) :
    ∫⁻ t, ENNReal.ofReal (errGHG G t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (((1 + η) * (ΛV / (n : ℝ)) +
        4 * (1 + 1 / η) * EHH n ζ) * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have mE := hG.meas
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  set gM := gaussMat n (mW n) (2 / (mW n : ℝ)) with hgM
  set f : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => ENNReal.ofReal (errGHG G t) with hf
  have mf : Measurable f := ENNReal.measurable_ofReal.comp (measurable_errGHG0 hG.to0 hn1)
  set Gf : MlpParam (2 * n) (mW n) n → ℝ≥0∞ := fun W => ∫⁻ p, f (W, p) ∂PAF with hGf
  have mGf : Measurable Gf := mf.lintegral_prod_right'
  have eW : mlpGauss (2 * n) (mW n) n =
      ((hidGauss (2 * n) (mW n)).prod gM).map MeasurableEquiv.prodAssoc := by
    unfold mlpGauss hidGauss
    rw [Measure.prodAssoc_prod]
  have step1 : ∫⁻ t, f t ∂mlpTriple 2 n =
      ∫⁻ θ, (∫⁻ M₃, Gf (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n) := by
    have e0 : mlpTriple 2 n = (mlpGauss (2 * n) (mW n) n).prod PAF := rfl
    rw [e0, lintegral_prod _ mf.aemeasurable]
    change ∫⁻ W, Gf W ∂mlpGauss (2 * n) (mW n) n = _
    rw [eW, lintegral_map mGf MeasurableEquiv.prodAssoc.measurable]
    exact lintegral_prod (fun a => Gf (MeasurableEquiv.prodAssoc a))
      (mGf.comp MeasurableEquiv.prodAssoc.measurable).aemeasurable
  -- the bound for fixed θ
  set a : ℝ := (1 + η) * (1 / (n : ℝ)) with ha
  set S : ℝ := 4 / (n : ℝ) with hS
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  set dd : HidParam (2 * n) (mW n) → ℝ := fun θ => Lf θ * (DKV n θ + Lf θ / (n : ℝ)) with hdd
  have hdd0 : ∀ θ ∈ G, 0 ≤ dd θ := fun θ hθ =>
    mul_nonneg (hG.Lnn θ hθ) (add_nonneg (DKV_nonneg n θ) (div_nonneg (hG.Lnn θ hθ) hnpos.le))
  set k : HidParam (2 * n) (mW n) → ℝ := fun θ =>
    a * S * G.indicator dd θ +
      4 * (1 + 1 / η) * S * G.indicator (HbarH n ζ) θ with hk
  have hk0 : ∀ θ, 0 ≤ k θ := by
    intro θ
    have h1 : 0 ≤ G.indicator dd θ :=
      Set.indicator_nonneg hdd0 _
    have h2 : 0 ≤ G.indicator (HbarH n ζ) θ :=
      Set.indicator_nonneg (fun θ _ => HbarH_nonneg n ζ θ) _
    rw [hk]
    positivity
  have step2 : ∀ θ : HidParam (2 * n) (mW n),
      ∫⁻ M₃, Gf (θ.1, θ.2, M₃) ∂gM ≤ ENNReal.ofReal (k θ) := by
    intro θ
    have msec : Measurable (fun q : Matrix (Fin n) (Fin (mW n)) ℝ ×
        (MlpParam n (mA n) n × MlpParam n (mF n) 1) =>
        (((θ.1, θ.2, q.1) : MlpParam (2 * n) (mW n) n), q.2)) :=
      ((measurable_const.prodMk (measurable_const.prodMk measurable_fst))).prodMk measurable_snd
    have hswap : ∫⁻ M₃, Gf (θ.1, θ.2, M₃) ∂gM =
        ∫⁻ p, (∫⁻ M₃, f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) ∂gM) ∂PAF :=
      lintegral_lintegral_swap
        (f := fun (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ)
          (p : MlpParam n (mA n) n × MlpParam n (mF n) 1) =>
          f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p)) (mf.comp msec).aemeasurable
    rw [hswap]
    by_cases hθ : θ ∈ G
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∈ goodWHG G := fun M₃ => hθ
      have hin : ∀ p : MlpParam n (mA n) n × MlpParam n (mF n) 1,
          ∫⁻ M₃, f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) ∂gM =
          ENNReal.ofReal (∫ M₃, (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)
            p.1 p.2 - gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) p.1 p.2) ^ 2 ∂gM) := by
        rintro ⟨A, F⟩
        have hφ : BM (phiS A F) := bm_phiS hn1 A F
        have hb : BM (fun W : MlpParam (2 * n) (mW n) n =>
            ((∫ x, phiS A F x ∂muWn W) - ∫ x, phiS A F x ∂cheapHat W) ^ 2) :=
          ((bm_muW hN hφ).sub (bm_cheapHat hN hφ)).sq
        have hb' : BM (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
            (Part130.Bn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F -
              gHat ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) A F) ^ 2) := by
          have h1 := hb.comp (g := fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
            ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n))
            (measurable_const.prodMk (measurable_const.prodMk measurable_id))
          refine ⟨?_, h1.bdd.imp fun M hM M₃ => ?_⟩
          · convert h1.meas using 2 with M₃
            rw [integral_phiS_muWn hn1]
            unfold cheapHat gHat
            rw [integral_phiS_cheapIn hn1]
            rfl
          · have := hM M₃
            rw [integral_phiS_muWn hn1] at this
            unfold cheapHat at this
            rw [integral_phiS_cheapIn hn1] at this
            exact this
        rw [ofReal_integral_eq_lintegral_ofReal (hb'.integrable gM)
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
        refine lintegral_congr fun M₃ => ?_
        simp only [hf, errGHG, Set.indicator_of_mem (hW M₃)]
        congr 1
        ring
      simp_rw [hin]
      have hGθ : GoodEv n (Lf θ) ({θ} : Set (HidParam (2 * n) (mW n))) :=
        ⟨measurableSet_singleton θ,
          fun θ' h' => by rw [Set.mem_singleton_iff.mp h']; exact hG.win θ hθ,
          fun θ' h' => by rw [Set.mem_singleton_iff.mp h']; exact hG.frame θ hθ⟩
      refine (errFixedHatLGV hGθ hn (hG.Lnn θ hθ) (Set.mem_singleton θ) hζ0.le hζ1
        hη).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [hk]
      simp only [Set.indicator_of_mem hθ]
      rw [ha, hS, hdd]
      apply le_of_eq
      ring
    · have hW : ∀ M₃ : Matrix (Fin n) (Fin (mW n)) ℝ,
          ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n) ∉ goodWHG G := fun M₃ => hθ
      have hz : ∀ (p : MlpParam n (mA n) n × MlpParam n (mF n) 1)
          (M₃ : Matrix (Fin n) (Fin (mW n)) ℝ),
          f (((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n), p) = 0 := by
        intro p M₃
        simp only [hf, errGHG, Set.indicator_of_notMem (hW M₃), ENNReal.ofReal_zero]
      simp_rw [hz]
      simp
  obtain ⟨iH, hH⟩ := HbarHG0_mean hG.to0 hn hζ0 hζ1
  have i1 : Integrable (fun θ : HidParam (2 * n) (mW n) =>
      a * S * G.indicator dd θ) (hidGauss (2 * n) (mW n)) := hΛi.const_mul _
  have i2 : Integrable (fun θ : HidParam (2 * n) (mW n) =>
      4 * (1 + 1 / η) * S * G.indicator (HbarH n ζ) θ) (hidGauss (2 * n) (mW n)) := iH.const_mul _
  have ik : Integrable k (hidGauss (2 * n) (mW n)) := i1.add i2
  rw [step1]
  calc ∫⁻ θ, (∫⁻ M₃, Gf (θ.1, θ.2, M₃) ∂gM) ∂hidGauss (2 * n) (mW n)
      ≤ ∫⁻ θ, ENNReal.ofReal (k θ) ∂hidGauss (2 * n) (mW n) := lintegral_mono step2
    _ = ENNReal.ofReal (∫ θ, k θ ∂hidGauss (2 * n) (mW n)) :=
        (ofReal_integral_eq_lintegral_ofReal ik (Filter.Eventually.of_forall hk0)).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [hk, integral_add i1 i2, integral_const_mul, integral_const_mul]
        have h1 := mul_le_mul_of_nonneg_left hΛ (mul_nonneg ha0 hS0)
        have h2 := mul_le_mul_of_nonneg_left hH (by positivity : (0 : ℝ) ≤ 4 * (1 + 1 / η) * S)
        have e3 : a * S * ΛV = (1 + η) * (ΛV / (n : ℝ)) * S := by rw [ha]; ring
        have e4 : ((1 + η) * (ΛV / (n : ℝ)) + 4 * (1 + 1 / η) * EHH n ζ) * S =
            (1 + η) * (ΛV / (n : ℝ)) * S + 4 * (1 + 1 / η) * S * EHH n ζ := by ring
        rw [e4]
        linarith

/-- **`errVecAGV_lint` with a frame constant that depends on `θ`.** -/
theorem errVecAF_lint {n : ℕ} {G : Set (HidParam (2 * n) (mW n))}
    {Lf : HidParam (2 * n) (mW n) → ℝ} (hG : GoodEvF n G Lf)
    (hn : 4096 ≤ n) {ΛV : ℝ} (hΛ0 : 0 ≤ ΛV)
    (hΛi : Integrable (G.indicator fun θ => Lf θ * (DKV n θ + Lf θ / (n : ℝ)))
      (hidGauss (2 * n) (mW n)))
    (hΛ : ∫ θ, G.indicator (fun θ => Lf θ * (DKV n θ + Lf θ / (n : ℝ))) θ
      ∂hidGauss (2 * n) (mW n) ≤ ΛV)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η') :
    ∫⁻ t, ENNReal.ofReal (errGAG G t) ∂mlpTriple 2 n ≤
      ENNReal.ofReal (XF ΛV n ζ η η' * (4 / (n : ℝ))) := by
  unfold XF
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hEH := EHH_nonneg hn ζ
  have hp := pertA_nonneg n
  have m1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ENNReal.ofReal (errGHG G t)) :=
    ENNReal.measurable_ofReal.comp (measurable_errGHG0 hG.to0 hn1)
  have m2 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1 => ENNReal.ofReal (dGAG G t)) :=
    ENNReal.measurable_ofReal.comp (measurable_dGAG0 hG.to0 hn1)
  have key : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ENNReal.ofReal (errGAG G t) ≤
        ENNReal.ofReal (1 + η') * ENNReal.ofReal (errGHG G t) +
          ENNReal.ofReal (1 + 1 / η') * ENNReal.ofReal (dGAG G t) := by
    intro t
    have h0 := errGHG_nonneg G t
    have h0' := dGAG_nonneg G t
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases ht : t.1 ∈ goodWAG G
    · have ht' : t.1 ∈ goodWHG G := goodWAG_sub G ht
      simp only [errGAG, errGHG, dGAG, Set.indicator_of_mem ht, Set.indicator_of_mem ht']
      have hs := sq_split (η := 1 / η') (by positivity) (gA t.1 t.2.1 t.2.2)
        (gHat t.1 t.2.1 t.2.2) (Part130.Bn t.1 t.2.1 t.2.2)
      rw [one_div_one_div] at hs
      linarith
    · simp only [errGAG, Set.indicator_of_notMem ht]
      positivity
  calc ∫⁻ t, ENNReal.ofReal (errGAG G t) ∂mlpTriple 2 n
      ≤ ∫⁻ t, (ENNReal.ofReal (1 + η') * ENNReal.ofReal (errGHG G t) +
          ENNReal.ofReal (1 + 1 / η') * ENNReal.ofReal (dGAG G t)) ∂mlpTriple 2 n :=
        lintegral_mono key
    _ = ENNReal.ofReal (1 + η') * ∫⁻ t, ENNReal.ofReal (errGHG G t) ∂mlpTriple 2 n +
          ENNReal.ofReal (1 + 1 / η') * ∫⁻ t, ENNReal.ofReal (dGAG G t) ∂mlpTriple 2 n := by
        rw [lintegral_add_left (m1.const_mul _), lintegral_const_mul _ m1,
          lintegral_const_mul _ m2]
    _ ≤ ENNReal.ofReal (1 + η') * ENNReal.ofReal (((1 + η) * (ΛV / (n : ℝ)) +
            4 * (1 + 1 / η) * EHH n ζ) * (4 / (n : ℝ))) +
          ENNReal.ofReal (1 + 1 / η') * ENNReal.ofReal (pertA n * (4 / (n : ℝ))) :=
        add_le_add (mul_le_mul' le_rfl (errVecHatF_lint hG hn hΛi hΛ hζ0 hζ1 hη))
          (mul_le_mul' le_rfl (diffVecAG0_lint hG.to0 hn))
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring

/-- **The error bound with a frame constant that depends on `θ`.** For `n ≥ 4096`,
`0 < ζ < 1`, `k ≥ 1`: `E[1_good(W)·(g̃_k − B)²] ≤ (XF ΛV n ζ η η′ + 1/k)·(4/n)`. -/
theorem errSampleAF_lint {n : ℕ} (hn : 4096 ≤ n) {G : Set (HidParam (2 * n) (mW n))}
    {Lf : HidParam (2 * n) (mW n) → ℝ} (hG : GoodEvF n G Lf)
    {ΛV : ℝ} (hΛ0 : 0 ≤ ΛV)
    (hΛi : Integrable (G.indicator fun θ => Lf θ * (DKV n θ + Lf θ / (n : ℝ)))
      (hidGauss (2 * n) (mW n)))
    (hΛ : ∫ θ, G.indicator (fun θ => Lf θ * (DKV n θ + Lf θ / (n : ℝ))) θ
      ∂hidGauss (2 * n) (mW n) ≤ ΛV)
    {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η) {η' : ℝ} (hη' : 0 < η')
    {k : ℕ} (hk : 1 ≤ k) :
    ∫⁻ p, ENNReal.ofReal (errSAG G k p) ∂((mlpTriple 2 n).prod (gamK k n)) ≤
      ENNReal.ofReal ((XF ΛV n ζ η η' + (k : ℝ)⁻¹) * (4 / (n : ℝ))) := by
  have hn1 : 1 ≤ n := by omega
  have hN : 1 ≤ 2 * n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hmA : 1 ≤ mA n := by unfold mA; exact Nat.one_le_pow _ _ (by omega)
  have hmF : 1 ≤ mF n := by have := mF_ge hn; omega
  have hX := XF_nonneg hn hΛ0 ζ hη hη'
  set PW := mlpGauss (2 * n) (mW n) n with hPW
  set PAF := (mlpGauss n (mA n) n).prod (mlpGauss n (mF n) 1) with hPAF
  have e0 : mlpTriple 2 n = PW.prod PAF := rfl
  have mf : Measurable (fun p : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
      MlpParam n (mF n) 1) × (Fin k → Fin n → ℝ) => ENNReal.ofReal (errSAG G k p)) :=
    ENNReal.measurable_ofReal.comp (measurable_errSAG0 hG.to0 hn1 k)
  rw [lintegral_prod _ mf.aemeasurable]
  -- the second moment term, as a function of `(W, (A, F))`
  set Lo : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1 → ℝ≥0∞ :=
    fun t => Lout (stdGauss (Fin n)) (preA t.1) t.2 with hLo
  have mL : Measurable Lo := by
    have hj : Measurable (fun q : (MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
        MlpParam n (mF n) 1) × (Fin n → ℝ) =>
        ENNReal.ofReal (phiS q.1.2.1 q.1.2.2 (preA q.1.1 q.2) ^ 2)) :=
      ENNReal.measurable_ofReal.comp ((BstLean.Part131.continuous_phiN_all.measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk (measurable_sphPt.comp
          (measurable_preA.comp ((measurable_fst.comp measurable_fst).prodMk
            measurable_snd))))).pow_const 2)
    exact hj.lintegral_prod_right'
  have hLint : ∫⁻ t, Lo t ∂mlpTriple 2 n = ENNReal.ofReal (4 / (n : ℝ)) := by
    rw [e0, lintegral_prod _ mL.aemeasurable]
    have h : ∀ W : MlpParam (2 * n) (mW n) n,
        ∫⁻ q, Lo (W, q) ∂PAF = ENNReal.ofReal (4 / (n : ℝ)) := by
      intro W
      have := lintegral_Lout (mA := mA n) (mF := mF n) (stdGauss (Fin n)) hn1 hmA hmF
        (measurable_preA_W W)
      exact this
    simp_rw [h]
    simp
  have key : ∀ t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1,
      ∫⁻ γ, ENNReal.ofReal (errSAG G k (t, γ)) ∂gamK k n ≤
        ENNReal.ofReal (errGAG G t) + ENNReal.ofReal ((k : ℝ)⁻¹) * Lo t := by
    rintro ⟨W, A, F⟩
    have ho : Measurable (preA W) := measurable_preA_W W
    have hφ : BstLean.Part105.BM (fun γ : Fin n → ℝ => phiS A F (preA W γ)) :=
      (bm_phiS hn1 A F).comp ho
    obtain ⟨hi, he⟩ := iid_mean_sq (stdGauss (Fin n)) hφ hk (Part130.Bn W A F)
    by_cases hW : W ∈ goodWAG G
    · have e1 : ∀ γ : Fin k → Fin n → ℝ, errSAG G k ((W, A, F), γ) =
          ((k : ℝ)⁻¹ * ∑ i, phiS A F (preA W (γ i)) - Part130.Bn W A F) ^ 2 := by
        intro γ
        simp only [errSAG, Set.indicator_of_mem hW, gSampleA]
      simp_rw [e1]
      rw [show gamK k n = Measure.pi (fun _ : Fin k => stdGauss (Fin n)) from rfl,
        ← ofReal_integral_eq_lintegral_ofReal hi
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
      have he' : ∫ x : Fin k → Fin n → ℝ, ((k : ℝ)⁻¹ * ∑ i, phiS A F (preA W (x i)) -
          Part130.Bn W A F) ^ 2 ∂Measure.pi (fun _ : Fin k => stdGauss (Fin n)) =
          (∫ x, phiS A F (preA W x) ∂stdGauss (Fin n) - Part130.Bn W A F) ^ 2 +
            (k : ℝ)⁻¹ * Var[fun γ : Fin n → ℝ => phiS A F (preA W γ); stdGauss (Fin n)] := he
      rw [he', ← gA_eq hn1]
      have hv : Var[fun γ : Fin n → ℝ => phiS A F (preA W γ); stdGauss (Fin n)] ≤
          ∫ γ, phiS A F (preA W γ) ^ 2 ∂stdGauss (Fin n) := by
        rw [BstLean.Part134.var_bm (stdGauss (Fin n)) hφ]
        nlinarith [sq_nonneg (∫ γ, phiS A F (preA W γ) ∂stdGauss (Fin n))]
      have hGf : errGAG G (W, A, F) = (gA W A F - Part130.Bn W A F) ^ 2 := by
        simp only [errGAG, Set.indicator_of_mem hW]
      have i0 : 0 ≤ ∫ γ, phiS A F (preA W γ) ^ 2 ∂stdGauss (Fin n) :=
        integral_nonneg fun _ => sq_nonneg _
      rw [hLo]
      simp only
      rw [← ofReal_integral_out (stdGauss (Fin n)) hn1 A F ho, hGf,
        ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (sq_nonneg _)
          (mul_nonneg (by positivity) i0)]
      refine ENNReal.ofReal_le_ofReal ?_
      have := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ (k : ℝ)⁻¹)
      linarith
    · have e1 : ∀ γ : Fin k → Fin n → ℝ, errSAG G k ((W, A, F), γ) = 0 := by
        intro γ
        simp only [errSAG, Set.indicator_of_notMem hW]
      simp_rw [e1]
      simp
  calc ∫⁻ t, (∫⁻ γ, ENNReal.ofReal (errSAG G k (t, γ)) ∂gamK k n) ∂mlpTriple 2 n
      ≤ ∫⁻ t, (ENNReal.ofReal (errGAG G t) + ENNReal.ofReal ((k : ℝ)⁻¹) * Lo t) ∂mlpTriple 2 n :=
        lintegral_mono key
    _ = ∫⁻ t, ENNReal.ofReal (errGAG G t) ∂mlpTriple 2 n +
        ENNReal.ofReal ((k : ℝ)⁻¹) * ENNReal.ofReal (4 / (n : ℝ)) := by
        have m1 : Measurable (fun t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n ×
            MlpParam n (mF n) 1 => ENNReal.ofReal (errGAG G t)) :=
          ENNReal.measurable_ofReal.comp (measurable_errGAG0 hG.to0 hn1)
        rw [lintegral_add_left m1, lintegral_const_mul _ mL, hLint]
    _ ≤ ENNReal.ofReal (XF ΛV n ζ η η' * (4 / (n : ℝ))) +
        ENNReal.ofReal ((k : ℝ)⁻¹) * ENNReal.ofReal (4 / (n : ℝ)) :=
        add_le_add (errVecAF_lint hG hn hΛ0 hΛi hΛ hζ0 hζ1 hη hη') le_rfl
    _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        ring


end BstLean.Part145

open BstLean.Part145 in
#print axioms errSampleAF_lint
open BstLean.Part145 in
#print axioms badAG0_prob_gen
open BstLean.Part145 in
#print axioms zeroPtAG0_null
open BstLean.Part145 in
#print axioms DKV_le_two
