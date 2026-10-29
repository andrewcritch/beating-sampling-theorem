import BstLean.Part143Var2

/-!
# Part 145 (abstract good hidden event), file 1: the event and the Part 140 lemmas

`GoodEv n Lc G`: the three properties of an abstract good hidden event `G` that the chain of
Parts 140 to 143 uses of `goodHat n`. This file makes again the lemmas of `Part140Frame`,
`Part140Tau`, `Part140Cheap` and `Part140Err` that read the event, with `G` in the place of
`goodHat n`. Each copy has the suffix `G` in its name. The proofs are those of the sources.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part145

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 BstLean.Part140

/-- The three properties of an abstract good hidden event. -/
structure GoodEv (n : ℕ) (Lc : ℝ) (G : Set (HidParam (2 * n) (mW n))) : Prop where
  meas : MeasurableSet G
  win : ∀ θ ∈ G, 2 / ((2 * n : ℕ) : ℝ) * (48 / 100) ≤ Bh (2 * n) (mW n) θ ∧
      Bh (2 * n) (mW n) θ ≤ 2 / ((2 * n : ℕ) : ℝ) * (508 / 1000)
  frame : ∀ θ ∈ G, ∀ w : Fin (mW n) → ℝ,
      ∫ u, (∑ j, eDir (bhat θ) (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n) ≤
        Lc / (n : ℝ) * ∑ j, w j ^ 2

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

variable {n : ℕ}
  {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
  (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ G)

include hG hn hθ

omit hn in
/-- On `G`: `0.48·γ ≤ t|b̂|² ≤ 0.508·γ`. -/
lemma BhG_hat : 2 / ((2 * n : ℕ) : ℝ) * (48 / 100) ≤ Bh (2 * n) (mW n) θ ∧
    Bh (2 * n) (mW n) θ ≤ 2 / ((2 * n : ℕ) : ℝ) * (508 / 1000) :=
  hG.win θ hθ

lemma BhG_pos : 0 < Bh (2 * n) (mW n) θ := by
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  have := (BhG_hat hG hθ).1
  nlinarith

lemma normSqG_bhat_pos : 0 < normSq (bhat θ) := by
  have h := BhG_pos hG hn hθ
  unfold Bh at h
  have hm : (0 : ℝ) < mW n := by
    have := mW_ge_million hn
    exact_mod_cast (by omega : 0 < mW n)
  by_contra h0
  have : normSq (bhat θ) = 0 := le_antisymm (not_lt.mp h0) (normSq_nonneg _)
  rw [this, mul_zero] at h
  exact lt_irrefl _ h

lemma bhatG_ne : bhat θ ≠ 0 := by
  intro h0
  have h := normSqG_bhat_pos hG hn hθ
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

variable {n : ℕ}
  {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
  (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ G)

include hG hn hθ

/-- On `G`: `0.4798 ≤ ℓ₀² ≤ 0.508`. -/
theorem B0G_window : 4798 / 10000 ≤ B0 (2 * n) (mW n) θ ∧ B0 (2 * n) (mW n) θ ≤ 508 / 1000 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  obtain ⟨hk1, hk2⟩ := kap1_window hn
  obtain ⟨hB1, hB2⟩ := BhG_hat hG hθ
  have hBpos := BhG_pos hG hn hθ
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
theorem w0HG_window : wLowH ≤ w0H (2 * n) (mW n) θ ∧
    w0H (2 * n) (mW n) θ ≤ 1 / (4798 / 10000) - 1 := by
  obtain ⟨hB1, hB2⟩ := B0G_window hG hn hθ
  have hB0 : 0 < B0 (2 * n) (mW n) θ := by linarith
  unfold w0H wLowH
  have h1 := one_div_le_one_div_of_le hB0 hB2
  have h2 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4798 / 10000) hB1
  constructor <;> linarith

theorem tauHatG_sq : tauHat (2 * n) (mW n) θ ^ 2 =
    Bh (2 * n) (mW n) θ * w0H (2 * n) (mW n) θ := by
  have h1 := (w0HG_window hG hn hθ).1
  have h2 := wLowH_pos
  have hB := BhG_pos hG hn hθ
  unfold tauHat
  rw [← w0H_eq, max_eq_right (by linarith)]
  exact Real.sq_sqrt (mul_nonneg hB.le (by linarith))

theorem tauHatG_pos : 0 < tauHat (2 * n) (mW n) θ := by
  have h1 := (w0HG_window hG hn hθ).1
  have h2 := wLowH_pos
  have hB := BhG_pos hG hn hθ
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

variable {n : ℕ}
  {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
  (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ G)

include hG hn hθ

/-- On `G` and the good inputs: `|ŵ − ŵ₀| ≤ ζ′`. -/
lemma wCloseHG {ζ : ℝ} (hζ1 : ζ < 1) {u : Fin (2 * n) → ℝ}
    (hu : (u, θ) ∈ goodUH (2 * n) (mW n) ζ) :
    |wH (2 * n) (mW n) u θ - w0H (2 * n) (mW n) θ| ≤ zetaPH ζ := by
  obtain ⟨hD, hl⟩ := hu
  have hζ0 : 0 ≤ ζ := (abs_nonneg _).trans hD
  have h1ζ : 0 < 1 - ζ := by linarith
  have hw := w_diff (by norm_num : (0 : ℝ) < 4798 / 10000) (B0G_window hG hn hθ).1 hζ1 hD hl
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
theorem goodG_ptH {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) {u : Fin (2 * n) → ℝ}
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
  have hnb := normSqG_bhat_pos hG hn hθ
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
  have hKpos : 0 < K := BhG_pos hG hn hθ
  set w := wH (2 * n) (mW n) u θ with hw
  set wb := w0H (2 * n) (mW n) θ with hwb
  have hτ2 : τ ^ 2 = K * w := by
    rw [hτ, div_pow]
    exact tauH_sq hN hm u hnb.ne' hkpos.ne' hTpos.ne'
  have hτ02 : tauHat (2 * n) (mW n) θ ^ 2 = K * wb := tauHatG_sq hG hn hθ
  have hτ0pos := tauHatG_pos hG hn hθ
  obtain ⟨hwb1, -⟩ := w0HG_window hG hn hθ
  have hwLow := wLowH_pos
  have hwb0 : 0 < wb := by linarith
  have hw0 : 0 ≤ w := by
    have : 0 ≤ K * w := by rw [← hτ2]; positivity
    exact nonneg_of_mul_nonneg_right this hKpos
  have hclose : |w - wb| ≤ zetaPH ζ := wCloseHG hG hn hθ hζ1 hu
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
lemma KfunHG_le {ζ : ℝ} (hζ1 : ζ < 1) (u : Fin (2 * n) → ℝ) :
    KfunH n ζ (u, θ) ≤ (n : ℝ) / (wLowH ^ 2 * cRhoH ζ) * zetaPH ζ ^ 2 + 1 := by
  have hc := cRhoH_pos ζ
  have hwl := wLowH_pos
  have hC : 0 ≤ (n : ℝ) / (wLowH ^ 2 * cRhoH ζ) := by positivity
  by_cases hp : (u, θ) ∈ goodUH (2 * n) (mW n) ζ
  · rw [KfunH_of_mem hp]
    have hclose := wCloseHG hG hn hθ hζ1 hp
    have hsq : (wH (2 * n) (mW n) u θ - w0H (2 * n) (mW n) θ) ^ 2 ≤ zetaPH ζ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hclose 2
    have := mul_le_mul_of_nonneg_left hsq hC
    linarith
  · rw [KfunH_of_notMem hp]
    have : 0 ≤ (n : ℝ) / (wLowH ^ 2 * cRhoH ζ) * zetaPH ζ ^ 2 := by positivity
    linarith

lemma KfunHG_integrable {ζ : ℝ} (hζ1 : ζ < 1) :
    Integrable (fun u => KfunH n ζ (u, θ)) (uniformSphere (2 * n)) := by
  have := uniformSphere_isProbability (2 * n) (by omega)
  refine Integrable.of_bound ((measurable_KfunH (by omega) ζ).comp
    measurable_prodMk_right).aestronglyMeasurable
    ((n : ℝ) / (wLowH ^ 2 * cRhoH ζ) * zetaPH ζ ^ 2 + 1) (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (KfunH_nonneg n ζ (u, θ))]
  exact KfunHG_le hG hn hθ hζ1 u

/-- **The cheap stand-in against the exact stand-in with the computed centre, at one `c`.** For
`n ≥ 4096`, `θ ∈ G`, `0 ≤ ζ < 1`, every `c ∈ ℝⁿ`, bounded measurable `φ`, real `a`:
`(E_{ν̂_c} φ − E_{ν̂′_c} φ)² ≤ 2·HbarH n ζ θ·(E_{ν̂_c}(φ − a)² + E_{ν̂′_c}(φ − a)²)`. -/
theorem cheapMeanHatG {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) (c : Fin n → ℝ)
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
      exact goodG_ptH hG hn hθ hζ0 hζ1 hp
    · right
      rw [KfunH_of_notMem hp]
  have h := cheap_mix (uniformSphere (2 * n)) (by omega : 2 ≤ n) (2 / (mW n : ℝ)) (bhat θ) c hh
    (tauHatG_pos hG hn hθ) ((measurable_KfunH (by omega) ζ).comp measurable_prodMk_right)
    (KfunHG_integrable hG hn hθ hζ1) hK hψ
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

variable {n : ℕ}
  {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
  (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)

include hG hn hζ0 hζ1

/-- **The mean of `HbarH` on the good event.** `θ ↦ 1_goodHat(θ)·HbarH n ζ θ` is integrable, and
`E_θ[1_goodHat·HbarH n ζ θ] ≤ EHH n ζ`. -/
theorem HbarHG_mean :
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
    (fun θ hθ => (B0G_window hG hn hθ).1)
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

/-- The abstract good hidden event `G` as an event of the whole World network. -/
def goodWHG {n : ℕ} (G : Set (HidParam (2 * n) (mW n))) : Set (MlpParam (2 * n) (mW n) n) := {W |
    (W.1, W.2.1) ∈ G}

lemma goodWHG_meas {n : ℕ}
    {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
    : MeasurableSet (goodWHG G) :=
  (measurable_fst.prodMk (measurable_fst.comp measurable_snd)) (hG.meas)

/-- The squared error of the cheap estimate on the good event of `W`:
`1_good(W)·(g₀ − B)²`, a function of `(W, A, F)`. -/
noncomputable def errGHG {n : ℕ} (G : Set (HidParam (2 * n) (mW n)))
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) : ℝ :=
  (goodWHG G).indicator (fun W => (gHat W t.2.1 t.2.2 - Part130.Bn W t.2.1 t.2.2) ^ 2) t.1

lemma errGHG_nonneg {n : ℕ} (G : Set (HidParam (2 * n) (mW n)))
    (t : MlpParam (2 * n) (mW n) n × MlpParam n (mA n) n × MlpParam n (mF n) 1) :
    0 ≤ errGHG G t :=
  Set.indicator_nonneg (fun _ _ => sq_nonneg _) _

lemma measurable_errGHG {n : ℕ}
    {Lc : ℝ} {G : Set (HidParam (2 * n) (mW n))} (hG : GoodEv n Lc G)
    (hn : 1 ≤ n) : Measurable (errGHG G) := by
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
    (measurable_fst (goodWHG_meas hG))

end BstLean.Part145

