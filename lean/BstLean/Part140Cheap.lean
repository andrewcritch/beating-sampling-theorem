import BstLean.Part140Tau
import BstLean.Part138Num

/-!
# Part 140: the cheap stand-in with the computed centre, for fixed `(M₁, M₂)`

Role: `delegations/statements/p140-spec.md` (item 3). Paper sources: `onW17c-cx.md` §5
(the one-pass Hellinger term `EH2₁`), `onW16c-cx.md` §5, `onW5-opus-prover.md` §4.5 (Lemma D3).

`N = 2n`, `m = mW n`, `t = 2/m`, `θ = (M₁, M₂)`, `b̂ = bhat θ` (the computed centre of Part 137),
`τ̂₀ = tauHat (2n) (mW n) θ` (Part 140, a function of `|b̂|²` and `n`), `ŵ`, `ŵ₀`, `G_ζ` of
`Part140Tau`.

* `zetaPH`, `rLowH`, `cRhoH`: the paper's `ζ′`, `r_low`, `(1 + √r_low)²(1 + r_low)` with the
  constants of the computed centre (`L = 0.4798`, `wLowH = 1/0.508 − 1`).
* `KfunH n ζ (u, θ)`: `n(ŵ − ŵ₀)²/(wLowH²·cRhoH ζ)` on `G_ζ`, and `1` off `G_ζ`;
  `HbarH n ζ θ = E_u KfunH`.
* `good_ptH`: on `goodHat n` and `G_ζ`: `λ̂(u) > 0` and
  `hellG n (σ̂(u)/λ̂(u)) τ̂₀ ≤ n(ŵ − ŵ₀)²/(wLowH²·cRhoH ζ)`.
* **`cheapMeanHat`**, **`cheapStandInHat`**: `θ ∈ goodHat n`, `η > 0`:
  `E_{M₃}(E_{μ_W} φ − E_{ν̂′} φ)² ≤ (1 + η)·(1.83/n)·E_c Var_{ν̂_c} φ
     + 2(1 + 1/η)·HbarH·E_c(E_{ν̂_c}(φ − a)² + E_{ν̂′_c}(φ − a)²)`,
  `ν̂′ = cheapIn (M₃ b̂) τ̂₀` the distribution of `sphPt(M₃ b̂ + τ̂₀γ)`.
* **`HbarH_mean`**: `E_θ[1_goodHat·HbarH n ζ θ] ≤ EHH n ζ`; **`EHH_le`**:
  `EHH n (1/20) ≤ 250·n/m` for `n ≥ 4096`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part140

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part105 (BM)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part138

/-! ## The constants -/

/-- The paper's `ζ′` for the computed centre: the bound of `|ŵ − ŵ₀|` on the good inputs. -/
noncomputable def zetaPH (ζ : ℝ) : ℝ := ζ * (3 + ζ) / (4798 / 10000 * (1 - ζ) ^ 2)

/-- The paper's `r_low` for the computed centre. -/
noncomputable def rLowH (ζ : ℝ) : ℝ := max 0 (1 - zetaPH ζ / wLowH)

/-- `(1 + √r_low)²(1 + r_low)`. -/
noncomputable def cRhoH (ζ : ℝ) : ℝ := (1 + √(rLowH ζ)) ^ 2 * (1 + rLowH ζ)

lemma zetaPH_nonneg {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) : 0 ≤ zetaPH ζ := by
  unfold zetaPH
  have : 0 < 1 - ζ := by linarith
  positivity

lemma rLowH_nonneg (ζ : ℝ) : 0 ≤ rLowH ζ := le_max_left _ _

lemma cRhoH_ge_one (ζ : ℝ) : 1 ≤ cRhoH ζ := by
  unfold cRhoH
  have h1 := rLowH_nonneg ζ
  have h2 := Real.sqrt_nonneg (rLowH ζ)
  nlinarith [mul_nonneg h2 h2, mul_nonneg (mul_nonneg h2 h2) h1, mul_nonneg h2 h1]

lemma cRhoH_pos (ζ : ℝ) : 0 < cRhoH ζ := lt_of_lt_of_le one_pos (cRhoH_ge_one ζ)

/-- `KfunH n ζ (u, θ)`: `n(ŵ − ŵ₀)²/(wLowH²·cRhoH ζ)` on the good set of inputs, `1` off it. -/
noncomputable def KfunH (n : ℕ) (ζ : ℝ) (p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) : ℝ :=
  (goodUH (2 * n) (mW n) ζ).indicator
      (fun p => (n : ℝ) / (wLowH ^ 2 * cRhoH ζ) *
        (wH (2 * n) (mW n) p.1 p.2 - w0H (2 * n) (mW n) p.2) ^ 2) p +
    (goodUH (2 * n) (mW n) ζ)ᶜ.indicator (fun _ => (1 : ℝ)) p

/-- **`HbarH n ζ θ = E_u KfunH n ζ (u, θ)`**: the bound of the mean squared Hellinger distance of
the exact and the cheap stand-in with the computed centre, at `θ = (M₁, M₂)`. -/
noncomputable def HbarH (n : ℕ) (ζ : ℝ) (θ : HidParam (2 * n) (mW n)) : ℝ :=
  ∫ u, KfunH n ζ (u, θ) ∂uniformSphere (2 * n)

lemma KfunH_of_mem {n : ℕ} {ζ : ℝ} {p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)}
    (hp : p ∈ goodUH (2 * n) (mW n) ζ) :
    KfunH n ζ p = (n : ℝ) / (wLowH ^ 2 * cRhoH ζ) *
      (wH (2 * n) (mW n) p.1 p.2 - w0H (2 * n) (mW n) p.2) ^ 2 := by
  unfold KfunH
  rw [Set.indicator_of_mem hp, Set.indicator_of_notMem (by simpa using hp), add_zero]

lemma KfunH_of_notMem {n : ℕ} {ζ : ℝ} {p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)}
    (hp : p ∉ goodUH (2 * n) (mW n) ζ) : KfunH n ζ p = 1 := by
  unfold KfunH
  rw [Set.indicator_of_notMem hp, Set.indicator_of_mem (by simpa using hp), zero_add]

lemma KfunH_nonneg (n : ℕ) (ζ : ℝ) (p : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) :
    0 ≤ KfunH n ζ p := by
  by_cases hp : p ∈ goodUH (2 * n) (mW n) ζ
  · rw [KfunH_of_mem hp]
    have := cRhoH_pos ζ
    have := wLowH_pos
    positivity
  · rw [KfunH_of_notMem hp]; exact zero_le_one

lemma measurable_KfunH {n : ℕ} (hn : 1 ≤ n) (ζ : ℝ) : Measurable (KfunH n ζ) := by
  have hN : 1 ≤ 2 * n := by omega
  unfold KfunH
  exact ((((measurable_wH hN).sub ((measurable_w0H hN).comp measurable_snd)).pow_const
    2).const_mul _).indicator (goodUH_meas hN ζ) |>.add
    (measurable_const.indicator (goodUH_meas hN ζ).compl)

lemma HbarH_nonneg (n : ℕ) (ζ : ℝ) (θ : HidParam (2 * n) (mW n)) : 0 ≤ HbarH n ζ θ :=
  integral_nonneg fun u => KfunH_nonneg n ζ (u, θ)

/-- `(x − z)² ≤ (1 + η)(x − y)² + (1 + 1/η)(y − z)²` for `η > 0`. -/
lemma sq_split {η : ℝ} (hη : 0 < η) (x y z : ℝ) :
    (x - z) ^ 2 ≤ (1 + η) * (x - y) ^ 2 + (1 + 1 / η) * (y - z) ^ 2 := by
  have h : (1 + η) * (x - y) ^ 2 + (1 + 1 / η) * (y - z) ^ 2 - (x - z) ^ 2 =
      (η * (x - y) - (y - z)) ^ 2 / η := by
    field_simp
    ring
  have h2 : 0 ≤ (η * (x - y) - (y - z)) ^ 2 / η := by positivity
  linarith

/-! ## The facts on the good event -/

section good

variable {n : ℕ} (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ goodHat n)

include hn hθ

/-- On `goodHat n` and the good inputs: `|ŵ − ŵ₀| ≤ ζ′`. -/
lemma wCloseH {ζ : ℝ} (hζ1 : ζ < 1) {u : Fin (2 * n) → ℝ}
    (hu : (u, θ) ∈ goodUH (2 * n) (mW n) ζ) :
    |wH (2 * n) (mW n) u θ - w0H (2 * n) (mW n) θ| ≤ zetaPH ζ := by
  obtain ⟨hD, hl⟩ := hu
  have hζ0 : 0 ≤ ζ := (abs_nonneg _).trans hD
  have h1ζ : 0 < 1 - ζ := by linarith
  have hw := w_diff (by norm_num : (0 : ℝ) < 4798 / 10000) (B0_window hn hθ).1 hζ1 hD hl
  refine hw.trans ?_
  unfold zetaPH
  rw [one_div_mul_eq_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  have : (2 + ζ) * |lamH (2 * n) (mW n) (u, θ).1 (u, θ).2 - 1| ≤ (2 + ζ) * ζ :=
    mul_le_mul_of_nonneg_left hl (by linarith)
  have hD' : |Dn (2 * n) (mW n) (u, θ).1 (u, θ).2 - 1| ≤ ζ := hD
  nlinarith

/-- **The good inputs**: for `θ ∈ goodHat n` and `u ∈ G_ζ`: `λ̂(u) > 0`, and the squared Hellinger
distance of `N(c, (σ̂(u)/λ̂(u))²I)` and `N(c, τ̂₀²I)` is at most `n(ŵ − ŵ₀)²/(wLowH²·cRhoH ζ)`. -/
theorem good_ptH {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) {u : Fin (2 * n) → ℝ}
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
  have hnb := normSq_bhat_pos hn hθ
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
  have hKpos : 0 < K := Bh_pos hn hθ
  set w := wH (2 * n) (mW n) u θ with hw
  set wb := w0H (2 * n) (mW n) θ with hwb
  have hτ2 : τ ^ 2 = K * w := by
    rw [hτ, div_pow]
    exact tauH_sq hN hm u hnb.ne' hkpos.ne' hTpos.ne'
  have hτ02 : tauHat (2 * n) (mW n) θ ^ 2 = K * wb := tauHat_sq hn hθ
  have hτ0pos := tauHat_pos hn hθ
  obtain ⟨hwb1, -⟩ := w0H_window hn hθ
  have hwLow := wLowH_pos
  have hwb0 : 0 < wb := by linarith
  have hw0 : 0 ≤ w := by
    have : 0 ≤ K * w := by rw [← hτ2]; positivity
    exact nonneg_of_mul_nonneg_right this hKpos
  have hclose : |w - wb| ≤ zetaPH ζ := wCloseH hn hθ hζ1 hu
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
lemma KfunH_le {ζ : ℝ} (hζ1 : ζ < 1) (u : Fin (2 * n) → ℝ) :
    KfunH n ζ (u, θ) ≤ (n : ℝ) / (wLowH ^ 2 * cRhoH ζ) * zetaPH ζ ^ 2 + 1 := by
  have hc := cRhoH_pos ζ
  have hwl := wLowH_pos
  have hC : 0 ≤ (n : ℝ) / (wLowH ^ 2 * cRhoH ζ) := by positivity
  by_cases hp : (u, θ) ∈ goodUH (2 * n) (mW n) ζ
  · rw [KfunH_of_mem hp]
    have hclose := wCloseH hn hθ hζ1 hp
    have hsq : (wH (2 * n) (mW n) u θ - w0H (2 * n) (mW n) θ) ^ 2 ≤ zetaPH ζ ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hclose 2
    have := mul_le_mul_of_nonneg_left hsq hC
    linarith
  · rw [KfunH_of_notMem hp]
    have : 0 ≤ (n : ℝ) / (wLowH ^ 2 * cRhoH ζ) * zetaPH ζ ^ 2 := by positivity
    linarith

lemma KfunH_integrable {ζ : ℝ} (hζ1 : ζ < 1) :
    Integrable (fun u => KfunH n ζ (u, θ)) (uniformSphere (2 * n)) := by
  have := uniformSphere_isProbability (2 * n) (by omega)
  refine Integrable.of_bound ((measurable_KfunH (by omega) ζ).comp
    measurable_prodMk_right).aestronglyMeasurable
    ((n : ℝ) / (wLowH ^ 2 * cRhoH ζ) * zetaPH ζ ^ 2 + 1) (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (KfunH_nonneg n ζ (u, θ))]
  exact KfunH_le hn hθ hζ1 u

/-- **The cheap stand-in against the exact stand-in with the computed centre, at one `c`.** For
`n ≥ 4096`, `θ ∈ goodHat n`, `0 ≤ ζ < 1`, every `c ∈ ℝⁿ`, bounded measurable `φ`, real `a`:
`(E_{ν̂_c} φ − E_{ν̂′_c} φ)² ≤ 2·HbarH n ζ θ·(E_{ν̂_c}(φ − a)² + E_{ν̂′_c}(φ − a)²)`. -/
theorem cheapMeanHat {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) (c : Fin n → ℝ)
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
      exact good_ptH hn hθ hζ0 hζ1 hp
    · right
      rw [KfunH_of_notMem hp]
  have h := cheap_mix (uniformSphere (2 * n)) (by omega : 2 ≤ n) (2 / (mW n : ℝ)) (bhat θ) c hh
    (tauHat_pos hn hθ) ((measurable_KfunH (by omega) ζ).comp measurable_prodMk_right)
    (KfunH_integrable hn hθ hζ1) hK hψ
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

/-- **The cheap stand-in theorem with the computed centre, for fixed `(M₁, M₂)`.** For
`n ≥ 4096`, `θ = (M₁, M₂) ∈ goodHat n`, `0 ≤ ζ < 1`, `η > 0`, bounded measurable `φ` and every real `a`,
with the expectation over `M₃`:
`E(E_{μ_W} φ − E_{ν̂′} φ)² ≤ (1 + η)·(1.83/n)·E_c Var_{ν̂_c} φ
   + 2(1 + 1/η)·HbarH n ζ θ·E_c(E_{ν̂_c}(φ − a)² + E_{ν̂′_c}(φ − a)²)`.
`ν̂′ = cheapIn (M₃ b̂) τ̂₀` is the distribution of `sphPt(M₃ b̂ + τ̂₀γ)`. -/
theorem cheapStandInHat {ζ : ℝ} (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1) {η : ℝ} (hη : 0 < η)
    {φ : (Fin n → ℝ) → ℝ} (hφ : BM φ) (a : ℝ) :
    ∫ M₃, ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂cheapIn (M₃.mulVec (bhat θ)) (tauHat (2 * n) (mW n) θ)) ^ 2
        ∂gaussMat n (mW n) (2 / (mW n : ℝ)) ≤
      (1 + η) * (183 / 100 / (n : ℝ) *
        ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ))
          (bhat θ) c] ∂cDist n (2 / (mW n : ℝ)) (bhat θ)) +
      2 * (1 + 1 / η) * HbarH n ζ θ *
        ∫ c, (∫ x, (φ x - a) ^ 2
              ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) (bhat θ) c +
            ∫ x, (φ x - a) ^ 2 ∂cheapIn c (tauHat (2 * n) (mW n) θ))
          ∂cDist n (2 / (mW n : ℝ)) (bhat θ) := by
  have hN : 1 ≤ 2 * n := by omega
  have := uniformSphere_isProbability (2 * n) hN
  have hh : Measurable (hid2 θ.1 θ.2) := (continuous_hid2 θ.1 θ.2).measurable
  set P := gaussMat n (mW n) (2 / (mW n : ℝ)) with hP
  set b := bhat θ with hb
  set τ₀ := tauHat (2 * n) (mW n) θ with hτ₀
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
      (1 + η) * ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2 +
      2 * (1 + 1 / η) * HbarH n ζ θ *
        (∫ x, (φ x - a) ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
            (M₃.mulVec b) +
          ∫ x, (φ x - a) ^ 2 ∂cheapIn (M₃.mulVec b) τ₀) := by
    intro M₃
    have h1 := cheapMeanHat hn hθ hζ0 hζ1 (M₃.mulVec b) hφ a
    exact (sq_split hη _ _ _).trans (add_le_add le_rfl
      (by
        have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 1 + 1 / η)
        have e : (1 + 1 / η) * (2 * HbarH n ζ θ *
            (∫ x, (φ x - a) ^ 2
                ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
                  (M₃.mulVec b) +
              ∫ x, (φ x - a) ^ 2 ∂cheapIn (M₃.mulVec b) τ₀)) =
            2 * (1 + 1 / η) * HbarH n ζ θ *
            (∫ x, (φ x - a) ^ 2
                ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
                  (M₃.mulVec b) +
              ∫ x, (φ x - a) ^ 2 ∂cheapIn (M₃.mulVec b) τ₀) := by ring
        rw [e] at h2
        exact h2))
  have i1 : Integrable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      (1 + η) * ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2) P := ((BM.const (1 + η)).mul (bX.sub bY).sq).integrable P
  have i2 : Integrable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      2 * (1 + 1 / η) * HbarH n ζ θ *
        (∫ x, (φ x - a) ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
            (M₃.mulVec b) +
          ∫ x, (φ x - a) ^ 2 ∂cheapIn (M₃.mulVec b) τ₀)) P :=
    ((BM.const (2 * (1 + 1 / η) * HbarH n ζ θ)).mul bS).integrable P
  have i12 : Integrable (fun M₃ : Matrix (Fin n) (Fin (mW n)) ℝ =>
      (1 + η) * ((∫ x, φ x ∂muWn ((θ.1, θ.2, M₃) : MlpParam (2 * n) (mW n) n)) -
        ∫ x, φ x ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
          (M₃.mulVec b)) ^ 2 +
      2 * (1 + 1 / η) * HbarH n ζ θ *
        (∫ x, (φ x - a) ^ 2 ∂standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b
            (M₃.mulVec b) +
          ∫ x, (φ x - a) ^ 2 ∂cheapIn (M₃.mulVec b) τ₀)) P := i1.add i2
  have hmono := integral_mono ((bX.sub bZ).sq.integrable P) i12 hpt
  rw [integral_add i1 i2, integral_const_mul, integral_const_mul] at hmono
  have h136 := standInHat140 hn hθ hφ
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
      183 / 100 / (n : ℝ) *
        ∫ c, Var[φ; standIn (uniformSphere (2 * n)) (hid2 θ.1 θ.2) (2 / (mW n : ℝ)) b c]
          ∂cDist n (2 / (mW n : ℝ)) b := h136
  have h137 := mul_le_mul_of_nonneg_left h136' (by positivity : (0 : ℝ) ≤ 1 + η)
  linarith

end good

/-! ## The mean of `HbarH` on the good event -/

/-- The paper's `ω₁²` for the computed centre. -/
noncomputable def OmegaH2 (n : ℕ) (ζ : ℝ) : ℝ :=
  (1 / (4798 / 10000 * (1 - ζ) ^ 2) *
    (√(10 / (mW n : ℝ) + 25 / (mW n : ℝ) ^ 2) +
      (2 + ζ) * (cHat2 (2 * n) (mW n) / kap1 (2 * n)))) ^ 2

/-- The paper's `β₁` for the computed centre. -/
noncomputable def BetaH (n : ℕ) (ζ : ℝ) : ℝ :=
  (10 / (mW n : ℝ) + 25 / (mW n : ℝ) ^ 2 + (cHat2 (2 * n) (mW n) / kap1 (2 * n)) ^ 2) / ζ ^ 2

/-- **`EHH n ζ`**: the bound of `E_θ[1_goodHat·HbarH]`: `n·ω₁²/(wLowH²·cRhoH ζ) + β₁`. -/
noncomputable def EHH (n : ℕ) (ζ : ℝ) : ℝ :=
  (n : ℝ) / (wLowH ^ 2 * cRhoH ζ) * OmegaH2 n ζ + BetaH n ζ

lemma OmegaH2_nonneg (n : ℕ) (ζ : ℝ) : 0 ≤ OmegaH2 n ζ := sq_nonneg _

lemma BetaH_nonneg {n : ℕ} (hn : 4096 ≤ n) (ζ : ℝ) : 0 ≤ BetaH n ζ := by
  have hm : (0 : ℝ) < mW n := by
    have := mW_ge_million hn
    exact_mod_cast (by omega : 0 < mW n)
  unfold BetaH
  positivity

lemma EHH_nonneg {n : ℕ} (hn : 4096 ≤ n) (ζ : ℝ) : 0 ≤ EHH n ζ := by
  unfold EHH
  have h1 := BetaH_nonneg hn ζ
  have h2 := OmegaH2_nonneg n ζ
  have h3 := cRhoH_pos ζ
  have h4 := wLowH_pos
  have : 0 ≤ (n : ℝ) / (wLowH ^ 2 * cRhoH ζ) * OmegaH2 n ζ := by positivity
  linarith

section mean

variable {n : ℕ} (hn : 4096 ≤ n) {ζ : ℝ} (hζ0 : 0 < ζ) (hζ1 : ζ < 1)

include hn hζ0 hζ1

/-- **The mean of `HbarH` on the good event.** `θ ↦ 1_goodHat(θ)·HbarH n ζ θ` is integrable, and
`E_θ[1_goodHat·HbarH n ζ θ] ≤ EHH n ζ`. -/
theorem HbarH_mean :
    Integrable ((goodHat n).indicator (HbarH n ζ)) (hidGauss (2 * n) (mW n)) ∧
      ∫ θ, (goodHat n).indicator (HbarH n ζ) θ ∂hidGauss (2 * n) (mW n) ≤ EHH n ζ := by
  have hN : 1 ≤ 2 * n := by omega
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have := uniformSphere_isProbability (2 * n) hN
  have mE := goodHat_meas (n := n) (by omega)
  obtain ⟨hk1, -⟩ := kap1_window hn
  have hkpos : 0 < kap1 (2 * n) := by linarith
  set μP := (uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n)) with hμP
  set C : ℝ := (n : ℝ) / (wLowH ^ 2 * cRhoH ζ) with hC
  have hC0 : 0 ≤ C := by
    have := cRhoH_pos ζ
    have := wLowH_pos
    rw [hC]; positivity
  set S := goodSH (goodHat n) ζ with hS
  set Bd : Set ((Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n)) :=
    {p | p.2 ∈ goodHat n ∧ p ∉ goodUH (2 * n) (mW n) ζ} with hBd
  have mS : MeasurableSet S := goodSH_meas hN mE ζ
  have mBd : MeasurableSet Bd := (measurable_snd mE).inter (goodUH_meas hN ζ).compl
  set F1 : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) → ℝ :=
    S.indicator (fun p => (wH (2 * n) (mW n) p.1 p.2 - w0H (2 * n) (mW n) p.2) ^ 2) with hF1
  set F2 : (Fin (2 * n) → ℝ) × HidParam (2 * n) (mW n) → ℝ :=
    Bd.indicator (fun _ => (1 : ℝ)) with hF2
  obtain ⟨iF1, hF1le⟩ := tauFluctH_gen_int (N := 2 * n) (m := mW n) hN hm hkpos mE
    (by norm_num : (0 : ℝ) < 4798 / 10000) hζ0.le hζ1
    (fun θ hθ => (B0_window hn hθ).1)
  have iF2 : Integrable F2 μP := (integrable_const (1 : ℝ)).indicator mBd
  have iF : Integrable (fun p => C * F1 p + F2 p) μP := (iF1.const_mul C).add iF2
  -- the pointwise identity
  have hpt : ∀ (θ : HidParam (2 * n) (mW n)) (u : Fin (2 * n) → ℝ),
      (goodHat n).indicator (fun θ => KfunH n ζ (u, θ)) θ = C * F1 (u, θ) + F2 (u, θ) := by
    intro θ u
    by_cases hθ : θ ∈ goodHat n
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
  have hfun : (goodHat n).indicator (HbarH n ζ) =
      fun θ => ∫ u, (C * F1 (u, θ) + F2 (u, θ)) ∂uniformSphere (2 * n) := by
    funext θ
    simp_rw [← hpt θ]
    by_cases hθ : θ ∈ goodHat n
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

/-! ## Numbers at `ζ = 1/20` -/

lemma rLowH_ge : 636 / 1000 ≤ rLowH (1 / 20) := by
  unfold rLowH zetaPH wLowH
  refine le_trans ?_ (le_max_right _ _)
  norm_num

lemma cRhoH_ge : 528 / 100 ≤ cRhoH (1 / 20) := by
  have hr := rLowH_ge
  have hs : 797 / 1000 ≤ √(rLowH (1 / 20)) := by
    refine Real.le_sqrt_of_sq_le ?_
    refine le_trans ?_ hr
    norm_num
  unfold cRhoH
  have h1 : ((1 : ℝ) + 797 / 1000) ^ 2 ≤ (1 + √(rLowH (1 / 20))) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 2
  have h2 : (1 : ℝ) + 636 / 1000 ≤ 1 + rLowH (1 / 20) := by linarith
  have h3 := mul_le_mul h1 h2 (by norm_num) (by positivity)
  refine le_trans ?_ h3
  norm_num

section num

variable {n : ℕ} (hn : 4096 ≤ n)

include hn

/-- `cHat2/κ₁ ≤ 5.741/√m`. -/
lemma cHat2_div_le :
    cHat2 (2 * n) (mW n) / kap1 (2 * n) ≤ 5741 / 1000 * √(1 / (mW n : ℝ)) := by
  have hmM := mW_ge_million hn
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
    linarith
  obtain ⟨hk1, -⟩ := kap1_window hn
  have a2 := mul_sqrt_le hmpos (cHat2_nonneg (2 * n) (mW n))
    (cHat2_sq_le (N := 2 * n) (by omega) hmM) (by norm_num : (0 : ℝ) ≤ 2834 / 1000)
    (by norm_num)
  have hs : 0 < √(mW n : ℝ) := Real.sqrt_pos.mpr hmpos
  have e : √(1 / (mW n : ℝ)) = 1 / √(mW n : ℝ) := by
    rw [Real.sqrt_div (by norm_num), Real.sqrt_one]
  rw [e]
  have h1 : cHat2 (2 * n) (mW n) ≤ 2834 / 1000 / √(mW n : ℝ) := by
    rw [le_div_iff₀ hs]
    exact a2
  have h2 : cHat2 (2 * n) (mW n) / kap1 (2 * n) ≤
      2834 / 1000 / √(mW n : ℝ) / (49372 / 100000) :=
    div_le_div₀ (by positivity) h1 (by norm_num) hk1
  refine h2.trans ?_
  rw [div_div, div_le_iff₀ (by positivity)]
  have e2 : 5741 / 1000 * (1 / √(mW n : ℝ)) * (√(mW n : ℝ) * (49372 / 100000)) =
      5741 / 1000 * (49372 / 100000) := by
    field_simp
  rw [e2]
  norm_num

lemma OmegaH2_le : OmegaH2 n (1 / 20) ≤ 1195 / (mW n : ℝ) := by
  have hm6 : (1000000 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_million hn
  have hm0 : (0 : ℝ) < mW n := by linarith
  set x : ℝ := 1 / (mW n : ℝ) with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx6 : x ≤ 1 / 1000000 := by
    rw [hx]; exact one_div_le_one_div_of_le (by norm_num) hm6
  set q : ℝ := √x with hq
  have hq0 : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q ^ 2 = x := Real.sq_sqrt hx0.le
  have e1 : 10 / (mW n : ℝ) + 25 / (mW n : ℝ) ^ 2 = 10 * x + 25 * x ^ 2 := by
    rw [hx]; ring
  have s1 : √(10 / (mW n : ℝ) + 25 / (mW n : ℝ) ^ 2) ≤ 317 / 100 * q := by
    rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 317 / 100 * q)]
    refine Real.sqrt_le_sqrt ?_
    rw [e1, mul_pow, hq2]
    nlinarith [mul_le_mul_of_nonneg_left hx6 hx0.le]
  have s2 : cHat2 (2 * n) (mW n) / kap1 (2 * n) ≤ 5741 / 1000 * q := cHat2_div_le hn
  obtain ⟨hk1, -⟩ := kap1_window hn
  have hc0 : 0 ≤ cHat2 (2 * n) (mW n) / kap1 (2 * n) :=
    div_nonneg (cHat2_nonneg _ _) (by linarith)
  unfold OmegaH2
  have h1 : 1 / (4798 / 10000 * (1 - (1 / 20 : ℝ)) ^ 2) *
      (√(10 / (mW n : ℝ) + 25 / (mW n : ℝ) ^ 2) +
        (2 + 1 / 20) * (cHat2 (2 * n) (mW n) / kap1 (2 * n))) ≤
      1 / (4798 / 10000 * (1 - (1 / 20 : ℝ)) ^ 2) *
      (317 / 100 * q + (2 + 1 / 20) * (5741 / 1000 * q)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    exact add_le_add s1 (mul_le_mul_of_nonneg_left s2 (by norm_num))
  have h2 := pow_le_pow_left₀ (by positivity) h1 2
  refine h2.trans ?_
  have e3 : (1 / (4798 / 10000 * (1 - (1 / 20 : ℝ)) ^ 2) *
      (317 / 100 * q + (2 + 1 / 20) * (5741 / 1000 * q))) ^ 2 =
      (1 / (4798 / 10000 * (1 - (1 / 20 : ℝ)) ^ 2) *
        (317 / 100 + (2 + 1 / 20) * (5741 / 1000))) ^ 2 * q ^ 2 := by ring
  rw [e3, hq2, div_eq_mul_one_div (1195 : ℝ), ← hx]
  refine mul_le_mul_of_nonneg_right ?_ hx0.le
  norm_num

lemma BetaH_le : BetaH n (1 / 20) ≤ 17200 / (mW n : ℝ) := by
  have hm6 : (1000000 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_million hn
  have hm0 : (0 : ℝ) < mW n := by linarith
  set x : ℝ := 1 / (mW n : ℝ) with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have hx6 : x ≤ 1 / 1000000 := by
    rw [hx]; exact one_div_le_one_div_of_le (by norm_num) hm6
  have s2 := cHat2_div_le hn
  rw [← hx] at s2
  obtain ⟨hk1, -⟩ := kap1_window hn
  have hc0 : 0 ≤ cHat2 (2 * n) (mW n) / kap1 (2 * n) :=
    div_nonneg (cHat2_nonneg _ _) (by linarith)
  have s3 : (cHat2 (2 * n) (mW n) / kap1 (2 * n)) ^ 2 ≤ (5741 / 1000) ^ 2 * x := by
    have := pow_le_pow_left₀ hc0 s2 2
    rwa [mul_pow, Real.sq_sqrt hx0.le] at this
  have e : BetaH n (1 / 20) =
      (10 * x + 25 * x ^ 2 + (cHat2 (2 * n) (mW n) / kap1 (2 * n)) ^ 2) / (1 / 20) ^ 2 := by
    unfold BetaH; rw [hx]; ring
  rw [e, div_eq_mul_one_div (17200 : ℝ), ← hx, div_le_iff₀ (by norm_num)]
  have := mul_le_mul_of_nonneg_left hx6 hx0.le
  nlinarith

/-- **The explicit size of `EHH`**: `EHH n (1/20) ≤ 250·n/m` for `n ≥ 4096`. -/
theorem EHH_le : EHH n (1 / 20) ≤ 250 * (n : ℝ) / (mW n : ℝ) := by
  have hm6 : (1000000 : ℝ) ≤ mW n := by exact_mod_cast mW_ge_million hn
  have hm0 : (0 : ℝ) < mW n := by linarith
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  set x : ℝ := 1 / (mW n : ℝ) with hx
  have hx0 : 0 < x := by rw [hx]; positivity
  have h1 := OmegaH2_le hn
  have h2 := BetaH_le hn
  rw [div_eq_mul_one_div (1195 : ℝ), ← hx] at h1
  rw [div_eq_mul_one_div (17200 : ℝ), ← hx] at h2
  have hc := cRhoH_ge
  have hw := wLowH_pos
  have hk : (n : ℝ) / (wLowH ^ 2 * cRhoH (1 / 20)) ≤ (n : ℝ) * (202 / 1000) := by
    have a1 : (n : ℝ) / (wLowH ^ 2 * cRhoH (1 / 20)) ≤ (n : ℝ) / (wLowH ^ 2 * (528 / 100)) :=
      div_le_div_of_nonneg_left hn0.le (by positivity)
        (mul_le_mul_of_nonneg_left hc (by positivity))
    refine a1.trans ?_
    rw [div_eq_mul_one_div]
    refine mul_le_mul_of_nonneg_left ?_ hn0.le
    unfold wLowH
    norm_num
  have hO0 := OmegaH2_nonneg n (1 / 20)
  have h3 : (n : ℝ) / (wLowH ^ 2 * cRhoH (1 / 20)) * OmegaH2 n (1 / 20) ≤
      (n : ℝ) * (202 / 1000) * (1195 * x) :=
    mul_le_mul hk h1 hO0 (by positivity)
  unfold EHH
  rw [div_eq_mul_one_div (250 * (n : ℝ)), ← hx]
  have h4 : 17200 * x ≤ 42 / 10 * (n : ℝ) * x := by
    refine mul_le_mul_of_nonneg_right ?_ hx0.le
    linarith
  have h5 : 0 ≤ (n : ℝ) * x := by positivity
  nlinarith

end num

end BstLean.Part140

open BstLean.Part140 in
#print axioms good_ptH
open BstLean.Part140 in
#print axioms cheapMeanHat
open BstLean.Part140 in
#print axioms cheapStandInHat
open BstLean.Part140 in
#print axioms HbarH_mean
open BstLean.Part140 in
#print axioms EHH_le
