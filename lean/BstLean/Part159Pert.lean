import BstLean.Part159Hat

/-!
# Part 159 (file `Pert`): the Hellinger moment for a centre near the computed centre

Role: `delegations/statements/p159-spec.md`, item 3. Do not use `sorry`, `native_decide` or
`axiom`.

Paper: `theorem7-02-world.tex`, Lemma `t7:p02:moment` (the World replacement moment), for a
general centre map `b(W₁, W₂)` and a general scalar `τ₀(W₁, W₂)` of the form
`τ₀² = B·(B·c − 1)`, `B = t_W|b|²` (the paper: `c = N/(S_W κ̃²)`; Part 140: `c = 1/(γκ₁²)`).

`N = 2n`, `m = mW n`, `t = 2/m`, `γ = 2/N`, `κ₁ = kap1 N`, `b̂ = bhat`, `D(u) = t|h(u)|²/γ`.
For the centre `b`: `T_b(u) = t⟨h(u), b⟩`, `q = √(c·γκ₁²)`, `x(u) = q·T_b(u)/(γκ₁)`
(so that `x² = c·T_b²/γ`), `w(u) = B·c·D/x² − 1`, `w₀ = B·c − 1`.

* `hell_scalar`: the Hellinger term of two scalars from `τ_u² = K·w`, `τ₀² = K·w₀`, `w ≥ ρ·w₀`.
* `pert_pt`: for one input with `|D − 1| ≤ ζ`, `|x − 1| ≤ ζ`:
  `H_u² ≤ n/((A_lo − 1)²·c_ρ)·(A_hi/(1 − ζ)²)²·(|D − 1| + (2 + ζ)|x − 1|)²`.
* `xG_L2`: `‖1_G·(x − 1)‖₂ ≤ q_hi·cHat2/κ₁ + ρ₂ + q_hi·(ε/κ₁)·√(1 + a_r)` if on `G`:
  `t|b − b̂|² ≤ γε²`, `q ≤ q_hi`, and `‖1_G·(q − 1)‖₂ ≤ ρ₂`.
* **`pert_moment`**: a majorant `K` of `E_u H_u²` on `G` with
  `E[1_G·K] ≤ vPert = n/((A_lo − 1)²·c_ρ)·Ω² + 2β` (the formula of the paper for `v_W`).
-/

namespace BstLean.Part159

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability)
open BstLean.Part130 BstLean.Part134
open BstLean.Part133 (L2le dotp_add_right)
open BstLean.Part136 (HidParam hidGauss mW_ge_million normSq_res continuous_hid2_joint)
open BstLean.Part137 (bhat measurable_bhat Dn That cHat2 continuous_Dn Dn_L2 normFluct137_joint
  dotL_sq_le)
open BstLean.Part138 (hellG hellG_le hell_ratio)
open BstLean.Part140
open BstLean.Part156 BstLean.Part157

variable {n : ℕ}

/-! ## Scalars -/

lemma hu2_le_hellG {k : ℕ} (hk : k ≠ 0) {l s τ₀ : ℝ} (hl : 0 < l) (hs : 0 ≤ s) (hτ : 0 < τ₀) :
    hu2 k l s τ₀ ≤ hellG k (s / l) τ₀ := by
  unfold hu2
  split_ifs with hc
  · exact le_rfl
  · have h0 : s = 0 := by
      by_contra h
      exact hc ⟨hl, lt_of_le_of_ne hs (Ne.symm h), hτ⟩
    rw [h0, zero_div, hellG_zero hk]

/-- **The Hellinger term of two scalars.** If `τ_u² = K·w`, `τ₀² = K·w₀`, `w₀ > 0` and
`w ≥ ρ·w₀`, then `hellG k τ_u τ₀ ≤ k·(w − w₀)²/(w₀²·(1 + √ρ)²(1 + ρ))`. -/
lemma hell_scalar {k : ℕ} (hk : 2 ≤ k) {τu τ K w w0 ρ : ℝ} (hτu : 0 ≤ τu) (hτ : 0 < τ)
    (hK : 0 < K) (h1 : τu ^ 2 = K * w) (h2 : τ ^ 2 = K * w0) (hw0 : 0 < w0) (hρ : 0 ≤ ρ)
    (hr : ρ * w0 ≤ w) :
    hellG k τu τ ≤ k * ((w - w0) ^ 2 / (w0 ^ 2 * ((1 + √ρ) ^ 2 * (1 + ρ)))) := by
  have a1 := hellG_le hk hτu hτ
  have hr2 : ρ * τ ^ 2 ≤ τu ^ 2 := by
    rw [h1, h2]
    nlinarith [mul_le_mul_of_nonneg_left hr hK.le]
  have a2 := hell_ratio hτu hτ hρ hr2
  have e4 : τ ^ 4 = (K * w0) ^ 2 := by rw [← h2]; ring
  have hc : 0 < (1 + √ρ) ^ 2 * (1 + ρ) := by positivity
  have a3 : (τu ^ 2 - τ ^ 2) ^ 2 / (τ ^ 4 * ((1 + √ρ) ^ 2 * (1 + ρ))) =
      (w - w0) ^ 2 / (w0 ^ 2 * ((1 + √ρ) ^ 2 * (1 + ρ))) := by
    rw [e4, h1, h2]
    field_simp
  calc hellG k τu τ ≤ (k : ℝ) * (τu - τ) ^ 2 / (τu ^ 2 + τ ^ 2) := a1
    _ = (k : ℝ) * ((τu - τ) ^ 2 / (τu ^ 2 + τ ^ 2)) := by rw [mul_div_assoc]
    _ ≤ (k : ℝ) * ((w - w0) ^ 2 / (w0 ^ 2 * ((1 + √ρ) ^ 2 * (1 + ρ)))) :=
      mul_le_mul_of_nonneg_left (a2.trans (le_of_eq a3)) (by positivity)

/-- The bound of `|w − w₀|` on the good inputs: `A_hi·ζ(3 + ζ)/(1 − ζ)²`. -/
noncomputable def zetaG (Ahi ζ : ℝ) : ℝ := Ahi * (ζ * (3 + ζ)) / (1 - ζ) ^ 2

/-- The lower bound of the ratio `w/w₀` on the good inputs. -/
noncomputable def rLowG (Alo Ahi ζ : ℝ) : ℝ := max 0 (1 - zetaG Ahi ζ / (Alo - 1))

/-- `(1 + √r_low)²(1 + r_low)`. -/
noncomputable def cRhoG (Alo Ahi ζ : ℝ) : ℝ :=
  (1 + √(rLowG Alo Ahi ζ)) ^ 2 * (1 + rLowG Alo Ahi ζ)

lemma rLowG_nonneg (Alo Ahi ζ : ℝ) : 0 ≤ rLowG Alo Ahi ζ := le_max_left _ _

lemma cRhoG_pos (Alo Ahi ζ : ℝ) : 0 < cRhoG Alo Ahi ζ := by
  unfold cRhoG
  have := rLowG_nonneg Alo Ahi ζ
  positivity

/-- The scalar form of `pert_pt`: real numbers only. `nb = |b|²`, `nh = |h|²`, `d = ⟨h, b⟩`,
`l = λ`, `s = σ`. -/
lemma pert_scalar {k : ℕ} (hk : 2 ≤ k) {t γ κ nb nh d l s cc τ Alo Ahi ζ D x : ℝ}
    (ht : 0 < t) (hγ : 0 < γ) (hκ : 0 < κ) (hnb0 : 0 ≤ nb)
    (hlam : l = d / nb) (hs0 : 0 ≤ s) (hs2 : nb ≠ 0 → s ^ 2 = t * (nh - d ^ 2 / nb))
    (hcc : 0 ≤ cc) (hAlo : 1 < Alo) (hζ0 : 0 ≤ ζ) (hζ1 : ζ < 1)
    (hA1 : Alo ≤ t * nb * cc) (hA2 : t * nb * cc ≤ Ahi)
    (hτ2 : τ ^ 2 = t * nb * (t * nb * cc - 1)) (hτ : 0 < τ)
    (hD : D = t * nh / γ) (hx : x = √(cc * (γ * κ ^ 2)) * (t * d / (γ * κ)))
    (hgD : |D - 1| ≤ ζ) (hgx : |x - 1| ≤ ζ) :
    hu2 k l s τ ≤
      k / ((Alo - 1) ^ 2 * cRhoG Alo Ahi ζ) * (Ahi / (1 - ζ) ^ 2) ^ 2 *
        (|D - 1| + (2 + ζ) * |x - 1|) ^ 2 := by
  have hBb0 : 0 ≤ t * nb := mul_nonneg ht.le hnb0
  have hBcc : 0 < t * nb * cc := by linarith
  have hBbpos : 0 < t * nb := by
    rcases hBb0.eq_or_lt with h0 | h0
    · rw [← h0, zero_mul] at hBcc; exact absurd hBcc (lt_irrefl _)
    · exact h0
  have hccpos : 0 < cc := by
    rcases hcc.eq_or_lt with h0 | h0
    · rw [← h0, mul_zero] at hBcc; exact absurd hBcc (lt_irrefl _)
    · exact h0
  have hnbpos : 0 < nb := by
    rcases hnb0.eq_or_lt with h0 | h0
    · rw [← h0, mul_zero] at hBbpos; exact absurd hBbpos (lt_irrefl _)
    · exact h0
  have hq0 : 0 ≤ √(cc * (γ * κ ^ 2)) := Real.sqrt_nonneg _
  have hq2 : √(cc * (γ * κ ^ 2)) ^ 2 = cc * (γ * κ ^ 2) := Real.sq_sqrt (by positivity)
  have h1ζ : 0 < 1 - ζ := by linarith
  have hx1 := abs_le.mp hgx
  have hxpos : 0 < x := by linarith
  have hγκ : 0 < γ * κ := mul_pos hγ hκ
  have hTpos : 0 < t * d := by
    by_contra hneg
    have h1 : t * d / (γ * κ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (not_lt.mp hneg) hγκ.le
    have h2 : x ≤ 0 := by rw [hx]; exact mul_nonpos_of_nonneg_of_nonpos hq0 h1
    linarith
  have hdpos : 0 < d := by
    by_contra hneg
    have : t * d ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le (not_lt.mp hneg)
    linarith
  have hl : 0 < l := by rw [hlam]; positivity
  have hs2' := hs2 hnbpos.ne'
  have hτu0 : 0 ≤ s / l := div_nonneg hs0 hl.le
  obtain ⟨w, hw⟩ : ∃ w : ℝ, w = t * nh * (t * nb) / (t * d) ^ 2 - 1 := ⟨_, rfl⟩
  have hτu2 : (s / l) ^ 2 = t * nb * w := by
    rw [div_pow, hs2', hlam, hw]
    field_simp
  have hx2 : x ^ 2 = cc * (t * d) ^ 2 / γ := by
    rw [hx, mul_pow, hq2]
    field_simp
  have htD : t * nh = γ * D := by rw [hD]; field_simp
  have hx2pos : 0 < x ^ 2 := by positivity
  have hw' : w = t * nb * cc * D / x ^ 2 - 1 := by
    rw [hw, htD, hx2]
    field_simp
  obtain ⟨w0, hw0⟩ : ∃ w0 : ℝ, w0 = t * nb * cc - 1 := ⟨_, rfl⟩
  have hw0lo : Alo - 1 ≤ w0 := by linarith
  have hw0pos : 0 < w0 := by linarith
  have hdiff : w - w0 = t * nb * cc * (D - x ^ 2) / x ^ 2 := by
    rw [hw', hw0]
    field_simp
    ring
  obtain ⟨R, hR⟩ : ∃ R : ℝ, R = |D - 1| + (2 + ζ) * |x - 1| := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hR]; positivity
  have hnum : |D - x ^ 2| ≤ R := by
    have e2 : D - x ^ 2 = (D - 1) - (x - 1) * (x + 1) := by ring
    rw [e2, hR]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul]
    have h3 : |x + 1| ≤ 2 + ζ := by
      rw [abs_of_pos (by linarith)]
      linarith
    nlinarith [abs_nonneg (x - 1), abs_nonneg (x + 1)]
  have hden : (1 - ζ) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ h1ζ.le (by linarith) 2
  have hAhi0 : 0 ≤ Ahi := hBcc.le.trans hA2
  have habs : |w - w0| ≤ Ahi / (1 - ζ) ^ 2 * R := by
    rw [hdiff, abs_div, abs_mul, abs_of_pos hBcc, abs_of_pos hx2pos]
    rw [div_le_iff₀ hx2pos]
    have h4 : t * nb * cc * |D - x ^ 2| ≤ Ahi * R := mul_le_mul hA2 hnum (abs_nonneg _) hAhi0
    have h5 : Ahi * R ≤ Ahi / (1 - ζ) ^ 2 * R * x ^ 2 := by
      have h6 : Ahi * R = Ahi / (1 - ζ) ^ 2 * R * (1 - ζ) ^ 2 := by field_simp
      rw [h6]
      exact mul_le_mul_of_nonneg_left hden (by positivity)
    linarith
  have hRle : R ≤ ζ * (3 + ζ) := by
    have h7 : (2 + ζ) * |x - 1| ≤ (2 + ζ) * ζ := mul_le_mul_of_nonneg_left hgx (by linarith)
    have h8 : ζ * (3 + ζ) = ζ + (2 + ζ) * ζ := by ring
    rw [hR, h8]
    linarith
  have hz : |w - w0| ≤ zetaG Ahi ζ := by
    refine habs.trans ?_
    unfold zetaG
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hRle hAhi0) (by positivity)
  have hwnn : 0 ≤ w := by
    have : 0 ≤ t * nb * w := by rw [← hτu2]; positivity
    exact nonneg_of_mul_nonneg_right this hBbpos
  have hAlo1 : 0 < Alo - 1 := by linarith
  have hr : rLowG Alo Ahi ζ * w0 ≤ w := by
    unfold rLowG
    rcases le_total (1 - zetaG Ahi ζ / (Alo - 1)) 0 with h0 | h0
    · rw [max_eq_left h0, zero_mul]; exact hwnn
    · rw [max_eq_right h0]
      have hz0 : 0 ≤ zetaG Ahi ζ := (abs_nonneg _).trans hz
      have h1 : zetaG Ahi ζ ≤ zetaG Ahi ζ / (Alo - 1) * w0 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hAlo1]
        exact mul_le_mul_of_nonneg_left hw0lo hz0
      have h2 := (abs_le.mp hz).1
      have e : (1 - zetaG Ahi ζ / (Alo - 1)) * w0 = w0 - zetaG Ahi ζ / (Alo - 1) * w0 := by ring
      rw [e]
      linarith
  have hτ2' : τ ^ 2 = t * nb * w0 := by rw [hw0]; exact hτ2
  have hH := hell_scalar hk hτu0 hτ hBbpos hτu2 hτ2' hw0pos (rLowG_nonneg Alo Ahi ζ) hr
  have hcρ := cRhoG_pos Alo Ahi ζ
  have hsq : (w - w0) ^ 2 ≤ (Ahi / (1 - ζ) ^ 2 * R) ^ 2 := by
    rw [← sq_abs (w - w0)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  have hfin : (k : ℝ) * ((w - w0) ^ 2 / (w0 ^ 2 * cRhoG Alo Ahi ζ)) ≤
      k / ((Alo - 1) ^ 2 * cRhoG Alo Ahi ζ) * (Ahi / (1 - ζ) ^ 2) ^ 2 * R ^ 2 := by
    have h1 : (w - w0) ^ 2 / (w0 ^ 2 * cRhoG Alo Ahi ζ) ≤
        (Ahi / (1 - ζ) ^ 2 * R) ^ 2 / ((Alo - 1) ^ 2 * cRhoG Alo Ahi ζ) :=
      div_le_div₀ (sq_nonneg _) hsq (by positivity)
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hAlo1.le hw0lo 2) hcρ.le)
    refine (mul_le_mul_of_nonneg_left h1 hk0).trans (le_of_eq ?_)
    field_simp
  rw [← hR]
  exact (hu2_le_hellG (by omega) hl hs0 hτ).trans (hH.trans hfin)

/-- **The Hellinger term of one good input, for a general centre `b` and a scalar
`τ² = B(B·c − 1)`, `B = t|b|²`.** `D = t|h|²/γ`, `x = √(c·γκ²)·t⟨h, b⟩/(γκ)`. -/
theorem pert_pt {k m : ℕ} (hk : 2 ≤ k) {t γ κ : ℝ} (ht : 0 < t) (hγ : 0 < γ) (hκ : 0 < κ)
    (h b : Fin m → ℝ) {cc τ Alo Ahi ζ : ℝ} (hcc : 0 ≤ cc) (hAlo : 1 < Alo) (hζ0 : 0 ≤ ζ)
    (hζ1 : ζ < 1)
    (hA1 : Alo ≤ t * normSq b * cc) (hA2 : t * normSq b * cc ≤ Ahi)
    (hτ2 : τ ^ 2 = t * normSq b * (t * normSq b * cc - 1)) (hτ : 0 < τ)
    {D x : ℝ} (hD : D = t * normSq h / γ)
    (hx : x = √(cc * (γ * κ ^ 2)) * (t * dotp h b / (γ * κ)))
    (hgD : |D - 1| ≤ ζ) (hgx : |x - 1| ≤ ζ) :
    hu2 k (lam b h) (sig t b h) τ ≤
      k / ((Alo - 1) ^ 2 * cRhoG Alo Ahi ζ) * (Ahi / (1 - ζ) ^ 2) ^ 2 *
        (|D - 1| + (2 + ζ) * |x - 1|) ^ 2 := by
  have hs0 : 0 ≤ sig t b h := by unfold sig; positivity
  have hs2 : normSq b ≠ 0 → sig t b h ^ 2 = t * (normSq h - dotp h b ^ 2 / normSq b) := by
    intro hb
    unfold sig
    rw [mul_pow, Real.sq_sqrt ht.le, Real.sq_sqrt (normSq_nonneg _), normSq_res hb]
    rfl
  exact pert_scalar hk ht hγ hκ (normSq_nonneg b) (rfl : lam b h = dotp h b / normSq b) hs0 hs2
    hcc hAlo hζ0 hζ1 hA1 hA2 hτ2 hτ hD hx hgD hgx

/-! ## The moment over the input and the hidden matrices -/

/-- `q = √(c·γκ₁²)`: the ratio of the calibration constant of the scalar to that of Part 140. -/
noncomputable def qOf (n : ℕ) (cc : WHid n → ℝ) (θ : WHid n) : ℝ :=
  √(cc θ * (2 / ((2 * n : ℕ) : ℝ) * kap1 (2 * n) ^ 2))

/-- `T_b(u) = t⟨h(u), b⟩`. -/
noncomputable def TbOf (b : WHid n → Fin (mW n) → ℝ) (p : (Fin (2 * n) → ℝ) × WHid n) : ℝ :=
  2 / (mW n : ℝ) * dotp (hid2 p.2.1 p.2.2 p.1) (b p.2)

/-- `x(u) = q·T_b(u)/(γκ₁)` (`x² = c·T_b²/γ`; `x = 1` is the calibrated value). -/
noncomputable def xOf (b : WHid n → Fin (mW n) → ℝ) (cc : WHid n → ℝ)
    (p : (Fin (2 * n) → ℝ) × WHid n) : ℝ :=
  qOf n cc p.2 * (TbOf b p / (2 / ((2 * n : ℕ) : ℝ) * kap1 (2 * n)))

lemma measurable_qOf {cc : WHid n → ℝ} (mcc : Measurable cc) : Measurable (qOf n cc) :=
  (mcc.mul_const _).sqrt

lemma measurable_hid2P :
    Measurable (fun z : (Fin (2 * n) → ℝ) × WHid n => hid2 z.2.1 z.2.2 z.1) :=
  (continuous_hid2_joint.comp (continuous_snd.prodMk continuous_fst)).measurable

lemma measurable_TbOf {b : WHid n → Fin (mW n) → ℝ} (mb : Measurable b) :
    Measurable (TbOf b) :=
  (BstLean.Part132.measurable_dotp_comp measurable_hid2P (mb.comp measurable_snd)).const_mul _

lemma measurable_xOf {b : WHid n → Fin (mW n) → ℝ} (mb : Measurable b) {cc : WHid n → ℝ}
    (mcc : Measurable cc) : Measurable (xOf b cc) :=
  ((measurable_qOf mcc).comp measurable_snd).mul ((measurable_TbOf mb).div_const _)

/-- `a_r = √(10/m + 25/m²) = ‖D − 1‖₂`. -/
noncomputable def arW (n : ℕ) : ℝ := √(10 / (mW n : ℝ) + 25 / (mW n : ℝ) ^ 2)

/-- The bound of `‖1_G·(x − 1)‖₂`. -/
noncomputable def lxG (n : ℕ) (ε ρ₂ qhi : ℝ) : ℝ :=
  qhi * (cHat2 (2 * n) (mW n) / kap1 (2 * n)) + ρ₂ + qhi * (ε / kap1 (2 * n)) * √(1 + arW n)

/-- **The bound of the restricted Hellinger moment** (the paper's formula for `v_W(n)`):
`n/((A_lo − 1)²·c_ρ)·(A_hi/(1 − ζ)²·(a_r + (2 + ζ)·l_x))² + 2·(a_r² + l_x²)/ζ²`. -/
noncomputable def vPert (n : ℕ) (ε ρ₂ Alo Ahi qhi ζ : ℝ) : ℝ :=
  (n : ℝ) / ((Alo - 1) ^ 2 * cRhoG Alo Ahi ζ) *
      (Ahi / (1 - ζ) ^ 2 * (arW n + (2 + ζ) * lxG n ε ρ₂ qhi)) ^ 2 +
    2 * ((arW n ^ 2 + lxG n ε ρ₂ qhi ^ 2) / ζ ^ 2)

lemma arW_pos (hn : 4096 ≤ n) : 0 < arW n := by
  have hm : (0 : ℝ) < mW n := by
    have := mW_ge_million hn
    exact_mod_cast (by omega : 0 < mW n)
  unfold arW
  positivity

lemma Dn_nonneg' (p : (Fin (2 * n) → ℝ) × WHid n) : 0 ≤ Dn (2 * n) (mW n) p.1 p.2 := by
  unfold Dn
  have := normSq_nonneg (hid2 p.2.1 p.2.2 p.1)
  positivity

/-- `‖√D‖₂ ≤ √(1 + a_r)`. -/
lemma sqrtD_L2 (hn : 4096 ≤ n) :
    L2le ((uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n)))
      (fun p => √(Dn (2 * n) (mW n) p.1 p.2)) (√(1 + arW n)) := by
  have hN : 1 ≤ 2 * n := by omega
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have := uniformSphere_isProbability (2 * n) hN
  have ha := arW_pos hn
  obtain ⟨i1, e1⟩ := normFluct137_joint (N := 2 * n) (m := mW n) hN hm
  have mD : Measurable (fun p : (Fin (2 * n) → ℝ) × WHid n => Dn (2 * n) (mW n) p.1 p.2) :=
    continuous_Dn.measurable
  refine L2le.of_sq_le mD.sqrt.aestronglyMeasurable
    (G := fun p => (1 + arW n / 2) + 1 / (2 * arW n) * (Dn (2 * n) (mW n) p.1 p.2 - 1) ^ 2)
    ?_ ?_ ?_
  · exact (integrable_const _).add (i1.const_mul _)
  · intro p
    rw [Real.sq_sqrt (Dn_nonneg' p)]
    set y := Dn (2 * n) (mW n) p.1 p.2 - 1 with hy
    have h1 : |y| ≤ arW n / 2 + 1 / (2 * arW n) * y ^ 2 := by
      have h2 : y ^ 2 = |y| ^ 2 := by rw [sq_abs]
      rw [h2, ← sub_nonneg]
      have h3 : arW n / 2 + 1 / (2 * arW n) * |y| ^ 2 - |y| = (|y| - arW n) ^ 2 / (2 * arW n) := by
        field_simp
        ring
      rw [h3]
      positivity
    have h4 : y ≤ |y| := le_abs_self y
    linarith
  · rw [integral_add (integrable_const _) (i1.const_mul _), integral_const_mul, e1]
    simp only [integral_const, probReal_univ, one_smul]
    rw [Real.sq_sqrt (by positivity)]
    have e3 : (10 / (mW n : ℝ) + 25 / (mW n : ℝ) ^ 2) = arW n ^ 2 := by
      unfold arW
      rw [Real.sq_sqrt (by positivity)]
    rw [e3]
    have : 1 / (2 * arW n) * arW n ^ 2 = arW n / 2 := by field_simp
    rw [this]
    linarith

/-- **The second moment of `x − 1` on a hidden event `G`.** If on `G`: `t|b − b̂|² ≤ γε²` and
`q ≤ q_hi`, and `‖1_G·(q − 1)‖₂ ≤ ρ₂`, then `‖1_G·(x − 1)‖₂ ≤ l_x`. -/
theorem xG_L2 (hn : 4096 ≤ n) {b : WHid n → Fin (mW n) → ℝ} (mb : Measurable b)
    {cc : WHid n → ℝ} (mcc : Measurable cc) {G : Set (WHid n)} (mG : MeasurableSet G)
    {ε ρ₂ qhi : ℝ} (hε : 0 ≤ ε) (hρ : 0 ≤ ρ₂) (hqhi : 0 ≤ qhi)
    (h1 : ∀ θ ∈ G, 2 / (mW n : ℝ) * normSq (b θ - bhat θ) ≤ 2 / ((2 * n : ℕ) : ℝ) * ε ^ 2)
    (h2 : ∀ θ ∈ G, qOf n cc θ ≤ qhi)
    (h5 : L2le (hidGauss (2 * n) (mW n)) (G.indicator fun θ => qOf n cc θ - 1) ρ₂) :
    L2le ((uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n)))
      (fun p => |(Prod.snd ⁻¹' G).indicator (fun p => xOf b cc p - 1) p|) (lxG n ε ρ₂ qhi) := by
  have hN : 1 ≤ 2 * n := by omega
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have hmpos : (0 : ℝ) < mW n := by exact_mod_cast hm
  have := uniformSphere_isProbability (2 * n) hN
  obtain ⟨hk1, -⟩ := kap1_window hn
  have hκ : 0 < kap1 (2 * n) := by linarith
  have hNpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast hN
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by positivity
  set μP := (uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n)) with hμP
  have hc0 : 0 ≤ cHat2 (2 * n) (mW n) / kap1 (2 * n) :=
    div_nonneg (BstLean.Part140.cHat2_nonneg _ _) hκ.le
  -- the three pieces
  have A1 := (lamH_L2 (N := 2 * n) (m := mW n) hN hm hκ).const_mul_nonneg hqhi
  have hmap : μP.map Prod.snd = hidGauss (2 * n) (mW n) := by
    rw [hμP, Measure.map_snd_prod, measure_univ, one_smul]
  have A2' := h5.comp_map (P := μP) measurable_snd hmap
  have mq : Measurable (fun p : (Fin (2 * n) → ℝ) × WHid n =>
      |G.indicator (fun θ => qOf n cc θ - 1) p.2|) :=
    ((((measurable_qOf mcc).sub_const 1).indicator mG).comp measurable_snd).abs
  have A2 : L2le μP (fun p : (Fin (2 * n) → ℝ) × WHid n =>
      |G.indicator (fun θ => qOf n cc θ - 1) p.2|) ρ₂ :=
    L2le.of_abs_le mq.aestronglyMeasurable A2' fun p => by rw [abs_abs]
  have A3 := (sqrtD_L2 hn).const_mul_nonneg
    (c := qhi * (ε / kap1 (2 * n))) (by positivity)
  have A12 := A1.add' A2 (mul_nonneg hqhi hc0) hρ
  have A123 := A12.add' A3 (add_nonneg (mul_nonneg hqhi hc0) hρ) (by positivity)
  have mf : Measurable (fun p : (Fin (2 * n) → ℝ) × WHid n =>
      |(Prod.snd ⁻¹' G).indicator (fun p => xOf b cc p - 1) p|) :=
    (((measurable_xOf mb mcc).sub_const 1).indicator (measurable_snd mG)).abs
  unfold lxG
  refine L2le.of_abs_le mf.aestronglyMeasurable A123 fun p => ?_
  rw [abs_abs]
  have hD0 := Dn_nonneg' p
  have hg0 : 0 ≤ qhi * |lamH (2 * n) (mW n) p.1 p.2 - 1| +
      |G.indicator (fun θ => qOf n cc θ - 1) p.2| +
      qhi * (ε / kap1 (2 * n)) * √(Dn (2 * n) (mW n) p.1 p.2) := by positivity
  refine le_trans ?_ (le_abs_self _)
  by_cases hp : p.2 ∈ G
  · have hp' : p ∈ Prod.snd ⁻¹' G := hp
    rw [Set.indicator_of_mem hp', Set.indicator_of_mem hp]
    set q := qOf n cc p.2 with hq
    have hq0 : 0 ≤ q := Real.sqrt_nonneg _
    have hqle : q ≤ qhi := h2 p.2 hp
    set hv := hid2 p.2.1 p.2.2 p.1 with hhv
    set δ := b p.2 - bhat p.2 with hδ
    set γ := (2 : ℝ) / ((2 * n : ℕ) : ℝ) with hγdef
    set κ := kap1 (2 * n) with hκdef
    have hγκ : 0 < γ * κ := mul_pos hγ hκ
    have hb : b p.2 = bhat p.2 + δ := by rw [hδ]; abel
    have hT : TbOf b p = That (2 * n) (mW n) p.1 p.2 + 2 / (mW n : ℝ) * dotp hv δ := by
      unfold TbOf That
      rw [hb, dotp_add_right]
      ring
    have hx : xOf b cc p - 1 = q * (lamH (2 * n) (mW n) p.1 p.2 - 1) + (q - 1) +
        q * (2 / (mW n : ℝ) * dotp hv δ / (γ * κ)) := by
      unfold xOf lamH
      rw [hT]
      ring
    -- Cauchy–Schwarz
    have hcs : (2 / (mW n : ℝ) * dotp hv δ) ^ 2 ≤
        (γ * ε) ^ 2 * Dn (2 * n) (mW n) p.1 p.2 := by
      have h3 : dotp hv δ ^ 2 ≤ normSq hv * normSq δ := dotL_sq_le hv δ
      have h4 : 2 / (mW n : ℝ) * normSq hv = γ * Dn (2 * n) (mW n) p.1 p.2 := by
        rw [hhv, hγdef]
        unfold Dn
        field_simp
      have h5' : 2 / (mW n : ℝ) * normSq δ ≤ γ * ε ^ 2 := h1 p.2 hp
      have h6 : (2 / (mW n : ℝ) * dotp hv δ) ^ 2 ≤
          (2 / (mW n : ℝ) * normSq hv) * (2 / (mW n : ℝ) * normSq δ) := by
        have : (0 : ℝ) ≤ (2 / (mW n : ℝ)) ^ 2 := by positivity
        nlinarith [mul_le_mul_of_nonneg_left h3 this]
      rw [h4] at h6
      have h7 : γ * Dn (2 * n) (mW n) p.1 p.2 * (2 / (mW n : ℝ) * normSq δ) ≤
          γ * Dn (2 * n) (mW n) p.1 p.2 * (γ * ε ^ 2) :=
        mul_le_mul_of_nonneg_left h5' (by positivity)
      calc (2 / (mW n : ℝ) * dotp hv δ) ^ 2 ≤ _ := h6
        _ ≤ _ := h7
        _ = (γ * ε) ^ 2 * Dn (2 * n) (mW n) p.1 p.2 := by ring
    have habs : |2 / (mW n : ℝ) * dotp hv δ| ≤ γ * ε * √(Dn (2 * n) (mW n) p.1 p.2) := by
      have h8 := Real.abs_le_sqrt hcs
      rwa [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)] at h8
    have h9 : |2 / (mW n : ℝ) * dotp hv δ / (γ * κ)| ≤
        ε / κ * √(Dn (2 * n) (mW n) p.1 p.2) := by
      rw [abs_div, abs_of_pos hγκ, div_le_iff₀ hγκ]
      refine habs.trans (le_of_eq ?_)
      field_simp
    rw [hx]
    have t1 : |q * (lamH (2 * n) (mW n) p.1 p.2 - 1)| ≤
        qhi * |lamH (2 * n) (mW n) p.1 p.2 - 1| := by
      rw [abs_mul, abs_of_nonneg hq0]
      exact mul_le_mul_of_nonneg_right hqle (abs_nonneg _)
    have t3 : |q * (2 / (mW n : ℝ) * dotp hv δ / (γ * κ))| ≤
        qhi * (ε / κ) * √(Dn (2 * n) (mW n) p.1 p.2) := by
      rw [abs_mul, abs_of_nonneg hq0, mul_assoc]
      exact mul_le_mul hqle h9 (abs_nonneg _) hqhi
    have t4 := abs_add_three (q * (lamH (2 * n) (mW n) p.1 p.2 - 1)) (q - 1)
      (q * (2 / (mW n : ℝ) * dotp hv δ / (γ * κ)))
    linarith
  · have hp' : p ∉ Prod.snd ⁻¹' G := hp
    rw [Set.indicator_of_notMem hp', abs_zero]
    exact hg0

/-- **The restricted Hellinger moment for a centre near the computed centre** (Lemma
`t7:p02:moment` of the paper in a general form). `G` is a measurable hidden event. On `G`:
`t|b − b̂|² ≤ γε²`; the scalar is `τ² = B(B·c − 1)` with `B = t|b|²`, `c ≥ 0`,
`A_lo ≤ B·c ≤ A_hi`, `1 < A_lo`; `q = √(c·γκ₁²) ≤ q_hi`; and `‖1_G·(q − 1)‖₂ ≤ ρ₂`. Then there
is a majorant `K` of `E_u H_u²` on `G` with `E[1_G·K] ≤ vPert`. -/
theorem pert_moment (hn : 4096 ≤ n) {b : WHid n → Fin (mW n) → ℝ} (mb : Measurable b)
    {cc τ : WHid n → ℝ} (mcc : Measurable cc) {G : Set (WHid n)} (mG : MeasurableSet G)
    {ε ρ₂ Alo Ahi qhi ζ : ℝ} (hε : 0 ≤ ε) (hρ : 0 ≤ ρ₂) (hAlo : 1 < Alo) (hqhi : 0 ≤ qhi)
    (hζ0 : 0 < ζ) (hζ1 : ζ < 1)
    (h1 : ∀ θ ∈ G, 2 / (mW n : ℝ) * normSq (b θ - bhat θ) ≤ 2 / ((2 * n : ℕ) : ℝ) * ε ^ 2)
    (h2 : ∀ θ ∈ G, 0 ≤ cc θ ∧ qOf n cc θ ≤ qhi)
    (h3 : ∀ θ ∈ G, Alo ≤ 2 / (mW n : ℝ) * normSq (b θ) * cc θ ∧
      2 / (mW n : ℝ) * normSq (b θ) * cc θ ≤ Ahi)
    (h4 : ∀ θ ∈ G, τ θ ^ 2 = 2 / (mW n : ℝ) * normSq (b θ) *
      (2 / (mW n : ℝ) * normSq (b θ) * cc θ - 1) ∧ 0 < τ θ)
    (h5 : L2le (hidGauss (2 * n) (mW n)) (G.indicator fun θ => qOf n cc θ - 1) ρ₂) :
    ∃ K : WHid n → ℝ, Integrable (G.indicator K) (hidGauss (2 * n) (mW n)) ∧
      (∀ θ ∈ G, hellHid b τ θ ≤ K θ) ∧
      ∫ θ, G.indicator K θ ∂hidGauss (2 * n) (mW n) ≤ vPert n ε ρ₂ Alo Ahi qhi ζ := by
  have hN : 1 ≤ 2 * n := by omega
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have hmpos : (0 : ℝ) < mW n := by exact_mod_cast hm
  have := uniformSphere_isProbability (2 * n) hN
  obtain ⟨hk1, -⟩ := kap1_window hn
  have hκ : 0 < kap1 (2 * n) := by linarith
  have hNpos : (0 : ℝ) < ((2 * n : ℕ) : ℝ) := by exact_mod_cast hN
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by positivity
  have h1ζ : 0 < 1 - ζ := by linarith
  have hAlo1 : 0 < Alo - 1 := by linarith
  have hcρ := cRhoG_pos Alo Ahi ζ
  set μP := (uniformSphere (2 * n)).prod (hidGauss (2 * n) (mW n)) with hμP
  have mD : Measurable (fun p : (Fin (2 * n) → ℝ) × WHid n => Dn (2 * n) (mW n) p.1 p.2) :=
    continuous_Dn.measurable
  have mx := measurable_xOf (n := n) mb mcc
  have ha := arW_pos hn
  have hc0 : 0 ≤ cHat2 (2 * n) (mW n) / kap1 (2 * n) :=
    div_nonneg (BstLean.Part140.cHat2_nonneg _ _) hκ.le
  have hlx0 : 0 ≤ lxG n ε ρ₂ qhi := by unfold lxG; positivity
  set good : Set ((Fin (2 * n) → ℝ) × WHid n) :=
    {p | |Dn (2 * n) (mW n) p.1 p.2 - 1| ≤ ζ ∧ |xOf b cc p - 1| ≤ ζ} with hgood
  have mgood : MeasurableSet good :=
    (measurableSet_le (mD.sub_const 1).abs measurable_const).inter
      (measurableSet_le (mx.sub_const 1).abs measurable_const)
  set GP : Set ((Fin (2 * n) → ℝ) × WHid n) := Prod.snd ⁻¹' G with hGP
  have mGP : MeasurableSet GP := measurable_snd mG
  set R : (Fin (2 * n) → ℝ) × WHid n → ℝ := fun p =>
    |Dn (2 * n) (mW n) p.1 p.2 - 1| + (2 + ζ) * |xOf b cc p - 1| with hR
  have mR : Measurable R := (mD.sub_const 1).abs.add (((mx.sub_const 1).abs).const_mul _)
  set CK : ℝ := (n : ℝ) / ((Alo - 1) ^ 2 * cRhoG Alo Ahi ζ) * (Ahi / (1 - ζ) ^ 2) ^ 2 with hCK
  have hCK0 : 0 ≤ CK := by rw [hCK]; positivity
  set F1 : (Fin (2 * n) → ℝ) × WHid n → ℝ := (GP ∩ good).indicator (fun p => R p ^ 2) with hF1
  set F2 : (Fin (2 * n) → ℝ) × WHid n → ℝ :=
    (GP ∩ goodᶜ).indicator (fun _ => (1 : ℝ)) with hF2
  have mF1 : Measurable F1 := (mR.pow_const 2).indicator (mGP.inter mgood)
  have mF2 : Measurable F2 := measurable_const.indicator (mGP.inter mgood.compl)
  -- the two `L²` bounds
  have hX := xG_L2 hn mb mcc mG hε hρ hqhi h1 (fun θ hθ => (h2 θ hθ).2) h5
  have hDL := Dn_L2 (N := 2 * n) (m := mW n) hN hm
  have hRf := hDL.add' (hX.const_mul_nonneg (by linarith : (0 : ℝ) ≤ 2 + ζ))
    (Real.sqrt_nonneg _) (mul_nonneg (by linarith) hlx0)
  have hF1le : ∀ p, F1 p ≤ (|Dn (2 * n) (mW n) p.1 p.2 - 1| + (2 + ζ) *
      |GP.indicator (fun p => xOf b cc p - 1) p|) ^ 2 := by
    intro p
    by_cases hp : p ∈ GP ∩ good
    · rw [hF1, Set.indicator_of_mem hp, Set.indicator_of_mem hp.1]
    · rw [hF1, Set.indicator_of_notMem hp]
      positivity
  have hF1nn : ∀ p, 0 ≤ F1 p := fun p => Set.indicator_nonneg (fun _ _ => sq_nonneg _) p
  have iF1 : Integrable F1 μP := by
    refine Integrable.mono' hRf.int_sq mF1.aestronglyMeasurable
      (Filter.Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hF1nn p)]
    exact hF1le p
  have hF1int : ∫ p, F1 p ∂μP ≤ (arW n + (2 + ζ) * lxG n ε ρ₂ qhi) ^ 2 :=
    (integral_mono iF1 hRf.int_sq hF1le).trans hRf.le
  have iF2 : Integrable F2 μP := (integrable_const (1 : ℝ)).indicator (mGP.inter mgood.compl)
  have hF2int : ∫ p, F2 p ∂μP ≤ (arW n ^ 2 + lxG n ε ρ₂ qhi ^ 2) / ζ ^ 2 := by
    have e : ∫ p, F2 p ∂μP = μP.real (GP ∩ goodᶜ) := by
      rw [hF2, integral_indicator (mGP.inter mgood.compl), setIntegral_const, smul_eq_mul,
        mul_one]
    rw [e]
    set g : (Fin (2 * n) → ℝ) × WHid n → ℝ := fun p =>
      |Dn (2 * n) (mW n) p.1 p.2 - 1| ^ 2 +
        |GP.indicator (fun p => xOf b cc p - 1) p| ^ 2 with hg
    have ig : Integrable g μP := hDL.int_sq.add hX.int_sq
    have hgle : ∫ p, g p ∂μP ≤ arW n ^ 2 + lxG n ε ρ₂ qhi ^ 2 := by
      rw [hg, integral_add hDL.int_sq hX.int_sq]
      exact add_le_add hDL.le hX.le
    have hsub : GP ∩ goodᶜ ⊆ {p | ζ ^ 2 ≤ g p} := by
      intro p hp
      have hng : ¬ (|Dn (2 * n) (mW n) p.1 p.2 - 1| ≤ ζ ∧ |xOf b cc p - 1| ≤ ζ) := hp.2
      change ζ ^ 2 ≤ |Dn (2 * n) (mW n) p.1 p.2 - 1| ^ 2 +
        |GP.indicator (fun p => xOf b cc p - 1) p| ^ 2
      rw [Set.indicator_of_mem hp.1]
      by_cases hd : |Dn (2 * n) (mW n) p.1 p.2 - 1| ≤ ζ
      · have hx : ζ < |xOf b cc p - 1| := by
          by_contra h
          exact hng ⟨hd, not_lt.mp h⟩
        have := pow_le_pow_left₀ hζ0.le hx.le 2
        nlinarith [sq_nonneg (|Dn (2 * n) (mW n) p.1 p.2 - 1|)]
      · have := pow_le_pow_left₀ hζ0.le (not_le.mp hd).le 2
        nlinarith [sq_nonneg (|xOf b cc p - 1|)]
    have hmk := mul_meas_ge_le_integral_of_nonneg (μ := μP) (f := g)
      (Filter.Eventually.of_forall fun p => by positivity) ig (ζ ^ 2)
    have hle : μP.real (GP ∩ goodᶜ) ≤ μP.real {p | ζ ^ 2 ≤ g p} :=
      measureReal_mono hsub (measure_ne_top _ _)
    rw [le_div_iff₀ (by positivity)]
    calc μP.real (GP ∩ goodᶜ) * ζ ^ 2 ≤ μP.real {p | ζ ^ 2 ≤ g p} * ζ ^ 2 :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = ζ ^ 2 * μP.real {p | ζ ^ 2 ≤ g p} := mul_comm _ _
      _ ≤ ∫ p, g p ∂μP := hmk
      _ ≤ _ := hgle
  -- the majorant
  set F : (Fin (2 * n) → ℝ) × WHid n → ℝ := fun p => CK * F1 p + 2 * F2 p with hF
  have mF : Measurable F := (mF1.const_mul _).add (mF2.const_mul _)
  have iF : Integrable F μP := (iF1.const_mul CK).add (iF2.const_mul 2)
  refine ⟨fun θ => ∫ u, F (u, θ) ∂uniformSphere (2 * n), ?_, ?_, ?_⟩
  all_goals
    have hKG : G.indicator (fun θ => ∫ u, F (u, θ) ∂uniformSphere (2 * n)) =
        fun θ => ∫ u, F (u, θ) ∂uniformSphere (2 * n) := by
      funext θ
      by_cases hθ : θ ∈ G
      · rw [Set.indicator_of_mem hθ]
      · rw [Set.indicator_of_notMem hθ]
        have h0 : ∀ u : Fin (2 * n) → ℝ, F (u, θ) = 0 := by
          intro u
          have a1 : (u, θ) ∉ GP ∩ good := fun h => hθ h.1
          have a2 : (u, θ) ∉ GP ∩ goodᶜ := fun h => hθ h.1
          simp only [hF, hF1, hF2]
          rw [Set.indicator_of_notMem a1, Set.indicator_of_notMem a2]
          ring
        simp [h0]
  · rw [hKG]
    exact iF.integral_prod_right
  · intro θ hθ
    obtain ⟨hcc, -⟩ := h2 θ hθ
    obtain ⟨hA1, hA2⟩ := h3 θ hθ
    obtain ⟨hτ2, hτ⟩ := h4 θ hθ
    have hbdd : ∀ u : Fin (2 * n) → ℝ, F (u, θ) ≤ CK * (ζ * (3 + ζ)) ^ 2 + 2 := by
      intro u
      have b1 : F1 (u, θ) ≤ (ζ * (3 + ζ)) ^ 2 := by
        by_cases hp : (u, θ) ∈ GP ∩ good
        · rw [hF1, Set.indicator_of_mem hp]
          obtain ⟨hgD, hgx⟩ := hp.2
          have hR0 : 0 ≤ R (u, θ) := by simp only [hR]; positivity
          have hRle : R (u, θ) ≤ ζ * (3 + ζ) := by
            simp only [hR]
            have h7 : (2 + ζ) * |xOf b cc (u, θ) - 1| ≤ (2 + ζ) * ζ :=
              mul_le_mul_of_nonneg_left hgx (by linarith)
            have h8 : ζ * (3 + ζ) = ζ + (2 + ζ) * ζ := by ring
            rw [h8]
            linarith
          exact pow_le_pow_left₀ hR0 hRle 2
        · rw [hF1, Set.indicator_of_notMem hp]
          positivity
      have b2 : F2 (u, θ) ≤ 1 := by
        rw [hF2]
        exact Set.indicator_le_self' (fun _ _ => zero_le_one) _
      have := mul_le_mul_of_nonneg_left b1 hCK0
      simp only [hF]
      linarith
    have hFnn : ∀ p, 0 ≤ F p := fun p => by
      have : 0 ≤ F2 p := Set.indicator_nonneg (fun _ _ => zero_le_one) p
      simp only [hF]
      nlinarith [hF1nn p]
    have iFθ : Integrable (fun u : Fin (2 * n) → ℝ => F (u, θ)) (uniformSphere (2 * n)) := by
      refine Integrable.of_bound (mF.comp measurable_prodMk_right).aestronglyMeasurable
        (CK * (ζ * (3 + ζ)) ^ 2 + 2) (Filter.Eventually.of_forall fun u => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (hFnn _)]
      exact hbdd u
    unfold hellHid
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun u => hu2_nonneg _ _ _ _)
      iFθ (Filter.Eventually.of_forall fun u => ?_)
    beta_reduce
    have hpG : (u, θ) ∈ GP := hθ
    by_cases hg : (u, θ) ∈ good
    · have a1 : (u, θ) ∈ GP ∩ good := ⟨hpG, hg⟩
      have a2 : (u, θ) ∉ GP ∩ goodᶜ := fun h => h.2 hg
      have e : F (u, θ) = CK * R (u, θ) ^ 2 := by
        simp only [hF, hF1, hF2]
        rw [Set.indicator_of_mem a1, Set.indicator_of_notMem a2]
        ring
      rw [e]
      obtain ⟨hgD, hgx⟩ := hg
      exact pert_pt (k := n) (m := mW n) (by omega) (t := 2 / (mW n : ℝ))
        (γ := 2 / ((2 * n : ℕ) : ℝ)) (κ := kap1 (2 * n)) (by positivity) hγ hκ
        (hid2 θ.1 θ.2 u) (b θ) hcc hAlo hζ0.le hζ1 hA1 hA2 hτ2 hτ
        (D := Dn (2 * n) (mW n) u θ) (x := xOf b cc (u, θ)) rfl rfl hgD hgx
    · have a1 : (u, θ) ∉ GP ∩ good := fun h => hg h.2
      have a2 : (u, θ) ∈ GP ∩ goodᶜ := ⟨hpG, hg⟩
      have e : F (u, θ) = 2 := by
        simp only [hF, hF1, hF2]
        rw [Set.indicator_of_notMem a1, Set.indicator_of_mem a2]
        ring
      rw [e]
      exact hu2_le_two _ _ _ _
  · rw [hKG, ← integral_prod_symm _ iF]
    have e : ∫ p, F p ∂μP = CK * ∫ p, F1 p ∂μP + 2 * ∫ p, F2 p ∂μP := by
      simp only [hF]
      rw [integral_add (iF1.const_mul CK) (iF2.const_mul 2), integral_const_mul,
        integral_const_mul]
    rw [e]
    have b1 := mul_le_mul_of_nonneg_left hF1int hCK0
    have b2 := mul_le_mul_of_nonneg_left hF2int (by norm_num : (0 : ℝ) ≤ 2)
    have e2 : CK * (arW n + (2 + ζ) * lxG n ε ρ₂ qhi) ^ 2 =
        (n : ℝ) / ((Alo - 1) ^ 2 * cRhoG Alo Ahi ζ) *
          (Ahi / (1 - ζ) ^ 2 * (arW n + (2 + ζ) * lxG n ε ρ₂ qhi)) ^ 2 := by
      rw [hCK]; ring
    unfold vPert
    rw [← e2]
    linarith

end BstLean.Part159

open BstLean.Part159 in
#print axioms hell_scalar
open BstLean.Part159 in
#print axioms pert_pt
open BstLean.Part159 in
#print axioms xG_L2
open BstLean.Part159 in
#print axioms pert_moment
