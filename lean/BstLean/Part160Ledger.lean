import BstLean.Part160Defs

/-!
# Part 160 (file `Ledger`): the ledger of Part 156 with a free Agent frame constant

Role: `delegations/statements/p160-spec.md`, item 3. Do not use `sorry`, `native_decide` or
`axiom`.

The ledger of Part 156 has the Agent frame constant `c_frame = 1.743` (`cfL`). Here the frame
constant is any real `cf ≥ 1.743`, and the dimension has `16384·cf ≤ 1.743·n`.

Method: with `l = cfL/cf ∈ (0, 1]` use the exponents `τ_+ = l·τpL`, `τ_- = l·τmL`.

* `Tfun_scale_le`: `Tfun c (l τ) ≤ l·Tfun c τ` (convexity of `exp`); `Tfun_ge`: `τ ≤ Tfun c τ`.
* `Eplus_scale`: `E_+(cf, l τ) ≤ l·E_+(cfL, τ)`.
* `Eminus_scale`: `E_-(cf, l τ) ≤ l·E'`, `E' = −τ/1000 + τ·βM + (wM/cfL)(exp(cfL·T(τ)·αM) − 1)`
  (`E'` has `τ` in the place of `T(τ)` in the middle term; it is a little larger than `E_-`).
* `EprimeL_le`: `E' ≤ −0.0003732` at the ledger constants (`E_- ≤ −0.000389…` in Part 156).
* `Bplus_frameconst`, `Bminus_frameconst`: for `κ ≥ 1` and `16384·κ·cf ≤ cfL·n`:
  `B_+ ≤ (0.00146335214251)^κ`, `B_- ≤ (0.002211)^κ` (`BmF = 0.002211`).
* `classifier_networks_frameconst_kappa`, `classifier_networks_frameconst`,
  `classifier_networks_frameconst_success`: the conditional theorem of Parts 157 and 158 with the
  hypothesis `FRAME_A_hyp D (cf / n)`.
-/

namespace BstLean.Part160

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134
open BstLean.Part156 BstLean.Part157

/-- `Tfun c (l τ) ≤ l·Tfun c τ` for `0 ≤ l ≤ 1` (convexity of `exp`; both signs of `τ`). -/
lemma Tfun_scale_le {c l : ℝ} (hc : 0 < c) (hl0 : 0 ≤ l) (hl1 : l ≤ 1) (τ : ℝ) :
    Tfun c (l * τ) ≤ l * Tfun c τ := by
  have h := convexOn_exp.2 (Set.mem_univ (τ * c)) (Set.mem_univ (0 : ℝ)) hl0
    (by linarith : (0 : ℝ) ≤ 1 - l) (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at h
  unfold Tfun
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right hc]
  have e : l * τ * c = l * (τ * c) := by ring
  rw [e]
  linarith

/-- `τ ≤ Tfun c τ`. -/
lemma Tfun_ge {c : ℝ} (hc : 0 < c) (τ : ℝ) : τ ≤ Tfun c τ := by
  unfold Tfun
  rw [le_div_iff₀ hc]
  have := Real.add_one_le_exp (τ * c)
  linarith

/-- **The upper exponent scales**: for `0 < cf0 ≤ cf` and `l = cf0/cf`:
`E_+(cf, l τ) ≤ l·E_+(cf0, τ)`. -/
lemma Eplus_scale {a h hW cW cf0 cf τ : ℝ} (hhW : 0 ≤ hW) (hcW : 0 < cW) (hcf0 : 0 < cf0)
    (hcf : cf0 ≤ cf) (hτ : 0 < τ) :
    Eplus a h hW cW cf (cf0 / cf * τ) ≤ cf0 / cf * Eplus a h hW cW cf0 τ := by
  have hcfp : 0 < cf := lt_of_lt_of_le hcf0 hcf
  set l := cf0 / cf with hl
  have hl0 : 0 < l := div_pos hcf0 hcfp
  have hl1 : l ≤ 1 := (div_le_one hcfp).2 hcf
  have hT := Tfun_scale_le hcW hl0.le hl1 τ
  have hT0 : 0 < Tfun cW τ := Tfun_pos hcW hτ
  have hT0' : 0 < Tfun cW (l * τ) := Tfun_pos hcW (mul_pos hl0 hτ)
  have hα : 0 ≤ alphaP hW (wP a h) := by
    unfold alphaP; have := div_nonneg hhW (Real.sqrt_nonneg (wP a h)); linarith
  have hβ : 0 ≤ betaP hW (wP a h) := by
    unfold betaP; have := mul_nonneg hhW (Real.sqrt_nonneg (wP a h)); positivity
  have hw : 0 ≤ wP a h := by unfold wP; positivity
  have hcfl : cf * l = cf0 := by rw [hl]; field_simp
  have harg : cf * Tfun cW (l * τ) * alphaP hW (wP a h) ≤
      cf0 * Tfun cW τ * alphaP hW (wP a h) := by
    refine mul_le_mul_of_nonneg_right ?_ hα
    calc cf * Tfun cW (l * τ) ≤ cf * (l * Tfun cW τ) := mul_le_mul_of_nonneg_left hT hcfp.le
      _ = cf0 * Tfun cW τ := by rw [← mul_assoc, hcfl]
  have hexp := exp_le_exp.2 harg
  have hpos : 0 ≤ exp (cf * Tfun cW (l * τ) * alphaP hW (wP a h)) - 1 := by
    have := Real.one_le_exp (mul_nonneg (mul_nonneg hcfp.le hT0'.le) hα)
    linarith
  have hq : wP a h / cf = l * (wP a h / cf0) := by rw [hl]; field_simp
  unfold Eplus cprRhs
  have h1 : Tfun cW (l * τ) * betaP hW (wP a h) ≤ l * (Tfun cW τ * betaP hW (wP a h)) := by
    have := mul_le_mul_of_nonneg_right hT hβ
    linarith
  have h2 : wP a h / cf * (exp (cf * Tfun cW (l * τ) * alphaP hW (wP a h)) - 1) ≤
      l * (wP a h / cf0 * (exp (cf0 * Tfun cW τ * alphaP hW (wP a h)) - 1)) := by
    rw [hq, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hw hcf0.le)) hl0.le
  linarith

/-- The exponent that replaces `E_-` after scaling: `τ` is in the place of `T(τ)` in the middle
term. -/
noncomputable def Eprime (a h hW cW cf τ : ℝ) : ℝ :=
  -τ * (1 / 1000) + (τ * betaM hW (wM a h) +
    wM a h / cf * (exp (cf * Tfun cW τ * alphaM hW (wM a h)) - 1))

/-- **The lower exponent after scaling**: for `0 < cf0 ≤ cf` and `l = cf0/cf`:
`E_-(cf, l τ) ≤ l·E'(cf0, τ)`. -/
lemma Eminus_scale {a h hW cW cf0 cf τ : ℝ} (hhW : 0 ≤ hW) (hcW : 0 < cW) (hcf0 : 0 < cf0)
    (hcf : cf0 ≤ cf) (hα : 0 ≤ alphaM hW (wM a h)) :
    Eminus a h hW cW cf (cf0 / cf * τ) ≤ cf0 / cf * Eprime a h hW cW cf0 τ := by
  have hcfp : 0 < cf := lt_of_lt_of_le hcf0 hcf
  set l := cf0 / cf with hl
  have hl0 : 0 < l := div_pos hcf0 hcfp
  have hl1 : l ≤ 1 := (div_le_one hcfp).2 hcf
  have hT := Tfun_scale_le hcW hl0.le hl1 τ
  have hTge := Tfun_ge hcW (l * τ)
  have hβ : betaM hW (wM a h) ≤ 0 := by
    unfold betaM; have := mul_nonneg hhW (Real.sqrt_nonneg (wM a h)); linarith
  have hw : 0 ≤ wM a h := by unfold wM; positivity
  have hcfl : cf * l = cf0 := by rw [hl]; field_simp
  have harg : cf * Tfun cW (l * τ) * alphaM hW (wM a h) ≤
      cf0 * Tfun cW τ * alphaM hW (wM a h) := by
    refine mul_le_mul_of_nonneg_right ?_ hα
    calc cf * Tfun cW (l * τ) ≤ cf * (l * Tfun cW τ) := mul_le_mul_of_nonneg_left hT hcfp.le
      _ = cf0 * Tfun cW τ := by rw [← mul_assoc, hcfl]
  have hexp := exp_le_exp.2 harg
  have hq : wM a h / cf = l * (wM a h / cf0) := by rw [hl]; field_simp
  unfold Eminus Eprime cprRhs
  have h1 : Tfun cW (l * τ) * betaM hW (wM a h) ≤ l * (τ * betaM hW (wM a h)) := by
    have := mul_le_mul_of_nonpos_right hTge hβ
    linarith
  have h2 : wM a h / cf * (exp (cf * Tfun cW (l * τ) * alphaM hW (wM a h)) - 1) ≤
      l * (wM a h / cf0 * (exp (cf0 * Tfun cW τ * alphaM hW (wM a h)) - 1)) := by
    rw [hq, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hw hcf0.le)) hl0.le
  linarith

/-! ## The numbers at the ledger constants -/

lemma sqrt_wM_L : √(wM aL (hAL + dsL)) = √(1 / 100 / aL) - (hAL + dsL) := by
  unfold wM
  exact Real.sqrt_sq (by have := side1_ledger; unfold hWL at this; linarith)

lemma alphaM_L_nonneg : 0 ≤ alphaM hWL (wM aL (hAL + dsL)) := by
  unfold alphaM
  rw [sqrt_wM_L]
  have h1 := side1_ledger
  have hW0 : (0 : ℝ) < hWL := by unfold hWL; norm_num
  have : hWL / (√(1 / 100 / aL) - (hAL + dsL)) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
  linarith

/-- `E' ≤ −0.0003732` at the ledger constants. -/
theorem EprimeL_le :
    Eprime aL (hAL + dsL) hWL cWL cfL τmL ≤ -(3732 / 10 ^ 7 : ℝ) := by
  have hlo := BstLean.Part156.x0_lo
  have hhi := BstLean.Part156.x0_hi
  have hT := BstLean.Part156.Tm_bounds.2
  have hW0 : (0 : ℝ) < hWL := by unfold hWL; norm_num
  have hcf : (0 : ℝ) < cfL := by unfold cfL; norm_num
  set x0 := √(1 / 100 / aL) with hx0
  set h := hAL + dsL with hh
  have hhv : h = 6593 / 10 ^ 6 + 1 / 10 ^ 20 := hL_eq
  have hs0 : (0 : ℝ) < 66630010657559783 / 10 ^ 18 - h := by rw [hhv]; norm_num
  have hr0 : 0 < x0 - h := by linarith
  have hsw : √(wM aL h) = x0 - h := sqrt_wM_L
  have hw : wM aL h = (x0 - h) ^ 2 := rfl
  have hαlo : 1 - hWL / (66630010657559783 / 10 ^ 18 - h) ≤ 1 - hWL / (x0 - h) := by
    have := div_le_div_of_nonneg_left hW0.le hs0 (by linarith : (66630010657559783 / 10 ^ 18 : ℝ) - h ≤ x0 - h)
    linarith
  have hαlo0 : 0 ≤ 1 - hWL / (66630010657559783 / 10 ^ 18 - h) := by
    have : hWL / (66630010657559783 / 10 ^ 18 - h) ≤ 1 :=
      (div_le_one hs0).2 (by rw [hhv]; unfold hWL; norm_num)
    linarith
  have harg : cfL * Tfun cWL τmL * (1 - hWL / (x0 - h)) ≤
      (-554957327725628994 / 10 ^ 18 : ℝ) := by
    have h1 : Tfun cWL τmL * (1 - hWL / (x0 - h)) ≤
        (-33174219061549001 / 10 ^ 17 : ℝ) * (1 - hWL / (x0 - h)) :=
      mul_le_mul_of_nonneg_right hT (by linarith)
    have h2 : (-33174219061549001 / 10 ^ 17 : ℝ) * (1 - hWL / (x0 - h)) ≤
        (-33174219061549001 / 10 ^ 17 : ℝ) * (1 - hWL / (66630010657559783 / 10 ^ 18 - h)) :=
      mul_le_mul_of_nonpos_left hαlo (by norm_num)
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hcf.le
    have h4 : cfL * ((-33174219061549001 / 10 ^ 17 : ℝ) *
        (1 - hWL / (66630010657559783 / 10 ^ 18 - h))) ≤ (-554957327725628994 / 10 ^ 18 : ℝ) := by
      rw [hhv]; unfold cfL hWL; norm_num
    calc cfL * Tfun cWL τmL * (1 - hWL / (x0 - h))
        = cfL * (Tfun cWL τmL * (1 - hWL / (x0 - h))) := by ring
      _ ≤ _ := h3.trans h4
  have he : exp (cfL * Tfun cWL τmL * (1 - hWL / (x0 - h))) ≤
      (574096758688152709 / 10 ^ 18 : ℝ) := (exp_le_exp.2 harg).trans BstLean.Part156.exp_y4
  unfold Eprime alphaM betaM
  rw [hsw, hw]
  have hτ : τmL = -(4432057116 / 10 ^ 10) := rfl
  have h1 : τmL * -(hWL * (x0 - h)) ≤
      4432057116 / 10 ^ 10 * (hWL * (66630010657559784 / 10 ^ 18 - h)) := by
    rw [hτ]
    have := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (by linarith : x0 - h ≤ 66630010657559784 / 10 ^ 18 - h) hW0.le)
      (by norm_num : (0 : ℝ) ≤ 4432057116 / 10 ^ 10)
    linarith
  have h2 : (x0 - h) ^ 2 / cfL * (exp (cfL * Tfun cWL τmL * (1 - hWL / (x0 - h))) - 1) ≤
      (66630010657559783 / 10 ^ 18 - h) ^ 2 / cfL * ((574096758688152709 / 10 ^ 18 : ℝ) - 1) := by
    have h3 : (66630010657559783 / 10 ^ 18 - h) ^ 2 / cfL ≤ (x0 - h) ^ 2 / cfL :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hs0.le (by linarith) 2) hcf.le
    calc (x0 - h) ^ 2 / cfL * (exp (cfL * Tfun cWL τmL * (1 - hWL / (x0 - h))) - 1)
        ≤ (x0 - h) ^ 2 / cfL * ((574096758688152709 / 10 ^ 18 : ℝ) - 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonpos_right h3 (by norm_num)
  have h3 : -τmL * (1 / 1000) + (4432057116 / 10 ^ 10 * (hWL * (66630010657559784 / 10 ^ 18 - h)) +
      (66630010657559783 / 10 ^ 18 - h) ^ 2 / cfL * ((574096758688152709 / 10 ^ 18 : ℝ) - 1)) ≤
      -(3732 / 10 ^ 7 : ℝ) := by
    rw [hhv, hτ]; unfold hWL cfL; norm_num
  linarith

/-- `BmF = 0.002211`: the bound of the lower endpoint tail with a free frame constant. -/
noncomputable def BmF : ℝ := 2211 / 10 ^ 6

lemma exp_xMF : exp (16384 * (-(3732 / 10 ^ 7 : ℝ)) / 8) ≤ (46566 / 10 ^ 5 : ℝ) := by
  refine exp_le_taylor (b := 1) 24 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

lemma exp_EprimeL : exp (16384 * -(3732 / 10 ^ 7 : ℝ)) ≤ BmF := by
  refine (exp_n_le le_rfl exp_xMF).trans ?_
  unfold BmF; norm_num

/-- `τ_+` for the frame constant `cf`. -/
noncomputable def τpF (cf : ℝ) : ℝ := cfL / cf * τpL
/-- `τ_-` for the frame constant `cf`. -/
noncomputable def τmF (cf : ℝ) : ℝ := cfL / cf * τmL

lemma EplusF_le {cf : ℝ} (hcf : cfL ≤ cf) :
    Eplus aL (hAL + dsL) hWL cWL cf (τpF cf) ≤
      cfL / cf * Eplus aL (hAL + dsL) hWL cWL cfL τpL :=
  Eplus_scale (by unfold hWL; norm_num) (by unfold cWL; norm_num) (by unfold cfL; norm_num) hcf
    (by unfold τpL; norm_num)

lemma EminusF_le {cf : ℝ} (hcf : cfL ≤ cf) :
    Eminus aL (hAL + dsL) hWL cWL cf (τmF cf) ≤ cfL / cf * -(3732 / 10 ^ 7 : ℝ) := by
  have hcf0 : (0 : ℝ) < cfL := by unfold cfL; norm_num
  have h := Eminus_scale (a := aL) (h := hAL + dsL) (cW := cWL) (τ := τmL)
    (by unfold hWL; norm_num : (0 : ℝ) ≤ hWL) (by unfold cWL; norm_num) hcf0 hcf alphaM_L_nonneg
  exact h.trans (mul_le_mul_of_nonneg_left EprimeL_le
    (div_nonneg hcf0.le (hcf0.le.trans hcf)))

lemma EplusF_nonpos {cf : ℝ} (hcf : cfL ≤ cf) :
    Eplus aL (hAL + dsL) hWL cWL cf (τpF cf) ≤ 0 := by
  have hcf0 : (0 : ℝ) < cfL := by unfold cfL; norm_num
  exact (EplusF_le hcf).trans (mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg hcf0.le (hcf0.le.trans hcf)) Eplus_ledger_neg.le)

lemma EminusF_nonpos {cf : ℝ} (hcf : cfL ≤ cf) :
    Eminus aL (hAL + dsL) hWL cWL cf (τmF cf) ≤ 0 := by
  have hcf0 : (0 : ℝ) < cfL := by unfold cfL; norm_num
  exact (EminusF_le hcf).trans (mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg hcf0.le (hcf0.le.trans hcf)) (by norm_num))

/-- `exp (n·E) ≤ B^κ` if `E ≤ l·E₀`, `E₀ ≤ 0`, `n·l ≥ 16384·κ` and `exp (16384·E₀) ≤ B`. -/
lemma tail_kappa {n l κ E E₀ B : ℝ} (hκ : 0 ≤ κ) (hE : E ≤ l * E₀) (hE₀ : E₀ ≤ 0) (hn : 0 ≤ n)
    (hnl : 16384 * κ ≤ n * l) (hB : exp (16384 * E₀) ≤ B) : exp (n * E) ≤ B ^ κ := by
  calc exp (n * E) ≤ exp (n * (l * E₀)) := exp_le_exp.2 (mul_le_mul_of_nonneg_left hE hn)
    _ ≤ exp (16384 * E₀ * κ) := exp_le_exp.2 (by nlinarith)
    _ = exp (16384 * E₀) ^ κ := Real.exp_mul _ _
    _ ≤ B ^ κ := Real.rpow_le_rpow (exp_pos _).le hB hκ

lemma nl_ge {n cf κ : ℝ} (hcf : cfL ≤ cf) (hncf : 16384 * κ * cf ≤ cfL * n) :
    16384 * κ ≤ n * (cfL / cf) := by
  have hcf0 : (0 : ℝ) < cfL := by unfold cfL; norm_num
  have hcfp : 0 < cf := lt_of_lt_of_le hcf0 hcf
  rw [← mul_div_assoc, le_div_iff₀ hcfp]
  linarith

/-- **The upper tail with a free frame constant**: `B_+ ≤ (0.00146335214251)^κ`. -/
theorem Bplus_frameconst {n cf κ : ℝ} (hn : 0 ≤ n) (hcf : cfL ≤ cf) (hκ : 0 ≤ κ)
    (hncf : 16384 * κ * cf ≤ cfL * n) :
    Bplus n aL (hAL + dsL) hWL cWL cf (τpF cf) ≤ (146335214251 / 10 ^ 14 : ℝ) ^ κ := by
  unfold Bplus
  exact tail_kappa hκ (EplusF_le hcf) Eplus_ledger_neg.le hn (nl_ge hcf hncf)
    (by have := Bplus_ledger; unfold Bplus at this; exact this)

/-- **The lower tail with a free frame constant**: `B_- ≤ (0.002211)^κ`. -/
theorem Bminus_frameconst {n cf κ : ℝ} (hn : 0 ≤ n) (hcf : cfL ≤ cf) (hκ : 0 ≤ κ)
    (hncf : 16384 * κ * cf ≤ cfL * n) :
    Bminus n aL (hAL + dsL) hWL cWL cf (τmF cf) ≤ BmF ^ κ := by
  unfold Bminus
  exact tail_kappa hκ (EminusF_le hcf) (by norm_num) hn (nl_ge hcf hncf) exp_EprimeL

variable {n : ℕ}

/-- **The conditional classifier theorem with a free Agent frame constant and a free factor
`κ ≥ 1`.** For `cf ≥ 1.743` and `16384·κ·cf ≤ 1.743·n`: IF the events have the charges
`δ_hid`, `v_W`, `δ_extra` (with the Hellinger radius), and on `H ∩ {H̄_W ≤ h_W} ∩ E₁` the World
frame bound `1.377/n`, the Agent frame bound `cf/n` and the Agent replacement hold, THEN the
failure probability is at most
`δ_hid + v_W/h_W² + δ_extra + (0.00146335214251)^κ + (0.002211)^κ + 2 e^{−100}`. -/
theorem classifier_networks_frameconst_kappa (hn : 16384 ≤ n) {cf κ : ℝ} (hcf : cfL ≤ cf)
    (hκ : 1 ≤ κ) (hncf : 16384 * κ * cf ≤ cfL * n) (D : Design n) (t : ℝ)
    {H E₁ : Set (Ret n)} {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (cf / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real (failNet D t aL (10 ^ 12)) ≤
      δhid + vW / hWL ^ 2 + δextra + (146335214251 / 10 ^ 14 : ℝ) ^ κ + BmF ^ κ +
        2 * exp (-100) := by
  have hn1 : 1 ≤ n := by omega
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hcf0 : (0 : ℝ) < cfL := by unfold cfL; norm_num
  have hcfp : 0 < cf := lt_of_lt_of_le hcf0 hcf
  have hLW : 0 < cWL / (n : ℝ) := div_pos (by unfold cWL; norm_num) hnpos
  have hLA : 0 < cf / (n : ℝ) := div_pos hcfp hnpos
  have hG := BstLean.Part158.gaussFrameMGF
  have hGPW := gpw_of_frame hn1 hG D.toCentres t hLW hFW
  have hGPA := gpa_of_frame hn1 hG D t hLA hFA
  have hRW := replw_of_test hn1 D t (replw_test_of_Hbar hn1 D hWL H E₁)
  have hRA' := repla_of_mix D t hRA
  obtain ⟨hH, hE₁, hHm, hhid, hHint, hvW, hextra⟩ := hEv
  have mr := measurable_retVal D.toCentres
  have hmap := noise_retVal D.toCentres
  have mpair : Measurable (fun x : Ret n × (ResW n × ResA n) => (retVal D.toCentres x.1, x.2)) :=
    (mr.comp measurable_fst).prodMk measurable_snd
  have hpm : Measurable (fun x : Ret n × (ResW n × ResA n) =>
      pRes D.toCentres t (retVal D.toCentres x.1) x.2) := by
    have h := (measurable_pRes D.toCentres t).comp mpair
    exact h
  have hp0 : ∀ x : Ret n × (ResW n × ResA n),
      0 ≤ pRes D.toCentres t (retVal D.toCentres x.1) x.2 := fun x => pRes_nonneg _ _ _ _
  have hp1 : ∀ x : Ret n × (ResW n × ResA n),
      pRes D.toCentres t (retVal D.toCentres x.1) x.2 ≤ 1 := fun x => pRes_le_one hn1 _ _ _ _
  have hPm : ∀ c : Ret n, Measurable (PStand D t (retVal D.toCentres c)) :=
    fun c => measurable_PStand D t _
  have hP0 : ∀ (c : Ret n) (x : ResA n), 0 ≤ PStand D t (retVal D.toCentres c) x :=
    fun c x => PStand_nonneg _ _ _ _
  have hP1 : ∀ (c : Ret n) (x : ResA n), PStand D t (retVal D.toCentres c) x ≤ 1 :=
    fun c x => PStand_le_one _ _ _ _
  have hXm : ∀ i : Fin (10 ^ 12), Measurable (fun x : Ret n × (Fin (10 ^ 12) → DrawSp n) =>
      hits D t (10 ^ 12) i (retVal D.toCentres x.1, x.2)) := by
    intro i
    have h1 : Measurable (fun x : Ret n × (Fin (10 ^ 12) → DrawSp n) =>
        (retVal D.toCentres x.1, x.2)) := (mr.comp measurable_fst).prodMk measurable_snd
    have h2 := (measurable_hits D t (10 ^ 12) i).comp h1
    exact h2
  have hX01 : ∀ (i : Fin (10 ^ 12)) (x : Ret n × (Fin (10 ^ 12) → DrawSp n)),
      hits D t (10 ^ 12) i (retVal D.toCentres x.1, x.2) = 0 ∨
        hits D t (10 ^ 12) i (retVal D.toCentres x.1, x.2) = 1 :=
    fun i x => hits_01 D t (10 ^ 12) i _
  have hH' : MeasurableSet (retVal D.toCentres ⁻¹' H) := mr hH
  have hE₁' : MeasurableSet (retVal D.toCentres ⁻¹' E₁) := mr hE₁
  have hHm' : Measurable (fun c => HbarW D (retVal D.toCentres c)) := hHm.comp mr
  have hhid' : (noiseC n).real (retVal D.toCentres ⁻¹' H)ᶜ ≤ δhid := by
    have e : (retVal D.toCentres ⁻¹' H)ᶜ = retVal D.toCentres ⁻¹' Hᶜ := rfl
    rw [e, ← map_measureReal_apply mr hH.compl, hmap]
    exact hhid
  have hHint' : IntegrableOn (fun c => HbarW D (retVal D.toCentres c) ^ 2)
      (retVal D.toCentres ⁻¹' H) (noiseC n) := by
    have h1 : Integrable (fun c => HbarW D c ^ 2) ((retDist D.toCentres).restrict H) := hHint
    rw [← hmap, Measure.restrict_map mr hH] at h1
    exact (integrable_map_measure ((hHm.pow_const 2).aestronglyMeasurable) mr.aemeasurable).1 h1
  have hvW' : ∫ c in retVal D.toCentres ⁻¹' H, HbarW D (retVal D.toCentres c) ^ 2 ∂noiseC n ≤
      vW := by
    have h1 := setIntegral_map (μ := noiseC n) hH
      (f := fun c => HbarW D c ^ 2) (g := retVal D.toCentres)
      ((hHm.pow_const 2).aestronglyMeasurable) mr.aemeasurable
    rw [hmap] at h1
    rw [← h1]
    exact hvW
  have hextra' : (noiseC n).real (retVal D.toCentres ⁻¹' H ∩ (retVal D.toCentres ⁻¹' E₁)ᶜ) ≤
      δextra := by
    have e : retVal D.toCentres ⁻¹' H ∩ (retVal D.toCentres ⁻¹' E₁)ᶜ =
        retVal D.toCentres ⁻¹' (H ∩ E₁ᶜ) := rfl
    rw [e, ← map_measureReal_apply mr (hH.inter hE₁.compl), hmap]
    exact hextra
  have key := master_sampling (noiseC n) (resW n) (resA n) (sampMeas (10 ^ 12) n)
    (p := fun x : Ret n × (ResW n × ResA n) => pRes D.toCentres t (retVal D.toCentres x.1) x.2)
    hpm hp0 hp1
    (P := fun c => PStand D t (retVal D.toCentres c)) hPm hP0 hP1
    (X := fun i (x : Ret n × (Fin (10 ^ 12) → DrawSp n)) =>
      hits D t (10 ^ 12) i (retVal D.toCentres x.1, x.2)) hXm hX01
    (qt := fun c => qTilde D t (retVal D.toCentres c))
    (H := retVal D.toCentres ⁻¹' H) (E₁ := retVal D.toCentres ⁻¹' E₁) hH' hE₁'
    (Hbar := fun c => HbarW D (retVal D.toCentres c)) hHm'
    (n := (n : ℝ)) (cW := cWL) (cf := cf) (hW := hWL) (hA := hAL) (ds := dsL) (a := aL)
    (τp := τpF cf) (τm := τmF cf) (δhid := δhid) (δextra := δextra) (vW := vW)
    hnpos (by unfold cWL; norm_num) hcfp (by unfold hWL; norm_num)
    (by unfold hAL; norm_num) (by unfold dsL; norm_num) (by unfold aL; norm_num)
    (by unfold τpF; exact mul_pos (div_pos hcf0 hcfp) (by unfold τpL; norm_num))
    (by unfold τmF; exact mul_neg_of_pos_of_neg (div_pos hcf0 hcfp) (by unfold τmL; norm_num))
    side1_ledger side2_ledger
    (EplusF_nonpos hcf) (EminusF_nonpos hcf) hhid' hHint' hvW' hextra'
    (fun c hc ωA s => hGPW (retVal D.toCentres c) hc ωA s)
    (fun c hc u => hGPA (retVal D.toCentres c) hc u)
    (fun c hc ωA => hRW (retVal D.toCentres c) hc ωA)
    (fun c hc => hRA' (retVal D.toCentres c) hc)
    (fun c _ => hits_indep D t (10 ^ 12) (retVal D.toCentres c))
    (fun c _ i => hits_mean D t (10 ^ 12) (retVal D.toCentres c) i)
  have hk : 2 * exp (-((10 ^ 12 : ℕ) : ℝ) * dsL ^ 2) = 2 * exp (-100) := by
    unfold dsL; norm_num
  rw [hk] at key
  have hκ0 : (0 : ℝ) ≤ κ := by linarith
  have h3 := Bplus_frameconst hnpos.le hcf hκ0 hncf
  have h4 := Bminus_frameconst hnpos.le hcf hκ0 hncf
  rw [failNet_eq]
  linarith

/-- **The conditional classifier theorem with a free Agent frame constant.** For `cf ≥ 1.743`
and `16384·cf ≤ 1.743·n`: the failure probability is at most
`δ_hid + v_W/h_W² + δ_extra + 0.00146335214251 + 0.002211 + 2 e^{−100}`. -/
theorem classifier_networks_frameconst (hn : 16384 ≤ n) {cf : ℝ} (hcf : cfL ≤ cf)
    (hncf : 16384 * cf ≤ cfL * n) (D : Design n) (t : ℝ) {H E₁ : Set (Ret n)}
    {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (cf / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real (failNet D t aL (10 ^ 12)) ≤
      δhid + vW / hWL ^ 2 + δextra + 146335214251 / 10 ^ 14 + BmF + 2 * exp (-100) := by
  have h := classifier_networks_frameconst_kappa hn hcf (le_refl 1) (by linarith) D t hEv hFW
    hFA hRA
  simpa using h

/-- **Success with a free Agent frame constant.** If `cf ≥ 1.743`, `16384·cf ≤ 1.743·n` and
`δ_hid + v_W/h_W² + δ_extra ≤ 0.0063`, the program succeeds with probability at least
`99/100`. -/
theorem classifier_networks_frameconst_success (hn : 16384 ≤ n) {cf : ℝ} (hcf : cfL ≤ cf)
    (hncf : 16384 * cf ≤ cfL * n) (D : Design n) (t : ℝ) {H E₁ : Set (Ret n)}
    {δhid vW δextra : ℝ}
    (hEv : EVENTS_hyp D.toCentres H E₁ (HbarW D) δhid vW δextra)
    (hsum : δhid + vW / hWL ^ 2 + δextra ≤ 63 / 10 ^ 4)
    (hFW : FRAME_W_hyp D.toCentres (cWL / n) (goodSet H E₁ (HbarW D) hWL))
    (hFA : FRAME_A_hyp D (cf / n) (goodSet H E₁ (HbarW D) hWL))
    (hRA : REPLA_mix_hyp D t hAL (goodSet H E₁ (HbarW D) hWL)) :
    99 / 100 ≤ ((mlpTriple 2 n).prod (sampMeas (10 ^ 12) n)).real
      {x | successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} := by
  have h := classifier_networks_frameconst hn hcf hncf D t hEv hFW hFA hRA
  have hT : IsProbabilityMeasure (mlpTriple 2 n) := by unfold mlpTriple; infer_instance
  have hc : {x : Net3 n × (Fin (10 ^ 12) → DrawSp n) |
      successNet x.1 t (progOut D t aL (10 ^ 12) x.1 x.2)} = (failNet D t aL (10 ^ 12))ᶜ := by
    ext x
    simp [failNet]
  have h2 := two_exp_neg_100
  rw [hc, measureReal_compl (measurableSet_failNet D t aL _), probReal_univ]
  unfold BmF at h
  norm_num at h ⊢
  linarith

end BstLean.Part160

open BstLean.Part160 in
#print axioms EprimeL_le
open BstLean.Part160 in
#print axioms Bplus_frameconst
open BstLean.Part160 in
#print axioms Bminus_frameconst
open BstLean.Part160 in
#print axioms classifier_networks_frameconst_kappa
open BstLean.Part160 in
#print axioms classifier_networks_frameconst
open BstLean.Part160 in
#print axioms classifier_networks_frameconst_success
