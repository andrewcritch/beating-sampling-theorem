import BstLean.Part156Master

/-!
# Part 156 (item 5, numeric part): the ledger at `n = 16 384`

The constants are those of the "source-corrected certificate" at `n = 16 384`:
`a = 2.2524763228`, `h_W = 0.0024160420`, `τ_+ = 0.1668810709`, `τ_- = -0.4432057116`,
`c_W = 1.377`, `c_frame = 1.743`, `h_A = 0.006583 + 10⁻²⁰`, `d_s = 0.00001`, `k = 10¹²`,
`v_W = 0.000741853 · (0.004)²`, hidden charge `0.001900001`, extra events `0.001104285235085`.

This file proves, with verified rational bounds of `exp` and `√`:

* the side conditions `√(0.01/a) > h + h_W` and `√(0.01/a) ≥ 2h`, with `h = h_A + d_s`;
* `E_+ < 0` and `E_- < 0`;
* `B_+ ≤ 0.00146335214251` and `B_- ≤ 0.001694618447832`;
* `ledger_total`: `0.001900001 + v_W/h_W² + B_+ + B_- + 2 exp (-100) + 0.001104285235085
  < 0.008195686 < 1/100`.

These are statements about real numbers. They are NOT statements about the networks.
The rational constants in the proofs were computed outside Lean; Lean checks every inequality.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part156

open Real

/-- An upper bound of `exp x` from the Taylor polynomial of degree `N - 1`, for `|x| ≤ b ≤ 1`. -/
lemma exp_le_taylor {x b u : ℝ} (N : ℕ) (hN : 0 < N) (h1 : -b ≤ x) (h2 : x ≤ b) (hb : b ≤ 1)
    (hu : (∑ m ∈ Finset.range N, x ^ m / (m.factorial : ℝ)) +
      b ^ N * (((N : ℝ) + 1) / ((N.factorial : ℝ) * N)) ≤ u) : exp x ≤ u := by
  have hx : |x| ≤ b := abs_le.2 ⟨h1, h2⟩
  have h := Real.exp_bound (hx.trans hb) hN
  have h3 : |x| ^ N ≤ b ^ N := pow_le_pow_left₀ (abs_nonneg _) hx N
  have h4 : (0 : ℝ) ≤ ((N : ℝ) + 1) / ((N.factorial : ℝ) * N) := by positivity
  have h5 := mul_le_mul_of_nonneg_right h3 h4
  have h6 := (abs_le.1 h).2
  push_cast at h6
  linarith

/-- A lower bound of `exp x` from the Taylor polynomial of degree `N - 1`, for `|x| ≤ b ≤ 1`. -/
lemma le_exp_taylor {x b u : ℝ} (N : ℕ) (hN : 0 < N) (h1 : -b ≤ x) (h2 : x ≤ b) (hb : b ≤ 1)
    (hu : u ≤ (∑ m ∈ Finset.range N, x ^ m / (m.factorial : ℝ)) -
      b ^ N * (((N : ℝ) + 1) / ((N.factorial : ℝ) * N))) : u ≤ exp x := by
  have hx : |x| ≤ b := abs_le.2 ⟨h1, h2⟩
  have h := Real.exp_bound (hx.trans hb) hN
  have h3 : |x| ^ N ≤ b ^ N := pow_le_pow_left₀ (abs_nonneg _) hx N
  have h4 : (0 : ℝ) ≤ ((N : ℝ) + 1) / ((N.factorial : ℝ) * N) := by positivity
  have h5 := mul_le_mul_of_nonneg_right h3 h4
  have h6 := (abs_le.1 h).1
  push_cast at h6
  linarith

/-- An upper bound of `E_+` from bounds of `√(0.01/a)`, of `T_+` and of one exponential. -/
lemma Eplus_le_of_bounds {a h hW cW cf τ x0lo x0hi Thi y ehi : ℝ}
    (hh : 0 ≤ h) (hhW : 0 ≤ hW) (hcW : 0 < cW) (hcf : 0 < cf) (hτ : 0 < τ)
    (hx0lo : 0 < x0lo) (hlo : x0lo ≤ √(1 / 100 / a)) (hhi : √(1 / 100 / a) ≤ x0hi)
    (hT : Tfun cW τ ≤ Thi) (hy : cf * Thi * (1 + hW / (x0lo + h)) ≤ y) (he : exp y ≤ ehi) :
    Eplus a h hW cW cf τ ≤
      -τ * (1 / 100) + (Thi * (hW * (x0hi + h) + hW ^ 2) + (x0hi + h) ^ 2 / cf * (ehi - 1)) := by
  set x0 := √(1 / 100 / a) with hx0
  have hT0 : 0 < Tfun cW τ := Tfun_pos hcW hτ
  have hr0 : 0 < x0 + h := by linarith
  have hsw : √(wP a h) = x0 + h := by
    unfold wP
    exact Real.sqrt_sq hr0.le
  have hw : wP a h = (x0 + h) ^ 2 := rfl
  have hα : hW / (x0 + h) ≤ hW / (x0lo + h) :=
    div_le_div_of_nonneg_left hhW (by linarith) (by linarith)
  have hα0 : 0 ≤ hW / (x0 + h) := div_nonneg hhW hr0.le
  have harg : cf * Tfun cW τ * (1 + hW / (x0 + h)) ≤ y := by
    refine le_trans ?_ hy
    have h1 : cf * Tfun cW τ ≤ cf * Thi := mul_le_mul_of_nonneg_left hT hcf.le
    exact mul_le_mul h1 (by linarith) (by linarith) (by nlinarith)
  have he2 : exp (cf * Tfun cW τ * (1 + hW / (x0 + h))) ≤ ehi := (exp_le_exp.2 harg).trans he
  have hbr : 0 ≤ exp (cf * Tfun cW τ * (1 + hW / (x0 + h))) - 1 := by
    have : 0 ≤ cf * Tfun cW τ * (1 + hW / (x0 + h)) :=
      mul_nonneg (mul_nonneg hcf.le hT0.le) (by linarith)
    have := Real.one_le_exp this
    linarith
  unfold Eplus cprRhs alphaP betaP
  rw [hsw, hw]
  have h1 : Tfun cW τ * (hW * (x0 + h) + hW ^ 2) ≤ Thi * (hW * (x0hi + h) + hW ^ 2) := by
    refine mul_le_mul hT ?_ (by positivity) (hT0.le.trans hT)
    have := mul_le_mul_of_nonneg_left (add_le_add_right hhi h) hhW
    linarith
  have h2 : (x0 + h) ^ 2 / cf * (exp (cf * Tfun cW τ * (1 + hW / (x0 + h))) - 1) ≤
      (x0hi + h) ^ 2 / cf * (ehi - 1) := by
    refine mul_le_mul ?_ (by linarith) hbr (by positivity)
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hr0.le (by linarith) 2) hcf.le
  linarith

/-- An upper bound of `E_-` from bounds of `√(0.01/a)`, of `T_-` and of one exponential. -/
lemma Eminus_le_of_bounds {a h hW cW cf τ x0lo x0hi Tlo Thi y ehi : ℝ}
    (hhW : 0 ≤ hW) (hcW : 0 < cW) (hcf : 0 < cf) (hτ : τ < 0)
    (hx0lo : h + hW < x0lo) (hlo : x0lo ≤ √(1 / 100 / a)) (hhi : √(1 / 100 / a) ≤ x0hi)
    (hTlo : Tlo ≤ Tfun cW τ) (hThi : Tfun cW τ ≤ Thi) (hThi0 : Thi ≤ 0)
    (hy : cf * Thi * (1 - hW / (x0lo - h)) ≤ y) (he : exp y ≤ ehi) (he1 : ehi ≤ 1) :
    Eminus a h hW cW cf τ ≤
      -τ * (1 / 1000) + (-Tlo * (hW * (x0hi - h)) + (x0lo - h) ^ 2 / cf * (ehi - 1)) := by
  set x0 := √(1 / 100 / a) with hx0
  have hT0 : Tfun cW τ < 0 := Tfun_neg hcW hτ
  have hs0 : 0 < x0lo - h := by linarith
  have hr0 : 0 < x0 - h := by linarith
  have hsw : √(wM a h) = x0 - h := by
    unfold wM
    exact Real.sqrt_sq hr0.le
  have hw : wM a h = (x0 - h) ^ 2 := rfl
  have hα : hW / (x0 - h) ≤ hW / (x0lo - h) :=
    div_le_div_of_nonneg_left hhW hs0 (by linarith)
  have hαlo : 0 ≤ 1 - hW / (x0lo - h) := by
    have : hW / (x0lo - h) < 1 := (div_lt_one hs0).2 (by linarith)
    linarith
  have harg : cf * Tfun cW τ * (1 - hW / (x0 - h)) ≤ y := by
    refine le_trans ?_ hy
    have h1 : Tfun cW τ * (1 - hW / (x0 - h)) ≤ Thi * (1 - hW / (x0 - h)) :=
      mul_le_mul_of_nonneg_right hThi (by linarith)
    have h2 : Thi * (1 - hW / (x0 - h)) ≤ Thi * (1 - hW / (x0lo - h)) :=
      mul_le_mul_of_nonpos_left (by linarith) hThi0
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hcf.le
    calc cf * Tfun cW τ * (1 - hW / (x0 - h)) = cf * (Tfun cW τ * (1 - hW / (x0 - h))) := by ring
      _ ≤ cf * (Thi * (1 - hW / (x0lo - h))) := h3
      _ = _ := by ring
  have he2 : exp (cf * Tfun cW τ * (1 - hW / (x0 - h))) ≤ ehi := (exp_le_exp.2 harg).trans he
  unfold Eminus cprRhs alphaM betaM
  rw [hsw, hw]
  have h1 : Tfun cW τ * -(hW * (x0 - h)) ≤ -Tlo * (hW * (x0hi - h)) := by
    have h2 : -Tfun cW τ * (hW * (x0 - h)) ≤ -Tlo * (hW * (x0hi - h)) := by
      refine mul_le_mul (by linarith) ?_ (by positivity) (by linarith)
      exact mul_le_mul_of_nonneg_left (by linarith) hhW
    linarith
  have h2 : (x0 - h) ^ 2 / cf * (exp (cf * Tfun cW τ * (1 - hW / (x0 - h))) - 1) ≤
      (x0lo - h) ^ 2 / cf * (ehi - 1) := by
    have h3 : (x0lo - h) ^ 2 / cf ≤ (x0 - h) ^ 2 / cf :=
      div_le_div_of_nonneg_right (pow_le_pow_left₀ hs0.le (by linarith) 2) hcf.le
    calc (x0 - h) ^ 2 / cf * (exp (cf * Tfun cW τ * (1 - hW / (x0 - h))) - 1)
        ≤ (x0 - h) ^ 2 / cf * (ehi - 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ (x0lo - h) ^ 2 / cf * (ehi - 1) :=
          mul_le_mul_of_nonpos_right h3 (by linarith)
  linarith

/-- `exp (16384 E) ≤ u⁸` if `E ≤ Ehi` and `exp (16384 Ehi / 8) ≤ u`. -/
lemma exp_n_le {E Ehi u : ℝ} (hE : E ≤ Ehi) (hu : exp (16384 * Ehi / 8) ≤ u) :
    exp (16384 * E) ≤ u ^ 8 := by
  calc exp (16384 * E) ≤ exp (16384 * Ehi) := exp_le_exp.2 (by linarith)
    _ = exp (16384 * Ehi / 8) ^ 8 := by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    _ ≤ u ^ 8 := pow_le_pow_left₀ (exp_pos _).le hu 8

/-! ## The constants of the ledger -/

/-- `a = 2.2524763228`. -/
noncomputable def aL : ℝ := 22524763228 / 10 ^ 10
/-- `h_W = 0.0024160420`. -/
noncomputable def hWL : ℝ := 24160420 / 10 ^ 10
/-- `τ_+ = 0.1668810709`. -/
noncomputable def τpL : ℝ := 1668810709 / 10 ^ 10
/-- `τ_- = -0.4432057116`. -/
noncomputable def τmL : ℝ := -(4432057116 / 10 ^ 10)
/-- `c_W = 1.377`. -/
noncomputable def cWL : ℝ := 1377 / 1000
/-- `c_frame = 1.743`. -/
noncomputable def cfL : ℝ := 1743 / 1000
/-- `h_A = 0.006583 + 10⁻²⁰`. -/
noncomputable def hAL : ℝ := 6583 / 10 ^ 6 + 1 / 10 ^ 20
/-- `d_s = 0.00001`. -/
noncomputable def dsL : ℝ := 1 / 10 ^ 5
/-- `v_W = 0.000741853 · (0.004)²`. -/
noncomputable def vWL : ℝ := 741853 / 10 ^ 9 * (4 / 1000) ^ 2
/-- The hidden World charge `0.001900001`. -/
noncomputable def δhidL : ℝ := 1900001 / 10 ^ 9
/-- The charge of the other retained-data events `0.001104285235085`. -/
noncomputable def δextraL : ℝ := 1104285235085 / 10 ^ 15

lemma hL_eq : hAL + dsL = 6593 / 10 ^ 6 + 1 / 10 ^ 20 := by
  unfold hAL dsL; norm_num

lemma x0_lo : (66630010657559783 / 10 ^ 18 : ℝ) ≤ √(1 / 100 / aL) := by
  refine Real.le_sqrt_of_sq_le ?_
  unfold aL; norm_num

lemma x0_hi : √(1 / 100 / aL) ≤ (66630010657559784 / 10 ^ 18 : ℝ) := by
  rw [Real.sqrt_le_iff]
  refine ⟨by norm_num, ?_⟩
  unfold aL; norm_num

/-- The first side condition: `(h_A + d_s) + h_W < √(0.01/a)`. -/
theorem side1_ledger : (hAL + dsL) + hWL < √(1 / 100 / aL) := by
  refine lt_of_lt_of_le ?_ x0_lo
  rw [hL_eq]; unfold hWL; norm_num

/-- The second side condition: `2 (h_A + d_s) ≤ √(0.01/a)`. -/
theorem side2_ledger : 2 * (hAL + dsL) ≤ √(1 / 100 / aL) := by
  refine le_trans ?_ x0_lo
  rw [hL_eq]; norm_num

lemma Tp_hi : Tfun cWL τpL ≤ (187612431819833476 / 10 ^ 18 : ℝ) := by
  have he : exp (τpL * cWL) ≤ (1258342318615910696 / 10 ^ 18 : ℝ) := by
    unfold τpL cWL
    refine exp_le_taylor (b := 1 / 4) 16 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  unfold Tfun
  rw [div_le_iff₀ (by unfold cWL; norm_num)]
  have : (1258342318615910696 / 10 ^ 18 : ℝ) - 1 ≤ (187612431819833476 / 10 ^ 18 : ℝ) * cWL := by unfold cWL; norm_num
  linarith

lemma exp_y2 : exp (337798330858948858 / 10 ^ 18 : ℝ) ≤ (1401857763445286477 / 10 ^ 18 : ℝ) := by
  refine exp_le_taylor (b := 1 / 2) 20 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- `E_+ ≤ -0.000398378...` at the ledger constants. -/
theorem Eplus_ledger : Eplus aL (hAL + dsL) hWL cWL cfL τpL ≤ (-398378020446457486 / 10 ^ 21 : ℝ) := by
  have h := Eplus_le_of_bounds (a := aL) (h := hAL + dsL) (hW := hWL) (cW := cWL) (cf := cfL)
    (τ := τpL) (x0lo := (66630010657559783 / 10 ^ 18 : ℝ)) (x0hi := (66630010657559784 / 10 ^ 18 : ℝ)) (Thi := (187612431819833476 / 10 ^ 18 : ℝ)) (y := (337798330858948858 / 10 ^ 18 : ℝ)) (ehi := (1401857763445286477 / 10 ^ 18 : ℝ))
    (by rw [hL_eq]; norm_num) (by unfold hWL; norm_num) (by unfold cWL; norm_num)
    (by unfold cfL; norm_num) (by unfold τpL; norm_num) (by norm_num) x0_lo x0_hi Tp_hi
    (by rw [hL_eq]; unfold cfL hWL; norm_num) exp_y2
  refine h.trans ?_
  rw [hL_eq]; unfold τpL hWL cfL; norm_num

lemma exp_xP : exp (16384 * (-398378020446457486 / 10 ^ 21 : ℝ) / 8) ≤ (44225077839071266335 / 10 ^ 20 : ℝ) := by
  refine exp_le_taylor (b := 1) 24 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- `B_+ ≤ 0.00146335214251` at the ledger constants. -/
theorem Bplus_ledger : Bplus 16384 aL (hAL + dsL) hWL cWL cfL τpL ≤ (146335214251 / 10 ^ 14 : ℝ) := by
  unfold Bplus
  refine (exp_n_le Eplus_ledger exp_xP).trans ?_
  norm_num

lemma Tm_bounds : (-331742190615490011 / 10 ^ 18 : ℝ) ≤ Tfun cWL τmL ∧ Tfun cWL τmL ≤ (-33174219061549001 / 10 ^ 17 : ℝ) := by
  have he : (543191003522470255 / 10 ^ 18 : ℝ) ≤ exp (τmL * cWL) := by
    unfold τmL cWL
    refine le_exp_taylor (b := 5 / 8) 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have he' : exp (τmL * cWL) ≤ (543191003522470256 / 10 ^ 18 : ℝ) := by
    unfold τmL cWL
    refine exp_le_taylor (b := 5 / 8) 22 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) ?_
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hc : (0 : ℝ) < cWL := by unfold cWL; norm_num
  unfold Tfun
  constructor
  · rw [le_div_iff₀ hc]
    have : (-331742190615490011 / 10 ^ 18 : ℝ) * cWL ≤ (543191003522470255 / 10 ^ 18 : ℝ) - 1 := by unfold cWL; norm_num
    linarith
  · rw [div_le_iff₀ hc]
    have : (543191003522470256 / 10 ^ 18 : ℝ) - 1 ≤ (-33174219061549001 / 10 ^ 17 : ℝ) * cWL := by unfold cWL; norm_num
    linarith

lemma exp_y4 : exp (-554957327725628994 / 10 ^ 18 : ℝ) ≤ (574096758688152709 / 10 ^ 18 : ℝ) := by
  refine exp_le_taylor (b := 5 / 8) 22 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- `E_- ≤ -0.000389422...` at the ledger constants. -/
theorem Eminus_ledger : Eminus aL (hAL + dsL) hWL cWL cfL τmL ≤ (-3894224650887130731 / 10 ^ 22 : ℝ) := by
  have h := Eminus_le_of_bounds (a := aL) (h := hAL + dsL) (hW := hWL) (cW := cWL) (cf := cfL)
    (τ := τmL) (x0lo := (66630010657559783 / 10 ^ 18 : ℝ)) (x0hi := (66630010657559784 / 10 ^ 18 : ℝ)) (Tlo := (-331742190615490011 / 10 ^ 18 : ℝ)) (Thi := (-33174219061549001 / 10 ^ 17 : ℝ)) (y := (-554957327725628994 / 10 ^ 18 : ℝ))
    (ehi := (574096758688152709 / 10 ^ 18 : ℝ))
    (by unfold hWL; norm_num) (by unfold cWL; norm_num)
    (by unfold cfL; norm_num) (by unfold τmL; norm_num)
    (by rw [hL_eq]; unfold hWL; norm_num) x0_lo x0_hi Tm_bounds.1 Tm_bounds.2 (by norm_num)
    (by rw [hL_eq]; unfold cfL hWL; norm_num) exp_y4 (by norm_num)
  refine h.trans ?_
  rw [hL_eq]; unfold τmL hWL cfL; norm_num

lemma exp_xM : exp (16384 * (-3894224650887130731 / 10 ^ 22 : ℝ) / 8) ≤ (45043693145625126229 / 10 ^ 20 : ℝ) := by
  refine exp_le_taylor (b := 1) 24 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- `B_- ≤ 0.001694618447832` at the ledger constants. -/
theorem Bminus_ledger : Bminus 16384 aL (hAL + dsL) hWL cWL cfL τmL ≤ (1694618447832 / 10 ^ 15 : ℝ) := by
  unfold Bminus
  refine (exp_n_le Eminus_ledger exp_xM).trans ?_
  norm_num

/-- `E_+ < 0` at the ledger constants. -/
theorem Eplus_ledger_neg : Eplus aL (hAL + dsL) hWL cWL cfL τpL < 0 :=
  lt_of_le_of_lt Eplus_ledger (by norm_num)

/-- `E_- < 0` at the ledger constants. -/
theorem Eminus_ledger_neg : Eminus aL (hAL + dsL) hWL cWL cfL τmL < 0 :=
  lt_of_le_of_lt Eminus_ledger (by norm_num)

/-- `exp (-100) ≤ 2⁻¹⁰⁰`. -/
lemma exp_neg_hundred : exp (-100) ≤ (1 / 2 : ℝ) ^ 100 := by
  have h1 : exp (-1) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    refine one_div_le_one_div_of_le (by norm_num) ?_
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  calc exp (-100) = exp (-1) ^ 100 := by
        rw [← Real.exp_nat_mul]; congr 1; norm_num
    _ ≤ (1 / 2 : ℝ) ^ 100 := pow_le_pow_left₀ (exp_pos _).le h1 100

/-- **The numeric ledger at `n = 16 384`.** With `k = 10¹²` and `d_s = 10⁻⁵`, `k d_s² = 100`.
`δ_hidden + v_W/h_W² + B_+ + B_- + 2 exp (-100) + δ_extra < 0.008195686`. -/
theorem ledger_total :
    δhidL + vWL / hWL ^ 2 + Bplus 16384 aL (hAL + dsL) hWL cWL cfL τpL +
      Bminus 16384 aL (hAL + dsL) hWL cWL cfL τmL + 2 * exp (-100) + δextraL
      < 8195686 / 10 ^ 9 := by
  have h1 := Bplus_ledger
  have h2 := Bminus_ledger
  have h3 := exp_neg_hundred
  have h4 : δhidL + vWL / hWL ^ 2 + (146335214251 / 10 ^ 14 : ℝ) + (1694618447832 / 10 ^ 15 : ℝ) + 2 * (1 / 2 : ℝ) ^ 100 + δextraL
      < 8195686 / 10 ^ 9 := by
    unfold δhidL vWL hWL δextraL; norm_num
  linarith

/-- The numeric ledger is below `1/100`. -/
theorem ledger_total_lt :
    δhidL + vWL / hWL ^ 2 + Bplus 16384 aL (hAL + dsL) hWL cWL cfL τpL +
      Bminus 16384 aL (hAL + dsL) hWL cWL cfL τmL + 2 * exp (-100) + δextraL
      < 1 / 100 :=
  lt_trans ledger_total (by norm_num)

/-- `2 exp (-k d_s²) = 2 exp (-100)` for `k = 10¹²`, `d_s = 10⁻⁵`. -/
lemma sampling_ledger : 2 * exp (-((10 : ℝ) ^ 12) * dsL ^ 2) = 2 * exp (-100) := by
  unfold dsL; norm_num

end BstLean.Part156
