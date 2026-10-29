import BstLean.Part160Lib

/-!
# Part 160 (file `MFU`): the remainder constant of Lemma PR with its Gaussian factor

Do not use `sorry`, `native_decide` or `axiom`.

Paper: `theorem7-05-centre.tex`, Lemma `t7:p05:PR` (PR⁺), change (A).

* `Ures_exp`: `U(a) ≤ K₀·exp(−a²/2)` for every real `a`, with `U = Ures` and
  `K₀ = (π − 2)/(4π)` of Part 154. With `PR_scalar` of Part 154 (remainder at most
  `ρ²σσ′√U(α)√U(α′)`) this is the bound `K₀ρ²σσ′ exp(−(α² + α′²)/4)` of Lemma PR⁺.

Proof (no numerical evaluation): `(U e^{a²/2})′ = −e^{a²/2}·T`, `T = 2G − aU`. The derivatives
are `T′ = T₁`, `T₁′ = T₂`, `T₂′ = T₃`, `T₃′ = φ·W`, `W′ = 4φ·(4a⁴ − 12a² + 3)`; `T`, `T₁`, `T₂`,
`T₃` tend to `0` at infinity and `T(0) = T₂(0) = W(0) = 0`. The quartic is a convex quadratic in
`a²`; from this the set `{T₃ > 0}` is an interval, `T₂` stays nonnegative once it is positive,
`T₁` stays nonpositive once it is nonpositive, and `T ≥ 0` on `[0, ∞)`.
-/

namespace BstLean.Part160

open MeasureTheory Real Set Filter Topology
open BstLean.Part153 (phiG PhiG psiG phiG_pos PhiG_le_one hasDerivAt_phiG hasDerivAt_PhiG)
open BstLean.Part154

/-! ## Two forms of the mean value theorem -/

lemma exists_deriv_neg {g g' : ℝ → ℝ} (hd : ∀ x, HasDerivAt g (g' x) x) {x y : ℝ} (hxy : x < y)
    (h : g y < g x) : ∃ v ∈ Ioo x y, g' v < 0 := by
  have hc : ContinuousOn g (Icc x y) := fun z _ => (hd z).continuousAt.continuousWithinAt
  obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_slope g g' hxy hc (fun z _ => hd z)
  refine ⟨c, hc1, ?_⟩
  rw [hc2]
  exact div_neg_of_neg_of_pos (by linarith) (by linarith)

lemma exists_deriv_pos {g g' : ℝ → ℝ} (hd : ∀ x, HasDerivAt g (g' x) x) {x y : ℝ} (hxy : x < y)
    (h : g x < g y) : ∃ v ∈ Ioo x y, 0 < g' v := by
  have hc : ContinuousOn g (Icc x y) := fun z _ => (hd z).continuousAt.continuousWithinAt
  obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_slope g g' hxy hc (fun z _ => hd z)
  refine ⟨c, hc1, ?_⟩
  rw [hc2]
  exact div_pos (by linarith) (by linarith)

lemma exists_deriv_pos_after {g g' : ℝ → ℝ} (hd : ∀ x, HasDerivAt g (g' x) x) {L : ℝ}
    (hl : Tendsto g atTop (𝓝 L)) {y : ℝ} (h : g y < L) : ∃ z, y < z ∧ 0 < g' z := by
  by_contra hcon
  push Not at hcon
  have hcont : Continuous g := continuous_iff_continuousAt.mpr fun a => (hd a).continuousAt
  have hanti : AntitoneOn g (Ici y) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici _) hcont.continuousOn
      (fun a _ => (hd a).differentiableAt.differentiableWithinAt) fun z hz => ?_
    rw [interior_Ici] at hz
    rw [(hd z).deriv]
    exact hcon z (mem_Ioi.mp hz)
  have : L ≤ g y := by
    refine le_of_tendsto hl ?_
    filter_upwards [eventually_ge_atTop y] with z hz
    exact hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hz) hz
  linarith

lemma exists_deriv_neg_after {g g' : ℝ → ℝ} (hd : ∀ x, HasDerivAt g (g' x) x) {L : ℝ}
    (hl : Tendsto g atTop (𝓝 L)) {y : ℝ} (h : L < g y) : ∃ z, y < z ∧ g' z < 0 := by
  by_contra hcon
  push Not at hcon
  have hcont : Continuous g := continuous_iff_continuousAt.mpr fun a => (hd a).continuousAt
  have hmono : MonotoneOn g (Ici y) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici _) hcont.continuousOn
      (fun a _ => (hd a).differentiableAt.differentiableWithinAt) fun z hz => ?_
    rw [interior_Ici] at hz
    rw [(hd z).deriv]
    exact hcon z (mem_Ioi.mp hz)
  have : g y ≤ L := by
    refine ge_of_tendsto hl ?_
    filter_upwards [eventually_ge_atTop y] with z hz
    exact hmono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hz) hz
  linarith

/-! ## The functions -/

/-- `T = 2G − aU`. -/
noncomputable def TT0 (a : ℝ) : ℝ := 2 * GG a - a * Ures a
/-- `T₁ = 2P − U + 2aG`. -/
noncomputable def TT1 (a : ℝ) : ℝ := 2 * PP a - Ures a + 2 * a * GG a
/-- `T₂ = 2φQ + 4G + 2aP`. -/
noncomputable def TT2 (a : ℝ) : ℝ := 2 * (phiG a * QQ a) + 4 * GG a + 2 * a * PP a
/-- `T₃ = 2φ²(4a² − 2) + 6P`. -/
noncomputable def TT3 (a : ℝ) : ℝ := 2 * (phiG a * phiG a) * (4 * a ^ 2 - 2) + 6 * PP a
/-- `W = 6(2Φ − 1) − 16a³φ`. -/
noncomputable def WW (a : ℝ) : ℝ := 6 * (2 * PhiG a - 1) - 16 * a ^ 3 * phiG a

lemma hasDerivAt_TT0 (a : ℝ) : HasDerivAt TT0 (TT1 a) a := by
  have h := ((hasDerivAt_GG a).const_mul 2).sub ((hasDerivAt_id a).mul (hasDerivAt_Ures a))
  refine HasDerivAt.congr_deriv (show HasDerivAt TT0 _ a from h) ?_
  unfold TT1
  simp only [id]
  ring

lemma hasDerivAt_TT1 (a : ℝ) : HasDerivAt TT1 (TT2 a) a := by
  have h := (((hasDerivAt_PP a).const_mul 2).sub (hasDerivAt_Ures a)).add
    (((hasDerivAt_id a).const_mul 2).mul (hasDerivAt_GG a))
  refine HasDerivAt.congr_deriv (show HasDerivAt TT1 _ a from h) ?_
  unfold TT2
  simp only [id]
  ring

lemma hasDerivAt_TT2 (a : ℝ) : HasDerivAt TT2 (TT3 a) a := by
  have h := ((((hasDerivAt_phiG a).mul (hasDerivAt_QQ a)).const_mul 2).add
    ((hasDerivAt_GG a).const_mul 4)).add (((hasDerivAt_id a).const_mul 2).mul (hasDerivAt_PP a))
  refine HasDerivAt.congr_deriv (show HasDerivAt TT2 _ a from h) ?_
  unfold TT3 PP QQ
  simp only [id]
  ring

lemma hasDerivAt_TT3 (a : ℝ) : HasDerivAt TT3 (phiG a * WW a) a := by
  have hφ := hasDerivAt_phiG a
  have hp : HasDerivAt (fun a : ℝ => 4 * a ^ 2 - 2) (4 * (2 * a)) a := by
    have := ((hasDerivAt_pow 2 a).const_mul 4).sub_const 2
    convert this using 1; ring
  have h := (((hφ.mul hφ).const_mul 2).mul hp).add ((hasDerivAt_PP a).const_mul 6)
  refine HasDerivAt.congr_deriv (show HasDerivAt TT3 _ a from h) ?_
  unfold WW QQ
  simp only [Pi.mul_apply]
  ring

lemma hasDerivAt_WW (a : ℝ) :
    HasDerivAt WW (4 * phiG a * (4 * (a ^ 2) ^ 2 - 12 * a ^ 2 + 3)) a := by
  have hφ := hasDerivAt_phiG a
  have hΦ := hasDerivAt_PhiG a
  have hp : HasDerivAt (fun a : ℝ => 16 * a ^ 3) (16 * (3 * a ^ 2)) a := by
    have := (hasDerivAt_pow 3 a).const_mul 16
    convert this using 1
  have h := (((hΦ.const_mul 2).sub_const 1).const_mul 6).sub (hp.mul hφ)
  refine HasDerivAt.congr_deriv (show HasDerivAt WW _ a from h) ?_
  ring

/-! ## Limits at infinity -/

lemma tendsto_pow_mul_phiG (k : ℕ) : Tendsto (fun a : ℝ => a ^ k * phiG a) atTop (𝓝 0) := by
  have h1 := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero k).const_mul (√(2 * π))⁻¹
  rw [mul_zero] at h1
  refine squeeze_zero' ?_ ?_ h1
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact mul_nonneg (pow_nonneg ht k) (phiG_pos t).le
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with t ht
    have he : rexp (-(t ^ 2 / 2)) ≤ rexp (-t) := Real.exp_le_exp.mpr (by nlinarith)
    have hk : 0 ≤ t ^ k := pow_nonneg (by linarith) k
    have hc : 0 ≤ (√(2 * π))⁻¹ := by positivity
    unfold phiG
    calc t ^ k * ((√(2 * π))⁻¹ * rexp (-(t ^ 2 / 2)))
        = (√(2 * π))⁻¹ * (t ^ k * rexp (-(t ^ 2 / 2))) := by ring
      _ ≤ (√(2 * π))⁻¹ * (t ^ k * rexp (-t)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hk) hc

lemma tendsto_pow_mul_tail (k : ℕ) :
    Tendsto (fun a : ℝ => a ^ (k + 1) * (1 - PhiG a)) atTop (𝓝 0) := by
  refine squeeze_zero' ?_ ?_ (tendsto_pow_mul_phiG k)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have h2 := PhiG_le_one t
    exact mul_nonneg (pow_nonneg ht _) (by linarith)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have h1 := mul_tail_le t
    have hk : 0 ≤ t ^ k := pow_nonneg ht k
    calc t ^ (k + 1) * (1 - PhiG t) = t ^ k * (t * (1 - PhiG t)) := by ring
      _ ≤ t ^ k * phiG t := mul_le_mul_of_nonneg_left h1 hk

/-- `U = Φ(1 − Φ) − φ² − aG`. -/
lemma Ures_eq_GG (a : ℝ) :
    Ures a = PhiG a * (1 - PhiG a) - phiG a * phiG a - a * GG a := by
  rw [Ures_closed]
  unfold GG psiG
  ring

lemma tendsto_a_GG : Tendsto (fun a : ℝ => a * GG a) atTop (𝓝 0) := by
  have h1 := tendsto_pow_mul_phiG 1
  have h2 := tendsto_pow_mul_tail 1
  have h := (h1.mul ((tendsto_PhiG.const_mul 2).sub_const 1)).sub (h2.mul tendsto_PhiG)
  rw [show (0 * (2 * 1 - 1) - 0 * 1 : ℝ) = 0 by norm_num] at h
  refine h.congr fun t => ?_
  unfold GG; ring

lemma tendsto_a2_GG : Tendsto (fun a : ℝ => a ^ 2 * GG a) atTop (𝓝 0) := by
  have h1 := tendsto_pow_mul_phiG 2
  have h2 := tendsto_pow_mul_tail 2
  have h := (h1.mul ((tendsto_PhiG.const_mul 2).sub_const 1)).sub (h2.mul tendsto_PhiG)
  rw [show (0 * (2 * 1 - 1) - 0 * 1 : ℝ) = 0 by norm_num] at h
  refine h.congr fun t => ?_
  unfold GG; ring

lemma tendsto_Ures : Tendsto Ures atTop (𝓝 0) := by
  have h := ((tendsto_PhiG.mul tendsto_tail).sub (tendsto_phiG.mul tendsto_phiG)).sub tendsto_a_GG
  rw [show (1 * 0 - 0 * 0 - 0 : ℝ) = 0 by norm_num] at h
  refine h.congr fun t => ?_
  rw [Ures_eq_GG]

lemma tendsto_a_Ures : Tendsto (fun a : ℝ => a * Ures a) atTop (𝓝 0) := by
  have h0 := tendsto_pow_mul_tail 0
  have h1 := tendsto_pow_mul_phiG 1
  have h := ((h0.mul tendsto_PhiG).sub (h1.mul tendsto_phiG)).sub tendsto_a2_GG
  rw [show (0 * 1 - 0 * 0 - 0 : ℝ) = 0 by norm_num] at h
  refine h.congr fun t => ?_
  rw [Ures_eq_GG]; ring

lemma tendsto_a_PP : Tendsto (fun a : ℝ => a * PP a) atTop (𝓝 0) := by
  have h0 := tendsto_pow_mul_tail 0
  have h1 := tendsto_pow_mul_phiG 1
  have h := ((h1.mul tendsto_phiG).const_mul 2).sub (h0.mul tendsto_PhiG)
  rw [show (2 * (0 * 0) - 0 * 1 : ℝ) = 0 by norm_num] at h
  refine h.congr fun t => ?_
  unfold PP; ring

lemma tendsto_TT0 : Tendsto TT0 atTop (𝓝 0) := by
  have h := (tendsto_GG.const_mul 2).sub tendsto_a_Ures
  rw [show (2 * 0 - 0 : ℝ) = 0 by norm_num] at h
  exact h

lemma tendsto_TT1 : Tendsto TT1 atTop (𝓝 0) := by
  have h := ((tendsto_PP.const_mul 2).sub tendsto_Ures).add (tendsto_a_GG.const_mul 2)
  rw [show (2 * 0 - 0 + 2 * 0 : ℝ) = 0 by norm_num] at h
  refine h.congr fun t => ?_
  unfold TT1; ring

lemma tendsto_TT2 : Tendsto TT2 atTop (𝓝 0) := by
  have h1 := tendsto_pow_mul_phiG 1
  have hQ : Tendsto (fun a : ℝ => phiG a * QQ a) atTop (𝓝 0) := by
    have h := (tendsto_phiG.mul ((tendsto_PhiG.const_mul 2).sub_const 1)).sub
      ((h1.mul tendsto_phiG).const_mul 4)
    rw [show (0 * (2 * 1 - 1) - 4 * (0 * 0) : ℝ) = 0 by norm_num] at h
    refine h.congr fun t => ?_
    unfold QQ; ring
  have h := ((hQ.const_mul 2).add (tendsto_GG.const_mul 4)).add (tendsto_a_PP.const_mul 2)
  rw [show (2 * 0 + 4 * 0 + 2 * 0 : ℝ) = 0 by norm_num] at h
  refine h.congr fun t => ?_
  unfold TT2; ring

lemma tendsto_TT3 : Tendsto TT3 atTop (𝓝 0) := by
  have h1 := tendsto_pow_mul_phiG 1
  have h := (((h1.mul h1).const_mul 8).sub ((tendsto_phiG.mul tendsto_phiG).const_mul 4)).add
    (tendsto_PP.const_mul 6)
  rw [show (8 * (0 * 0) - 4 * (0 * 0) + 6 * 0 : ℝ) = 0 by norm_num] at h
  refine h.congr fun t => ?_
  unfold TT3; ring

/-! ## Values at zero -/

lemma TT0_zero : TT0 0 = 0 := by unfold TT0; rw [GG_zero]; ring
lemma TT2_zero : TT2 0 = 0 := by unfold TT2; rw [GG_zero, QQ_zero]; ring
lemma WW_zero : WW 0 = 0 := by unfold WW; rw [PhiG_zero]; ring

/-! ## The sign chain -/

/-- A convex quadratic is not negative, positive, negative at three increasing points. -/
lemma quad_convex {x1 x2 x3 : ℝ} (h12 : x1 < x2) (h23 : x2 < x3)
    (h1 : 4 * x1 ^ 2 - 12 * x1 + 3 < 0) (h3 : 4 * x3 ^ 2 - 12 * x3 + 3 < 0) :
    4 * x2 ^ 2 - 12 * x2 + 3 < 0 := by
  have e : (4 * x2 ^ 2 - 12 * x2 + 3) * (x3 - x1) =
      (4 * x1 ^ 2 - 12 * x1 + 3) * (x3 - x2) + (4 * x3 ^ 2 - 12 * x3 + 3) * (x2 - x1) -
        4 * (x2 - x1) * (x3 - x2) * (x3 - x1) := by ring
  have ha : 0 < x3 - x2 := by linarith
  have hb : 0 < x2 - x1 := by linarith
  have hc : 0 < x3 - x1 := by linarith
  have h4 : (4 * x2 ^ 2 - 12 * x2 + 3) * (x3 - x1) < 0 := by
    rw [e]
    have t1 := mul_neg_of_neg_of_pos h1 ha
    have t2 := mul_neg_of_neg_of_pos h3 hb
    have t3 : 0 < 4 * (x2 - x1) * (x3 - x2) * (x3 - x1) := by positivity
    linarith
  by_contra hcon
  rw [not_lt] at hcon
  have := mul_nonneg hcon hc.le
  linarith

/-- The set `{T₃ > 0} ∩ [0, ∞)` is an interval. -/
lemma TT3_interval {u v z : ℝ} (hu : 0 ≤ u) (huv : u < v) (hvz : v < z) (h1 : 0 < TT3 u)
    (h3 : 0 < TT3 z) : 0 < TT3 v := by
  by_contra hcon
  rw [not_lt] at hcon
  obtain ⟨s, hs, hs'⟩ := exists_deriv_neg hasDerivAt_TT3 huv (lt_of_le_of_lt hcon h1)
  obtain ⟨t, ht, ht'⟩ := exists_deriv_pos hasDerivAt_TT3 hvz (lt_of_le_of_lt hcon h3)
  obtain ⟨r, hr, hr'⟩ := exists_deriv_neg_after hasDerivAt_TT3 tendsto_TT3 h3
  have hWs : WW s < 0 := by
    by_contra h; rw [not_lt] at h
    have := mul_nonneg (phiG_pos s).le h; linarith
  have hWt : 0 < WW t := by
    by_contra h; rw [not_lt] at h
    have := mul_nonpos_of_nonneg_of_nonpos (phiG_pos t).le h; linarith
  have hWr : WW r < 0 := by
    by_contra h; rw [not_lt] at h
    have := mul_nonneg (phiG_pos r).le h; linarith
  have hs0 : 0 < s := lt_of_le_of_lt hu hs.1
  have hst : s < t := hs.2.trans ht.1
  have htr : t < r := ht.2.trans hr
  obtain ⟨s1, hs1, hs1'⟩ := exists_deriv_neg hasDerivAt_WW hs0 (by rw [WW_zero]; exact hWs)
  obtain ⟨t1, ht1, ht1'⟩ := exists_deriv_pos hasDerivAt_WW hst (hWs.trans hWt)
  obtain ⟨r1, hr1, hr1'⟩ := exists_deriv_neg hasDerivAt_WW htr (hWr.trans hWt)
  have q1 : 4 * (s1 ^ 2) ^ 2 - 12 * s1 ^ 2 + 3 < 0 := by
    by_contra h; rw [not_lt] at h
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (phiG_pos s1).le) h; linarith
  have q2 : 0 < 4 * (t1 ^ 2) ^ 2 - 12 * t1 ^ 2 + 3 := by
    by_contra h; rw [not_lt] at h
    have := mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (phiG_pos t1).le) h
    linarith
  have q3 : 4 * (r1 ^ 2) ^ 2 - 12 * r1 ^ 2 + 3 < 0 := by
    by_contra h; rw [not_lt] at h
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) (phiG_pos r1).le) h; linarith
  have hs1p : 0 < s1 := hs1.1
  have hst1 : s1 < t1 := hs1.2.trans ht1.1
  have htr1 : t1 < r1 := ht1.2.trans hr1.1
  have x12 : s1 ^ 2 < t1 ^ 2 := pow_lt_pow_left₀ hst1 hs1p.le (by norm_num)
  have x23 : t1 ^ 2 < r1 ^ 2 := pow_lt_pow_left₀ htr1 (by linarith) (by norm_num)
  have := quad_convex x12 x23 q1 q3
  linarith

/-- `T₂` is nonnegative after a point of `[0, ∞)` where it is positive. -/
lemma TT2_up {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (h : 0 < TT2 x) : 0 ≤ TT2 y := by
  by_contra hcon
  rw [not_le] at hcon
  have hxy' : x < y := by
    rcases hxy.eq_or_lt with e | e
    · rw [e] at h; linarith
    · exact e
  have hx0 : 0 < x := by
    rcases hx.eq_or_lt with e | e
    · rw [← e, TT2_zero] at h; exact absurd h (lt_irrefl _)
    · exact e
  obtain ⟨u, hu, hu'⟩ := exists_deriv_pos hasDerivAt_TT2 hx0 (by rw [TT2_zero]; exact h)
  obtain ⟨v, hv, hv'⟩ := exists_deriv_neg hasDerivAt_TT2 hxy' (hcon.trans h)
  obtain ⟨z, hz, hz'⟩ := exists_deriv_pos_after hasDerivAt_TT2 tendsto_TT2 hcon
  have := TT3_interval hu.1.le (hu.2.trans hv.1) (hv.2.trans hz) hu' hz'
  linarith

/-- `T₁` is nonpositive after a point of `[0, ∞)` where it is nonpositive. -/
lemma TT1_down {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (h : TT1 x ≤ 0) : TT1 y ≤ 0 := by
  by_contra hcon
  rw [not_le] at hcon
  have hxy' : x < y := by
    rcases hxy.eq_or_lt with e | e
    · rw [e] at h; linarith
    · exact e
  obtain ⟨v, hv, hv'⟩ := exists_deriv_pos hasDerivAt_TT1 hxy' (lt_of_le_of_lt h hcon)
  obtain ⟨z, hz, hz'⟩ := exists_deriv_neg_after hasDerivAt_TT1 tendsto_TT1 hcon
  have := TT2_up (hx.trans hv.1.le) (hv.2.trans hz).le hv'
  linarith

/-- `aU(a) ≤ 2G(a)` for `a ≥ 0`. -/
lemma TT0_nonneg {y : ℝ} (hy : 0 ≤ y) : 0 ≤ TT0 y := by
  by_contra hcon
  rw [not_le] at hcon
  have hy0 : 0 < y := by
    rcases hy.eq_or_lt with e | e
    · rw [← e, TT0_zero] at hcon; exact absurd hcon (lt_irrefl _)
    · exact e
  obtain ⟨v, hv, hv'⟩ := exists_deriv_neg hasDerivAt_TT0 hy0 (by rw [TT0_zero]; exact hcon)
  obtain ⟨z, hz, hz'⟩ := exists_deriv_pos_after hasDerivAt_TT0 tendsto_TT0 hcon
  have := TT1_down hv.1.le (hv.2.trans hz).le hv'.le
  linarith

/-- **The remainder constant with its Gaussian factor** (Lemma `t7:p05:PR`):
`U(a) ≤ K₀·exp(−a²/2)` for every real `a`. -/
theorem Ures_exp (a : ℝ) : Ures a ≤ K0 * rexp (-(a ^ 2) / 2) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x => Ures x * rexp (x ^ 2 / 2))
      (-(rexp (x ^ 2 / 2) * TT0 x)) x := by
    intro x
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) x x := by
      have := (hasDerivAt_pow 2 x).div_const 2
      convert this using 1; ring
    have h := (hasDerivAt_Ures x).mul h1.exp
    refine HasDerivAt.congr_deriv h ?_
    unfold TT0; ring
  have hcont : Continuous (fun x => Ures x * rexp (x ^ 2 / 2)) :=
    continuous_iff_continuousAt.mpr fun a => (hd a).continuousAt
  have hanti : AntitoneOn (fun x => Ures x * rexp (x ^ 2 / 2)) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici _) hcont.continuousOn
      (fun a _ => (hd a).differentiableAt.differentiableWithinAt) fun z hz => ?_
    rw [interior_Ici] at hz
    rw [(hd z).deriv]
    have := mul_nonneg (Real.exp_pos (z ^ 2 / 2)).le (TT0_nonneg (mem_Ioi.mp hz).le)
    linarith
  have key : ∀ b : ℝ, 0 ≤ b → Ures b ≤ K0 * rexp (-(b ^ 2) / 2) := fun b hb => by
    have h := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hb) hb
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, Real.exp_zero,
      mul_one] at h
    rw [Ures_zero] at h
    have he : rexp (-(b ^ 2) / 2) = (rexp (b ^ 2 / 2))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [he, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
    exact h
  rcases le_total 0 a with ha | ha
  · exact key a ha
  · have := key (-a) (by linarith)
    rwa [Ures_neg, neg_sq] at this

/-- `√U(a)·√U(a′) ≤ K₀·exp(−(a² + a′²)/4)`. -/
theorem sqrt_Ures_mul_le (a a' : ℝ) :
    √(Ures a) * √(Ures a') ≤ K0 * rexp (-(a ^ 2 + a' ^ 2) / 4) := by
  have hK := K0_pos
  have h1 : √(Ures a) ≤ √K0 * rexp (-(a ^ 2) / 4) := by
    rw [← Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_pow, Real.sq_sqrt hK.le, ← Real.exp_nat_mul]
    have := Ures_exp a
    convert this using 3
    push_cast; ring
  have h2 : √(Ures a') ≤ √K0 * rexp (-(a' ^ 2) / 4) := by
    rw [← Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)]
    refine Real.sqrt_le_sqrt ?_
    rw [mul_pow, Real.sq_sqrt hK.le, ← Real.exp_nat_mul]
    have := Ures_exp a'
    convert this using 3
    push_cast; ring
  calc √(Ures a) * √(Ures a') ≤ (√K0 * rexp (-(a ^ 2) / 4)) * (√K0 * rexp (-(a' ^ 2) / 4)) :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le)
    _ = K0 * rexp (-(a ^ 2 + a' ^ 2) / 4) := by
        rw [mul_mul_mul_comm, Real.mul_self_sqrt hK.le, ← Real.exp_add]
        congr 2; ring

end BstLean.Part160

open BstLean.Part160 in
#print axioms Ures_exp
open BstLean.Part160 in
#print axioms sqrt_Ures_mul_le
