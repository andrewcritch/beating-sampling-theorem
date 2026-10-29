import BstLean.Part112Mehler

/-!
# Part 134: the second-order Gebelein inequality with the sharp constant 1

Part 112 (`BstLean.Part112.mehler2`) has `|Cov(f(X), g(Y)) − ρ·c_f·c_g| ≤ 2ρ²·a₂(f)·a₂(g)` for a
Gaussian pair with correlation `ρ` in every coordinate. This file removes the factor `2`
(`mehler2_sharp`). It is the form of the Hermite (Mehler) expansion that Theorem S1 (c) needs:
the part of degree one is exact, and the part of degree at least two contracts by `ρ²`.

Proof. `ñ(c) = E(T_c h)² − c²|c_h|²` (`Part112.nt`) is the squared norm of the part of `T_c h`
orthogonal to the first chaos. Self-adjointness and Cauchy–Schwarz give `ñ(r)² ≤ ñ(a)ñ(b)` for
`r² = ab` (`nt_mid`). With `a = 1`, by induction, `ñ(c)^{2^k} ñ(1) ≤ ñ(1)^{2^k} ñ(c^{2^k})`. Part
112 has `ñ(c) ≤ 2c⁴ñ(1)`; so `ñ(c)^{2^k} ≤ 2 (c⁴ñ(1))^{2^k}` for every `k`, hence
`ñ(c) ≤ c⁴ñ(1)` (`nt_le_sharp`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part134

open MeasureTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part105
open BstLean.Part112 (lc asq nt Bf nt_nonneg nt_le chaosLimit lc_Tou lc_lin lc_sub_const Bf_sq_le
  cov_eq)

variable {ι : Type} [Fintype ι] {f g h : (ι → ℝ) → ℝ}

/-- `ñ(r)² ≤ ñ(a) ñ(b)` if `r² = ab`. -/
lemma nt_mid {a b r : ℝ} (ha : |a| ≤ 1) (hb : |b| ≤ 1) (hr : |r| ≤ 1) (hrab : r * r = a * b)
    (hh : BM h) : nt r h ^ 2 ≤ nt a h * nt b h := by
  have bA := Tou_BM (ι := ι) a hh
  have bB := Tou_BM (ι := ι) b hh
  have e : Nou r h = ∫ x, Tou a h x * Tou b h x ∂stdGauss ι := by
    calc Nou r h = ∫ x, Tou r h x * Tou r h x ∂stdGauss ι := by simp only [Nou, pow_two]
      _ = ∫ x, h x * Tou r (Tou r h) x ∂stdGauss ι := (Tou_selfadj hr hh (Tou_BM r hh)).symm
      _ = ∫ x, h x * Tou a (Tou b h) x ∂stdGauss ι := by
          rw [Tou_Tou hr hr hh, hrab, ← Tou_Tou ha hb hh]
      _ = ∫ x, Tou a h x * Tou b h x ∂stdGauss ι := Tou_selfadj ha hh (Tou_BM b hh)
  have hr2 : r ^ 2 = a * b := by rw [sq]; exact hrab
  have key : ∀ t : ℝ, 0 ≤ nt b h * (t * t) + 2 * nt r h * t + nt a h := by
    intro t
    have hF : BM (fun y => Tou a h y + t * Tou b h y) := bA.add ((BM.const t).mul bB)
    have h0 := nt_nonneg (c := 1) (by simp) hF
    have e1 : Nou 1 (fun y => Tou a h y + t * Tou b h y) =
        Nou a h + 2 * t * Nou r h + t * t * Nou b h := by
      rw [Nou_one, e]
      simp only [Nou]
      have : (fun x => (Tou a h x + t * Tou b h x) ^ 2) = fun x =>
          Tou a h x ^ 2 + (2 * t) * (Tou a h x * Tou b h x) + (t * t) * Tou b h x ^ 2 := by
        funext x; ring
      rw [this, integral_add ((bA.sq.add ((BM.const _).mul (bA.mul bB))).integrable _)
        (((BM.const _).mul bB.sq).integrable _),
        integral_add (bA.sq.integrable _) (((BM.const _).mul (bA.mul bB)).integrable _),
        integral_const_mul, integral_const_mul]
    have e2 : asq (fun y => Tou a h y + t * Tou b h y) = (a + t * b) ^ 2 * asq h := by
      simp only [asq]
      simp_rw [lc_lin t bA bB, lc_Tou ha hh, lc_Tou hb hh]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e3 : nt b h * (t * t) + 2 * nt r h * t + nt a h =
        Nou a h + 2 * t * Nou r h + t * t * Nou b h - 1 ^ 2 * ((a + t * b) ^ 2 * asq h) := by
      unfold nt; rw [hr2]; ring
    rw [e3]
    unfold nt at h0
    rw [e1, e2] at h0
    exact h0
  have := discrim_le_zero key
  unfold discrim at this
  nlinarith

lemma pow_two_pow_bound {A B : ℝ} (hB : 0 ≤ B)
    (h : ∀ k : ℕ, A ^ (2 ^ k) ≤ 2 * B ^ (2 ^ k)) : A ≤ B := by
  by_contra hlt
  push Not at hlt
  rcases hB.eq_or_lt with hB0 | hBpos
  · have := h 0
    rw [← hB0] at this
    simp at this
    linarith
  · set x := A / B with hx
    have hx1 : 1 < x := by rw [hx, one_lt_div hBpos]; exact hlt
    have hk : ∀ k : ℕ, x ^ (2 ^ k) ≤ 2 := by
      intro k
      rw [hx, div_pow, div_le_iff₀ (pow_pos hBpos _)]
      exact h k
    obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt 2 hx1
    have hmono : x ^ N ≤ x ^ (2 ^ N) :=
      pow_le_pow_right₀ hx1.le (Nat.lt_two_pow_self).le
    linarith [hk N]

section meanzero

variable (hh : BM h) (h0 : ∫ x, h x ∂stdGauss ι = 0)
include hh

lemma nt_iter {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (k : ℕ) :
    nt c h ^ (2 ^ k) * nt 1 h ≤ nt 1 h ^ (2 ^ k) * nt (c ^ (2 ^ k)) h := by
  have habs : ∀ j : ℕ, |c ^ j| ≤ 1 := fun j => by
    rw [abs_of_nonneg (pow_nonneg hc0 j)]; exact pow_le_one₀ hc0 hc1
  have y0 : 0 ≤ nt 1 h := nt_nonneg (by simp) hh
  induction k with
  | zero => simp [mul_comm]
  | succ k ih =>
    have x0 : 0 ≤ nt c h := nt_nonneg (by rw [abs_of_nonneg hc0]; exact hc1) hh
    have z0 : 0 ≤ nt (c ^ (2 ^ k)) h := nt_nonneg (habs _) hh
    have z1 : 0 ≤ nt (c ^ (2 ^ (k + 1))) h := nt_nonneg (habs _) hh
    have hmid : nt (c ^ (2 ^ k)) h ^ 2 ≤ nt 1 h * nt (c ^ (2 ^ (k + 1))) h := by
      refine nt_mid (by simp) (habs _) (habs _) ?_ hh
      rw [one_mul, ← pow_add, pow_succ]; ring_nf
    rcases y0.eq_or_lt with hy | hy
    · rw [← hy]; simp
    · have hsq : (nt c h ^ (2 ^ k) * nt 1 h) ^ 2 ≤ (nt 1 h ^ (2 ^ k) * nt (c ^ (2 ^ k)) h) ^ 2 :=
        pow_le_pow_left₀ (mul_nonneg (pow_nonneg x0 _) y0) ih 2
      have h3 : (nt c h ^ (2 ^ (k + 1)) * nt 1 h) * nt 1 h ≤
          (nt 1 h ^ (2 ^ (k + 1)) * nt (c ^ (2 ^ (k + 1))) h) * nt 1 h := by
        calc (nt c h ^ (2 ^ (k + 1)) * nt 1 h) * nt 1 h
            = (nt c h ^ (2 ^ k) * nt 1 h) ^ 2 := by
              rw [show (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k, pow_mul]; ring
          _ ≤ (nt 1 h ^ (2 ^ k) * nt (c ^ (2 ^ k)) h) ^ 2 := hsq
          _ = nt 1 h ^ (2 ^ (k + 1)) * nt (c ^ (2 ^ k)) h ^ 2 := by
              rw [show (2 : ℕ) ^ (k + 1) = 2 ^ k * 2 from pow_succ 2 k, pow_mul]; ring
          _ ≤ nt 1 h ^ (2 ^ (k + 1)) * (nt 1 h * nt (c ^ (2 ^ (k + 1))) h) :=
              mul_le_mul_of_nonneg_left hmid (pow_nonneg y0 _)
          _ = _ := by ring
      exact le_of_mul_le_mul_right h3 hy

include h0

/-- **`ñ(c) ≤ c⁴ ñ(1)`** for bounded `h` of mean zero: the part of `T_c h` above the first chaos
contracts by `c²` in norm. -/
theorem nt_le_sharp {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : nt c h ≤ c ^ 4 * nt 1 h := by
  have y0 : 0 ≤ nt 1 h := nt_nonneg (by simp) hh
  have x0 : 0 ≤ nt c h := nt_nonneg (by rw [abs_of_nonneg hc0]; exact hc1) hh
  rcases y0.eq_or_lt with hy | hy
  · have := nt_le hh h0 chaosLimit hc0 hc1
    rw [← hy] at this ⊢
    linarith
  · refine pow_two_pow_bound (by positivity) fun k => ?_
    have h1 := nt_iter hh hc0 hc1 k
    have h2 := nt_le hh h0 chaosLimit (pow_nonneg hc0 (2 ^ k)) (pow_le_one₀ hc0 hc1)
    have h3 : nt c h ^ (2 ^ k) * nt 1 h ≤ (2 * (c ^ 4 * nt 1 h) ^ (2 ^ k)) * nt 1 h := by
      calc nt c h ^ (2 ^ k) * nt 1 h ≤ nt 1 h ^ (2 ^ k) * nt (c ^ (2 ^ k)) h := h1
        _ ≤ nt 1 h ^ (2 ^ k) * (2 * (c ^ (2 ^ k)) ^ 4 * nt 1 h) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg y0 _)
        _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (2 ^ k) 4]; ring
    exact le_of_mul_le_mul_right h3 hy

end meanzero

/-- The sharp second-order Gebelein inequality for `0 ≤ ρ ≤ 1`. -/
theorem mehler2_sharp_nonneg {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hf : BM f) (hg : BM g) :
    |∫ w, f w.1 * g (ρ • w.1 + sC ρ • w.2) ∂((stdGauss ι).prod (stdGauss ι)) -
        (∫ x, f x ∂stdGauss ι) * (∫ x, g x ∂stdGauss ι) -
        ρ * ∑ i, (∫ x, f x * x i ∂stdGauss ι) * (∫ x, g x * x i ∂stdGauss ι)| ≤
      ρ ^ 2 *
        Real.sqrt (∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι -
          ∑ i, (∫ x, f x * x i ∂stdGauss ι) ^ 2) *
        Real.sqrt (∫ x, (g x - ∫ y, g y ∂stdGauss ι) ^ 2 ∂stdGauss ι -
          ∑ i, (∫ x, g x * x i ∂stdGauss ι) ^ 2) := by
  set mf := ∫ y, f y ∂stdGauss ι with hmf
  set mg := ∫ y, g y ∂stdGauss ι with hmg
  set f' : (ι → ℝ) → ℝ := fun x => f x - mf with hf'
  set g' : (ι → ℝ) → ℝ := fun x => g x - mg with hg'
  have bf' : BM f' := hf.sub (BM.const mf)
  have bg' : BM g' := hg.sub (BM.const mg)
  have mf' : ∫ x, f' x ∂stdGauss ι = 0 := by
    simp only [hf']
    rw [integral_sub (hf.integrable _) (integrable_const _)]
    simp [hmf]
  have mg' : ∫ x, g' x ∂stdGauss ι = 0 := by
    simp only [hg']
    rw [integral_sub (hg.integrable _) (integrable_const _)]
    simp [hmg]
  set r := Real.sqrt ρ with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = ρ := Real.sq_sqrt hρ0
  have hr4 : r ^ 4 = ρ ^ 2 := by rw [show r ^ 4 = (r ^ 2) ^ 2 by ring, hr2]
  have hr1 : r ≤ 1 := by rw [hr]; exact Real.sqrt_le_one.mpr hρ1
  have hrabs : |r| ≤ 1 := by rw [abs_of_nonneg hr0]; exact hr1
  have lf : ∀ i, lc f' i = ∫ x, f x * x i ∂stdGauss ι := fun i => lc_sub_const hf mf i
  have lg : ∀ i, lc g' i = ∫ x, g x * x i ∂stdGauss ι := fun i => lc_sub_const hg mg i
  have eB : ∫ w, f w.1 * g (ρ • w.1 + sC ρ • w.2) ∂((stdGauss ι).prod (stdGauss ι)) -
        mf * mg - ρ * ∑ i, (∫ x, f x * x i ∂stdGauss ι) * (∫ x, g x * x i ∂stdGauss ι) =
      Bf r f' g' := by
    rw [cov_eq hρ0 hρ1 hf hg]
    simp only [Bf, lf, lg, hr2]
    rfl
  have eF : ∫ x, (f x - mf) ^ 2 ∂stdGauss ι - ∑ i, (∫ x, f x * x i ∂stdGauss ι) ^ 2 =
      nt 1 f' := by
    simp only [nt, asq, lf, Nou_one]; ring
  have eG : ∫ x, (g x - mg) ^ 2 ∂stdGauss ι - ∑ i, (∫ x, g x * x i ∂stdGauss ι) ^ 2 =
      nt 1 g' := by
    simp only [nt, asq, lg, Nou_one]; ring
  rw [eB, eF, eG]
  have h1 := Bf_sq_le hrabs bf' bg'
  have h2 := nt_le_sharp bf' mf' hr0 hr1
  have h3 := nt_le_sharp bg' mg' hr0 hr1
  rw [hr4] at h2 h3
  have a0 : 0 ≤ nt 1 f' := nt_nonneg (by simp) bf'
  have b0 : 0 ≤ nt 1 g' := nt_nonneg (by simp) bg'
  have h4 : Bf r f' g' ^ 2 ≤ (ρ ^ 2) ^ 2 * (nt 1 f' * nt 1 g') := by
    calc _ ≤ nt r f' * nt r g' := h1
      _ ≤ (ρ ^ 2 * nt 1 f') * (ρ ^ 2 * nt 1 g') :=
          mul_le_mul h2 h3 (nt_nonneg hrabs bg') (by positivity)
      _ = _ := by ring
  have h5 := Real.abs_le_sqrt h4
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), Real.sqrt_mul a0] at h5
  linarith

/-- **The second-order Gebelein inequality with constant 1** (signed Mehler step). For a
Gaussian pair `(X, Y)`, `Y = ρ X + √(1−ρ²) Z`, `|ρ| ≤ 1`, and bounded measurable `f`, `g`:
`|Cov(f(X), g(Y)) − ρ·c_f·c_g| ≤ ρ²·a₂(f)·a₂(g)`, `c_f = E[f(X) X]` (the first chaos),
`a₂(f)² = Var f − |c_f|²`. -/
theorem mehler2_sharp {ρ : ℝ} (hρ : |ρ| ≤ 1) (hf : BM f) (hg : BM g) :
    |∫ w, f w.1 * g (ρ • w.1 + sC ρ • w.2) ∂((stdGauss ι).prod (stdGauss ι)) -
        (∫ x, f x ∂stdGauss ι) * (∫ x, g x ∂stdGauss ι) -
        ρ * ∑ i, (∫ x, f x * x i ∂stdGauss ι) * (∫ x, g x * x i ∂stdGauss ι)| ≤
      ρ ^ 2 *
        Real.sqrt (∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι -
          ∑ i, (∫ x, f x * x i ∂stdGauss ι) ^ 2) *
        Real.sqrt (∫ x, (g x - ∫ y, g y ∂stdGauss ι) ^ 2 ∂stdGauss ι -
          ∑ i, (∫ x, g x * x i ∂stdGauss ι) ^ 2) := by
  rcases le_or_gt 0 ρ with h0 | h0
  · exact mehler2_sharp_nonneg h0 (by rw [abs_of_nonneg h0] at hρ; exact hρ) hf hg
  · have hρ' : -ρ ≤ 1 := by rw [abs_of_neg h0] at hρ; exact hρ
    set gn : (ι → ℝ) → ℝ := fun y => g (-y) with hgn
    have bgn : BM gn := hg.comp measurable_neg
    have h1 := mehler2_sharp_nonneg (ι := ι) (by linarith : 0 ≤ -ρ) hρ' hf bgn
    have hs : sC (-ρ) = sC ρ := by simp [sC]
    have e1 : ∫ w, f w.1 * gn ((-ρ) • w.1 + sC (-ρ) • w.2) ∂((stdGauss ι).prod (stdGauss ι)) =
        ∫ w, f w.1 * g (ρ • w.1 + sC ρ • w.2) ∂((stdGauss ι).prod (stdGauss ι)) := by
      rw [hs]
      have bL : BM (fun w : (ι → ℝ) × (ι → ℝ) => f w.1 * gn ((-ρ) • w.1 + sC ρ • w.2)) :=
        (hf.comp measurable_fst).mul (bgn.comp (meas_comb (-ρ) (sC ρ)))
      have bR : BM (fun w : (ι → ℝ) × (ι → ℝ) => f w.1 * g (ρ • w.1 + sC ρ • w.2)) :=
        (hf.comp measurable_fst).mul (hg.comp (meas_comb ρ (sC ρ)))
      rw [integral_prod _ (bL.integrable _), integral_prod _ (bR.integrable _)]
      congr 1
      funext x
      simp only [integral_const_mul]
      congr 1
      have := gauss_neg (ι := ι) (fun z => g (ρ • x + sC ρ • z))
        (hg.meas.comp (measurable_const.add (measurable_const_smul (sC ρ))))
      rw [← this]
      congr 1
      funext z
      simp only [hgn]
      congr 1
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
      ring
    have e2 : ∫ x, gn x ∂stdGauss ι = ∫ x, g x ∂stdGauss ι := gauss_neg g hg.meas
    have e3 : ∫ x, (gn x - ∫ y, g y ∂stdGauss ι) ^ 2 ∂stdGauss ι =
        ∫ x, (g x - ∫ y, g y ∂stdGauss ι) ^ 2 ∂stdGauss ι :=
      gauss_neg (fun x => (g x - ∫ y, g y ∂stdGauss ι) ^ 2) (hg.sub (BM.const _)).sq.meas
    have e4 : ∀ i, ∫ x, gn x * x i ∂stdGauss ι = -∫ x, g x * x i ∂stdGauss ι := by
      intro i
      have := gauss_neg (ι := ι) (fun z => g z * (-(z i)))
        (hg.meas.mul (measurable_pi_apply i).neg)
      simp only [Pi.neg_apply, neg_neg] at this
      rw [show (fun x => gn x * x i) = fun z : ι → ℝ => g (-z) * z i from rfl, this,
        ← integral_neg]
      congr 1
      funext z
      ring
    simp_rw [e4] at h1
    rw [e1, e2, e3] at h1
    have e5 : (-ρ) * ∑ i, (∫ x, f x * x i ∂stdGauss ι) * -(∫ x, g x * x i ∂stdGauss ι) =
        ρ * ∑ i, (∫ x, f x * x i ∂stdGauss ι) * (∫ x, g x * x i ∂stdGauss ι) := by
      simp only [mul_neg, Finset.sum_neg_distrib]; ring
    simp only [neg_sq] at h1
    rw [e5] at h1
    exact h1

end BstLean.Part134

open BstLean.Part134 in
#print axioms nt_le_sharp
open BstLean.Part134 in
#print axioms mehler2_sharp
