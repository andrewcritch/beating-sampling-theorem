import BstLean.Part149Win
import BstLean.Part149Kern
import BstLean.Part145B1

/-!
# Part 149, helper `KK`: a second-order expansion of `κ∘κ` at a point of the window

Do not use `sorry`, `native_decide` or `axiom`.

Notation: `kg t = (π − arccos t)/π = 1/2 + arcsin t/π` is the derivative of `κ`.

* `kg_le_of`, `kg_ge_of`: certified rational bounds of `kg`.
* `arcsin_slope_up`, `arcsin_slope_down`: for `0 ≤ u ≤ 16/25`, the slopes of `arcsin` from `u`
  to a point of `[−1, 1]` are at most `(25/18)·π`.
* `kappa_quad_gen`: `κ(s) ≤ κ(u) + kg(u)(s − u) + (25/36)(s − u)²` for `0 ≤ u ≤ 16/25` and
  all `s ∈ [−1, 1]`.
* **`kk_quad_at_sharp`**: for `0.462 ≤ q ≤ 0.527` there is `b` with `9/20 ≤ b ≤ 1/2` and
  `0 ≤ κ(κ(s)) − κ(κ(q)) − b(s − q) ≤ (6/5)(s − q)²` for all `s ∈ [−1, 1]`
  (`b = kg(κ(q))·kg(q)`, the derivative of `κ∘κ` at `q`).
* **`kk_quad_at`**: the same with `0 ≤ b ≤ 1/2`, absolute value and the constant `5/2`.
-/

namespace BstLean.Part149

open Real Set
open BstLean.Part130 BstLean.Part132 BstLean.Part145
open BstLean.Part135 (kappa_le_of_le9 arcsin_le_poly9)

lemma kg_eq (t : ℝ) : kg t = 1 / 2 + Real.arcsin t / π := by
  unfold kg
  exact kappa_deriv_eq t

/-- A certified upper bound of `kg`. -/
lemma kg_le_of {t a c : ℝ} (hta : t ≤ a) (ha0 : 0 ≤ a) (ha : a ≤ 7 / 10)
    (hc : a + a ^ 3 / 6 + 3 * a ^ 5 / 40 + 5 * a ^ 7 / 112 + a ^ 9 / 15 ≤ c * 3.1415) :
    kg t ≤ 1 / 2 + c := by
  have hp := Real.pi_pos
  have h1 := Real.monotone_arcsin hta
  have h2 := arcsin_le_poly9 ha0 ha
  have h3 := Real.pi_gt_d4
  have hP : 0 ≤ a + a ^ 3 / 6 + 3 * a ^ 5 / 40 + 5 * a ^ 7 / 112 + a ^ 9 / 15 := by positivity
  have hc0 : 0 ≤ c := by
    by_contra hneg
    rw [not_le] at hneg
    nlinarith
  have h4 : c * 3.1415 ≤ c * π := mul_le_mul_of_nonneg_left h3.le hc0
  rw [kg_eq]
  have : Real.arcsin t / π ≤ c := by
    rw [div_le_iff₀ hp]; linarith
  linarith

/-- A certified lower bound of `kg`. -/
lemma kg_ge_of {t a c : ℝ} (hat : a ≤ t) (ha0 : 0 ≤ a) (ha : a ≤ 1) (hc0 : 0 ≤ c)
    (hc : c * 3.1416 ≤ a + a ^ 3 / 6 + 3 * a ^ 5 / 40 + 5 * a ^ 7 / 112) :
    1 / 2 + c ≤ kg t := by
  have hp := Real.pi_pos
  have h1 := Real.monotone_arcsin hat
  have h2 := arcsin_ge_poly7 ha0 ha
  have h3 := Real.pi_lt_d4
  have h4 : c * π ≤ c * 3.1416 := mul_le_mul_of_nonneg_left h3.le hc0
  rw [kg_eq]
  have : c ≤ Real.arcsin t / π := by
    rw [le_div_iff₀ hp]; linarith
  linarith

lemma arcsin_secant_one {u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 16 / 25) :
    (Real.arcsin 1 - Real.arcsin u) / (1 - u) ≤ 25 / 18 * π := by
  have hp := Real.pi_pos
  have h1u : 0 < 1 - u := by linarith
  rw [div_le_iff₀ h1u, Real.arcsin_one]
  have ha : 0 ≤ Real.arcsin u := Real.arcsin_nonneg.mpr hu0
  have hm : 0 ≤ π * (16 / 25 - u) := mul_nonneg hp.le (by linarith)
  nlinarith

/-- Slopes of `arcsin` from `u ∈ [0, 16/25]` to the right. -/
lemma arcsin_slope_up {u s : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 16 / 25) (hus : u < s) (hs : s ≤ 1) :
    Real.arcsin s - Real.arcsin u ≤ 25 / 18 * π * (s - u) := by
  have hmem : u ∈ Icc (0 : ℝ) 1 := ⟨hu0, by linarith⟩
  have hne1 : (1 : ℝ) ≠ u := by intro h; linarith
  have h := arcsin_convexOn.secant_mono hmem ⟨by linarith, hs⟩ (right_mem_Icc.mpr zero_le_one)
    hus.ne' hne1 hs
  have h2 := h.trans (arcsin_secant_one hu0 hu)
  rwa [div_le_iff₀ (by linarith)] at h2

/-- Slopes of `arcsin` from `u ∈ [0, 16/25]` to the left. -/
lemma arcsin_slope_down {u s : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 16 / 25) (hs : -1 ≤ s) (hsu : s < u) :
    Real.arcsin u - Real.arcsin s ≤ 25 / 18 * π * (u - s) := by
  have hp := Real.pi_pos
  rcases le_total 0 s with h0 | h0
  · have hmem : u ∈ Icc (0 : ℝ) 1 := ⟨hu0, by linarith⟩
    have hne1 : (1 : ℝ) ≠ u := by intro h; linarith
    have h := arcsin_convexOn.secant_mono hmem ⟨h0, by linarith⟩
      (right_mem_Icc.mpr zero_le_one) hsu.ne hne1 (by linarith)
    have h2 := h.trans (arcsin_secant_one hu0 hu)
    rw [div_le_iff_of_neg (by linarith)] at h2
    linarith
  · have ha := arcsin_le_half_pi_mul hu0 (by linarith : u ≤ 1)
    have hb := arcsin_le_half_pi_mul (t := -s) (by linarith) (by linarith)
    rw [Real.arcsin_neg] at hb
    have hm : 0 ≤ π * (u - s) := mul_nonneg hp.le (by linarith)
    nlinarith

/-- **A second-order upper bound of `κ` at a point `u ∈ [0, 16/25]`, on all of `[−1, 1]`.** -/
theorem kappa_quad_gen {u s : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 16 / 25) (hs : s ∈ Icc (-1 : ℝ) 1) :
    kappa s ≤ kappa u + kg u * (s - u) + 25 / 36 * (s - u) ^ 2 := by
  have hp := Real.pi_pos
  have h := ge_of_deriv_sign
    (f := fun x : ℝ => (kappa u + kg u * (x - u) + 25 / 36 * (x - u) ^ 2) - kappa x)
    (f' := fun x : ℝ => (kg u + 2 * (25 / 36) * (x - u)) - (π - Real.arccos x) / π)
    (a := -1) (b := 1) (c := u)
    (by have := continuous_kappa; fun_prop)
    (fun x hx => (hasDerivAt_quadQ _ _ _ _ x).sub (hasDerivAt_kappa hx.1 hx.2))
    (by linarith) (by linarith)
    (by
      intro x hx
      simp only [kappa_deriv_eq, kg_eq]
      have ha := arcsin_slope_up hu0 hu hx.1 hx.2.le
      have hb : (Real.arcsin x - Real.arcsin u) / π ≤ 25 / 18 * (x - u) := by
        rw [div_le_iff₀ hp]; linarith
      rw [sub_div] at hb
      linarith)
    (by
      intro x hx
      simp only [kappa_deriv_eq, kg_eq]
      have ha := arcsin_slope_down hu0 hu hx.1.le hx.2
      have hb : (Real.arcsin u - Real.arcsin x) / π ≤ 25 / 18 * (u - x) := by
        rw [div_le_iff₀ hp]; linarith
      rw [sub_div] at hb
      linarith)
    s hs
  beta_reduce at h
  nlinarith

/-- **The second-order expansion of `κ∘κ` at a point of the window, sharp form.**
`b = kg(κ(q))·kg(q)` is the derivative of `κ∘κ` at `q`. -/
theorem kk_quad_at_sharp {q : ℝ} (h1 : 462 / 1000 ≤ q) (h2 : q ≤ 527 / 1000) :
    ∃ b : ℝ, 9 / 20 ≤ b ∧ b ≤ 1 / 2 ∧ ∀ s ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ kappa (kappa s) - kappa (kappa q) - b * (s - q) ∧
      kappa (kappa s) - kappa (kappa q) - b * (s - q) ≤ 6 / 5 * (s - q) ^ 2 := by
  have hl : (58392 / 100000 : ℝ) ≤ kappa q :=
    kappa_ge_of_le7 (a := 462 / 1000) (by norm_num) h1 (by linarith) (by norm_num)
  have hu : kappa q ≤ (62714 / 100000 : ℝ) :=
    kappa_le_of_le9 (a := 527 / 1000) (by linarith) h2 (by norm_num) (by norm_num)
  have hB1 : kg q ≤ 1 / 2 + 18 / 100 :=
    kg_le_of (a := 527 / 1000) h2 (by norm_num) (by norm_num) (by norm_num)
  have hB0 : 1 / 2 + 15 / 100 ≤ kg q :=
    kg_ge_of (a := 462 / 1000) h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hA1 : kg (kappa q) ≤ 1 / 2 + 22 / 100 :=
    kg_le_of (a := 62714 / 100000) hu (by norm_num) (by norm_num) (by norm_num)
  have hA0 : 1 / 2 + 195 / 1000 ≤ kg (kappa q) :=
    kg_ge_of (a := 58392 / 100000) hl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = kg (kappa q) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = kg q := ⟨_, rfl⟩
  rw [← hA] at hA0 hA1
  rw [← hB] at hB0 hB1
  have hq : q ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hkq : kappa q ∈ Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  refine ⟨A * B, by nlinarith, by nlinarith, fun s hs => ?_⟩
  have ms := kappa_mem hs.1 hs.2
  have hks : kappa s ∈ Icc (-1 : ℝ) 1 := ⟨by linarith [ms.1], ms.2⟩
  have t1 := kappa_tangent_ge hks hkq
  have t2 := kappa_tangent_ge hs hq
  have u1 := kappa_quad_gen (u := kappa q) (by linarith) (by linarith) hks
  have u2 := kappa_quad_gen (u := q) (by linarith) (by linarith) hs
  rw [← hA] at t1 u1
  rw [← hB] at t2 u2
  obtain ⟨d, hd⟩ : ∃ d : ℝ, d = kappa s - kappa q := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = s - q := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : ℝ, F = kappa (kappa s) - kappa (kappa q) := ⟨_, rfl⟩
  have t1' : A * d ≤ F := by rw [hd, hF]; linarith
  have t2' : B * e ≤ d := by rw [hd, he]; linarith
  have u1' : F ≤ A * d + 25 / 36 * d ^ 2 := by rw [hd, hF]; linarith
  have u2' : d ≤ B * e + 25 / 36 * e ^ 2 := by rw [hd, he]; linarith
  have hde : d ^ 2 ≤ e ^ 2 := by
    rcases le_total q s with h | h
    · have := kappa_lipschitz hq.1 h hs.2
      have hd0 : 0 ≤ d := by rw [hd]; exact this.1
      have hd1 : d ≤ e := by rw [hd, he]; exact this.2
      nlinarith
    · have := kappa_lipschitz hs.1 h hq.2
      have hd0 : 0 ≤ -d := by rw [hd]; linarith [this.1]
      have hd1 : -d ≤ -e := by rw [hd, he]; linarith [this.2]
      nlinarith
  have hA' : 0 ≤ A := by linarith
  have e1 : kappa (kappa s) - kappa (kappa q) - A * B * (s - q) = F - A * B * e := by
    rw [hF, he]
  rw [e1, ← he]
  have m1 := mul_le_mul_of_nonneg_left t2' hA'
  have m2 := mul_le_mul_of_nonneg_left u2' hA'
  have m3 : A * e ^ 2 ≤ (1 / 2 + 22 / 100) * e ^ 2 :=
    mul_le_mul_of_nonneg_right hA1 (sq_nonneg e)
  constructor
  · linarith
  · linarith

/-- **The second-order expansion of `κ∘κ` at a point of the window.** -/
theorem kk_quad_at {q : ℝ} (h1 : 462 / 1000 ≤ q) (h2 : q ≤ 527 / 1000) :
    ∃ b : ℝ, 0 ≤ b ∧ b ≤ 1 / 2 ∧ ∀ s ∈ Set.Icc (-1 : ℝ) 1,
      |kappa (kappa s) - kappa (kappa q) - b * (s - q)| ≤ 5 / 2 * (s - q) ^ 2 := by
  obtain ⟨b, hb0, hb1, h⟩ := kk_quad_at_sharp h1 h2
  refine ⟨b, by linarith, hb1, fun s hs => ?_⟩
  obtain ⟨a, c⟩ := h s hs
  rw [abs_of_nonneg a]
  nlinarith [sq_nonneg (s - q)]

end BstLean.Part149

#print axioms BstLean.Part149.kk_quad_at_sharp
#print axioms BstLean.Part149.kk_quad_at
