import BstLean.Part150Rep

/-!
# Part 150, item 2: pointwise bounds of `dChar J t = e^{−t²/2} − cos(t/√J)^J`

Paper source: `onW45-opus-prover.md` §2, Lemma B-F, Step 2 (the three regions).

* Taylor bounds: `exp_neg_le2`, `exp_neg_ge3`, `exp_neg_le4`, `cos_le4`, `sin_le5`, `cos_ge6`.
* `cos_le_exp`: `cos u ≤ e^{−u²/2}` for `0 ≤ u ≤ 2`.
* `exp_sub_cos_le`: `e^{−u²/2} − cos u ≤ u⁴/12` for `0 ≤ u ≤ 1`.
* `RegA c`: the statement of Region A with the constant `c`:
  `e^{−Ju²/2} − cos(u)^J ≤ c·J·u⁴·e^{−Ju²/2}` for `0 ≤ u ≤ 1`. `regA_sqrt_e : RegA (√e/12)`.
  (The paper has `κ_4 = −ln cos 1 − 1/2 = 0.1156…`; `√e/12 = 0.1374…`.)
* `dChar_A`, `dChar_B`, `dChar_C`: the three regions.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part150

open MeasureTheory ProbabilityTheory Real Set Filter Topology

/-- A function with `f 0 = 0` and a nonnegative derivative on `[0, ∞)` is nonnegative there. -/
lemma nonneg_of_deriv_nonneg {f f' : ℝ → ℝ} (h0 : f 0 = 0) (hd : ∀ x, HasDerivAt f (f' x) x)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ f' x) : ∀ x, 0 ≤ x → 0 ≤ f x := by
  have hm : MonotoneOn f (Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [interior_Ici] at hx
    rw [(hd x).deriv]
    exact hpos x (le_of_lt hx)
  intro x hx
  have := hm (Set.mem_Ici.mpr (le_refl (0 : ℝ))) (Set.mem_Ici.mpr hx) hx
  rwa [h0] at this

lemma hasDerivAt_exp_neg (x : ℝ) : HasDerivAt (fun w : ℝ => rexp (-w)) (-rexp (-x)) x := by
  have h := (hasDerivAt_neg x).exp
  convert h using 1; ring

lemma exp_neg_le2 {w : ℝ} (hw : 0 ≤ w) : rexp (-w) ≤ 1 - w + w ^ 2 / 2 := by
  have h := nonneg_of_deriv_nonneg (f := fun w => (1 - w + w ^ 2 / 2) - rexp (-w))
    (f' := fun w => (0 - 1 + w) - -rexp (-w)) (by simp) (fun x => by
      have h2 : HasDerivAt (fun w : ℝ => w ^ 2 / 2) x x := by
        have := (hasDerivAt_pow 2 x).div_const 2
        convert this using 1; ring
      exact ((((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add h2).sub
        (hasDerivAt_exp_neg x)))
    (fun x _ => by have := Real.add_one_le_exp (-x); linarith) w hw
  linarith

lemma exp_neg_ge3 {w : ℝ} (hw : 0 ≤ w) : 1 - w + w ^ 2 / 2 - w ^ 3 / 6 ≤ rexp (-w) := by
  have h := nonneg_of_deriv_nonneg (f := fun w => rexp (-w) - (1 - w + w ^ 2 / 2 - w ^ 3 / 6))
    (f' := fun w => -rexp (-w) - (0 - 1 + w - w ^ 2 / 2)) (by simp) (fun x => by
      have h2 : HasDerivAt (fun w : ℝ => w ^ 2 / 2) x x := by
        have := (hasDerivAt_pow 2 x).div_const 2
        convert this using 1; ring
      have h3 : HasDerivAt (fun w : ℝ => w ^ 3 / 6) (x ^ 2 / 2) x := by
        have := (hasDerivAt_pow 3 x).div_const 6
        convert this using 1; ring
      exact (hasDerivAt_exp_neg x).sub
        ((((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add h2).sub h3))
    (fun x hx => by have := exp_neg_le2 hx; linarith) w hw
  linarith

lemma exp_neg_le4 {w : ℝ} (hw : 0 ≤ w) :
    rexp (-w) ≤ 1 - w + w ^ 2 / 2 - w ^ 3 / 6 + w ^ 4 / 24 := by
  have h := nonneg_of_deriv_nonneg
    (f := fun w => (1 - w + w ^ 2 / 2 - w ^ 3 / 6 + w ^ 4 / 24) - rexp (-w))
    (f' := fun w => (0 - 1 + w - w ^ 2 / 2 + w ^ 3 / 6) - -rexp (-w)) (by simp) (fun x => by
      have h2 : HasDerivAt (fun w : ℝ => w ^ 2 / 2) x x := by
        have := (hasDerivAt_pow 2 x).div_const 2
        convert this using 1; ring
      have h3 : HasDerivAt (fun w : ℝ => w ^ 3 / 6) (x ^ 2 / 2) x := by
        have := (hasDerivAt_pow 3 x).div_const 6
        convert this using 1; ring
      have h4 : HasDerivAt (fun w : ℝ => w ^ 4 / 24) (x ^ 3 / 6) x := by
        have := (hasDerivAt_pow 4 x).div_const 24
        convert this using 1; ring
      exact (((((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).add h2).sub h3).add h4).sub
        (hasDerivAt_exp_neg x))
    (fun x hx => by have := exp_neg_ge3 hx; linarith) w hw
  linarith

lemma cos_le4 (u : ℝ) : Real.cos u ≤ 1 - u ^ 2 / 2 + u ^ 4 / 24 := by
  have hpos : ∀ u : ℝ, 0 ≤ u → Real.cos u ≤ 1 - u ^ 2 / 2 + u ^ 4 / 24 := by
    intro u hu
    have h := nonneg_of_deriv_nonneg (f := fun u => (1 - u ^ 2 / 2 + u ^ 4 / 24) - Real.cos u)
      (f' := fun u => (0 - u + u ^ 3 / 6) - -Real.sin u) (by simp) (fun x => by
        have h2 : HasDerivAt (fun w : ℝ => w ^ 2 / 2) x x := by
          have := (hasDerivAt_pow 2 x).div_const 2
          convert this using 1; ring
        have h4 : HasDerivAt (fun w : ℝ => w ^ 4 / 24) (x ^ 3 / 6) x := by
          have := (hasDerivAt_pow 4 x).div_const 24
          convert this using 1; ring
        exact ((((hasDerivAt_const x (1 : ℝ)).sub h2).add h4).sub (Real.hasDerivAt_cos x)))
      (fun x hx => by
        rcases hx.eq_or_lt with rfl | hx
        · simp
        · have := Real.sin_gt_sub_cube hx; linarith) u hu
    linarith
  rcases le_total 0 u with hu | hu
  · exact hpos u hu
  · have := hpos (-u) (neg_nonneg.mpr hu)
    rw [Real.cos_neg, show (-u) ^ 2 = u ^ 2 by ring, show (-u) ^ 4 = u ^ 4 by ring] at this
    exact this

lemma sin_le5 {u : ℝ} (hu : 0 ≤ u) : Real.sin u ≤ u - u ^ 3 / 6 + u ^ 5 / 120 := by
  have h := nonneg_of_deriv_nonneg (f := fun u => (u - u ^ 3 / 6 + u ^ 5 / 120) - Real.sin u)
    (f' := fun u => (1 - u ^ 2 / 2 + u ^ 4 / 24) - Real.cos u) (by simp) (fun x => by
      have h3 : HasDerivAt (fun w : ℝ => w ^ 3 / 6) (x ^ 2 / 2) x := by
        have := (hasDerivAt_pow 3 x).div_const 6
        convert this using 1; ring
      have h5 : HasDerivAt (fun w : ℝ => w ^ 5 / 120) (x ^ 4 / 24) x := by
        have := (hasDerivAt_pow 5 x).div_const 120
        convert this using 1; ring
      exact ((((hasDerivAt_id x).sub h3).add h5).sub (Real.hasDerivAt_sin x)))
    (fun x _ => by have := cos_le4 x; linarith) u hu
  linarith

lemma cos_ge6 (u : ℝ) : 1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 ≤ Real.cos u := by
  have hpos : ∀ u : ℝ, 0 ≤ u → 1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720 ≤ Real.cos u := by
    intro u hu
    have h := nonneg_of_deriv_nonneg
      (f := fun u => Real.cos u - (1 - u ^ 2 / 2 + u ^ 4 / 24 - u ^ 6 / 720))
      (f' := fun u => -Real.sin u - (0 - u + u ^ 3 / 6 - u ^ 5 / 120)) (by simp) (fun x => by
        have h2 : HasDerivAt (fun w : ℝ => w ^ 2 / 2) x x := by
          have := (hasDerivAt_pow 2 x).div_const 2
          convert this using 1; ring
        have h4 : HasDerivAt (fun w : ℝ => w ^ 4 / 24) (x ^ 3 / 6) x := by
          have := (hasDerivAt_pow 4 x).div_const 24
          convert this using 1; ring
        have h6 : HasDerivAt (fun w : ℝ => w ^ 6 / 720) (x ^ 5 / 120) x := by
          have := (hasDerivAt_pow 6 x).div_const 720
          convert this using 1; ring
        exact (Real.hasDerivAt_cos x).sub
          ((((hasDerivAt_const x (1 : ℝ)).sub h2).add h4).sub h6))
      (fun x hx => by have := sin_le5 hx; linarith) u hu
    linarith
  rcases le_total 0 u with hu | hu
  · exact hpos u hu
  · have := hpos (-u) (neg_nonneg.mpr hu)
    rw [Real.cos_neg, show (-u) ^ 2 = u ^ 2 by ring, show (-u) ^ 4 = u ^ 4 by ring,
      show (-u) ^ 6 = u ^ 6 by ring] at this
    exact this

/-- `cos u ≤ e^{−u²/2}` for `|u| ≤ 2` (so on `[−π/2, π/2]`). -/
theorem cos_le_exp {u : ℝ} (hu : |u| ≤ 2) : Real.cos u ≤ rexp (-(u ^ 2 / 2)) := by
  have h1 := cos_le4 u
  have h2 := exp_neg_ge3 (w := u ^ 2 / 2) (by positivity)
  have hu2 : u ^ 2 ≤ 4 := by
    have := sq_le_sq' (neg_le_of_abs_le hu) (le_of_abs_le hu); linarith
  nlinarith [sq_nonneg (u ^ 2), mul_nonneg (sq_nonneg (u ^ 2)) (sub_nonneg.mpr hu2)]

/-- `e^{−u²/2} − cos u ≤ u⁴/12` for `|u| ≤ 1`. -/
theorem exp_sub_cos_le {u : ℝ} (hu : |u| ≤ 1) : rexp (-(u ^ 2 / 2)) - Real.cos u ≤ u ^ 4 / 12 := by
  have h1 := cos_ge6 u
  have h2 := exp_neg_le4 (w := u ^ 2 / 2) (by positivity)
  have hu2 : u ^ 2 ≤ 1 := by
    have := sq_le_sq' (neg_le_of_abs_le hu) (le_of_abs_le hu); linarith
  nlinarith [sq_nonneg (u ^ 3), mul_nonneg (sq_nonneg (u ^ 3)) (sub_nonneg.mpr hu2),
    sq_nonneg (u ^ 2)]

lemma pow_sub_pow_le_mul {a b : ℝ} (hb : 0 ≤ b) (hab : b ≤ a) (J : ℕ) :
    a * (a ^ J - b ^ J) ≤ J * (a - b) * a ^ J := by
  have ha : 0 ≤ a := hb.trans hab
  induction J with
  | zero => simp
  | succ J ih =>
    have hbJ : b ^ J ≤ a ^ J := pow_le_pow_left₀ hb hab J
    have e : a * (a ^ (J + 1) - b ^ (J + 1)) =
        a * (a * (a ^ J - b ^ J)) + a * (b ^ J * (a - b)) := by ring
    rw [e]
    have h1 : a * (a * (a ^ J - b ^ J)) ≤ a * (J * (a - b) * a ^ J) :=
      mul_le_mul_of_nonneg_left ih ha
    have h2 : a * (b ^ J * (a - b)) ≤ a * (a ^ J * (a - b)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hbJ (sub_nonneg.mpr hab)) ha
    calc a * (a * (a ^ J - b ^ J)) + a * (b ^ J * (a - b))
        ≤ a * (J * (a - b) * a ^ J) + a * (a ^ J * (a - b)) := add_le_add h1 h2
      _ = ((J + 1 : ℕ) : ℝ) * (a - b) * a ^ (J + 1) := by push_cast; ring

/-- The statement of Region A with the constant `c`. -/
def RegA (c : ℝ) : Prop :=
  ∀ (J : ℕ) (u : ℝ), 0 ≤ u → u ≤ 1 →
    rexp (-((J : ℝ) * u ^ 2 / 2)) - Real.cos u ^ J ≤ c * J * u ^ 4 * rexp (-((J : ℝ) * u ^ 2 / 2))

lemma exp_pow_J (J : ℕ) (u : ℝ) : rexp (-(u ^ 2 / 2)) ^ J = rexp (-((J : ℝ) * u ^ 2 / 2)) := by
  rw [← Real.exp_nat_mul]; congr 1; ring

/-- Region A holds with the constant `√e/12`. -/
theorem regA_sqrt_e : RegA (rexp (1 / 2) / 12) := by
  intro J u hu0 hu1
  have habs : |u| ≤ 1 := by rw [abs_of_nonneg hu0]; exact hu1
  set a := rexp (-(u ^ 2 / 2)) with ha
  have hapos : 0 < a := Real.exp_pos _
  have hcos0 : 0 ≤ Real.cos u :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos])
      (by linarith [Real.pi_gt_three])
  have hle : Real.cos u ≤ a := cos_le_exp (by linarith)
  have hd : a - Real.cos u ≤ u ^ 4 / 12 := exp_sub_cos_le habs
  have h := pow_sub_pow_le_mul hcos0 hle J
  have hinv : a⁻¹ ≤ rexp (1 / 2) := by
    rw [ha, ← Real.exp_neg]
    apply Real.exp_le_exp.mpr
    nlinarith
  rw [← exp_pow_J]
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have haJ : 0 ≤ a ^ J := by positivity
  have h3 : a ^ J - Real.cos u ^ J ≤ a⁻¹ * (J * (a - Real.cos u) * a ^ J) := by
    rw [← div_eq_inv_mul, le_div_iff₀ hapos]; linarith
  refine h3.trans ?_
  have h4 : (J : ℝ) * (a - Real.cos u) * a ^ J ≤ J * (u ^ 4 / 12) * a ^ J := by
    gcongr
  calc a⁻¹ * (J * (a - Real.cos u) * a ^ J) ≤ rexp (1 / 2) * (J * (u ^ 4 / 12) * a ^ J) := by
        refine mul_le_mul hinv h4 ?_ (Real.exp_pos _).le
        exact mul_nonneg (mul_nonneg hJ0 (sub_nonneg.mpr hle)) haJ
    _ = rexp (1 / 2) / 12 * J * u ^ 4 * a ^ J := by ring

/-! ## The three regions for `dChar` -/

lemma dChar_eq {J : ℕ} (hJ : 1 ≤ J) (t : ℝ) :
    dChar J t = rexp (-((J : ℝ) * (t / √(J : ℝ)) ^ 2 / 2)) - Real.cos (t / √(J : ℝ)) ^ J := by
  unfold dChar
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  rw [div_pow, Real.sq_sqrt hJ0.le]
  congr 3
  field_simp

/-- Regions A and B: `0 ≤ dChar J t ≤ e^{−t²/2}` for `0 ≤ t ≤ 2√J`. -/
theorem dChar_B {J : ℕ} (hJ : 1 ≤ J) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ π / 2 * √(J : ℝ)) :
    0 ≤ dChar J t ∧ dChar J t ≤ rexp (-(t ^ 2 / 2)) := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have hs : 0 < √(J : ℝ) := Real.sqrt_pos.mpr hJ0
  have hu0 : 0 ≤ t / √(J : ℝ) := div_nonneg ht0 hs.le
  have hu1 : t / √(J : ℝ) ≤ π / 2 := by rw [div_le_iff₀ hs]; exact ht
  have hcos0 : 0 ≤ Real.cos (t / √(J : ℝ)) :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hu1
  have hle : Real.cos (t / √(J : ℝ)) ≤ rexp (-((t / √(J : ℝ)) ^ 2 / 2)) :=
    cos_le_exp (by rw [abs_of_nonneg hu0]; linarith [Real.pi_le_four])
  have hp := pow_le_pow_left₀ hcos0 hle J
  rw [exp_pow_J] at hp
  constructor
  · rw [dChar_eq hJ]; linarith
  · unfold dChar; linarith [pow_nonneg hcos0 J]

/-- Region A: `0 ≤ dChar J t ≤ c·t⁴·e^{−t²/2}/J` for `0 ≤ t ≤ √J`. -/
theorem dChar_A {c : ℝ} (hc : RegA c) {J : ℕ} (hJ : 1 ≤ J) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : t ≤ √(J : ℝ)) : dChar J t ≤ c * t ^ 4 * rexp (-(t ^ 2 / 2)) / J := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  have hs : 0 < √(J : ℝ) := Real.sqrt_pos.mpr hJ0
  have hu0 : 0 ≤ t / √(J : ℝ) := div_nonneg ht0 hs.le
  have hu1 : t / √(J : ℝ) ≤ 1 := by rw [div_le_iff₀ hs]; linarith
  have h := hc J (t / √(J : ℝ)) hu0 hu1
  rw [← dChar_eq hJ] at h
  refine h.trans (le_of_eq ?_)
  have e1 : (J : ℝ) * (t / √(J : ℝ)) ^ 2 / 2 = t ^ 2 / 2 := by
    rw [div_pow, Real.sq_sqrt hJ0.le]; field_simp
  have e2 : (t / √(J : ℝ)) ^ 4 = t ^ 4 / (J : ℝ) ^ 2 := by
    rw [div_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul (√(J : ℝ)), Real.sq_sqrt hJ0.le]
  rw [e1, e2]
  field_simp

/-- Region C (every `t`): `|dChar J t| ≤ e^{−t²/2} + |cos(t/√J)|^J`. -/
theorem dChar_C (J : ℕ) (t : ℝ) :
    |dChar J t| ≤ rexp (-(t ^ 2 / 2)) + |Real.cos (t / √(J : ℝ))| ^ J := by
  unfold dChar
  refine (abs_sub _ _).trans ?_
  rw [abs_of_pos (Real.exp_pos _), abs_pow]

end BstLean.Part150
