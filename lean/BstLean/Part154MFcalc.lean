import BstLean.Part154Defs

/-!
# Part 154: Lemma MF, the real analysis (the function `𝒢(τ, v) = ψ_{√v}(τ)`)
Statements fixed by the lead agent.
-/

namespace BstLean.Part154

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (relu reluV normSq)
open BstLean.Part137 (psiS)
open BstLean.Part153 (phiG PhiG psiG nrm)
open BstLean.Part153 (hasDerivAt_PhiG hasDerivAt_phiG phiG_pos PhiG_pos PhiG_le_one)

/-! ### Auxiliary facts -/

lemma phiG_zero_eq : phiG 0 = (√(2 * π))⁻¹ := by
  unfold phiG; simp

lemma phiG_zero_sq : phiG 0 ^ 2 = 1 / (2 * π) := by
  rw [phiG_zero_eq, inv_pow, Real.sq_sqrt (by positivity)]; simp

lemma phiG_le_zero (z : ℝ) : phiG z ≤ phiG 0 := by
  rw [phiG_zero_eq]; unfold phiG
  have h : rexp (-(z ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z])
  have hc : (0 : ℝ) ≤ (√(2 * π))⁻¹ := by positivity
  calc (√(2 * π))⁻¹ * rexp (-(z ^ 2 / 2)) ≤ (√(2 * π))⁻¹ * 1 := by gcongr
    _ = _ := mul_one _

/-- `sup_z |z|φ(z) = φ(1)`. -/
lemma abs_mul_phiG_le (z : ℝ) : |z| * phiG z ≤ phiG 1 := by
  unfold phiG
  have hc : (0 : ℝ) ≤ (√(2 * π))⁻¹ := by positivity
  have h1 : |z| ≤ rexp ((z ^ 2 - 1) / 2) := by
    have := Real.add_one_le_exp ((z ^ 2 - 1) / 2)
    have h2 : |z| ≤ (z ^ 2 - 1) / 2 + 1 := by
      nlinarith [sq_nonneg (|z| - 1), sq_abs z]
    linarith
  have h3 : |z| * rexp (-(z ^ 2 / 2)) ≤ rexp (-((1 : ℝ) ^ 2 / 2)) := by
    have e : rexp (-((1 : ℝ) ^ 2 / 2)) = rexp ((z ^ 2 - 1) / 2) * rexp (-(z ^ 2 / 2)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [e]; gcongr
  calc |z| * ((√(2 * π))⁻¹ * rexp (-(z ^ 2 / 2)))
      = (√(2 * π))⁻¹ * (|z| * rexp (-(z ^ 2 / 2))) := by ring
    _ ≤ (√(2 * π))⁻¹ * rexp (-((1 : ℝ) ^ 2 / 2)) := by gcongr

/-- `|z² − 1|φ(z) ≤ φ(0)`. -/
lemma abs_sq_sub_one_mul_phiG_le (z : ℝ) : |z ^ 2 - 1| * phiG z ≤ phiG 0 := by
  rw [phiG_zero_eq]; unfold phiG
  have hc : (0 : ℝ) ≤ (√(2 * π))⁻¹ := by positivity
  have h3 : |z ^ 2 - 1| * rexp (-(z ^ 2 / 2)) ≤ 1 := by
    have hpos : 0 < rexp (-(z ^ 2 / 2)) := Real.exp_pos _
    have hle : rexp (-(z ^ 2 / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg z])
    rcases le_total (z ^ 2) 1 with h | h
    · rw [abs_of_nonpos (by linarith)]
      nlinarith [sq_nonneg z]
    · rw [abs_of_nonneg (by linarith)]
      have h1 : z ^ 2 / 2 ≤ rexp (z ^ 2 / 2 - 1) := by
        have := Real.add_one_le_exp (z ^ 2 / 2 - 1); linarith
      have h2 : (2 : ℝ) ≤ rexp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
      have e : rexp (z ^ 2 / 2) = rexp (z ^ 2 / 2 - 1) * rexp 1 := by
        rw [← Real.exp_add]; congr 1; ring
      have h4 : z ^ 2 - 1 ≤ rexp (z ^ 2 / 2) := by
        rw [e]; nlinarith [Real.exp_pos (z ^ 2 / 2 - 1)]
      have e2 : rexp (z ^ 2 / 2) * rexp (-(z ^ 2 / 2)) = 1 := by
        rw [← Real.exp_add]; simp
      calc (z ^ 2 - 1) * rexp (-(z ^ 2 / 2)) ≤ rexp (z ^ 2 / 2) * rexp (-(z ^ 2 / 2)) := by gcongr
        _ = 1 := e2
  calc |z ^ 2 - 1| * ((√(2 * π))⁻¹ * rexp (-(z ^ 2 / 2)))
      = (√(2 * π))⁻¹ * (|z ^ 2 - 1| * rexp (-(z ^ 2 / 2))) := by ring
    _ ≤ (√(2 * π))⁻¹ * 1 := by gcongr
    _ = _ := mul_one _

/-- `Φ` is `φ(0)`-Lipschitz. -/
lemma PhiG_lip (x y : ℝ) : |PhiG x - PhiG y| ≤ phiG 0 * |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := PhiG) (f' := phiG)
    (s := Set.univ) (C := phiG 0) (fun x _ => (hasDerivAt_PhiG x).hasDerivWithinAt)
    (fun x _ => by rw [Real.norm_eq_abs, abs_of_pos (phiG_pos x)]; exact phiG_le_zero x)
    convex_univ (Set.mem_univ y) (Set.mem_univ x)
  simpa [Real.norm_eq_abs] using h

/-- Second-order Taylor bound on `[0, 1]`. -/
lemma taylor2 {h h1 h2 : ℝ → ℝ} {M : ℝ}
    (H1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h (h1 t) t)
    (H2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt h1 (h2 t) t)
    (HM : ∀ t ∈ Set.Icc (0 : ℝ) 1, |h2 t| ≤ M) :
    |h 1 - h 0 - h1 0| ≤ M / 2 := by
  have h0mem : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1mem : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have step : ∀ t ∈ Set.Icc (0 : ℝ) 1, |h1 t - h1 0| ≤ M * t := by
    intro t ht
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := h1) (f' := h2)
      (s := Set.Icc (0 : ℝ) 1) (C := M) (fun x hx => (H2 x hx).hasDerivWithinAt)
      (fun x hx => by rw [Real.norm_eq_abs]; exact HM x hx) (convex_Icc 0 1) h0mem ht
    simpa [Real.norm_eq_abs, abs_of_nonneg ht.1] using this
  have hint : ∀ x ∈ interior (Set.Icc (0 : ℝ) 1), x ∈ Set.Icc (0 : ℝ) 1 :=
    fun x hx => interior_subset hx
  -- upper bound
  have dU : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => h t - h1 0 * t - M * t ^ 2 / 2) (h1 t - h1 0 - M * t) t := by
    intro t ht
    have a1 : HasDerivAt (fun t => h t - h1 0 * t - M * t ^ 2 / 2)
        (h1 t - h1 0 * 1 - M * ((2 : ℕ) * t ^ (2 - 1)) / 2) t :=
      ((H1 t ht).sub ((hasDerivAt_id' t).const_mul (h1 0))).sub
        (((hasDerivAt_pow 2 t).const_mul M).div_const 2)
    convert a1 using 1
    first | (norm_num; done) | (norm_num; ring)
  have dL : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => h t - h1 0 * t + M * t ^ 2 / 2) (h1 t - h1 0 + M * t) t := by
    intro t ht
    have a1 : HasDerivAt (fun t => h t - h1 0 * t + M * t ^ 2 / 2)
        (h1 t - h1 0 * 1 + M * ((2 : ℕ) * t ^ (2 - 1)) / 2) t :=
      ((H1 t ht).sub ((hasDerivAt_id' t).const_mul (h1 0))).add
        (((hasDerivAt_pow 2 t).const_mul M).div_const 2)
    convert a1 using 1
    first | (norm_num; done) | (norm_num; ring)
  have aU : AntitoneOn (fun t => h t - h1 0 * t - M * t ^ 2 / 2) (Set.Icc (0 : ℝ) 1) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      (fun t ht => (dU t ht).continuousAt.continuousWithinAt)
      (fun t ht => (dU t (hint t ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [(dU t (hint t ht)).deriv]
        have := abs_le.mp (step t (hint t ht)); linarith)
  have aL : MonotoneOn (fun t => h t - h1 0 * t + M * t ^ 2 / 2) (Set.Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
      (fun t ht => (dL t ht).continuousAt.continuousWithinAt)
      (fun t ht => (dL t (hint t ht)).differentiableAt.differentiableWithinAt)
      (fun t ht => by
        rw [(dL t (hint t ht)).deriv]
        have := abs_le.mp (step t (hint t ht)); linarith)
  have u := aU h0mem h1mem zero_le_one
  have l := aL h0mem h1mem zero_le_one
  simp only at u l
  rw [abs_le]; constructor <;> linarith

/-- `√v ≥ s/√2` in the form `s ≤ √v·√2`. -/
lemma sqrt_lower {s v : ℝ} (_hs : 0 < s) (hv : s ^ 2 / 2 ≤ v) : s ≤ √v * √2 := by
  rw [← Real.sqrt_mul (by nlinarith [sq_nonneg s])]
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- `ψ_s(a) = aΦ(a/s) + sφ(a/s)` for `s > 0`. -/
theorem psiS_closed {s : ℝ} (hs : 0 < s) (a : ℝ) :
    psiS s a = a * PhiG (a / s) + s * phiG (a / s) := by
  rw [BstLean.Part153.psiS_scale hs, BstLean.Part153.psiS_one]
  unfold psiG
  field_simp

/-- The step of the linear term: on `v ≥ s²/2`. -/
theorem PhiG_diff_le {s v a β : ℝ} (hs : 0 < s) (hv : s ^ 2 / 2 ≤ v) :
    |PhiG (β * a / √v) - PhiG (a / s)| ≤
      phiG 0 * |a| * (√2 * |β - 1| / s + 2 * (√2 - 1) * |v - s ^ 2| / s ^ 3) := by
  have hv0 : 0 < v := by nlinarith [sq_pos_of_pos hs]
  set u := √v with hu
  set r := √2 with hr
  have hu0 : 0 < u := Real.sqrt_pos.mpr hv0
  have hu2 : u ^ 2 = v := Real.sq_sqrt hv0.le
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr1 : 1 ≤ r := by nlinarith
  have hsu : s ≤ u * r := sqrt_lower hs hv
  have hφ : 0 < phiG 0 := phiG_pos 0
  -- 1/u ≤ r/s
  have i1 : 1 / u ≤ r / s := by
    rw [div_le_div_iff₀ hu0 hs]; nlinarith
  -- s³ ≤ 2(r − 1)·u·s·(s + u)
  have i2 : s ^ 3 ≤ 2 * (r - 1) * (u * s * (s + u)) := by
    have e1 : s ^ 3 = (r - 1) * s * s * (r * s + s) := by linear_combination (-s ^ 3) * hr2
    have e2 : 2 * (r - 1) * (u * s * (s + u)) = (r - 1) * (u * r) * s * (r * s + u * r) := by
      linear_combination (-(r - 1) * u * s * (s + u)) * hr2
    rw [e1, e2]
    have hr10 : 0 ≤ r - 1 := by linarith
    gcongr
  have i3 : |1 / u - 1 / s| ≤ 2 * (r - 1) * |v - s ^ 2| / s ^ 3 := by
    have e : 1 / u - 1 / s = -(v - s ^ 2) / (u * s * (s + u)) := by
      rw [← hu2]; field_simp; ring
    have hd : 0 < u * s * (s + u) := by positivity
    rw [e, abs_div, abs_neg, abs_of_pos hd, div_le_div_iff₀ hd (by positivity)]
    have := mul_le_mul_of_nonneg_left i2 (abs_nonneg (v - s ^ 2))
    nlinarith
  have key : |β * a / u - a / s| ≤ |a| * (r * |β - 1| / s + 2 * (r - 1) * |v - s ^ 2| / s ^ 3) := by
    have e : β * a / u - a / s = a * ((β - 1) * (1 / u) + (1 / u - 1 / s)) := by
      field_simp; ring
    rw [e, abs_mul]
    gcongr
    refine (abs_add_le _ _).trans (add_le_add ?_ i3)
    rw [abs_mul, abs_of_pos (by positivity : 0 < 1 / u)]
    calc |β - 1| * (1 / u) ≤ |β - 1| * (r / s) := by gcongr
      _ = r * |β - 1| / s := by ring
  calc |PhiG (β * a / u) - PhiG (a / s)| ≤ phiG 0 * |β * a / u - a / s| := PhiG_lip _ _
    _ ≤ phiG 0 * (|a| * (r * |β - 1| / s + 2 * (r - 1) * |v - s ^ 2| / s ^ 3)) := by gcongr
    _ = _ := by ring

theorem PhiG_diff_sq_le {s v a β : ℝ} (hs : 0 < s) (hv : s ^ 2 / 2 ≤ v) :
    (PhiG (β * a / √v) - PhiG (a / s)) ^ 2 ≤
      1 / (2 * π) * a ^ 2 *
        (4 * (β - 1) ^ 2 / s ^ 2 + 8 * (√2 - 1) ^ 2 * (v - s ^ 2) ^ 2 / s ^ 6) := by
  have h := PhiG_diff_le (a := a) (β := β) hs hv
  have hr2 : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set X := √2 * |β - 1| / s with hX
  set Y := 2 * (√2 - 1) * |v - s ^ 2| / s ^ 3 with hY
  have h2 : (PhiG (β * a / √v) - PhiG (a / s)) ^ 2 ≤ (phiG 0 * |a| * (X + Y)) ^ 2 := by
    rw [← sq_abs (PhiG (β * a / √v) - PhiG (a / s))]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have eX : 2 * X ^ 2 = 4 * (β - 1) ^ 2 / s ^ 2 := by
    rw [hX, div_pow, mul_pow, hr2, sq_abs]; ring
  have eY : 2 * Y ^ 2 = 8 * (√2 - 1) ^ 2 * (v - s ^ 2) ^ 2 / s ^ 6 := by
    rw [hY, div_pow, mul_pow, mul_pow, sq_abs]; ring
  have h3 : (X + Y) ^ 2 ≤ 2 * X ^ 2 + 2 * Y ^ 2 := by nlinarith [sq_nonneg (X - Y)]
  calc (PhiG (β * a / √v) - PhiG (a / s)) ^ 2 ≤ (phiG 0 * |a| * (X + Y)) ^ 2 := h2
    _ = phiG 0 ^ 2 * a ^ 2 * (X + Y) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
    _ ≤ phiG 0 ^ 2 * a ^ 2 * (2 * X ^ 2 + 2 * Y ^ 2) := by
        gcongr
    _ = _ := by rw [eX, eY, phiG_zero_sq]

theorem PhiG_diff_le_one (x y : ℝ) : (PhiG x - PhiG y) ^ 2 ≤ 1 := by
  have := PhiG_pos x; have := PhiG_pos y
  have := PhiG_le_one x; have := PhiG_le_one y
  have h : |PhiG x - PhiG y| ≤ 1 := by rw [abs_le]; constructor <;> linarith
  calc (PhiG x - PhiG y) ^ 2 = |PhiG x - PhiG y| ^ 2 := (sq_abs _).symm
    _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = 1 := one_pow 2

/-- **The second-order Taylor bound of `𝒢`** on `v ≥ s²/2`. -/
theorem G_taylor {s v a β : ℝ} (hs : 0 < s) (hv : s ^ 2 / 2 ≤ v) :
    |psiS (√v) (β * a) - psiS s a -
        (PhiG (a / s) * ((β - 1) * a) + phiG (a / s) / (2 * s) * (v - s ^ 2))| ≤
      1 / 2 * (√2 * phiG 0 / s * (a ^ 2 * (β - 1) ^ 2) +
        2 * phiG 1 / s ^ 2 * (|a| * |β - 1| * |v - s ^ 2|) +
        phiG 0 / (√2 * s ^ 3) * (v - s ^ 2) ^ 2) := by
  have hv0 : 0 < v := by nlinarith [sq_pos_of_pos hs]
  set r := √2 with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr (by norm_num)
  have hr2 : r ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  set dτ := (β - 1) * a with hdτ
  set dv := v - s ^ 2 with hdv
  let w : ℝ → ℝ := fun t => s ^ 2 + t * dv
  let u : ℝ → ℝ := fun t => √(w t)
  let τ : ℝ → ℝ := fun t => a + t * dτ
  let z : ℝ → ℝ := fun t => τ t / u t
  let H : ℝ → ℝ := fun t => τ t * PhiG (z t) + u t * phiG (z t)
  let H1 : ℝ → ℝ := fun t => PhiG (z t) * dτ + phiG (z t) * (dv / (2 * u t))
  let H2 : ℝ → ℝ := fun t => phiG (z t) / u t * dτ ^ 2 - z t * phiG (z t) / u t ^ 2 * (dτ * dv) +
    (z t ^ 2 - 1) * phiG (z t) / (4 * u t ^ 3) * dv ^ 2
  have hw : ∀ t ∈ Set.Icc (0 : ℝ) 1, s ^ 2 / 2 ≤ w t := by
    intro t ht
    have e : w t = (1 - t) * s ^ 2 + t * v := by simp only [w, hdv]; ring
    rw [e]; nlinarith [ht.1, ht.2, sq_pos_of_pos hs]
  have hw0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < w t := fun t ht => by
    have := hw t ht; nlinarith [sq_pos_of_pos hs]
  have hu0 : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < u t := fun t ht => Real.sqrt_pos.mpr (hw0 t ht)
  have hu2 : ∀ t ∈ Set.Icc (0 : ℝ) 1, u t ^ 2 = w t := fun t ht => Real.sq_sqrt (hw0 t ht).le
  have dw : ∀ t, HasDerivAt w dv t := by
    intro t
    have := ((hasDerivAt_id t).mul_const dv).const_add (s ^ 2)
    simpa [w] using this
  have dτ' : ∀ t, HasDerivAt τ dτ t := by
    intro t
    have := ((hasDerivAt_id t).mul_const dτ).const_add a
    simpa [τ] using this
  have du : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt u (dv / (2 * u t)) t := by
    intro t ht
    have := (Real.hasDerivAt_sqrt (hw0 t ht).ne').comp t (dw t)
    have e : dv / (2 * u t) = 1 / (2 * √(w t)) * dv := by simp only [u]; ring
    rw [e]; exact this
  have dz : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt z (dτ / u t - z t * dv / (2 * u t ^ 2)) t := by
    intro t ht
    have := (dτ' t).div (du t ht) (hu0 t ht).ne'
    convert this using 1
    have := (hu0 t ht).ne'
    simp only [z]; field_simp
  have dΦ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => PhiG (z t)) (phiG (z t) * (dτ / u t - z t * dv / (2 * u t ^ 2))) t :=
    fun t ht => (hasDerivAt_PhiG (z t)).comp t (dz t ht)
  have dφ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun t => phiG (z t))
        (-(z t * phiG (z t)) * (dτ / u t - z t * dv / (2 * u t ^ 2))) t :=
    fun t ht => (hasDerivAt_phiG (z t)).comp t (dz t ht)
  have dH : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt H (H1 t) t := by
    intro t ht
    have := ((dτ' t).mul (dΦ t ht)).add ((du t ht).mul (dφ t ht))
    convert this using 1
    have h0 := (hu0 t ht).ne'
    have hz : τ t = z t * u t := by simp only [z]; field_simp
    simp only [H1]; rw [hz]; field_simp; ring
  have dH1 : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt H1 (H2 t) t := by
    intro t ht
    have h0 := (hu0 t ht).ne'
    have dq : HasDerivAt (fun t => dv / (2 * u t)) (-(dv * (2 * (dv / (2 * u t)))) / (2 * u t) ^ 2) t := by
      have := (hasDerivAt_const t dv).div ((du t ht).const_mul 2) (by positivity)
      convert this using 1
      simp
    have := ((dΦ t ht).mul_const dτ).add ((dφ t ht).mul dq)
    convert this using 1
    simp only [H2]; field_simp; ring
  -- the bound of the second derivative
  set M := r * phiG 0 / s * (a ^ 2 * (β - 1) ^ 2) +
        2 * phiG 1 / s ^ 2 * (|a| * |β - 1| * |dv|) +
        phiG 0 / (r * s ^ 3) * dv ^ 2 with hM
  have hφ0 : 0 < phiG 0 := phiG_pos 0
  have hφ1 : 0 < phiG 1 := phiG_pos 1
  have bM : ∀ t ∈ Set.Icc (0 : ℝ) 1, |H2 t| ≤ M := by
    intro t ht
    have hut := hu0 t ht
    have hsu : s ≤ u t * r := sqrt_lower hs (hw t ht)
    have hu2' := hu2 t ht
    have hwt := hw t ht
    have hφz := phiG_pos (z t)
    -- the three coefficients
    have cA : |phiG (z t) / u t| ≤ r * phiG 0 / s := by
      rw [abs_of_pos (by positivity), div_le_div_iff₀ hut hs]
      have := phiG_le_zero (z t)
      calc phiG (z t) * s ≤ phiG 0 * (u t * r) := by gcongr
        _ = r * phiG 0 * u t := by ring
    have cB : |z t * phiG (z t) / u t ^ 2| ≤ 2 * phiG 1 / s ^ 2 := by
      rw [abs_div, abs_mul, abs_of_pos hφz, abs_of_pos (by positivity : 0 < u t ^ 2),
        div_le_div_iff₀ (by positivity) (by positivity)]
      have := abs_mul_phiG_le (z t)
      have h2 : s ^ 2 ≤ 2 * u t ^ 2 := by linarith
      calc |z t| * phiG (z t) * s ^ 2 ≤ phiG 1 * (2 * u t ^ 2) := by
            gcongr
        _ = 2 * phiG 1 * u t ^ 2 := by ring
    have cC : |(z t ^ 2 - 1) * phiG (z t) / (4 * u t ^ 3)| ≤ phiG 0 / (r * s ^ 3) := by
      rw [abs_div, abs_mul, abs_of_pos hφz, abs_of_pos (by positivity : 0 < 4 * u t ^ 3),
        div_le_div_iff₀ (by positivity) (by positivity)]
      have := abs_sq_sub_one_mul_phiG_le (z t)
      have h3 : r * s ^ 3 ≤ 4 * u t ^ 3 := by
        have h4 : s ^ 3 ≤ (u t * r) ^ 3 := pow_le_pow_left₀ hs.le hsu 3
        have e : (u t * r) ^ 3 = 2 * r * u t ^ 3 := by linear_combination (r * u t ^ 3) * hr2
        have e2 : 4 * u t ^ 3 = r * (2 * r * u t ^ 3) := by linear_combination (-2 * u t ^ 3) * hr2
        rw [e2]; rw [e] at h4; gcongr
      exact mul_le_mul this h3 (by positivity) hφ0.le
    have e1 : |dτ ^ 2| = a ^ 2 * (β - 1) ^ 2 := by rw [abs_of_nonneg (sq_nonneg _), hdτ]; ring
    have e2 : |dτ * dv| = |a| * |β - 1| * |dv| := by rw [abs_mul, hdτ, abs_mul]; ring
    have e3 : |dv ^ 2| = dv ^ 2 := abs_of_nonneg (sq_nonneg _)
    have key : |H2 t| ≤ (|phiG (z t) / u t| * |dτ ^ 2|) +
        (|z t * phiG (z t) / u t ^ 2| * |dτ * dv|) +
        (|(z t ^ 2 - 1) * phiG (z t) / (4 * u t ^ 3)| * |dv ^ 2|) := by
      simp only [H2, ← abs_mul]
      exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    rw [e1, e2, e3] at key
    have hA := mul_le_mul_of_nonneg_right cA (by positivity : (0 : ℝ) ≤ a ^ 2 * (β - 1) ^ 2)
    have hB := mul_le_mul_of_nonneg_right cB (by positivity : (0 : ℝ) ≤ |a| * |β - 1| * |dv|)
    have hC := mul_le_mul_of_nonneg_right cC (by positivity : (0 : ℝ) ≤ dv ^ 2)
    rw [hM]; linarith
  have T := taylor2 dH dH1 bM
  -- endpoints
  have eu0 : u 0 = s := by simp only [u, w]; rw [zero_mul, add_zero]; exact Real.sqrt_sq hs.le
  have eu1 : u 1 = √v := by simp only [u, w, hdv]; congr 1; ring
  have eτ0 : τ 0 = a := by simp [τ]
  have eτ1 : τ 1 = β * a := by simp only [τ, hdτ]; ring
  have eH0 : H 0 = psiS s a := by
    simp only [H, z]; rw [eu0, eτ0]; exact (psiS_closed hs a).symm
  have eH1 : H 1 = psiS (√v) (β * a) := by
    simp only [H, z]; rw [eu1, eτ1]; exact (psiS_closed (Real.sqrt_pos.mpr hv0) _).symm
  have eH10 : H1 0 = PhiG (a / s) * dτ + phiG (a / s) / (2 * s) * dv := by
    simp only [H1, z]; rw [eu0, eτ0]; ring
  rw [eH0, eH1, eH10] at T
  calc _ ≤ M / 2 := T
    _ = _ := by ring

/-- The bound off the good set (`v ≥ 0` only). -/
theorem G_rough {s v a β : ℝ} (hs : 0 < s) (hv : 0 ≤ v) :
    |psiS (√v) (β * a) - psiS s a -
        (PhiG (a / s) * ((β - 1) * a) + phiG (a / s) / (2 * s) * (v - s ^ 2))| ≤
      2 * (|β - 1| * |a|) + 3 / 2 * phiG 0 / s * |v - s ^ 2| := by
  have hφ0 : 0 < phiG 0 := phiG_pos 0
  have hu : 0 ≤ √v := Real.sqrt_nonneg v
  have hu2 : √v ^ 2 = v := Real.sq_sqrt hv
  -- |√v − s| ≤ |v − s²|/s
  have i1 : |√v - s| ≤ |v - s ^ 2| / s := by
    rw [le_div_iff₀ hs]
    have e : v - s ^ 2 = (√v - s) * (√v + s) := by linear_combination -hu2
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < √v + s)]
    exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
  have a1 : |psiS (√v) (β * a) - psiS (√v) a| ≤ |β - 1| * |a| := by
    refine (BstLean.Part141.psiS_lip_x _ _ _).trans (le_of_eq ?_)
    rw [← abs_mul]; congr 1; ring
  have a2 : |psiS (√v) a - psiS s a| ≤ phiG 0 / s * |v - s ^ 2| := by
    refine (BstLean.Part150.psiS_lip_s_phi _ _ _).trans ?_
    rw [phiG_zero_eq, one_div]
    calc (√(2 * π))⁻¹ * |√v - s| ≤ (√(2 * π))⁻¹ * (|v - s ^ 2| / s) := by gcongr
      _ = _ := by ring
  have a3 : |PhiG (a / s) * ((β - 1) * a)| ≤ |β - 1| * |a| := by
    rw [abs_mul, abs_mul, abs_of_pos (PhiG_pos _)]
    exact mul_le_of_le_one_left (by positivity) (PhiG_le_one _)
  have a4 : |phiG (a / s) / (2 * s) * (v - s ^ 2)| ≤ 1 / 2 * (phiG 0 / s * |v - s ^ 2|) := by
    rw [abs_mul, abs_of_pos (by have := phiG_pos (a / s); positivity)]
    have := phiG_le_zero (a / s)
    calc phiG (a / s) / (2 * s) * |v - s ^ 2| ≤ phiG 0 / (2 * s) * |v - s ^ 2| := by gcongr
      _ = _ := by ring
  have a5 : 0 ≤ phiG 0 / s * |v - s ^ 2| := by positivity
  have e : 3 / 2 * phiG 0 / s * |v - s ^ 2| = 3 / 2 * (phiG 0 / s * |v - s ^ 2|) := by ring
  rw [e]
  rw [abs_le] at a1 a2 a3 a4 ⊢
  obtain ⟨a11, a12⟩ := a1
  obtain ⟨a21, a22⟩ := a2
  obtain ⟨a31, a32⟩ := a3
  obtain ⟨a41, a42⟩ := a4
  constructor <;> linarith

end BstLean.Part154
