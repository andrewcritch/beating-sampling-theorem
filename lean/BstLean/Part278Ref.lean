import BstLean.Part272Stated

/-!
# Part 278 (O1): the exact odd reference of the sphere moments

Paper: `theorem7-01-statement-program.tex`, Lemma `t7:p01:moments`, odd part.
For odd `n`, `P = (n−5)/2`, the law of the first coordinate of a uniform direction in
`ℝ^{n−1}` has density proportional to `(1 − z²)^{P + 1/2}`.

* `KK r d = K_r(d)`: `K₀(d) = π/2 − arcsin d`,
  `K_r(d) = (2r−1)/(2r)·K_{r−1}(d) − d(1−d²)^{r−1/2}/(2r)`.
* `KK_integral`: `K_r(d) = ∫_d^1 (1 − z²)^{r − 1/2} dz` for `|d| ≤ 1`.
* `KK_neg_one`: `K_{P+1}(−1) = π/D_P` (so `𝒩_P = D_P/π`).
* `sph_oddRef`: for odd `n ≥ 9` and `k ≥ 0`, `E ReLU(m + kT) = sphAoddRef n m k` and
  `E ReLU(m + kT)² = sphEoddRef n m k`.

The reference rule `sphAoddRef`, `sphEoddRef` has the form of `Part272.sphAodd`,
`Part272.sphEodd` with exact `π` and exact `arcsin`, and without the two clips.
-/

namespace BstLean.Part278

open Real MeasureTheory Set
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 measurable_unitF)
open BstLean.Part130 (relu measurable_relu continuous_relu)
open BstLean.Part272 (DD coord_law coord_mem coord_mean_at coord_sq_at integrable_coord
  integrable_coord_sq relu_bound relu_sq_bound)

/-! ## `K_r` and its integral form -/

/-- The exact `K_r(d)`, by the recurrence of the paper. -/
noncomputable def KK : ℕ → ℝ → ℝ
  | 0, d => π / 2 - arcsin d
  | r + 1, d => (2 * ((r : ℝ) + 1) - 1) / (2 * ((r : ℝ) + 1)) * KK r d -
      d * ((1 - d ^ 2) ^ r * √(1 - d ^ 2)) / (2 * ((r : ℝ) + 1))

theorem KK_zero_fun : KK 0 = fun d => π / 2 - arcsin d := by
  funext d; first | rfl | simp [KK]

theorem KK_succ_fun (r : ℕ) : KK (r + 1) = fun d =>
    (2 * ((r : ℝ) + 1) - 1) / (2 * ((r : ℝ) + 1)) * KK r d -
      d * ((1 - d ^ 2) ^ r * √(1 - d ^ 2)) / (2 * ((r : ℝ) + 1)) := by
  funext d; first | rfl | simp [KK]

theorem continuous_KK (r : ℕ) : Continuous (KK r) := by
  induction r with
  | zero => rw [KK_zero_fun]; exact continuous_const.sub continuous_arcsin
  | succ r ih =>
    rw [KK_succ_fun]
    exact (continuous_const.mul ih).sub ((continuous_id.mul
      (((continuous_const.sub (continuous_pow 2)).pow r).mul
        (continuous_const.sub (continuous_pow 2)).sqrt)).div_const _)

theorem KK_one (r : ℕ) : KK r 1 = 0 := by
  induction r with
  | zero => rw [KK_zero_fun]; simp [arcsin_one]
  | succ r ih => rw [KK_succ_fun]; simp [ih]

theorem KK_succ_neg_one (r : ℕ) :
    KK (r + 1) (-1) = (2 * ((r : ℝ) + 1) - 1) / (2 * ((r : ℝ) + 1)) * KK r (-1) := by
  rw [KK_succ_fun]; simp

theorem DD_pos (r : ℕ) : 0 < DD r := by
  induction r with
  | zero => simp [DD]
  | succ r ih =>
    simp only [DD]
    positivity

/-- `K_{P+1}(−1) = π/D_P`. -/
theorem KK_neg_one (P : ℕ) : KK (P + 1) (-1) = π / DD P := by
  induction P with
  | zero =>
    rw [KK_succ_neg_one, KK_zero_fun]
    simp only [DD, arcsin_neg_one]
    ring
  | succ P ih =>
    rw [KK_succ_neg_one, ih]
    have h0 := DD_pos P
    simp only [DD]
    push_cast
    field_simp
    ring

/-! ### Algebra for the derivatives (free variables) -/

theorem alg_B (r : ℕ) (W s : ℝ) (hW : W ≠ 0) (hss : s ^ 2 = W) :
    (r : ℝ) * W ^ (r - 1) = r * W ^ r / s ^ 2 := by
  rw [hss]
  cases r with
  | zero => simp
  | succ k => rw [Nat.add_sub_cancel, pow_succ, mul_div_assoc, mul_div_cancel_right₀ _ hW]

theorem alg_K (r : ℕ) (z s : ℝ) (hs : s ≠ 0) (hss : s ^ 2 = 1 - z ^ 2) :
    (2 * ((r : ℝ) + 1) - 1) / (2 * ((r : ℝ) + 1)) * (-((1 - z ^ 2) ^ r / s)) -
      (1 * ((1 - z ^ 2) ^ r * s) + z * (-(2 * z) * ((r : ℝ) * (1 - z ^ 2) ^ r / s ^ 2) * s +
        (1 - z ^ 2) ^ r * (-(z / s)))) / (2 * ((r : ℝ) + 1)) =
      -((1 - z ^ 2) ^ (r + 1) / s) := by
  have hC : (2 * ((r : ℝ) + 1)) ≠ 0 := by positivity
  have hz : z ^ 2 = 1 - s ^ 2 := by linarith
  rw [pow_succ (1 - z ^ 2) r]
  generalize (1 - z ^ 2) ^ r = A
  rw [← hss]
  calc _ = (-(2 * (r : ℝ) + 1) * A - A * s ^ 2 + (2 * (r : ℝ) + 1) * z ^ 2 * A) /
        (s * (2 * ((r : ℝ) + 1))) := by field_simp; ring
    _ = (-(2 * (r : ℝ) + 1) * A - A * s ^ 2 + (2 * (r : ℝ) + 1) * (1 - s ^ 2) * A) /
        (s * (2 * ((r : ℝ) + 1))) := by rw [hz]
    _ = -(A * s ^ 2 / s) := by field_simp; ring

theorem alg_J (r : ℕ) (z s A : ℝ) (hs : s ≠ 0) :
    -((-(2 * z) * (((r : ℝ) + 1) * A) * s + A * s ^ 2 * (-(z / s))) / (2 * (r : ℝ) + 3)) =
      z * (A * s) := by
  have hC : (2 * (r : ℝ) + 3) ≠ 0 := by positivity
  field_simp
  ring

/-! ### Derivatives -/

theorem hasDerivAt_W {z : ℝ} : HasDerivAt (fun d : ℝ => 1 - d ^ 2) (-(2 * z)) z :=
  ((hasDerivAt_pow 2 z).const_sub 1).congr_deriv (by norm_num)

theorem hasDerivAt_KK (r : ℕ) {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (KK r) (-((1 - z ^ 2) ^ r / √(1 - z ^ 2))) z := by
  have hW : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  have hs0 : √(1 - z ^ 2) ≠ 0 := (sqrt_pos.mpr hW).ne'
  have hss : √(1 - z ^ 2) ^ 2 = 1 - z ^ 2 := sq_sqrt hW.le
  induction r with
  | zero =>
    rw [KK_zero_fun]
    exact ((hasDerivAt_arcsin (ne_of_gt hz.1) hz.2.ne).const_sub (π / 2)).congr_deriv
      (by rw [pow_zero])
  | succ r ih =>
    rw [KK_succ_fun]
    have hP : HasDerivAt (fun d : ℝ => (1 - d ^ 2) ^ r)
        (-(2 * z) * ((r : ℝ) * (1 - z ^ 2) ^ r / √(1 - z ^ 2) ^ 2)) z :=
      (hasDerivAt_W.fun_pow r).congr_deriv
        (by linear_combination (-(2 * z)) * alg_B r _ _ hW.ne' hss)
    have hS : HasDerivAt (fun d : ℝ => √(1 - d ^ 2)) (-(z / √(1 - z ^ 2))) z :=
      (hasDerivAt_W.sqrt hW.ne').congr_deriv (by ring)
    have hG := (hasDerivAt_id' (x := z)).fun_mul (hP.fun_mul hS)
    have h := (ih.const_mul ((2 * ((r : ℝ) + 1) - 1) / (2 * ((r : ℝ) + 1)))).fun_sub
      (hG.div_const (2 * ((r : ℝ) + 1)))
    exact h.congr_deriv (by linear_combination alg_K r z (√(1 - z ^ 2)) hs0 hss)

theorem hasDerivAt_J1 (r : ℕ) {z : ℝ} (hz : z ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun d : ℝ => -((1 - d ^ 2) ^ (r + 1) * √(1 - d ^ 2) / (2 * (r : ℝ) + 3)))
      (z * ((1 - z ^ 2) ^ r * √(1 - z ^ 2))) z := by
  have hW : 0 < 1 - z ^ 2 := by nlinarith [hz.1, hz.2]
  have hs0 : √(1 - z ^ 2) ≠ 0 := (sqrt_pos.mpr hW).ne'
  have hss : √(1 - z ^ 2) ^ 2 = 1 - z ^ 2 := sq_sqrt hW.le
  have hP : HasDerivAt (fun d : ℝ => (1 - d ^ 2) ^ (r + 1))
      (-(2 * z) * (((r : ℝ) + 1) * (1 - z ^ 2) ^ r)) z :=
    (hasDerivAt_W.fun_pow (r + 1)).congr_deriv (by rw [Nat.add_sub_cancel]; push_cast; ring)
  have hS : HasDerivAt (fun d : ℝ => √(1 - d ^ 2)) (-(z / √(1 - z ^ 2))) z :=
    (hasDerivAt_W.sqrt hW.ne').congr_deriv (by ring)
  have h := ((hP.fun_mul hS).div_const (2 * (r : ℝ) + 3)).fun_neg
  refine h.congr_deriv ?_
  have hA := alg_J r z (√(1 - z ^ 2)) ((1 - z ^ 2) ^ r) hs0
  rw [hss, ← pow_succ] at hA
  linear_combination hA

/-! ### Integral forms -/

theorem one_sub_sq_nonneg {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) : 0 ≤ 1 - z ^ 2 := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hz.2) (by linarith [hz.1] : (0:ℝ) ≤ 1 + z)]

theorem rpow_half_neg (r : ℕ) {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) :
    (1 - z ^ 2) ^ ((r : ℝ) - 1 / 2) = (1 - z ^ 2) ^ r / √(1 - z ^ 2) := by
  have hne : (r : ℝ) - 1 / 2 ≠ 0 := by
    intro h
    have h2 : (2 * r : ℝ) = 1 := by linarith
    norm_cast at h2
    omega
  rw [rpow_sub' (one_sub_sq_nonneg hz) hne, rpow_natCast, ← sqrt_eq_rpow]

theorem rpow_half_pos (P : ℕ) {z : ℝ} (hz : z ∈ Icc (-1 : ℝ) 1) :
    (1 - z ^ 2) ^ ((((P + 1 : ℕ)) : ℝ) - 1 / 2) = (1 - z ^ 2) ^ P * √(1 - z ^ 2) := by
  rw [show (((P + 1 : ℕ)) : ℝ) - 1 / 2 = (P : ℝ) + 1 / 2 by push_cast; ring,
    rpow_add' (one_sub_sq_nonneg hz) (by positivity), rpow_natCast, ← sqrt_eq_rpow]

theorem uIcc_sub {d : ℝ} (hd : |d| ≤ 1) : uIcc d 1 ⊆ Icc (-1 : ℝ) 1 := by
  have h := abs_le.mp hd
  intro z hz
  rw [uIcc_of_le h.2] at hz
  exact ⟨h.1.trans hz.1, hz.2⟩

/-- **O1.** `K_r(d) = ∫_d^1 (1 − z²)^{r − 1/2} dz`. -/
theorem KK_integral (r : ℕ) {d : ℝ} (hd : |d| ≤ 1) :
    KK r d = ∫ z in d..1, (1 - z ^ 2) ^ ((r : ℝ) - 1 / 2) := by
  have h := abs_le.mp hd
  have hcont : ContinuousOn (fun y => -KK r y) (Icc d 1) :=
    (continuous_KK r).neg.continuousOn
  have hderiv : ∀ x ∈ Ioo d 1, HasDerivAt (fun y => -KK r y)
      ((1 - x ^ 2) ^ r / √(1 - x ^ 2)) x := fun x hx =>
    (hasDerivAt_KK r ⟨lt_of_le_of_lt h.1 hx.1, hx.2⟩).fun_neg.congr_deriv (neg_neg _)
  have hpos : ∀ x ∈ Ioo d 1, 0 ≤ (1 - x ^ 2) ^ r / √(1 - x ^ 2) := fun x hx =>
    div_nonneg (pow_nonneg (one_sub_sq_nonneg ⟨h.1.trans hx.1.le, hx.2.le⟩) r) (sqrt_nonneg _)
  have hint : IntervalIntegrable (fun x => (1 - x ^ 2) ^ r / √(1 - x ^ 2)) volume d 1 :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le h.2).mpr
      (intervalIntegral.integrableOn_deriv_of_nonneg hcont hderiv hpos)
  rw [intervalIntegral.integral_congr (g := fun x => (1 - x ^ 2) ^ r / √(1 - x ^ 2))
    (fun z hz => rpow_half_neg r (uIcc_sub hd hz)),
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h.2 hcont hderiv hint, KK_one]
  ring

/-- `J₀ = ∫_d^1 (1 − z²)^{P + 1/2} dz = K_{P+1}(d)`. -/
theorem J0_integral (P : ℕ) {d : ℝ} (hd : |d| ≤ 1) :
    ∫ z in d..1, (1 - z ^ 2) ^ P * √(1 - z ^ 2) = KK (P + 1) d := by
  rw [KK_integral (P + 1) hd]
  exact intervalIntegral.integral_congr fun z hz => (rpow_half_pos P (uIcc_sub hd hz)).symm

theorem continuous_wt (P : ℕ) : Continuous (fun z : ℝ => (1 - z ^ 2) ^ P * √(1 - z ^ 2)) :=
  ((continuous_const.sub (continuous_pow 2)).pow P).mul
    (continuous_const.sub (continuous_pow 2)).sqrt

/-- `J₁ = ∫_d^1 z(1 − z²)^{P + 1/2} dz = (1 − d²)^{P + 3/2}/(2P + 3)`. -/
theorem J1_integral (P : ℕ) {d : ℝ} (hd : |d| ≤ 1) :
    ∫ z in d..1, z * ((1 - z ^ 2) ^ P * √(1 - z ^ 2)) =
      (1 - d ^ 2) ^ (P + 1) * √(1 - d ^ 2) / (2 * (P : ℝ) + 3) := by
  have h := abs_le.mp hd
  have hc : Continuous (fun d : ℝ => -((1 - d ^ 2) ^ (P + 1) * √(1 - d ^ 2) / (2 * (P : ℝ) + 3))) :=
    ((((continuous_const.sub (continuous_pow 2)).pow (P + 1)).mul
      (continuous_const.sub (continuous_pow 2)).sqrt).div_const _).neg
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le h.2 hc.continuousOn
    (fun x hx => hasDerivAt_J1 P ⟨lt_of_le_of_lt h.1 hx.1, hx.2⟩)
    ((continuous_id.mul (continuous_wt P)).intervalIntegrable _ _)]
  simp

/-- `J₂ = ∫_d^1 z²(1 − z²)^{P + 1/2} dz = K_{P+1}(d) − K_{P+2}(d)`. -/
theorem J2_integral (P : ℕ) {d : ℝ} (hd : |d| ≤ 1) :
    ∫ z in d..1, z ^ 2 * ((1 - z ^ 2) ^ P * √(1 - z ^ 2)) = KK (P + 1) d - KK (P + 2) d := by
  have h : (fun z : ℝ => z ^ 2 * ((1 - z ^ 2) ^ P * √(1 - z ^ 2))) =
      fun z => (1 - z ^ 2) ^ P * √(1 - z ^ 2) - (1 - z ^ 2) ^ (P + 1) * √(1 - z ^ 2) := by
    funext z; ring
  rw [h, intervalIntegral.integral_sub ((continuous_wt P).intervalIntegrable _ _)
    ((continuous_wt (P + 1)).intervalIntegrable _ _), J0_integral P hd, J0_integral (P + 1) hd]

/-! ## The coordinate law for odd `n` -/

/-- The coordinate law in dimension `n − 1` for odd `n`: weight `(1 − z²)^P √(1 − z²)`,
normalizer `π/D_P`, `P = (n−5)/2`. -/
theorem coord_law_odd {n : ℕ} (hn : 9 ≤ n) (ho : Odd n) {g : ℝ → ℝ} (hg : Measurable g)
    (hb : ∃ M, ∀ z ∈ Icc (-1:ℝ) 1, |g z| ≤ M) :
    ∫ v, g (unitF53 v ⟨0, by omega⟩) ∂stdGauss (Fin (n-1)) =
      (∫ z in (-1:ℝ)..1, g z * ((1 - z ^ 2) ^ ((n-5)/2) * √(1 - z ^ 2))) /
        (π / DD ((n-5)/2)) := by
  have hexp : (((n-1 : ℕ) : ℝ) - 3) / 2 = ((((n-5)/2 + 1 : ℕ)) : ℝ) - 1 / 2 := by
    obtain ⟨q, rfl⟩ := ho
    rw [show (2*q+1-5)/2 + 1 = q - 1 by omega, Nat.cast_sub (by omega : 1 ≤ q),
      Nat.cast_sub (by omega : 1 ≤ 2*q+1)]
    push_cast
    ring
  have h1 : |(-1:ℝ)| ≤ 1 := by norm_num
  rw [coord_law (N := n-1) (by omega) hg hb, hexp, ← KK_integral ((n-5)/2 + 1) h1,
    KK_neg_one]
  congr 1
  exact intervalIntegral.integral_congr fun z hz => by
    simp only [rpow_half_pos ((n-5)/2) (uIcc_sub h1 hz)]

/-! ## The reference rule -/

/-- The exact odd first-moment combination `𝒩_P(mJ₀ + kJ₁)`, `𝒩_P = D_P/π`. -/
noncomputable def oddARef (n : ℕ) (m k : ℝ) : ℝ :=
  DD ((n - 5) / 2) / π * (m * KK ((n - 5) / 2 + 1) (-m / k) +
    k * ((1 - (-m / k) ^ 2) ^ ((n - 5) / 2 + 1) * √(1 - (-m / k) ^ 2) /
      (2 * (((n - 5) / 2 : ℕ) : ℝ) + 3)))

/-- The exact odd second-moment combination `𝒩_P(m²J₀ + 2mkJ₁ + k²J₂)`. -/
noncomputable def oddERef (n : ℕ) (m k : ℝ) : ℝ :=
  DD ((n - 5) / 2) / π * (m ^ 2 * KK ((n - 5) / 2 + 1) (-m / k) +
    2 * m * k * ((1 - (-m / k) ^ 2) ^ ((n - 5) / 2 + 1) * √(1 - (-m / k) ^ 2) /
      (2 * (((n - 5) / 2 : ℕ) : ℝ) + 3)) +
    k ^ 2 * (KK ((n - 5) / 2 + 1) (-m / k) - KK ((n - 5) / 2 + 2) (-m / k)))

/-- The exact odd first-moment rule (four branches, no clip). -/
noncomputable def sphAoddRef (n : ℕ) (m k : ℝ) : ℝ :=
  if k = 0 then relu m else if k ≤ m then m else if m ≤ -k then 0 else oddARef n m k

/-- The exact odd second-moment rule (four branches, no clip). -/
noncomputable def sphEoddRef (n : ℕ) (m k : ℝ) : ℝ :=
  if k = 0 then relu m ^ 2 else if k ≤ m then m ^ 2 + k ^ 2 / ((n : ℝ) - 1) else
    if m ≤ -k then 0 else oddERef n m k

/-- Only the active interval `(−m/k, 1]` contributes (continuous weight). -/
theorem active_split_w {m k : ℝ} (hk : 0 < k) (hm1 : -k < m) (hm2 : m < k) {φ ψ w : ℝ → ℝ}
    (hφ : Continuous φ) (hw : Continuous w) (hφ0 : ∀ t ≤ 0, φ t = 0)
    (hφψ : ∀ t, 0 ≤ t → φ t = ψ t) :
    ∫ z in (-1:ℝ)..1, φ (m + k*z) * w z = ∫ z in (-m/k)..1, ψ (m + k*z) * w z := by
  have hd1 : -1 ≤ -m/k := by rw [le_div_iff₀ hk]; linarith
  have hd2 : -m/k ≤ 1 := by rw [div_le_iff₀ hk]; linarith
  have hcont : Continuous (fun z => φ (m + k*z) * w z) :=
    (hφ.comp (continuous_const.add (continuous_const.mul continuous_id))).mul hw
  rw [← intervalIntegral.integral_add_adjacent_intervals (hcont.intervalIntegrable (-1) (-m/k))
    (hcont.intervalIntegrable (-m/k) 1)]
  have hz1 : ∫ z in (-1:ℝ)..(-m/k), φ (m + k*z) * w z = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0:ℝ)) ?_]
    · simp
    intro z hz
    rw [uIcc_of_le hd1] at hz
    have h1 := mul_le_mul_of_nonneg_left hz.2 hk.le
    have hkd : k * (-m/k) = -m := by field_simp
    have h2 : m + k*z ≤ 0 := by linarith
    simp only [hφ0 _ h2, zero_mul]
  rw [hz1, zero_add]
  refine intervalIntegral.integral_congr fun z hz => ?_
  rw [uIcc_of_le hd2] at hz
  have h1 := mul_le_mul_of_nonneg_left hz.1 hk.le
  have hkd : k * (-m/k) = -m := by field_simp
  have h2 : 0 ≤ m + k*z := by linarith
  simp only [hφψ _ h2]

theorem continuous_zwt (P : ℕ) :
    Continuous (fun z : ℝ => z * ((1 - z ^ 2) ^ P * √(1 - z ^ 2))) :=
  continuous_id.mul (continuous_wt P)

theorem lin_Jo (P : ℕ) (m k : ℝ) {d : ℝ} (hd : |d| ≤ 1) :
    ∫ z in d..1, (m + k*z) * ((1 - z ^ 2) ^ P * √(1 - z ^ 2)) =
      m * KK (P + 1) d + k * ((1 - d ^ 2) ^ (P + 1) * √(1 - d ^ 2) / (2 * (P : ℝ) + 3)) := by
  have h : (fun z : ℝ => (m + k*z) * ((1 - z ^ 2) ^ P * √(1 - z ^ 2))) =
      fun z => m * ((1 - z ^ 2) ^ P * √(1 - z ^ 2)) +
        k * (z * ((1 - z ^ 2) ^ P * √(1 - z ^ 2))) := by
    funext z; ring
  rw [h, intervalIntegral.integral_add (((continuous_wt P).const_mul m).intervalIntegrable _ _)
    (((continuous_zwt P).const_mul k).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    J0_integral P hd, J1_integral P hd]

theorem quad_Jo (P : ℕ) (m k : ℝ) {d : ℝ} (hd : |d| ≤ 1) :
    ∫ z in d..1, (m + k*z) ^ 2 * ((1 - z ^ 2) ^ P * √(1 - z ^ 2)) =
      m ^ 2 * KK (P + 1) d +
        2 * m * k * ((1 - d ^ 2) ^ (P + 1) * √(1 - d ^ 2) / (2 * (P : ℝ) + 3)) +
        k ^ 2 * (KK (P + 1) d - KK (P + 2) d) := by
  have h : (fun z : ℝ => (m + k*z) ^ 2 * ((1 - z ^ 2) ^ P * √(1 - z ^ 2))) =
      fun z => m ^ 2 * ((1 - z ^ 2) ^ P * √(1 - z ^ 2)) +
        2 * m * k * (z * ((1 - z ^ 2) ^ P * √(1 - z ^ 2))) +
        k ^ 2 * (z ^ 2 * ((1 - z ^ 2) ^ P * √(1 - z ^ 2))) := by
    funext z; ring
  rw [h, intervalIntegral.integral_add, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, J0_integral P hd, J1_integral P hd, J2_integral P hd]
  · exact ((continuous_wt P).const_mul _).intervalIntegrable _ _
  · exact ((continuous_zwt P).const_mul _).intervalIntegrable _ _
  · exact (((continuous_wt P).const_mul _).add
      ((continuous_zwt P).const_mul _)).intervalIntegrable _ _
  · exact (((continuous_pow 2).mul (continuous_wt P)).const_mul _).intervalIntegrable _ _

theorem abs_d_le {m k : ℝ} (hk : 0 < k) (hm1 : -k < m) (hm2 : m < k) : |-m/k| ≤ 1 := by
  rw [abs_le]
  constructor
  · rw [le_div_iff₀ hk]; linarith
  · rw [div_le_iff₀ hk]; linarith

/-- The first moment for odd `n`. -/
theorem sphAoddRef_eq {n : ℕ} (hn : 9 ≤ n) (ho : Odd n) (m : ℝ) {k : ℝ} (hk : 0 ≤ k) :
    ∫ v, relu (m + k * unitF53 v ⟨0, by omega⟩) ∂stdGauss (Fin (n-1)) = sphAoddRef n m k := by
  have hTm : ∀ v : Fin (n-1) → ℝ, unitF53 v ⟨0, by omega⟩ ∈ Icc (-1:ℝ) 1 :=
    fun v => coord_mem v _
  unfold sphAoddRef
  split_ifs with h0 h1 h2
  · subst h0; simp
  · have hr : ∀ v : Fin (n-1) → ℝ, relu (m + k * unitF53 v ⟨0, by omega⟩) =
        m + k * unitF53 v ⟨0, by omega⟩ := by
      intro v; unfold relu; apply max_eq_right
      nlinarith [mul_nonneg hk (by linarith [(hTm v).1] :
        (0:ℝ) ≤ unitF53 v ⟨0, by omega⟩ + 1)]
    simp_rw [hr]
    rw [integral_add (integrable_const _) ((integrable_coord _).const_mul _),
      integral_const_mul, coord_mean_at]
    simp
  · have hr : ∀ v : Fin (n-1) → ℝ, relu (m + k * unitF53 v ⟨0, by omega⟩) = 0 := by
      intro v; unfold relu; apply max_eq_left
      nlinarith [mul_nonneg hk (by linarith [(hTm v).2] :
        (0:ℝ) ≤ 1 - unitF53 v ⟨0, by omega⟩)]
    simp_rw [hr]
    simp
  · have hkp : 0 < k := lt_of_le_of_ne hk (Ne.symm h0)
    have hm1 : -k < m := lt_of_not_ge h2
    have hm2 : m < k := lt_of_not_ge h1
    have h := coord_law_odd hn ho (g := fun z => relu (m + k*z))
      (measurable_relu.comp (measurable_const.add (measurable_const.mul measurable_id)))
      (relu_bound m k hk)
    beta_reduce at h
    have hs := active_split_w hkp hm1 hm2 (φ := relu) (ψ := fun t => t)
      (w := fun z => (1 - z ^ 2) ^ ((n-5)/2) * √(1 - z ^ 2)) continuous_relu
      (continuous_wt _) (fun t ht => max_eq_left ht) (fun t ht => max_eq_right ht)
    beta_reduce at hs
    rw [h, hs, lin_Jo _ m k (abs_d_le hkp hm1 hm2), oddARef, div_div_eq_mul_div]
    ring

/-- The second moment for odd `n`. -/
theorem sphEoddRef_eq {n : ℕ} (hn : 9 ≤ n) (ho : Odd n) (m : ℝ) {k : ℝ} (hk : 0 ≤ k) :
    ∫ v, relu (m + k * unitF53 v ⟨0, by omega⟩) ^ 2 ∂stdGauss (Fin (n-1)) =
      sphEoddRef n m k := by
  have hTm : ∀ v : Fin (n-1) → ℝ, unitF53 v ⟨0, by omega⟩ ∈ Icc (-1:ℝ) 1 :=
    fun v => coord_mem v _
  unfold sphEoddRef
  split_ifs with h0 h1 h2
  · subst h0; simp
  · have hr : ∀ v : Fin (n-1) → ℝ, relu (m + k * unitF53 v ⟨0, by omega⟩) ^ 2 =
        m^2 + (2*m*k) * unitF53 v ⟨0, by omega⟩ + k^2 * (unitF53 v ⟨0, by omega⟩)^2 := by
      intro v
      have hp : relu (m + k * unitF53 v ⟨0, by omega⟩) = m + k * unitF53 v ⟨0, by omega⟩ := by
        unfold relu; apply max_eq_right
        nlinarith [mul_nonneg hk (by linarith [(hTm v).1] :
          (0:ℝ) ≤ unitF53 v ⟨0, by omega⟩ + 1)]
      rw [hp]; ring
    simp_rw [hr]
    rw [integral_add, integral_add, integral_const_mul, integral_const_mul, coord_mean_at,
      coord_sq_at (by omega), Nat.cast_sub (by omega : 1 ≤ n)]
    · have hc : ∫ _v : Fin (n-1) → ℝ, m^2 ∂stdGauss (Fin (n-1)) = m^2 := by simp
      rw [hc]
      push_cast
      ring
    all_goals first
      | exact integrable_const _
      | exact (integrable_coord _).const_mul _
      | exact (integrable_coord_sq _).const_mul _
      | exact (integrable_const _).add ((integrable_coord _).const_mul _)
  · have hr : ∀ v : Fin (n-1) → ℝ, relu (m + k * unitF53 v ⟨0, by omega⟩) ^ 2 = 0 := by
      intro v
      have hp : relu (m + k * unitF53 v ⟨0, by omega⟩) = 0 := by
        unfold relu; apply max_eq_left
        nlinarith [mul_nonneg hk (by linarith [(hTm v).2] :
          (0:ℝ) ≤ 1 - unitF53 v ⟨0, by omega⟩)]
      rw [hp]; ring
    simp_rw [hr]
    simp
  · have hkp : 0 < k := lt_of_le_of_ne hk (Ne.symm h0)
    have hm1 : -k < m := lt_of_not_ge h2
    have hm2 : m < k := lt_of_not_ge h1
    have h := coord_law_odd hn ho (g := fun z => relu (m + k*z) ^ 2)
      ((measurable_relu.comp (measurable_const.add (measurable_const.mul measurable_id))).pow_const 2)
      (relu_sq_bound m k hk)
    beta_reduce at h
    have hs := active_split_w hkp hm1 hm2 (φ := fun t => relu t ^ 2) (ψ := fun t => t^2)
      (w := fun z => (1 - z ^ 2) ^ ((n-5)/2) * √(1 - z ^ 2))
      (continuous_relu.pow 2) (continuous_wt _)
      (fun t ht => by simp only [relu, max_eq_left ht]; ring)
      (fun t ht => by simp only [relu, max_eq_right ht])
    beta_reduce at hs
    rw [h, hs, quad_Jo _ m k (abs_d_le hkp hm1 hm2), oddERef, div_div_eq_mul_div]
    ring

/-- **O1.** The odd reference closed forms are the exact sphere moments. -/
theorem sph_oddRef {n : ℕ} (hn : 9 ≤ n) (ho : Odd n) (m : ℝ) {k : ℝ} (hk : 0 ≤ k) :
    ∫ v, relu (m + k * unitF53 v ⟨0, by omega⟩) ∂stdGauss (Fin (n-1)) = sphAoddRef n m k ∧
    ∫ v, relu (m + k * unitF53 v ⟨0, by omega⟩) ^ 2 ∂stdGauss (Fin (n-1)) =
      sphEoddRef n m k :=
  ⟨sphAoddRef_eq hn ho m hk, sphEoddRef_eq hn ho m hk⟩

end BstLean.Part278
