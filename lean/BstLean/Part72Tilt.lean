import BstLean.Part72Exp
import BstLean.Part72Feat
import BstLean.Part71Transfer
import BstLean.Part56MomProg_Sphere

/-!
# Part 72: rank-one tilts below the critical point satisfy the moment conditions

`r1Tilt n v t` has density `exp(t(v·x)²)/Z` relative to the uniform distribution `σ` on the
sphere. Let `0 ≤ τ < 1/2`, `κ = 1/2 − τ`, `|v| = 1` and `0 ≤ t ≤ τn`.

* `r1_mean_zero`: `E_μ x = 0` (the density is even, `σ` is invariant under `x ↦ −x`).
* `r1_dir_moment`: `E_μ (w·x)^{2m} ≤ m!·(2/(κn))^m/κ` for every unit `w`
  (the exponential moment `E_μ exp((κn/2)(w·x)²) ≤ 1/κ` from `sphere_two_dir`, and
  `y^m ≤ m!·e^y`).
* `r1_p4`: `E_μ p₄^q ≤ (2q)!·(2/κ)^{2q}/(κ·n^q)`.
* `r1_good`: `Good72 n d k μ (wR τ) (Fov d (AR τ)) (AR τ)` for every `d ≥ 1` and `k`, with
  `AR τ = 2/κ²` and `wR τ i = (4i)!·(2/κ)^{4i}/κ`.

This follows omOV-opus §3 (Lemmas E1, E2) and §4.3 (EXP form for F3), with `√(1/κ)` replaced by
`1/κ`. Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part72

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (phiSq)
open BstLean.Part53 (c0 p4)

variable {n : ℕ}

/-- The normalizing constant `Z = E_σ exp(t(v·x)²)`. -/
noncomputable def r1Z (n : ℕ) (v : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∫ x, Real.exp (t * dirv v x ^ 2) ∂uniformSphere n

/-- **The rank-one tilt** `D_{t,v} ∝ exp(t(v·x)²)` on the sphere. -/
noncomputable def r1Tilt (n : ℕ) (v : Fin n → ℝ) (t : ℝ) : Measure (Fin n → ℝ) :=
  (uniformSphere n).withDensity (fun x => ENNReal.ofReal (Real.exp (t * dirv v x ^ 2) / r1Z n v t))

private lemma cont_dirv (v : Fin n → ℝ) : Continuous (fun x : Fin n → ℝ => dirv v x) := by
  unfold dirv; fun_prop

private lemma int_exp (hn : 1 ≤ n) (v : Fin n → ℝ) (t : ℝ) :
    Integrable (fun x => Real.exp (t * dirv v x ^ 2)) (uniformSphere n) :=
  sphere_integrable (BstLean.Part71.unif_sph hn) (by have := cont_dirv v; fun_prop)

lemma r1Z_ge_one (hn : 1 ≤ n) (v : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) : 1 ≤ r1Z n v t := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have h : ∫ _x, (1 : ℝ) ∂uniformSphere n ≤ r1Z n v t :=
    integral_mono (integrable_const 1) (int_exp hn v t) (fun x => by
      simp only
      exact Real.one_le_exp (by positivity))
  simpa using h

lemma r1_integral (hn : 1 ≤ n) (v : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) (f : (Fin n → ℝ) → ℝ) :
    ∫ x, f x ∂r1Tilt n v t =
      ∫ x, (Real.exp (t * dirv v x ^ 2) / r1Z n v t) * f x ∂uniformSphere n := by
  have hZ := r1Z_ge_one hn v ht
  have hm : Measurable (fun x => Real.exp (t * dirv v x ^ 2) / r1Z n v t) := by
    have := cont_dirv v; apply Continuous.measurable; fun_prop
  rw [r1Tilt, integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (by positivity)]
  rfl

/-- The rank-one tilt is a probability distribution carried by the sphere. -/
lemma r1_sph (hn : 1 ≤ n) (v : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) : SphLaw n (r1Tilt n v t) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  have hZ := r1Z_ge_one hn v ht
  refine ⟨⟨?_⟩, ?_⟩
  · rw [r1Tilt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal ((int_exp hn v t).div_const _)
        (Filter.Eventually.of_forall (fun x => by simp only [Pi.zero_apply]; positivity)),
      integral_div]
    rw [show (∫ x, Real.exp (t * dirv v x ^ 2) ∂uniformSphere n) = r1Z n v t from rfl,
      div_self (by linarith)]
    simp
  · exact (withDensity_absolutelyContinuous _ _).ae_le (BstLean.Part29.uniformSphere_ae_sphere n)

private lemma neg_inv (hn : 1 ≤ n) (F : (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    ∫ x, F x ∂uniformSphere n = ∫ x, F (-x) ∂uniformSphere n := by
  have h := BstLean.Part56.MomProg.uniformSphere_involution (n := n) (LinearIsometryEquiv.neg ℝ)
    (fun x => by simp)
  have hf : (fun x : Fin n → ℝ => WithLp.ofLp ((LinearIsometryEquiv.neg ℝ) (WithLp.toLp 2 x))) =
      fun x => -x := by
    funext x; simp
  rw [hf] at h
  conv_lhs => rw [← h]
  rw [integral_map (by fun_prop) hF.aestronglyMeasurable]

/-- **The mean of the rank-one tilt is zero.** -/
lemma r1_mean_zero (hn : 1 ≤ n) (v : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) (i : Fin n) :
    ∫ x, x i ∂r1Tilt n v t = 0 := by
  rw [r1_integral hn v ht]
  set F : (Fin n → ℝ) → ℝ := fun x => (Real.exp (t * dirv v x ^ 2) / r1Z n v t) * x i
  have hF : Continuous F := by have := cont_dirv v; fun_prop
  have h := neg_inv hn F hF
  have hneg : ∀ x, F (-x) = -F x := by
    intro x
    simp only [F, dirv, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, neg_sq]
  simp_rw [hneg, integral_neg] at h
  change ∫ x, F x ∂uniformSphere n = 0
  linarith

lemma Mean_r1 (hn : 1 ≤ n) (v : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) : Mean (r1Tilt n v t) = 0 := by
  unfold Mean
  simp [r1_mean_zero hn v ht]

/-- The exponential moment of the tilt in a direction `w`. -/
lemma r1_exp (hn : 1 ≤ n) (v w : Fin n → ℝ) (hv : ∑ i, v i ^ 2 = 1) (hw : ∑ i, w i ^ 2 = 1)
    {t a : ℝ} (ht : 0 ≤ t) (ha : 0 ≤ a) (hta : 2 * (t + a) < n) :
    ∫ x, Real.exp (a * dirv w x ^ 2) ∂r1Tilt n v t ≤ 1 / (1 - 2 * (t + a) / n) := by
  have hZ := r1Z_ge_one hn v ht
  rw [r1_integral hn v ht]
  refine le_trans ?_ (sphere_two_dir hn t a ht ha v w hv hw hta)
  have hc1 := cont_dirv v
  have hc2 := cont_dirv w
  apply integral_mono (sphere_integrable (BstLean.Part71.unif_sph hn) (by fun_prop))
    (sphere_integrable (BstLean.Part71.unif_sph hn) (by fun_prop))
  intro x
  simp only
  rw [Real.exp_add]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  exact div_le_self (Real.exp_pos _).le hZ

/-- `κ = 1/2 − τ`. -/
noncomputable def kap (τ : ℝ) : ℝ := 1 / 2 - τ

/-- **Directional moments of the tilt**: `E_μ (w·x)^{2m} ≤ m!·(2/(κn))^m/κ`. -/
theorem r1_dir_moment (hn : 1 ≤ n) (v w : Fin n → ℝ) (hv : ∑ i, v i ^ 2 = 1)
    (hw : ∑ i, w i ^ 2 = 1) {τ t : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ < 1 / 2) (ht0 : 0 ≤ t)
    (ht : t ≤ τ * n) (m : ℕ) :
    ∫ x, dirv w x ^ (2 * m) ∂r1Tilt n v t ≤
      (m.factorial : ℝ) * (2 / (kap τ * n)) ^ m / kap τ := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : 0 < kap τ := by unfold kap; linarith
  set a : ℝ := kap τ * n / 2 with ha
  have ha0 : 0 < a := by positivity
  have hta : 2 * (t + a) < n := by
    have : 2 * (t + a) ≤ (2 * τ + kap τ) * n := by rw [ha]; nlinarith
    have h2 : 2 * τ + kap τ < 1 := by unfold kap; linarith
    nlinarith
  have hbound : 1 / (1 - 2 * (t + a) / n) ≤ 1 / kap τ := by
    apply one_div_le_one_div_of_le hk
    rw [ha]
    have : 2 * t / n ≤ 2 * τ := by rw [div_le_iff₀ hnpos]; linarith
    have e : 2 * (t + kap τ * n / 2) / n = 2 * t / n + kap τ := by field_simp
    rw [e]; unfold kap at *; linarith
  have hE := (r1_exp hn v w hv hw ht0 ha0.le hta).trans hbound
  have hsph := r1_sph hn v ht0
  let := hsph.prob
  have hc := cont_dirv w
  have hpt : ∀ x, dirv w x ^ (2 * m) ≤
      ((m.factorial : ℝ) / a ^ m) * Real.exp (a * dirv w x ^ 2) := by
    intro x
    have h := Real.pow_div_factorial_le_exp (x := a * dirv w x ^ 2) (by positivity) m
    have hf : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    rw [div_le_iff₀ hf] at h
    rw [pow_mul, mul_pow] at *
    have ham : 0 < a ^ m := by positivity
    rw [div_mul_eq_mul_div, le_div_iff₀ ham]
    nlinarith [sq_nonneg (dirv w x)]
  calc ∫ x, dirv w x ^ (2 * m) ∂r1Tilt n v t
      ≤ ∫ x, ((m.factorial : ℝ) / a ^ m) * Real.exp (a * dirv w x ^ 2) ∂r1Tilt n v t :=
        integral_mono (sphere_integrable hsph (by fun_prop))
          (sphere_integrable hsph (by fun_prop)) hpt
    _ = ((m.factorial : ℝ) / a ^ m) * ∫ x, Real.exp (a * dirv w x ^ 2) ∂r1Tilt n v t :=
        integral_const_mul _ _
    _ ≤ ((m.factorial : ℝ) / a ^ m) * (1 / kap τ) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = (m.factorial : ℝ) * (2 / (kap τ * n)) ^ m / kap τ := by
        rw [ha, div_mul_eq_mul_div, mul_one_div]
        rw [show (2 / (kap τ * n)) ^ m = 1 / (kap τ * n / 2) ^ m by
          rw [one_div, ← inv_pow, inv_div]]
        ring

private lemma dirv_single (i : Fin n) (x : Fin n → ℝ) : dirv (Pi.single i 1) x = x i := by
  classical
  unfold dirv
  simp [Pi.single_apply]

private lemma single_unit (i : Fin n) : ∑ j, (Pi.single i (1 : ℝ) : Fin n → ℝ) j ^ 2 = 1 := by
  classical
  simp [Pi.single_apply]

/-- **The `p₄` moments of the tilt**: `E_μ p₄^q ≤ (2q)!·(2/κ)^{2q}/(κ·n^q)`, `q ≥ 1`. -/
theorem r1_p4 (hn : 1 ≤ n) (v : Fin n → ℝ) (hv : ∑ i, v i ^ 2 = 1) {τ t : ℝ} (hτ0 : 0 ≤ τ)
    (hτ : τ < 1 / 2) (ht0 : 0 ≤ t) (ht : t ≤ τ * n) (q : ℕ) (hq : 1 ≤ q) :
    ∫ x, p4 x ^ q ∂r1Tilt n v t ≤
      ((2 * q).factorial : ℝ) * (2 / kap τ) ^ (2 * q) / (kap τ * (n : ℝ) ^ q) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : 0 < kap τ := by unfold kap; linarith
  have hsph := r1_sph hn v ht0
  let := hsph.prob
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hpt : ∀ x : Fin n → ℝ, p4 x ^ (r + 1) ≤ (n : ℝ) ^ r * ∑ i, x i ^ (4 * (r + 1)) := by
    intro x
    have h := pow_sum_div_card_le_sum_pow (s := Finset.univ) (f := fun i => x i ^ 4)
      (fun i _ => by positivity) r
    simp only [Finset.card_univ, Fintype.card_fin] at h
    have hnr : (0 : ℝ) < (n : ℝ) ^ r := by positivity
    rw [div_le_iff₀ hnr] at h
    unfold p4
    simp_rw [pow_mul]
    linarith [mul_comm ((n : ℝ) ^ r) (∑ i, (x i ^ 4) ^ (r + 1))]
  have hcoord : ∀ i : Fin n, ∫ x, x i ^ (4 * (r + 1)) ∂r1Tilt n v t ≤
      ((2 * (r + 1)).factorial : ℝ) * (2 / (kap τ * n)) ^ (2 * (r + 1)) / kap τ := by
    intro i
    have h := r1_dir_moment hn v (Pi.single i 1) hv (single_unit i) hτ0 hτ ht0 ht (2 * (r + 1))
    simp_rw [dirv_single] at h
    rw [show 2 * (2 * (r + 1)) = 4 * (r + 1) by ring] at h
    exact h
  have hc : ∀ i : Fin n, Continuous (fun x : Fin n → ℝ => x i ^ (4 * (r + 1))) :=
    fun i => (continuous_apply i).pow _
  have hp4c : Continuous (fun x : Fin n → ℝ => p4 x ^ (r + 1)) := by unfold p4; fun_prop
  calc ∫ x, p4 x ^ (r + 1) ∂r1Tilt n v t
      ≤ ∫ x, (n : ℝ) ^ r * ∑ i, x i ^ (4 * (r + 1)) ∂r1Tilt n v t :=
        integral_mono (sphere_integrable hsph hp4c)
          (sphere_integrable hsph (by fun_prop)) hpt
    _ = (n : ℝ) ^ r * ∑ i, ∫ x, x i ^ (4 * (r + 1)) ∂r1Tilt n v t := by
        rw [integral_const_mul, integral_finset_sum _ (fun i _ => sphere_integrable hsph (hc i))]
    _ ≤ (n : ℝ) ^ r * ∑ _i : Fin n,
          ((2 * (r + 1)).factorial : ℝ) * (2 / (kap τ * n)) ^ (2 * (r + 1)) / kap τ := by
        gcongr with i
        exact hcoord i
    _ = ((2 * (r + 1)).factorial : ℝ) * (2 / kap τ) ^ (2 * (r + 1)) /
          (kap τ * (n : ℝ) ^ (r + 1)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [div_mul_eq_div_div, div_pow]
        field_simp
        ring

/-- The trace-moment weight of the tilt, `wR τ i = (4i)!·(2/κ)^{4i}/κ`. -/
noncomputable def wR (τ : ℝ) (i : ℕ) : ℝ := ((4 * i).factorial : ℝ) * (2 / kap τ) ^ (4 * i) / kap τ

/-- The overlap constant of the tilt, `AR τ = 2/κ²`. -/
noncomputable def AR (τ : ℝ) : ℝ := 2 / kap τ ^ 2

lemma wR_nonneg {τ : ℝ} (hτ : τ < 1 / 2) (i : ℕ) : 0 ≤ wR τ i := by
  have hk : 0 < kap τ := by unfold kap; linarith
  unfold wR; positivity

lemma AR_nonneg (τ : ℝ) : 0 ≤ AR τ := by unfold AR; positivity

/-- **The trace moments of the tilt** (P1): `E_μ δ°^{2i} ≤ wR τ i·d^{2i}/n^{2i}`. -/
theorem r1_dev (hn : 1 ≤ n) (v : Fin n → ℝ) (hv : ∑ i, v i ^ 2 = 1) {τ t : ℝ} (hτ0 : 0 ≤ τ)
    (hτ : τ < 1 / 2) (ht0 : 0 ≤ t) (ht : t ≤ τ * n) (d : ℕ) (i : ℕ) (hi : 1 ≤ i) :
    ∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂r1Tilt n v t ≤ wR τ i * (d : ℝ) ^ (2 * i) / (n : ℝ) ^ (2 * i) := by
  have hsph := r1_sph hn v ht0
  let := hsph.prob
  have hU := BstLean.Part53.lemmaU53 d
  have hδc : Continuous (fun x : Fin n → ℝ => (phiSq d x - c0 d) ^ (2 * i)) :=
    (BstLean.Part53.FloorCorrection.phiSq_continuous.sub continuous_const).pow _
  have hp4c : Continuous (fun x : Fin n → ℝ => p4 x ^ (2 * i)) := by unfold p4; fun_prop
  have hmono : ∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂r1Tilt n v t ≤
      ∫ x, (d : ℝ) ^ (2 * i) * p4 x ^ (2 * i) ∂r1Tilt n v t := by
    apply integral_mono_ae (sphere_integrable hsph hδc) (sphere_integrable hsph (by fun_prop))
    filter_upwards [hsph.sphere] with x hx
    obtain ⟨h0, h1⟩ := hU n x hx
    rw [← mul_pow]
    exact pow_le_pow_left₀ h0 h1 _
  rw [integral_const_mul] at hmono
  have hp := r1_p4 hn v hv hτ0 hτ ht0 ht (2 * i) (by omega)
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : 0 < kap τ := by unfold kap; linarith
  refine hmono.trans ((mul_le_mul_of_nonneg_left hp (by positivity)).trans (le_of_eq ?_))
  unfold wR
  rw [show 2 * (2 * i) = 4 * i by ring]
  field_simp

/-- **Rank-one tilts below the critical point satisfy `Good72`** (every `d ≥ 1`, every `k`). -/
theorem r1_good (hn : 1 ≤ n) (d k : ℕ) (hd : 1 ≤ d) (v : Fin n → ℝ) (hv : ∑ i, v i ^ 2 = 1)
    {τ t : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ < 1 / 2) (ht0 : 0 ≤ t) (ht : t ≤ τ * n) :
    Good72 n d k (r1Tilt n v t) (wR τ) (Fov d (AR τ)) (AR τ) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : 0 < kap τ := by unfold kap; linarith
  apply good_of_ov (r1_sph hn v ht0) d k hd (wR τ) (AR τ)
  · rw [Mean_r1 hn v ht0]; exact div_nonneg (AR_nonneg τ) hnpos.le
  · intro w hw
    have h := r1_dir_moment hn v w hv hw hτ0 hτ ht0 ht 1
    simp only [mul_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at h
    unfold dirv at h
    refine h.trans (le_of_eq ?_)
    unfold AR
    field_simp
  · intro i hi _
    exact r1_dev hn v hv hτ0 hτ ht0 ht d i hi

end BstLean.Part72
