import BstLean.Part136Final

/-!
# Part 140: the deterministic reduction for the stand-in factor with a GENERAL centre `b`

Role: `delegations/statements/p140-spec.md` (item 2). Paper sources: `onW5c-cx.md` §4,
`onW5-opus-prover.md` §3 (c), `onW8c-cx.md` §4 (the stand-in theorem holds for every centre `b`
that is a function of `(M₁, M₂)`; the residual directions are taken orthogonal to `b`; the price
is the rank-one term `|P_{b^⊥} h̄|² ≤ |h̄ − b|²`).

Part 136 (`det_frame`) is for the exact centre `b = h̄` only. This file has:

* `det_frame_b`: every probability space, every bounded measurable feature map `h`, every centre
  `b`: from a frame bound `A` of the centred features, `|h̄ − b|² ≤ ξ`,
  `‖⟨h(u), b⟩ − a‖₂ ≤ δ₂`, `‖|h(u)|² − d‖₂ ≤ δ`, `|b|² ≥ β`:
  `E_u ⟨e_b(u), w⟩² ≤ ((A + ξ)/s + δ₂²/ε₂² + δ²/ε₁²)·|w|²` for
  `0 < s ≤ d − ε₁ − (a + ε₂)²/β`, with `e_b(u) = eDir b (h u)` the unit residual direction of
  Part 134 for the centre `b`.
* `sphere_cov`: the frame bound of the centred features on the sphere, from the `L²` model of the
  Gram kernel (`cov_frame` of Part 136 with the two feature families of the sphere).
* `sphere_frame_b`: `det_frame_b` for a continuous feature map on the sphere.
* `cov_of_good`: the frame bound of the centred features of the World network on `goodHid`.
* `frameB_of_good`: `det_frame_b` for the World network on `goodHid`, in units of `m/N`.
* `frameB_num`: the frame bound `C/n` for `N = 2n`, `m = mW n`, `n ≥ n₀ ≥ 4096` from rational
  certificates.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part140

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere
  uniformSphere_moments)
open BstLean.Part105 (BM bm_cauchy_schwarz)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136

/-! ## The abstract reduction -/

section det

variable {U : Type*} [MeasurableSpace U] {m : ℕ} (μ : Measure U) [IsProbabilityMeasure μ]

/-- **The deterministic reduction for a general centre `b`.** `A` is a frame bound of the centred
features `h(u) − h̄`; `ξ ≥ |h̄ − b|²`; `X(u) = ⟨h(u), b⟩` is within `δ₂` of the constant `a ≥ 0` in
`L²(μ)`; `|h(u)|²` is within `δ` of `d` in `L²(μ)`; `|b|² ≥ β > 0`. Then the unit residual
directions `e_b(u) = eDir b (h u)` have the frame bound `(A + ξ)/s + δ₂²/ε₂² + δ²/ε₁²`, for every
`0 < s ≤ d − ε₁ − (a + ε₂)²/β`. -/
theorem det_frame_b {h : U → Fin m → ℝ} (hh : ∀ j, BM (fun u => h u j)) {b : Fin m → ℝ}
    {A ξ a δ₂ d δ ε₁ ε₂ β s : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ w : Fin m → ℝ,
      ∫ u, (∑ j, (h u j - hbar μ h j) * w j) ^ 2 ∂μ ≤ A * ∑ j, w j ^ 2)
    (hξ : ∑ j, (hbar μ h j - b j) ^ 2 ≤ ξ)
    (hX : ∫ u, (∑ j, h u j * b j - a) ^ 2 ∂μ ≤ δ₂ ^ 2)
    (hd : ∫ u, (normSq (h u) - d) ^ 2 ∂μ ≤ δ ^ 2)
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (ha : 0 ≤ a) (hβ : 0 < β) (hβb : β ≤ normSq b)
    (hs : 0 < s) (hsle : s ≤ d - ε₁ - (a + ε₂) ^ 2 / β) (w : Fin m → ℝ) :
    ∫ u, (∑ j, eDir b (h u) j * w j) ^ 2 ∂μ ≤
      ((A + ξ) / s + δ₂ ^ 2 / ε₂ ^ 2 + δ ^ 2 / ε₁ ^ 2) * ∑ j, w j ^ 2 := by
  have hbj : ∀ j, hbar μ h j = ∫ u, h u j ∂μ := fun j => rfl
  have hmeas : Measurable h := measurable_pi_iff.mpr fun j => (hh j).meas
  set X : U → ℝ := fun u => ∑ j, h u j * b j with hXdef
  have bX : BM X := bm_sum Finset.univ fun j _ => (hh j).mul (BM.const _)
  have bn : BM (fun u => normSq (h u)) := by
    change BM (fun u => ∑ j, h u j ^ 2)
    exact bm_sum Finset.univ fun j _ => (hh j).sq
  set Y := normSq b with hY
  have hYpos : 0 < Y := lt_of_lt_of_le hβ hβb
  have hY0 : normSq b ≠ 0 := hYpos.ne'
  have hξ0 : 0 ≤ ξ := le_trans (Finset.sum_nonneg fun j _ => sq_nonneg _) hξ
  -- the bad set of inputs
  set T : Set U := {u | ε₂ < |X u - a|} ∪ {u | ε₁ < |normSq (h u) - d|} with hT
  have mT : MeasurableSet T :=
    (measurableSet_lt measurable_const (bX.meas.sub measurable_const).abs).union
      (measurableSet_lt measurable_const (bn.meas.sub measurable_const).abs)
  have hμT : μ.real T ≤ δ₂ ^ 2 / ε₂ ^ 2 + δ ^ 2 / ε₁ ^ 2 := by
    refine (measureReal_union_le _ _).trans (add_le_add ?_ ?_)
    · exact (cheb μ (bX.sub (BM.const a)) hε₂).trans
        (div_le_div_of_nonneg_right hX (by positivity))
    · exact (cheb μ (bn.sub (BM.const d)) hε₁).trans
        (div_le_div_of_nonneg_right hd (by positivity))
  have hr : ∀ u, u ∉ T → s ≤ normSq (res b (h u)) := by
    intro u hu
    simp only [hT, Set.mem_union, Set.mem_ofPred_eq, not_or, not_lt] at hu
    obtain ⟨h1, h2⟩ := hu
    rw [normSq_res hY0]
    have hXu := abs_le.mp h1
    have hX2 : X u ^ 2 ≤ (a + ε₂) ^ 2 := by
      apply sq_le_sq' <;> linarith
    have hq : X u ^ 2 / Y ≤ (a + ε₂) ^ 2 / β :=
      div_le_div₀ (sq_nonneg _) hX2 hβ hβb
    have hnu := abs_le.mp h2
    have : (∑ j, h u j * b j) ^ 2 / normSq b = X u ^ 2 / Y := rfl
    rw [this]
    linarith
  -- the projected test vector
  set β' := (∑ j, b j * w j) / normSq b with hβ'
  set w' : Fin m → ℝ := fun j => w j - β' * b j with hw'
  have hsumb : ∑ j, b j * b j = Y := by
    simp only [hY, normSq]
    exact Finset.sum_congr rfl fun j _ => by rw [sq]
  have hβY : β' * Y = ∑ j, b j * w j := by
    rw [hβ']
    exact div_mul_cancel₀ _ hYpos.ne'
  have hw'0 : ∑ j, b j * w' j = 0 := by
    have e : ∀ j, b j * w' j = b j * w j - β' * (b j * b j) := fun j => by
      simp only [hw']; ring
    simp_rw [e]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsumb, hβY]
    ring
  have hw'n : ∑ j, w' j ^ 2 ≤ ∑ j, w j ^ 2 := by
    have e : ∀ j, w' j ^ 2 = w j ^ 2 - 2 * β' * (b j * w j) + β' ^ 2 * (b j * b j) := fun j => by
      simp only [hw']; ring
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
      hsumb, ← hβY]
    nlinarith [mul_nonneg (sq_nonneg β') hYpos.le]
  have hW0 : 0 ≤ ∑ j, w j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hW'0 : 0 ≤ ∑ j, w' j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  -- the centred part and the constant part
  set g : U → ℝ := fun u => ∑ j, (h u j - hbar μ h j) * w' j with hg
  set k : ℝ := ∑ j, hbar μ h j * w' j with hk
  have bgj : ∀ j, BM (fun u => (h u j - hbar μ h j) * w' j) := fun j =>
    ((hh j).sub (BM.const (hbar μ h j))).mul (BM.const (w' j))
  have bg : BM g := bm_sum Finset.univ fun j _ => bgj j
  have g0 : ∫ u, g u ∂μ = 0 := by
    simp only [hg]
    rw [integral_finsetSum _ fun j _ => (bgj j).integrable μ]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [integral_mul_const, integral_sub ((hh j).integrable μ) (integrable_const _), hbj j]
    simp
  have er : ∀ u, ∑ j, res b (h u) j * w j = g u + k := by
    intro u
    rw [res_dot]
    have e : ∀ j, h u j * (w j - (∑ j, b j * w j) / normSq b * b j) =
        (h u j - hbar μ h j) * w' j + hbar μ h j * w' j := fun j => by
      simp only [hw', hβ']; ring
    simp_rw [e]
    rw [Finset.sum_add_distrib]
  have hk2 : k ^ 2 ≤ ξ * ∑ j, w' j ^ 2 := by
    have e : k = ∑ j, (hbar μ h j - b j) * w' j := by
      have e1 : ∀ j, (hbar μ h j - b j) * w' j = hbar μ h j * w' j - b j * w' j := fun j => by
        ring
      simp_rw [e1]
      rw [Finset.sum_sub_distrib, hw'0, sub_zero]
    rw [e]
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => hbar μ h j - b j) w'
    exact cs.trans (mul_le_mul_of_nonneg_right hξ hW'0)
  have hgk : ∫ u, (g u + k) ^ 2 ∂μ = ∫ u, g u ^ 2 ∂μ + k ^ 2 := by
    have e : ∀ u, (g u + k) ^ 2 = g u ^ 2 + (2 * k * g u + k ^ 2) := fun u => by ring
    have j1 : Integrable (fun u => g u ^ 2) μ := bg.sq.integrable μ
    have j2 : Integrable (fun u => 2 * k * g u) μ := (bg.integrable μ).const_mul _
    have j3 : Integrable (fun u => 2 * k * g u + k ^ 2) μ := j2.add (integrable_const _)
    simp_rw [e]
    rw [integral_add j1 j3, integral_add j2 (integrable_const _), integral_const_mul, g0]
    simp
  have hAg : ∫ u, g u ^ 2 ∂μ ≤ A * ∑ j, w' j ^ 2 := hA w'
  -- the pointwise bound of the integrand
  have ptb : ∀ u, (∑ j, eDir b (h u) j * w j) ^ 2 ≤ ∑ j, w j ^ 2 := by
    intro u
    have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => eDir b (h u) j) w
    have h1 : ∑ j, eDir b (h u) j ^ 2 ≤ 1 := by
      rcases eDir_unit_or_zero b (h u) with h1 | h1
      · exact h1.le
      · rw [h1]; simp
    nlinarith
  have pt : ∀ u, (∑ j, eDir b (h u) j * w j) ^ 2 ≤
      s⁻¹ * (g u + k) ^ 2 + T.indicator (fun _ => ∑ j, w j ^ 2) u := by
    intro u
    by_cases hu : u ∈ T
    · rw [Set.indicator_of_mem hu]
      have h3 : 0 ≤ s⁻¹ * (g u + k) ^ 2 := by positivity
      linarith [ptb u]
    · rw [Set.indicator_of_notMem hu, add_zero]
      have hru := hr u hu
      have hnr : 0 < normSq (res b (h u)) := lt_of_lt_of_le hs hru
      have e : ∑ j, eDir b (h u) j * w j =
          (Real.sqrt (normSq (res b (h u))))⁻¹ * ∑ j, res b (h u) j * w j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [eDir, Pi.smul_apply, smul_eq_mul]
        ring
      rw [e, mul_pow, inv_pow, Real.sq_sqrt hnr.le, er u]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hs hru) (sq_nonneg _)
  have hm : Measurable (fun u => (∑ j, eDir b (h u) j * w j) ^ 2) :=
    (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp ((measurable_eDir b).comp hmeas)).mul_const _).pow_const 2
  have i1 : Integrable (fun u => (∑ j, eDir b (h u) j * w j) ^ 2) μ :=
    Integrable.of_bound hm.aestronglyMeasurable (∑ j, w j ^ 2)
      (Filter.Eventually.of_forall fun u => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]; exact ptb u)
  have bA : BM (fun u => (g u + k) ^ 2) := (bg.add (BM.const k)).sq
  have i2 : Integrable (fun u => s⁻¹ * (g u + k) ^ 2) μ := (bA.integrable μ).const_mul _
  have i3 : Integrable (T.indicator (fun _ : U => ∑ j, w j ^ 2)) μ :=
    (integrable_const _).indicator mT
  calc ∫ u, (∑ j, eDir b (h u) j * w j) ^ 2 ∂μ
      ≤ ∫ u, (s⁻¹ * (g u + k) ^ 2 + T.indicator (fun _ => ∑ j, w j ^ 2) u) ∂μ :=
        integral_mono i1 (i2.add i3) pt
    _ = s⁻¹ * (∫ u, g u ^ 2 ∂μ + k ^ 2) + μ.real T * ∑ j, w j ^ 2 := by
        rw [integral_add i2 i3, integral_const_mul, integral_indicator mT, setIntegral_const,
          smul_eq_mul, hgk]
    _ ≤ s⁻¹ * ((A + ξ) * ∑ j, w j ^ 2) +
          (δ₂ ^ 2 / ε₂ ^ 2 + δ ^ 2 / ε₁ ^ 2) * ∑ j, w j ^ 2 := by
        refine add_le_add (mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hs.le))
          (mul_le_mul_of_nonneg_right hμT hW0)
        have h1 : A * ∑ j, w' j ^ 2 ≤ A * ∑ j, w j ^ 2 := mul_le_mul_of_nonneg_left hw'n hA0
        have h2 : ξ * ∑ j, w' j ^ 2 ≤ ξ * ∑ j, w j ^ 2 := mul_le_mul_of_nonneg_left hw'n hξ0
        linarith
    _ = ((A + ξ) / s + δ₂ ^ 2 / ε₂ ^ 2 + δ ^ 2 / ε₁ ^ 2) * ∑ j, w j ^ 2 := by
        rw [div_eq_mul_inv]
        ring

end det

/-! ## The sphere -/

section sphere

variable {N m : ℕ}

/-- **The frame bound of the centred features on the sphere**, from the `L²` model
`a + c·⟨u, u′⟩ + c₂·(⟨u, u′⟩² − 1/N)` of the Gram kernel (distance `Δ`):
`E_u ⟨h(u) − h̄, w⟩² ≤ (c/N + 2c₂/(N(N + 2)) + Δ)·|w|²`. -/
theorem sphere_cov (hN : 1 ≤ N) {h : (Fin N → ℝ) → Fin m → ℝ} (hcont : Continuous h)
    {a c c₂ Δ : ℝ} (hc : 0 ≤ c) (hc₂ : 0 ≤ c₂) (hΔ : 0 ≤ Δ)
    (hD : ∫ uu, (dotp (h uu.1) (h uu.2) - a - c * dotp uu.1 uu.2 -
      c₂ * (dotp uu.1 uu.2 ^ 2 - 1 / (N : ℝ))) ^ 2 ∂lawU2 N ≤ Δ ^ 2) (w : Fin m → ℝ) :
    ∫ u, (∑ j, (h u j - hbar (uniformSphere N) h j) * w j) ^ 2 ∂uniformSphere N ≤
      (c * (1 / (N : ℝ)) + c₂ * (2 / ((N : ℝ) * (N + 2))) + Δ) * ∑ j, w j ^ 2 := by
  have := uniformSphere_isProbability N hN
  have hmom := uniformSphere_moments N hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  set hT : (Fin N → ℝ) → Fin m → ℝ := fun u j => trS (fun u => h u j) u with hhT
  set ℓT : (Fin N → ℝ) → Fin N → ℝ := fun u i => trS (fun u => u i) u with hℓT
  set qT : (Fin N → ℝ) → Fin N × Fin N → ℝ := fun u p => trS (fun u => quadF N u p) u with hqT
  have bh : ∀ j, BM (fun u => hT u j) := fun j =>
    bm_trS ((continuous_apply j).comp hcont)
  have bℓ : ∀ i, BM (fun u => ℓT u i) := fun i => bm_trS (continuous_apply i)
  have bq : ∀ p, BM (fun u => qT u p) := fun p => bm_trS (by
    unfold quadF
    exact ((continuous_apply p.1).mul (continuous_apply p.2)).sub continuous_const)
  have ptT : ∀ u : Fin N → ℝ, normSq u = 1 → hT u = h u ∧ ℓT u = u ∧ qT u = quadF N u := by
    intro u hu
    refine ⟨funext fun j => ?_, funext fun i => ?_, funext fun p => ?_⟩
    · simp only [hhT]; exact trS_of _ hu
    · simp only [hℓT]; exact trS_of _ hu
    · simp only [hqT]; exact trS_of _ hu
  have aeT : ∀ᵐ u ∂uniformSphere N, hT u = h u ∧ ℓT u = u ∧ qT u = quadF N u := by
    filter_upwards [uniformSphere_ae_sphere N] with u hu using ptT u hu
  have ebar : hbar (uniformSphere N) hT = hbar (uniformSphere N) h := by
    funext j
    unfold hbar
    refine integral_congr_ae ?_
    filter_upwards [aeT] with u hu
    rw [hu.1]
  have hτ : ∀ v : Fin N → ℝ, ∫ u, (∑ i, ℓT u i * v i) ^ 2 ∂uniformSphere N ≤
      1 / (N : ℝ) * ∑ i, v i ^ 2 := by
    intro v
    rw [← sphere_lin hN v]
    refine le_of_eq (integral_congr_ae ?_)
    filter_upwards [aeT] with u hu
    rw [hu.2.1]
  have hτ₂ : ∀ v : Fin N × Fin N → ℝ, ∫ u, (∑ p, qT u p * v p) ^ 2 ∂uniformSphere N ≤
      2 / ((N : ℝ) * (N + 2)) * ∑ p, v p ^ 2 := by
    intro v
    refine le_trans (le_of_eq (integral_congr_ae ?_)) (sphere_quad_frame hN v)
    filter_upwards [aeT] with u hu
    rw [hu.2.2]
  have hD' : ∫ p, (∑ k, hT p.1 k * hT p.2 k - a - c * ∑ i, ℓT p.1 i * ℓT p.2 i -
      c₂ * ∑ i, qT p.1 i * qT p.2 i) ^ 2
      ∂((uniformSphere N).prod (uniformSphere N)) ≤ Δ ^ 2 := by
    refine le_trans (le_of_eq (integral_congr_ae ?_)) hD
    have hu2 := lawU2_ae_unit hN
    unfold lawU2 at hu2
    filter_upwards [hu2] with uu huu
    rw [(ptT uu.1 huu.1).1, (ptT uu.1 huu.1).2.1, (ptT uu.2 huu.2).1, (ptT uu.2 huu.2).2.1,
      (ptT uu.1 huu.1).2.2, (ptT uu.2 huu.2).2.2, quadF_dot hN huu.1 huu.2]
    rfl
  have key := cov_frame (uniformSphere N) bh bℓ bq (by positivity) (by positivity) hτ hτ₂
    hc hc₂ hΔ hD' w
  rw [ebar] at key
  refine le_trans (le_of_eq (integral_congr_ae ?_)) key
  filter_upwards [aeT] with u hu
  rw [hu.1]

/-- **`det_frame_b` on the sphere** for a continuous feature map `h`. -/
theorem sphere_frame_b (hN : 1 ≤ N) {h : (Fin N → ℝ) → Fin m → ℝ} (hcont : Continuous h)
    {b : Fin m → ℝ} {A ξ a δ₂ d δ ε₁ ε₂ β s : ℝ} (hA0 : 0 ≤ A)
    (hA : ∀ w : Fin m → ℝ,
      ∫ u, (∑ j, (h u j - hbar (uniformSphere N) h j) * w j) ^ 2 ∂uniformSphere N ≤
        A * ∑ j, w j ^ 2)
    (hξ : ∑ j, (hbar (uniformSphere N) h j - b j) ^ 2 ≤ ξ)
    (hX : ∫ u, (∑ j, h u j * b j - a) ^ 2 ∂uniformSphere N ≤ δ₂ ^ 2)
    (hd : ∫ u, (normSq (h u) - d) ^ 2 ∂uniformSphere N ≤ δ ^ 2)
    (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (ha : 0 ≤ a) (hβ : 0 < β) (hβb : β ≤ normSq b)
    (hs : 0 < s) (hsle : s ≤ d - ε₁ - (a + ε₂) ^ 2 / β) (w : Fin m → ℝ) :
    ∫ u, (∑ j, eDir b (h u) j * w j) ^ 2 ∂uniformSphere N ≤
      ((A + ξ) / s + δ₂ ^ 2 / ε₂ ^ 2 + δ ^ 2 / ε₁ ^ 2) * ∑ j, w j ^ 2 := by
  have := uniformSphere_isProbability N hN
  set hT : (Fin N → ℝ) → Fin m → ℝ := fun u j => trS (fun u => h u j) u with hhT
  have bh : ∀ j, BM (fun u => hT u j) := fun j =>
    bm_trS ((continuous_apply j).comp hcont)
  have ptT : ∀ u : Fin N → ℝ, normSq u = 1 → hT u = h u := by
    intro u hu
    refine funext fun j => ?_
    simp only [hhT]; exact trS_of _ hu
  have aeT : ∀ᵐ u ∂uniformSphere N, hT u = h u := by
    filter_upwards [uniformSphere_ae_sphere N] with u hu using ptT u hu
  have ebar : hbar (uniformSphere N) hT = hbar (uniformSphere N) h := by
    funext j
    unfold hbar
    refine integral_congr_ae ?_
    filter_upwards [aeT] with u hu
    rw [hu]
  have hA' : ∀ w : Fin m → ℝ,
      ∫ u, (∑ j, (hT u j - hbar (uniformSphere N) hT j) * w j) ^ 2 ∂uniformSphere N ≤
        A * ∑ j, w j ^ 2 := by
    intro w
    rw [ebar]
    refine le_trans (le_of_eq (integral_congr_ae ?_)) (hA w)
    filter_upwards [aeT] with u hu
    rw [hu]
  have hX' : ∫ u, (∑ j, hT u j * b j - a) ^ 2 ∂uniformSphere N ≤ δ₂ ^ 2 := by
    refine le_trans (le_of_eq (integral_congr_ae ?_)) hX
    filter_upwards [aeT] with u hu
    rw [hu]
  have hd' : ∫ u, (normSq (hT u) - d) ^ 2 ∂uniformSphere N ≤ δ ^ 2 := by
    refine le_trans (le_of_eq (integral_congr_ae ?_)) hd
    filter_upwards [aeT] with u hu
    rw [hu]
  have hξ' : ∑ j, (hbar (uniformSphere N) hT j - b j) ^ 2 ≤ ξ := by rw [ebar]; exact hξ
  have key := det_frame_b (uniformSphere N) bh hA0 hA' hξ' hX' hd' hε₁ hε₂
    ha hβ hβb hs hsle w
  refine le_trans (le_of_eq (integral_congr_ae ?_)) key
  filter_upwards [aeT] with u hu
  rw [hu]

end sphere

/-! ## The World network on the good event -/

section good

variable {N m : ℕ}

/-- **The frame bound of the centred hidden features on the good event** (the first half of
`frame_of_good` of Part 136): for `θ ∈ goodHid N m p₁ p₂` and a polynomial model of `κ∘κ`:
`E_u ⟨h(u) − h̄, w⟩² ≤ (m/N)·(b/N + 2c₂/(N(N + 2)) + dK)·|w|²`. -/
theorem cov_of_good (hN : 1 ≤ N) (hm : 1 ≤ m) {p₁ p₂ b c2 η K₃ : ℝ} (hp₁ : 0 < p₁)
    (hb0 : 0 ≤ b) (hc2 : 0 ≤ c2) (hη : 0 ≤ η) (hK₃ : 0 ≤ K₃)
    (hmodel : ∀ t ∈ Icc (-1 : ℝ) 1,
      |kappa (kappa t) - kappa (kappa 0) - b * t - c2 * t ^ 2| ≤ η * t ^ 2 + K₃ * |t| ^ 3)
    {θ : HidParam N m} (hθ : θ ∈ goodHid N m p₁ p₂) (w : Fin m → ℝ) :
    ∫ u, (∑ j, (hid2 θ.1 θ.2 u j - hbar (uniformSphere N) (hid2 θ.1 θ.2) j) * w j) ^ 2
        ∂uniformSphere N ≤
      (m : ℝ) / N * (b / (N : ℝ) + c2 * (2 / ((N : ℝ) * (N + 2))) + dK N m p₁ η K₃) *
        ∑ j, w j ^ 2 := by
  have := lawU2_prob hN
  have := uniformSphere_isProbability N hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨S0, hS0def⟩ : ∃ S0 : ℝ, S0 = (m : ℝ) / N := ⟨_, rfl⟩
  have hS0 : 0 < S0 := by rw [hS0def]; positivity
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = kappa (kappa 0) := ⟨_, rfl⟩
  have hcF := cF2o_pos hm
  have hsp₁ : 0 < √p₁ := Real.sqrt_pos.mpr hp₁
  have hdK0 : 0 ≤ dK N m p₁ η K₃ := by unfold dK; positivity
  have hcontK : Continuous (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => fK N m (uu, θ)) :=
    continuous_fK.comp (continuous_id.prodMk continuous_const)
  -- the finite-width part
  have hfw : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => fK N m (uu, θ))
      (S0 * (cF2o m / √p₁)) := by
    refine ⟨hcontK.aestronglyMeasurable, lawU2_cont_integrable hN (hcontK.pow 2), ?_⟩
    have h1 := hθ.1
    unfold errK at h1
    refine h1.le.trans (le_of_eq ?_)
    have e : (cF2o m / √p₁) ^ 2 = cF2o m ^ 2 / p₁ := by rw [div_pow, Real.sq_sqrt hp₁.le]
    rw [mul_pow S0, e, hS0def]
    ring
  -- the part of `κ∘κ`
  have hmd : Measurable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => dotp uu.1 uu.2) :=
    continuous_dotp.measurable
  have hd4 : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => dotp uu.1 uu.2 ^ 2)
      (√3 / (N : ℝ)) := by
    unfold lawU2
    refine L2le.prod_const_left (hmd.pow_const 2).aestronglyMeasurable ?_
    filter_upwards [uniformSphere_ae_sphere N] with y hy
    exact sphere_dot4 hN hy
  have hd6 : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) => |dotp uu.1 uu.2| ^ 3)
      (√(15 / ((N : ℝ) * (N + 2) * (N + 4)))) := by
    unfold lawU2
    refine L2le.prod_const_left ((hmd.abs).pow_const 3).aestronglyMeasurable ?_
    filter_upwards [uniformSphere_ae_sphere N] with y hy
    exact sphere_dot6 hN hy
  have hmk : Measurable (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - q - b * dotp uu.1 uu.2 - c2 * dotp uu.1 uu.2 ^ 2) :=
    ((((continuous_kappa.comp (continuous_kappa.comp continuous_dotp)).measurable).sub
      measurable_const).sub (hmd.const_mul b)).sub ((hmd.pow_const 2).const_mul c2)
  have hbd := (hd4.const_mul_nonneg hη).add0 (hd6.const_mul_nonneg hK₃) (by positivity)
    (by positivity)
  have hdet0 : L2le (lawU2 N) (fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      kappa (kappa (dotp uu.1 uu.2)) - q - b * dotp uu.1 uu.2 - c2 * dotp uu.1 uu.2 ^ 2)
      (η * (√3 / (N : ℝ)) + K₃ * √(15 / ((N : ℝ) * (N + 2) * (N + 4)))) := by
    refine L2le.abs_le_ae_R hmk.aestronglyMeasurable hbd ?_
    filter_upwards [lawU2_ae_unit hN] with uu huu
    have h := hmodel _ (unit_dot_mem huu.1 huu.2)
    rw [← hq] at h
    rw [abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ η * dotp uu.1 uu.2 ^ 2 + K₃ * |dotp uu.1 uu.2| ^ 3)]
    exact h
  have hdet := hdet0.const_mul_nonneg hS0.le
  have hsum := hfw.add0 hdet (by positivity) (by positivity)
  have hD : ∫ uu, (dotp (hid2 θ.1 θ.2 uu.1) (hid2 θ.1 θ.2 uu.2) - S0 * (q + c2 / (N : ℝ)) -
      S0 * b * dotp uu.1 uu.2 - S0 * c2 * (dotp uu.1 uu.2 ^ 2 - 1 / (N : ℝ))) ^ 2 ∂lawU2 N ≤
      (S0 * dK N m p₁ η K₃) ^ 2 := by
    have h1 := (hsum.congr_fun (g := fun uu : (Fin N → ℝ) × (Fin N → ℝ) =>
      dotp (hid2 θ.1 θ.2 uu.1) (hid2 θ.1 θ.2 uu.2) - S0 * (q + c2 / (N : ℝ)) -
        S0 * b * dotp uu.1 uu.2 - S0 * c2 * (dotp uu.1 uu.2 ^ 2 - 1 / (N : ℝ)))
      (fun uu => by simp only [fK, hS0def, hq]; ring)).le
    refine h1.trans (le_of_eq ?_)
    unfold dK
    ring
  have key := sphere_cov hN (continuous_hid2 θ.1 θ.2) (a := S0 * (q + c2 / (N : ℝ)))
    (c := S0 * b) (c₂ := S0 * c2) (Δ := S0 * dK N m p₁ η K₃) (by positivity) (by positivity)
    (by positivity) hD w
  refine key.trans (le_of_eq ?_)
  rw [← hS0def]
  ring

/-- **The frame bound of the unit residual directions for a general centre `bc`, on the good
event**, in units of `m/N`. Hypotheses on the centre: `|h̄ − bc|² ≤ (m/N)·ξ`;
`‖⟨h(u), bc⟩ − (m/N)·a‖_{L²(u)} ≤ (m/N)·δ₂`; `|bc|² ≥ (m/N)·β`. -/
theorem frameB_of_good (hN : 1 ≤ N) (hm : 1 ≤ m) {p₁ p₂ ε₁ ε₂ s b c2 η K₃ ξ a δ₂ β : ℝ}
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂) (hb0 : 0 ≤ b) (hc2 : 0 ≤ c2)
    (hη : 0 ≤ η) (hK₃ : 0 ≤ K₃)
    (hmodel : ∀ t ∈ Icc (-1 : ℝ) 1,
      |kappa (kappa t) - kappa (kappa 0) - b * t - c2 * t ^ 2| ≤ η * t ^ 2 + K₃ * |t| ^ 3)
    {θ : HidParam N m} (hθ : θ ∈ goodHid N m p₁ p₂) {bc : Fin m → ℝ}
    (hξ : ∑ j, (hbar (uniformSphere N) (hid2 θ.1 θ.2) j - bc j) ^ 2 ≤ (m : ℝ) / N * ξ)
    (hX : ∫ u, (∑ j, hid2 θ.1 θ.2 u j * bc j - (m : ℝ) / N * a) ^ 2 ∂uniformSphere N ≤
      ((m : ℝ) / N * δ₂) ^ 2)
    (ha : 0 ≤ a) (hβ : 0 < β) (hβb : (m : ℝ) / N * β ≤ normSq bc)
    (hs : 0 < s) (hsle : s ≤ 1 - ε₁ - (a + ε₂) ^ 2 / β) (w : Fin m → ℝ) :
    ∫ u, (∑ j, eDir bc (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere N ≤
      ((b / (N : ℝ) + c2 * (2 / ((N : ℝ) * (N + 2))) + dK N m p₁ η K₃ + ξ) / s +
        δ₂ ^ 2 / ε₂ ^ 2 + cF2o m ^ 2 / p₂ / ε₁ ^ 2) * ∑ j, w j ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨S0, hS0def⟩ : ∃ S0 : ℝ, S0 = (m : ℝ) / N := ⟨_, rfl⟩
  have hS0 : 0 < S0 := by rw [hS0def]; positivity
  have hdK0 : 0 ≤ dK N m p₁ η K₃ := by
    have := cF2o_pos hm
    have : 0 < √p₁ := Real.sqrt_pos.mpr hp₁
    unfold dK; positivity
  rw [← hS0def] at hξ hX hβb
  set A0 : ℝ := b / (N : ℝ) + c2 * (2 / ((N : ℝ) * (N + 2))) + dK N m p₁ η K₃ with hA0def
  have hA00 : 0 ≤ A0 := by rw [hA0def]; positivity
  have hA : ∀ w : Fin m → ℝ,
      ∫ u, (∑ j, (hid2 θ.1 θ.2 u j - hbar (uniformSphere N) (hid2 θ.1 θ.2) j) * w j) ^ 2
          ∂uniformSphere N ≤ S0 * A0 * ∑ j, w j ^ 2 := by
    intro w
    have := cov_of_good hN hm hp₁ hb0 hc2 hη hK₃ hmodel hθ w
    rw [← hS0def] at this
    exact this
  have hd : ∫ u, (normSq (hid2 θ.1 θ.2 u) - S0) ^ 2 ∂uniformSphere N ≤
      (S0 * (cF2o m / √p₂)) ^ 2 := by
    have h1 := hθ.2
    unfold errD fD at h1
    rw [hS0def]
    refine h1.le.trans (le_of_eq ?_)
    have e : (cF2o m / √p₂) ^ 2 = cF2o m ^ 2 / p₂ := by rw [div_pow, Real.sq_sqrt hp₂.le]
    rw [mul_pow ((m : ℝ) / N) (cF2o m / √p₂), e]
    ring
  have hsle' : S0 * s ≤ S0 - S0 * ε₁ - (S0 * a + S0 * ε₂) ^ 2 / (S0 * β) := by
    have e : (S0 * a + S0 * ε₂) ^ 2 / (S0 * β) = S0 * ((a + ε₂) ^ 2 / β) := by
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left hsle hS0.le
    linarith
  have key := sphere_frame_b hN (continuous_hid2 θ.1 θ.2) (b := bc) (A := S0 * A0)
    (ξ := S0 * ξ) (a := S0 * a) (δ₂ := S0 * δ₂) (d := S0) (δ := S0 * (cF2o m / √p₂))
    (ε₁ := S0 * ε₁) (ε₂ := S0 * ε₂) (β := S0 * β) (s := S0 * s) (by positivity) hA hξ hX hd
    (by positivity) (by positivity) (by positivity) (by positivity) hβb (by positivity) hsle' w
  refine key.trans (le_of_eq ?_)
  congr 1
  have e1 : (S0 * A0 + S0 * ξ) / (S0 * s) = (A0 + ξ) / s := by
    field_simp
  have e2 : (S0 * δ₂) ^ 2 / (S0 * ε₂) ^ 2 = δ₂ ^ 2 / ε₂ ^ 2 := by
    field_simp
  have e3 : (S0 * (cF2o m / √p₂)) ^ 2 / (S0 * ε₁) ^ 2 = cF2o m ^ 2 / p₂ / ε₁ ^ 2 := by
    rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt hp₂.le]
    field_simp
  rw [e1, e2, e3]

end good

/-! ## Numbers at the widths of the Focus -/

/-- **The frame bound `C/n` for a general centre `bc` on the good event**, for every
`n ≥ n₀ ≥ 4096`, from the certificates of `lam_num` of Part 136 and the three hypotheses on the
centre in units of `m/N` and `1/n`: `|h̄ − bc|² ≤ (m/N)·ξ₀/n`,
`E_u(⟨h(u), bc⟩ − (m/N)·a)² ≤ (m/N)²·dT/n`, `|bc|² ≥ (m/N)·β`. -/
theorem frameB_num {n n0 : ℕ} (hn0 : 4096 ≤ n0) (hn : n0 ≤ n)
    {b c2 η K₃ r0 k0 k6 sp ε₁ ε₂ s p₂ D0 C ξ₀ a dT β : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 3017 / 10000) (hc2 : 0 ≤ c2) (hη : 0 ≤ η) (hK₃ : 0 ≤ K₃)
    (hmodel : ∀ t ∈ Icc (-1 : ℝ) 1,
      |kappa (kappa t) - kappa (kappa 0) - b * t - c2 * t ^ 2| ≤ η * t ^ 2 + K₃ * |t| ^ 3)
    (hr0 : 0 ≤ r0) (hr : 1 ≤ r0 ^ 2 * (n0 : ℝ) ^ 3)
    (hk0 : 0 ≤ k0) (hk : 2235 / 100 * r0 ≤ k0 ^ 2)
    (hk60 : 0 ≤ k6) (hk6 : 15 / (8 * (n0 : ℝ)) ≤ k6 ^ 2)
    (hsp : 0 < sp) (hp₂ : 0 < p₂) (hε₁ : 0 < ε₁) (hε₂ : 0 < ε₂)
    (hD0 : D0 = k0 / sp + η * (17321 / 20000) + K₃ * k6)
    (hdT : 0 ≤ dT) (ha : 0 ≤ a) (hβ : 0 < β)
    (hs : 0 < s) (hsle : s ≤ 1 - ε₁ - (a + ε₂) ^ 2 / β)
    (hC : (3017 / 20000 + c2 / (2 * (n0 : ℝ)) + D0 + ξ₀) / s + dT / ε₂ ^ 2 +
      2235 / 100 * r0 / ((n0 : ℝ) * p₂ * ε₁ ^ 2) ≤ C)
    {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ goodHid (2 * n) (mW n) (sp ^ 2) p₂)
    {bc : Fin (mW n) → ℝ}
    (hξ : ∑ j, (hbar (uniformSphere (2 * n)) (hid2 θ.1 θ.2) j - bc j) ^ 2 ≤
      (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * (ξ₀ / (n : ℝ)))
    (hX : ∫ u, (∑ j, hid2 θ.1 θ.2 u j * bc j - (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * a) ^ 2
        ∂uniformSphere (2 * n) ≤ ((mW n : ℝ) / ((2 * n : ℕ) : ℝ)) ^ 2 * (dT / (n : ℝ)))
    (hβb : (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * β ≤ normSq bc) (w : Fin (mW n) → ℝ) :
    ∫ u, (∑ j, eDir bc (hid2 θ.1 θ.2 u) j * w j) ^ 2 ∂uniformSphere (2 * n) ≤
      C / (n : ℝ) * ∑ j, w j ^ 2 := by
  have hn4 : 4096 ≤ n := hn0.trans hn
  have hn0' : (4096 : ℝ) ≤ n0 := by exact_mod_cast hn0
  have hn' : (n0 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0pos : (0 : ℝ) < n0 := by linarith
  have hnpos : (0 : ℝ) < n := by linarith
  have hN : 1 ≤ 2 * n := by omega
  have hmM := mW_ge_million hn4
  have hm : 1 ≤ mW n := by omega
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
    linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hcF := cF2o_pos hm
  have hcF2 := cF2o_sq_le hmM
  have hrat := ratio_le (by omega : 1 ≤ n0) hn hr0 hr
  have s3 := sqrt3_le
  have s30 : 0 ≤ √3 := Real.sqrt_nonneg _
  -- `n·cF2o ≤ k₀`
  have hncF : (n : ℝ) * cF2o (mW n) ≤ k0 := by
    refine le_of_abs_le (abs_le_of_sq_le_sq ?_ hk0)
    rw [mul_pow]
    have h1 : (n : ℝ) ^ 2 * cF2o (mW n) ^ 2 ≤ (n : ℝ) ^ 2 * (2235 / 100 / (mW n : ℝ)) :=
      mul_le_mul_of_nonneg_left hcF2 (sq_nonneg _)
    have e : (n : ℝ) ^ 2 * (2235 / 100 / (mW n : ℝ)) =
        2235 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) := by ring
    rw [e] at h1
    have h2 : 2235 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) ≤ 2235 / 100 * r0 :=
      mul_le_mul_of_nonneg_left hrat (by norm_num)
    linarith
  have hne6 := n_e6_le hn0pos hn' hk60 hk6
  have hD0nn : 0 ≤ D0 := by rw [hD0]; positivity
  -- `dK ≤ D₀/n`
  have hsqrt : √(sp ^ 2) = sp := Real.sqrt_sq hsp.le
  have hdKn : dK (2 * n) (mW n) (sp ^ 2) η K₃ ≤ D0 / (n : ℝ) := by
    unfold dK
    rw [hsqrt, hNcast, le_div_iff₀ hnpos, hD0]
    have e : (cF2o (mW n) / sp + η * (√3 / (2 * (n : ℝ))) +
        K₃ * √(15 / (2 * (n : ℝ) * (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 4)))) * (n : ℝ) =
        (n : ℝ) * cF2o (mW n) / sp + η * (√3 / 2) +
          K₃ * ((n : ℝ) * √(15 / (2 * (n : ℝ) * (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 4)))) := by
      field_simp
    rw [e]
    have h1 : (n : ℝ) * cF2o (mW n) / sp ≤ k0 / sp := div_le_div_of_nonneg_right hncF hsp.le
    have h2 : η * (√3 / 2) ≤ η * (17321 / 20000) :=
      mul_le_mul_of_nonneg_left (by linarith) hη
    have h3 := mul_le_mul_of_nonneg_left hne6 hK₃
    linarith
  have hdK0 : 0 ≤ dK (2 * n) (mW n) (sp ^ 2) η K₃ := by unfold dK; positivity
  have hδ : 0 ≤ √(dT / (n : ℝ)) := Real.sqrt_nonneg _
  have hX' : ∫ u, (∑ j, hid2 θ.1 θ.2 u j * bc j - (mW n : ℝ) / ((2 * n : ℕ) : ℝ) * a) ^ 2
      ∂uniformSphere (2 * n) ≤ ((mW n : ℝ) / ((2 * n : ℕ) : ℝ) * √(dT / (n : ℝ))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    exact hX
  have g2 := frameB_of_good hN hm (by positivity : (0 : ℝ) < sp ^ 2) hp₂ hε₁ hε₂ hb0 hc2 hη hK₃
    hmodel hθ hξ hX' ha hβ hβb hs hsle w
  refine g2.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun j _ => sq_nonneg _)
  rw [hNcast, Real.sq_sqrt (by positivity)]
  -- the three terms
  have hnn : (n0 : ℝ) * (n : ℝ) ≤ (n : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_right hn' hnpos.le
  have t1 : (b / (2 * (n : ℝ)) + c2 * (2 / (2 * (n : ℝ) * (2 * (n : ℝ) + 2))) +
      dK (2 * n) (mW n) (sp ^ 2) η K₃ + ξ₀ / (n : ℝ)) / s ≤
      (3017 / 20000 + c2 / (2 * (n0 : ℝ)) + D0 + ξ₀) / s / (n : ℝ) := by
    rw [div_right_comm]
    refine div_le_div_of_nonneg_right ?_ hs.le
    rw [add_div, add_div, add_div]
    have h1 : b / (2 * (n : ℝ)) ≤ 3017 / 20000 / (n : ℝ) := by
      have e1 : b / (2 * (n : ℝ)) = b / 2 / (n : ℝ) := by rw [div_div]
      rw [e1]
      exact div_le_div_of_nonneg_right (by linarith) hnpos.le
    have h2 : c2 * (2 / (2 * (n : ℝ) * (2 * (n : ℝ) + 2))) ≤ c2 / (2 * (n0 : ℝ)) / (n : ℝ) := by
      have e2 : c2 / (2 * (n0 : ℝ)) / (n : ℝ) = c2 * (1 / (2 * (n0 : ℝ) * (n : ℝ))) := by
        rw [div_div, mul_one_div]
      rw [e2]
      refine mul_le_mul_of_nonneg_left ?_ hc2
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      linarith
    linarith
  have t2 : dT / (n : ℝ) / ε₂ ^ 2 = dT / ε₂ ^ 2 / (n : ℝ) := by
    rw [div_right_comm]
  have t3 : cF2o (mW n) ^ 2 / p₂ / ε₁ ^ 2 ≤
      2235 / 100 * r0 / ((n0 : ℝ) * p₂ * ε₁ ^ 2) / (n : ℝ) := by
    have h1 : cF2o (mW n) ^ 2 ≤ 2235 / 100 * r0 / ((n0 : ℝ) * (n : ℝ)) := by
      refine hcF2.trans ?_
      have h2 : 1 / (mW n : ℝ) ≤ r0 / ((n0 : ℝ) * (n : ℝ)) := by
        have e : 1 / (mW n : ℝ) = (n : ℝ) ^ 2 / (mW n : ℝ) / ((n : ℝ) * (n : ℝ)) := by
          field_simp
        rw [e]
        have h3 : (n : ℝ) ^ 2 / (mW n : ℝ) / ((n : ℝ) * (n : ℝ)) ≤ r0 / ((n : ℝ) * (n : ℝ)) :=
          div_le_div_of_nonneg_right hrat (by positivity)
        have h4 : r0 / ((n : ℝ) * (n : ℝ)) ≤ r0 / ((n0 : ℝ) * (n : ℝ)) :=
          div_le_div_of_nonneg_left hr0 (by positivity)
            (mul_le_mul_of_nonneg_right hn' hnpos.le)
        linarith
      have e1 : 2235 / 100 / (mW n : ℝ) = 2235 / 100 * (1 / (mW n : ℝ)) := by ring
      have e2 : 2235 / 100 * r0 / ((n0 : ℝ) * (n : ℝ)) =
          2235 / 100 * (r0 / ((n0 : ℝ) * (n : ℝ))) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left h2 (by norm_num)
    have e : 2235 / 100 * r0 / ((n0 : ℝ) * p₂ * ε₁ ^ 2) / (n : ℝ) =
        2235 / 100 * r0 / ((n0 : ℝ) * (n : ℝ)) / p₂ / ε₁ ^ 2 := by
      field_simp
    rw [e]
    exact div_le_div_of_nonneg_right (div_le_div_of_nonneg_right h1 hp₂.le) (by positivity)
  have hCn : ((3017 / 20000 + c2 / (2 * (n0 : ℝ)) + D0 + ξ₀) / s + dT / ε₂ ^ 2 +
      2235 / 100 * r0 / ((n0 : ℝ) * p₂ * ε₁ ^ 2)) / (n : ℝ) ≤ C / (n : ℝ) :=
    div_le_div_of_nonneg_right hC hnpos.le
  rw [add_div, add_div] at hCn
  rw [t2]
  linarith

end BstLean.Part140

open BstLean.Part140 in
#print axioms det_frame_b
open BstLean.Part140 in
#print axioms sphere_cov
open BstLean.Part140 in
#print axioms sphere_frame_b
open BstLean.Part140 in
#print axioms cov_of_good
open BstLean.Part140 in
#print axioms frameB_of_good
open BstLean.Part140 in
#print axioms frameB_num
