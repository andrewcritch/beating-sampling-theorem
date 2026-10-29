import BstLean.Part140Norm

/-!
# Part 140, item 1: the computed centre `b̂ = ψ_s(M₂ h̄₁)` is close to the exact centre `h̄`

Role: `delegations/statements/p140-spec.md` (item 1). Paper sources: `onW5c-cx.md` §4
(`|ĥ₂ − h̄₂|² ≤ X·m/N²`), `onW8c-cx.md` §§3–4.

`N` inputs, hidden width `m`, `t = 2/m`, `γ = 2/N`, `θ = (M₁, M₂)`, `h̄ = hbarW θ`, `b̂ = bhat θ`.

* `dist2 N m θ = t|b̂ − h̄|²`; `Xh N m θ = t⟨h̄, b̂⟩ = E_u T̂(u)`; `Hh N m θ = t|h̄|²`.
* `dist2_eq`: `t|b̂ − h̄|² = t|b̂|² − 2t⟨h̄, b̂⟩ + t|h̄|²`.
* `Xh_L2`, `Hh_L2`: `‖t⟨h̄, b̂⟩ − γκ(q₁)‖₂ ≤ γ·cHat2`, `‖t|h̄|² − γq_N‖₂ ≤ γ·cF2o` over `θ` (Jensen
  over the input, from Lemma H2(b) and Lemma H2(d) of Part 137).
* **`dist2_L2`**: `‖t|b̂ − h̄|² − γ(q_N − κ(q₁))‖_{L²(θ)} ≤ γ·cDst N m`,
  `cDst = cB + 2·cHat2 + cF2o` (of order `m^{−1/2}`); and `0 ≤ q_N − κ(q₁) ≤ (8/25)/N`.
* **`centreDist_gen`**: `E_θ t|b̂ − h̄|² ≤ γ·((8/25)/N + cDst N m)`, every `N, m ≥ 1`.
* **`centreDist140`**: `N = 2n`, `m = mW n`, `n ≥ 4096`: `E_θ t|b̂ − h̄|² ≤ (19/50)·γ/N`.
* `goodDist n Xc`: the event `t|b̂ − h̄|² ≤ γ·Xc/N`; `goodDist_prob`: its complement has
  probability at most `(21/2)/((Xc − 8/25)²·n)` (`Xc > 8/25`).
* `errT θ = E_u(T̂(u) − γκ(q₁))²`; `errT_mean`; `errT_bad` (Markov).
* **`Bh_window`**: on `good136 n` and `goodDist n (3/4)`:
  `0.48·γ ≤ t|b̂|² ≤ 0.508·γ` (so `b̂ ≠ 0`).
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part140

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (stdGauss uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part105 (sphere_cont_integrable)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part134 BstLean.Part136
open BstLean.Part137

variable {N m : ℕ}

/-! ## Definitions and algebra -/

/-- **`t|b̂ − h̄|²`**: the squared distance of the computed centre and the exact centre. -/
noncomputable def dist2 (N m : ℕ) (θ : HidParam N m) : ℝ :=
  2 / (m : ℝ) * normSq (bhat θ - hbarW θ)

/-- `t⟨h̄, b̂⟩`. -/
noncomputable def Xh (N m : ℕ) (θ : HidParam N m) : ℝ := 2 / (m : ℝ) * dotp (hbarW θ) (bhat θ)

/-- `t|h̄|²`. -/
noncomputable def Hh (N m : ℕ) (θ : HidParam N m) : ℝ := 2 / (m : ℝ) * normSq (hbarW θ)

/-- The constant of the distance: `cB + 2·cHat2 + cF2o`. -/
noncomputable def cDst (N m : ℕ) : ℝ := cB N m + 2 * cHat2 N m + cF2o m

lemma dist2_eq (θ : HidParam N m) : dist2 N m θ = Bh N m θ - 2 * Xh N m θ + Hh N m θ := by
  unfold dist2 Bh Xh Hh
  rw [normSq_sub_eq, dotp_comm' (bhat θ) (hbarW θ)]
  ring

lemma dist2_nonneg (θ : HidParam N m) : 0 ≤ dist2 N m θ :=
  mul_nonneg (by positivity) (normSq_nonneg _)

lemma Hh_eq_Bn (hN : 1 ≤ N) (θ : HidParam N m) :
    Hh N m θ = 2 / (N : ℝ) * Part137.Bn N m θ := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  unfold Hh Part137.Bn
  field_simp

lemma measurable_dist2 (hN : 1 ≤ N) : Measurable (dist2 N m) :=
  (measurable_normSq.comp ((measurable_bhat hN).sub (measurable_hbarW hN))).const_mul _

lemma continuous_That_u (θ : HidParam N m) : Continuous (fun u => That N m u θ) :=
  continuous_const.mul (continuous_dotp.comp ((continuous_hid2_u θ).prodMk continuous_const))

/-- `E_u T̂(u) = t⟨h̄, b̂⟩`. -/
lemma That_mean (hN : 1 ≤ N) (θ : HidParam N m) :
    ∫ u, That N m u θ ∂uniformSphere N = Xh N m θ := by
  unfold That Xh
  rw [integral_const_mul]
  congr 1
  unfold dotp
  rw [integral_finsetSum _ fun j _ =>
    (sphere_cont_integrable hN (continuous_hid2_coord θ j)).mul_const _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_mul_const]
  rfl

/-! ## The three `L²` bounds over `θ` -/

/-- `‖t⟨h̄, b̂⟩ − γκ(q₁)‖_{L²(θ)} ≤ γ·cHat2 N m`. -/
theorem Xh_L2 (hN : 1 ≤ N) (hm : 1 ≤ m) :
    L2le (hidGauss N m) (fun θ => Xh N m θ - 2 / (N : ℝ) * kap1 N)
      (2 / (N : ℝ) * cHat2 N m) := by
  have := uniformSphere_isProbability N hN
  obtain ⟨h1, h2⟩ := hatFluct2_joint (m := m) hN hm
  have hj : L2le ((uniformSphere N).prod (hidGauss N m))
      (fun p : (Fin N → ℝ) × HidParam N m =>
        That N m p.1 p.2 - 2 / (N : ℝ) * kappa (q1 (e0 N))) (2 / (N : ℝ) * cHat2 N m) :=
    ⟨(((measurable_That hN).sub_const _ :)).aestronglyMeasurable, h1, h2⟩
  refine hj.integral_left.congr_fun fun θ => ?_
  rw [integral_sub (sphere_cont_integrable hN (continuous_That_u θ)) (integrable_const _),
    That_mean hN]
  simp [kap1]

/-- `‖t|h̄|² − γq_N‖_{L²(θ)} ≤ γ·cF2o m`. -/
theorem Hh_L2 (hN : 1 ≤ N) (hm : 1 ≤ m) :
    L2le (hidGauss N m) (fun θ => Hh N m θ - 2 / (N : ℝ) * qN N) (2 / (N : ℝ) * cF2o m) := by
  have := uniformSphere_isProbability N hN
  obtain ⟨h1, h2⟩ := innerFluct137_joint (m := m) hN hm
  have hj : L2le ((uniformSphere N).prod (hidGauss N m))
      (fun p : (Fin N → ℝ) × HidParam N m => Tn N m p.1 p.2 - 2 / (N : ℝ) * qN N)
      (2 / (N : ℝ) * cF2o m) :=
    ⟨(((measurable_Tn hN).sub_const _ :)).aestronglyMeasurable, h1, h2⟩
  refine hj.integral_left.congr_fun fun θ => ?_
  rw [integral_sub (sphere_cont_integrable hN (continuous_Tn_u θ)) (integrable_const _),
    Tn_mean hN]
  simp [Hh]

lemma cB_nonneg (N m : ℕ) : 0 ≤ cB N m := Real.sqrt_nonneg _

lemma cHat2_nonneg (N m : ℕ) : 0 ≤ cHat2 N m := Real.sqrt_nonneg _

lemma cDst_nonneg (hm : 1 ≤ m) : 0 ≤ cDst N m := by
  have := cB_nonneg N m
  have := cHat2_nonneg N m
  have := (cF2o_pos hm).le
  unfold cDst
  linarith

/-- **The distance in `L²(θ)`**: `‖t|b̂ − h̄|² − γ(q_N − κ(q₁))‖₂ ≤ γ·cDst N m`. -/
theorem dist2_L2 (hN : 1 ≤ N) (hm : 1 ≤ m) :
    L2le (hidGauss N m) (fun θ => dist2 N m θ - 2 / (N : ℝ) * (qN N - kap1 N))
      (2 / (N : ℝ) * cDst N m) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hγ : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
  have hB := bhatNorm_L2 (m := m) hN hm
  have hX := (Xh_L2 (m := m) hN hm).const_mul (-2)
  have hH := Hh_L2 (m := m) hN hm
  have e2 : |(-2 : ℝ)| = 2 := by norm_num
  rw [e2] at hX
  have h1 := hB.add' hX (mul_nonneg hγ (cB_nonneg N m))
    (mul_nonneg (by norm_num) (mul_nonneg hγ (cHat2_nonneg N m)))
  have h2 := h1.add' hH
    (add_nonneg (mul_nonneg hγ (cB_nonneg N m))
      (mul_nonneg (by norm_num) (mul_nonneg hγ (cHat2_nonneg N m))))
    (mul_nonneg hγ (cF2o_pos hm).le)
  refine (h2.congr_fun fun θ => ?_).congr_bound ?_
  · rw [dist2_eq]
    ring
  · unfold cDst
    ring

/-- `q_N − κ(q₁) ≤ (8/25)/N`. -/
lemma qN_sub_kap1_le (hN : 1 ≤ N) : qN N - kap1 N ≤ 8 / 25 / (N : ℝ) := by
  have h1 := qN_le hN
  have h2 := kap1_ge hN
  linarith

/-- **The mean squared distance, every `N, m ≥ 1`**:
`E_θ t|b̂ − h̄|² ≤ γ·((8/25)/N + cDst N m)`. -/
theorem centreDist_gen (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (dist2 N m) (hidGauss N m) ∧
      ∫ θ, dist2 N m θ ∂hidGauss N m ≤ 2 / (N : ℝ) * (8 / 25 / (N : ℝ) + cDst N m) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hγ : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
  have h := dist2_L2 (m := m) hN hm
  set c0 : ℝ := 2 / (N : ℝ) * (qN N - kap1 N) with hc0
  have hf : Integrable (fun θ => dist2 N m θ - c0) (hidGauss N m) :=
    ((memLp_two_iff_integrable_sq h.aesm).mpr h.int_sq).integrable one_le_two
  have hd : Integrable (dist2 N m) (hidGauss N m) := by
    have := hf.add (integrable_const c0)
    refine this.congr (Filter.Eventually.of_forall fun θ => ?_)
    simp
  refine ⟨hd, ?_⟩
  have h1 := sq_integral_le (ρ := hidGauss N m) h.int_sq
  have h2 : (∫ θ, (dist2 N m θ - c0) ∂hidGauss N m) ^ 2 ≤ (2 / (N : ℝ) * cDst N m) ^ 2 :=
    h1.trans h.le
  have h3 : ∫ θ, (dist2 N m θ - c0) ∂hidGauss N m ≤ 2 / (N : ℝ) * cDst N m :=
    le_of_abs_le (abs_le_of_sq_le_sq h2 (mul_nonneg hγ (cDst_nonneg hm)))
  rw [integral_sub hd (integrable_const _)] at h3
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h3
  have h4 : c0 ≤ 2 / (N : ℝ) * (8 / 25 / (N : ℝ)) :=
    mul_le_mul_of_nonneg_left (qN_sub_kap1_le hN) hγ
  linarith

/-- **The far event, every `N, m ≥ 1`** (Chebyshev): for `Xc > 8/25`,
`Pr(t|b̂ − h̄|² > γ·Xc/N) ≤ (N·cDst N m)²/(Xc − 8/25)²`. -/
theorem distBad_gen (hN : 1 ≤ N) (hm : 1 ≤ m) {Xc : ℝ} (hXc : 8 / 25 < Xc) :
    (hidGauss N m).real {θ | 2 / (N : ℝ) * (Xc / (N : ℝ)) < dist2 N m θ} ≤
      ((N : ℝ) * cDst N m) ^ 2 / (Xc - 8 / 25) ^ 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hγ : (0 : ℝ) < 2 / (N : ℝ) := by positivity
  have h := dist2_L2 (m := m) hN hm
  set c0 : ℝ := 2 / (N : ℝ) * (qN N - kap1 N) with hc0
  set ε : ℝ := 2 / (N : ℝ) * ((Xc - 8 / 25) / (N : ℝ)) with hε
  have hεpos : 0 < ε := by
    have : 0 < Xc - 8 / 25 := by linarith
    rw [hε]; positivity
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := hidGauss N m)
    (f := fun θ => (dist2 N m θ - c0) ^ 2) (Filter.Eventually.of_forall fun θ => sq_nonneg _)
    h.int_sq (ε ^ 2)
  have hsub : {θ : HidParam N m | 2 / (N : ℝ) * (Xc / (N : ℝ)) < dist2 N m θ} ⊆
      {θ | ε ^ 2 ≤ (dist2 N m θ - c0) ^ 2} := by
    intro θ hθ
    have hθ' : 2 / (N : ℝ) * (Xc / (N : ℝ)) < dist2 N m θ := hθ
    have h4 : c0 ≤ 2 / (N : ℝ) * (8 / 25 / (N : ℝ)) :=
      mul_le_mul_of_nonneg_left (qN_sub_kap1_le hN) hγ.le
    have h5 : ε ≤ dist2 N m θ - c0 := by
      have e : ε = 2 / (N : ℝ) * (Xc / (N : ℝ)) - 2 / (N : ℝ) * (8 / 25 / (N : ℝ)) := by
        rw [hε]; ring
      linarith
    exact pow_le_pow_left₀ hεpos.le h5 2
  have hmono := measureReal_mono (μ := hidGauss N m) hsub (measure_ne_top _ _)
  have h6 : ε ^ 2 * (hidGauss N m).real {θ | 2 / (N : ℝ) * (Xc / (N : ℝ)) < dist2 N m θ} ≤
      (2 / (N : ℝ) * cDst N m) ^ 2 :=
    (mul_le_mul_of_nonneg_left hmono (sq_nonneg _)).trans (hmk.trans h.le)
  have hX0 : 0 < Xc - 8 / 25 := by linarith
  rw [le_div_iff₀ (by positivity)]
  have e : ε ^ 2 = (2 / (N : ℝ)) ^ 2 * ((Xc - 8 / 25) ^ 2 / (N : ℝ) ^ 2) := by
    rw [hε]; ring
  rw [e] at h6
  have hg2 : (0 : ℝ) < (2 / (N : ℝ)) ^ 2 := by positivity
  have h7 : (2 / (N : ℝ)) ^ 2 * ((hidGauss N m).real
        {θ | 2 / (N : ℝ) * (Xc / (N : ℝ)) < dist2 N m θ} * (Xc - 8 / 25) ^ 2) ≤
      (2 / (N : ℝ)) ^ 2 * (((N : ℝ) * cDst N m) ^ 2) := by
    have e1 : (2 / (N : ℝ)) ^ 2 * ((hidGauss N m).real
        {θ | 2 / (N : ℝ) * (Xc / (N : ℝ)) < dist2 N m θ} * (Xc - 8 / 25) ^ 2) =
        (N : ℝ) ^ 2 * ((2 / (N : ℝ)) ^ 2 * ((Xc - 8 / 25) ^ 2 / (N : ℝ) ^ 2) *
          (hidGauss N m).real {θ | 2 / (N : ℝ) * (Xc / (N : ℝ)) < dist2 N m θ}) := by
      field_simp
    have e2 : (2 / (N : ℝ)) ^ 2 * (((N : ℝ) * cDst N m) ^ 2) =
        (N : ℝ) ^ 2 * (2 / (N : ℝ) * cDst N m) ^ 2 := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h6 (sq_nonneg _)
  exact le_of_mul_le_mul_left h7 hg2

/-! ## The integrated error of `T̂` -/

/-- `errT θ = E_u (T̂(u) − γκ(q₁))²`. -/
noncomputable def errT (θ : HidParam N m) : ℝ :=
  ∫ u, (That N m u θ - 2 / (N : ℝ) * kap1 N) ^ 2 ∂uniformSphere N

lemma errT_nonneg (θ : HidParam N m) : 0 ≤ errT θ := integral_nonneg fun _ => sq_nonneg _

lemma measurable_errT (hN : 1 ≤ N) : Measurable (errT (N := N) (m := m)) := by
  have := uniformSphere_isProbability N hN
  unfold errT
  exact (((((measurable_That hN).sub_const (2 / (N : ℝ) * kap1 N) :)).pow_const
    2).stronglyMeasurable.integral_prod_left').measurable

theorem errT_mean (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (errT (N := N) (m := m)) (hidGauss N m) ∧
      ∫ θ, errT θ ∂hidGauss N m ≤ (2 / (N : ℝ) * cHat2 N m) ^ 2 := by
  have := uniformSphere_isProbability N hN
  obtain ⟨h1, h2⟩ := hatFluct2_joint (m := m) hN hm
  refine ⟨h1.integral_prod_right, ?_⟩
  have e := integral_prod_symm _ h1
  unfold errT kap1
  rw [← e]
  exact h2

/-- Markov for `errT`. -/
theorem errT_bad (hN : 1 ≤ N) (hm : 1 ≤ m) {B : ℝ} (hB : 0 < B) :
    (hidGauss N m).real {θ | B < errT θ} ≤ (2 / (N : ℝ) * cHat2 N m) ^ 2 / B := by
  obtain ⟨hi, hle⟩ := errT_mean (m := m) hN hm
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := hidGauss N m) (f := errT)
    (Filter.Eventually.of_forall errT_nonneg) hi B
  have hsub : {θ : HidParam N m | B < errT θ} ⊆ {θ | B ≤ errT θ} :=
    fun θ (hθ : B < errT θ) => (le_of_lt hθ : B ≤ errT θ)
  have hmono := measureReal_mono (μ := hidGauss N m) hsub (measure_ne_top _ _)
  rw [le_div_iff₀ hB, mul_comm]
  exact (mul_le_mul_of_nonneg_left hmono hB.le).trans (hmk.trans hle)

/-! ## The window of `t|b̂|²` -/

/-- The triangle inequality for `nrm`. -/
lemma nrm_add_le' {ι : Type*} [Fintype ι] (a c : ι → ℝ) : nrm (a + c) ≤ nrm a + nrm c := by
  have h1 := normSq_add_eq a c
  have h2 := abs_dotp_le_nrm a c
  have h3 := le_abs_self (dotp a c)
  have ha := nrm_sq a
  have hc := nrm_sq c
  have hac := nrm_sq (a + c)
  refine le_of_abs_le (abs_le_of_sq_le_sq ?_ (add_nonneg (nrm_nonneg a) (nrm_nonneg c)))
  nlinarith

lemma normSq_sub_comm {ι : Type*} [Fintype ι] (a c : ι → ℝ) : normSq (a - c) = normSq (c - a) := by
  rw [normSq_sub_eq, normSq_sub_eq, dotp_comm' a c]
  ring

/-- The real-number core of the window: `x, y, z ≥ 0` with `|x − y| ≤ z`, `gL ≤ y² ≤ gU`,
`z² ≤ gξ`, and rational bounds of the three square roots. -/
lemma window_core {x y z L U ξ g sL sU sξ : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (_hz : 0 ≤ z)
    (hxy : x ≤ y + z) (hyx : y ≤ x + z) (hg : 0 < g) (hL : g * L ≤ y ^ 2) (hU : y ^ 2 ≤ g * U)
    (hξ : z ^ 2 ≤ g * ξ) (_h1 : 0 ≤ sL) (h1' : sL ^ 2 ≤ L) (h2 : 0 ≤ sU) (h2' : U ≤ sU ^ 2)
    (h3 : 0 ≤ sξ) (h3' : ξ ≤ sξ ^ 2) (h4 : sξ ≤ sL) :
    g * (sL - sξ) ^ 2 ≤ x ^ 2 ∧ x ^ 2 ≤ g * (sU + sξ) ^ 2 := by
  set r := √g with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hg
  have hr2 : r ^ 2 = g := Real.sq_sqrt hg.le
  have hyL : r * sL ≤ y := by
    refine le_of_abs_le (abs_le_of_sq_le_sq ?_ hy)
    rw [mul_pow, hr2]
    exact (mul_le_mul_of_nonneg_left h1' hg.le).trans hL
  have hyU : y ≤ r * sU := by
    refine le_of_abs_le (abs_le_of_sq_le_sq ?_ (mul_nonneg hr0.le h2))
    rw [mul_pow, hr2]
    exact hU.trans (mul_le_mul_of_nonneg_left h2' hg.le)
  have hzU : z ≤ r * sξ := by
    refine le_of_abs_le (abs_le_of_sq_le_sq ?_ (mul_nonneg hr0.le h3))
    rw [mul_pow, hr2]
    exact hξ.trans (mul_le_mul_of_nonneg_left h3' hg.le)
  constructor
  · have h5 : r * (sL - sξ) ≤ x := by nlinarith
    have h6 : 0 ≤ r * (sL - sξ) := mul_nonneg hr0.le (by linarith)
    have := pow_le_pow_left₀ h6 h5 2
    rw [mul_pow, hr2] at this
    exact this
  · have h5 : x ≤ r * (sU + sξ) := by nlinarith
    have := pow_le_pow_left₀ hx h5 2
    rw [mul_pow, hr2] at this
    exact this

/-- **The window of `t|b̂|²`, general form**: from `γL ≤ t|h̄|² ≤ γU` and `t|b̂ − h̄|² ≤ γξ`, with
rational bounds of the square roots. -/
theorem Bh_window_gen (hN : 1 ≤ N) (hm : 1 ≤ m) {θ : HidParam N m} {L U ξ sL sU sξ : ℝ}
    (hL : 2 / (N : ℝ) * L ≤ Hh N m θ) (hU : Hh N m θ ≤ 2 / (N : ℝ) * U)
    (hξ : dist2 N m θ ≤ 2 / (N : ℝ) * ξ) (h1 : 0 ≤ sL) (h1' : sL ^ 2 ≤ L) (h2 : 0 ≤ sU)
    (h2' : U ≤ sU ^ 2) (h3 : 0 ≤ sξ) (h3' : ξ ≤ sξ ^ 2) (h4 : sξ ≤ sL) :
    2 / (N : ℝ) * (sL - sξ) ^ 2 ≤ Bh N m θ ∧ Bh N m θ ≤ 2 / (N : ℝ) * (sU + sξ) ^ 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have ht : (0 : ℝ) < 2 / (m : ℝ) := by positivity
  set r := √(2 / (m : ℝ)) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr ht
  have hr2 : r ^ 2 = 2 / (m : ℝ) := Real.sq_sqrt ht.le
  set b := bhat θ with hb
  set h := hbarW θ with hh
  have eB : (r * nrm b) ^ 2 = Bh N m θ := by
    rw [mul_pow, hr2, nrm_sq]; rfl
  have eH : (r * nrm h) ^ 2 = Hh N m θ := by
    rw [mul_pow, hr2, nrm_sq]; rfl
  have eD : (r * nrm (b - h)) ^ 2 = dist2 N m θ := by
    rw [mul_pow, hr2, nrm_sq]; rfl
  have t1 : nrm b ≤ nrm h + nrm (b - h) := by
    have := nrm_add_le' h (b - h)
    have e : h + (b - h) = b := by abel
    rwa [e] at this
  have t2 : nrm h ≤ nrm b + nrm (b - h) := by
    have := nrm_add_le' b (h - b)
    have e : b + (h - b) = h := by abel
    rw [e] at this
    have e2 : nrm (h - b) = nrm (b - h) := by
      unfold nrm
      rw [normSq_sub_comm]
    rwa [e2] at this
  have key := window_core (x := r * nrm b) (y := r * nrm h) (z := r * nrm (b - h))
    (mul_nonneg hr0.le (nrm_nonneg _)) (mul_nonneg hr0.le (nrm_nonneg _))
    (mul_nonneg hr0.le (nrm_nonneg _))
    (by have := mul_le_mul_of_nonneg_left t1 hr0.le; linarith)
    (by have := mul_le_mul_of_nonneg_left t2 hr0.le; linarith)
    (by positivity : (0 : ℝ) < 2 / (N : ℝ)) (by rw [eH]; exact hL) (by rw [eH]; exact hU)
    (by rw [eD]; exact hξ) h1 h1' h2 h2' h3 h3' h4
  rw [eB] at key
  exact key

/-! ## The widths of the Focus -/

/-- `c·√M ≤ k` from `c² ≤ C/M` and `C ≤ k²`. -/
lemma mul_sqrt_le {c C k M : ℝ} (hM : 0 < M) (_hc : 0 ≤ c) (h : c ^ 2 ≤ C / M) (hk : 0 ≤ k)
    (hCk : C ≤ k ^ 2) : c * √M ≤ k := by
  refine le_of_abs_le (abs_le_of_sq_le_sq ?_ hk)
  rw [mul_pow, Real.sq_sqrt hM.le]
  have := mul_le_mul_of_nonneg_right h hM.le
  rw [div_mul_cancel₀ _ hM.ne'] at this
  linarith

/-- `cDst² ≤ 168/m` at the widths of the Focus. -/
lemma cDst_sq_le {n : ℕ} (hn : 4096 ≤ n) :
    cDst (2 * n) (mW n) ^ 2 ≤ 168 / (mW n : ℝ) := by
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
    linarith
  have a1 := mul_sqrt_le hmpos (cB_nonneg (2 * n) (mW n))
    (cB_sq_le (N := 2 * n) (by omega) hmM) (by norm_num : (0 : ℝ) ≤ 2552 / 1000) (by norm_num)
  have a2 := mul_sqrt_le hmpos (cHat2_nonneg (2 * n) (mW n))
    (cHat2_sq_le (N := 2 * n) (by omega) hmM) (by norm_num : (0 : ℝ) ≤ 2834 / 1000)
    (by norm_num)
  have a3 := mul_sqrt_le hmpos (cF2o_pos hm).le (cF2o_sq_le hmM)
    (by norm_num : (0 : ℝ) ≤ 4728 / 1000) (by norm_num)
  have hs : 0 < √(mW n : ℝ) := Real.sqrt_pos.mpr hmpos
  have h0 := cDst_nonneg (N := 2 * n) hm
  have h1 : cDst (2 * n) (mW n) * √(mW n : ℝ) ≤ 12948 / 1000 := by
    unfold cDst
    nlinarith
  have h2 : (cDst (2 * n) (mW n) * √(mW n : ℝ)) ^ 2 ≤ (12948 / 1000) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg h0 hs.le) h1 2
  rw [mul_pow, Real.sq_sqrt hmpos.le] at h2
  rw [le_div_iff₀ hmpos]
  nlinarith

/-- `n²/mW n ≤ 1/(64n)` for `n ≥ 4096`. -/
lemma nsq_div_mW_le {n : ℕ} (hn : 4096 ≤ n) : (n : ℝ) ^ 2 / (mW n : ℝ) ≤ 1 / (64 * (n : ℝ)) := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  refine ratio_le (n0 := n) (by omega) le_rfl (by positivity) ?_
  rw [div_pow, one_pow, mul_pow]
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (n : ℝ), mul_pos hnpos hnpos]

/-- **`centreDist140`** (item 1, the mean). `N = 2n`, `m = mW n`, every `n ≥ 4096`:
`E_θ t|b̂ − h̄|² ≤ (19/50)·γ/N`, `γ = 2/N`. (The relative squared distance is of order `1/N`.) -/
theorem centreDist140 {n : ℕ} (hn : 4096 ≤ n) :
    Integrable (dist2 (2 * n) (mW n)) (hidGauss (2 * n) (mW n)) ∧
      ∫ θ, dist2 (2 * n) (mW n) θ ∂hidGauss (2 * n) (mW n) ≤
        2 / ((2 * n : ℕ) : ℝ) * (19 / 50 / ((2 * n : ℕ) : ℝ)) := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
    linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  obtain ⟨hi, hle⟩ := centreDist_gen (N := 2 * n) (m := mW n) (by omega) hm
  refine ⟨hi, hle.trans ?_⟩
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have h0 := cDst_nonneg (N := 2 * n) hm
  -- `N·cDst ≤ 3/50`
  have h1 : (2 * (n : ℝ)) * cDst (2 * n) (mW n) ≤ 3 / 50 := by
    refine le_of_abs_le (abs_le_of_sq_le_sq ?_ (by norm_num))
    rw [mul_pow]
    have a := mul_le_mul_of_nonneg_left (cDst_sq_le hn) (sq_nonneg (2 * (n : ℝ)))
    have b := nsq_div_mW_le hn
    have e : (2 * (n : ℝ)) ^ 2 * (168 / (mW n : ℝ)) = 672 * ((n : ℝ) ^ 2 / (mW n : ℝ)) := by ring
    rw [e] at a
    have c : 672 * ((n : ℝ) ^ 2 / (mW n : ℝ)) ≤ 672 * (1 / (64 * (n : ℝ))) :=
      mul_le_mul_of_nonneg_left b (by norm_num)
    have d : 672 * (1 / (64 * (n : ℝ))) ≤ (3 / 50) ^ 2 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  rw [hNcast]
  have e : 19 / 50 / (2 * (n : ℝ)) = 8 / 25 / (2 * (n : ℝ)) + 3 / 50 / (2 * (n : ℝ)) := by ring
  rw [e]
  have h2 : cDst (2 * n) (mW n) ≤ 3 / 50 / (2 * (n : ℝ)) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  linarith

/-- **The event that the computed centre is near the exact centre**: `t|b̂ − h̄|² ≤ γ·Xc/N`. -/
def goodDist (n : ℕ) (Xc : ℝ) : Set (HidParam (2 * n) (mW n)) :=
  {θ | dist2 (2 * n) (mW n) θ ≤ 2 / ((2 * n : ℕ) : ℝ) * (Xc / ((2 * n : ℕ) : ℝ))}

lemma goodDist_meas {n : ℕ} (hn : 1 ≤ n) (Xc : ℝ) : MeasurableSet (goodDist n Xc) :=
  measurableSet_le (measurable_dist2 (by omega)) measurable_const

/-- **The probability of the far event**: for `n ≥ 4096` and `Xc > 8/25`:
`Pr(t|b̂ − h̄|² > γ·Xc/N) ≤ (21/2)/((Xc − 8/25)²·n)`. -/
theorem goodDist_prob {n : ℕ} (hn : 4096 ≤ n) {Xc : ℝ} (hXc : 8 / 25 < Xc) :
    (hidGauss (2 * n) (mW n)).real (goodDist n Xc)ᶜ ≤
      21 / 2 / ((Xc - 8 / 25) ^ 2 * (n : ℝ)) := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hmpos : (0 : ℝ) < mW n := by
    have : (1000000 : ℝ) ≤ mW n := by exact_mod_cast hmM
    linarith
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hX0 : 0 < Xc - 8 / 25 := by linarith
  have e : (goodDist n Xc)ᶜ = {θ | 2 / ((2 * n : ℕ) : ℝ) * (Xc / ((2 * n : ℕ) : ℝ)) <
      dist2 (2 * n) (mW n) θ} := by
    ext θ
    simp [goodDist, not_le]
  rw [e]
  refine (distBad_gen (N := 2 * n) (m := mW n) (by omega) hm hXc).trans ?_
  rw [hNcast, div_le_div_iff₀ (by positivity) (by positivity), mul_pow]
  have a := mul_le_mul_of_nonneg_left (cDst_sq_le hn) (sq_nonneg (2 * (n : ℝ)))
  have b := nsq_div_mW_le hn
  have e1 : (2 * (n : ℝ)) ^ 2 * (168 / (mW n : ℝ)) = 672 * ((n : ℝ) ^ 2 / (mW n : ℝ)) := by ring
  rw [e1] at a
  have c : 672 * ((n : ℝ) ^ 2 / (mW n : ℝ)) ≤ 672 * (1 / (64 * (n : ℝ))) :=
    mul_le_mul_of_nonneg_left b (by norm_num)
  have d : (2 * (n : ℝ)) ^ 2 * cDst (2 * n) (mW n) ^ 2 ≤ 21 / 2 / (n : ℝ) := by
    refine a.trans (c.trans (le_of_eq ?_))
    field_simp
    ring
  have hX2 : 0 < (Xc - 8 / 25) ^ 2 := by positivity
  calc (2 * (n : ℝ)) ^ 2 * cDst (2 * n) (mW n) ^ 2 * ((Xc - 8 / 25) ^ 2 * (n : ℝ))
      ≤ 21 / 2 / (n : ℝ) * ((Xc - 8 / 25) ^ 2 * (n : ℝ)) :=
        mul_le_mul_of_nonneg_right d (by positivity)
    _ = 21 / 2 * (Xc - 8 / 25) ^ 2 := by field_simp

/-- **`Bh_window`** (item 1, the event). For `n ≥ 4096`, on `good136 n` and `goodDist n (3/4)`:
`0.48·γ ≤ t|b̂|² ≤ 0.508·γ`. -/
theorem Bh_window {n : ℕ} (hn : 4096 ≤ n) {θ : HidParam (2 * n) (mW n)} (hθ : θ ∈ good136 n)
    (hd : θ ∈ goodDist n (3 / 4)) :
    2 / ((2 * n : ℕ) : ℝ) * (48 / 100) ≤ Bh (2 * n) (mW n) θ ∧
      Bh (2 * n) (mW n) θ ≤ 2 / ((2 * n : ℕ) : ℝ) * (508 / 1000) := by
  have hn' : (4096 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hN : 1 ≤ 2 * n := by omega
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hγ : (0 : ℝ) < 2 / ((2 * n : ℕ) : ℝ) := by rw [hNcast]; positivity
  obtain ⟨hB1, hB2⟩ := Bn136 hn hθ
  have hH := Hh_eq_Bn (m := mW n) hN θ
  have hξ : (3 : ℝ) / 4 / ((2 * n : ℕ) : ℝ) ≤ (96 / 10000) ^ 2 := by
    rw [hNcast, div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨k1, k2⟩ := Bh_window_gen (N := 2 * n) (m := mW n) hN hm (θ := θ)
    (L := 4936 / 10000) (U := 494 / 1000) (ξ := 3 / 4 / ((2 * n : ℕ) : ℝ))
    (sL := 7025 / 10000) (sU := 7029 / 10000) (sξ := 96 / 10000)
    (by rw [hH]; exact mul_le_mul_of_nonneg_left hB1 hγ.le)
    (by rw [hH]; exact mul_le_mul_of_nonneg_left hB2 hγ.le) hd (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hξ (by norm_num)
  constructor
  · refine le_trans (mul_le_mul_of_nonneg_left ?_ hγ.le) k1
    norm_num
  · refine k2.trans (mul_le_mul_of_nonneg_left ?_ hγ.le)
    norm_num

end BstLean.Part140

open BstLean.Part140 in
#print axioms dist2_L2
open BstLean.Part140 in
#print axioms centreDist_gen
open BstLean.Part140 in
#print axioms centreDist140
open BstLean.Part140 in
#print axioms distBad_gen
open BstLean.Part140 in
#print axioms goodDist_prob
open BstLean.Part140 in
#print axioms errT_mean
open BstLean.Part140 in
#print axioms errT_bad
open BstLean.Part140 in
#print axioms Bh_window_gen
open BstLean.Part140 in
#print axioms Bh_window
