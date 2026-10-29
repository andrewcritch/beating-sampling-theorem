import BstLean.Part143HidK
import BstLean.Part140Sharp

/-!
# Part 143, helper `hidK`, file `HidC`: the events of the computed centre, sharper probability

The events `goodDist n (3/4)`, `goodT n (1/400000)`, `goodHat n` of Part 140 do not change.

* `cH143 N m = √(cK143 N m/m)`; `innerFluct143_joint`, `Hh_L2_143`:
  `‖t|h̄|² − γ q_N‖_{L²(θ)} ≤ γ·cH143 N m` (in place of `γ·cF2o m`).
* `cDst143 N m = cB N m + 2·cHat2 N m + cH143 N m`; `dist2_L2_143`.
* `distBad_of_L2`: Chebyshev from an `L²` bound of `dist2` with any constant.
* `nsq_div_mW_le128`: `n²/mW n ≤ 1/(128 n)` for `n ≥ 16384`.
* `goodHatExtra143`, `goodHat_compl143`: for `n ≥ 16384`:
  `Pr(goodDist fails) + Pr(goodT fails) ≤ cExtra143/n`, `Pr(goodHat fails) ≤ P143 + cExtra143/n`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part143

open MeasureTheory ProbabilityTheory Real Set
open BstLean.Part29 (uniformSphere uniformSphere_isProbability uniformSphere_ae_sphere)
open BstLean.Part105 (sphere_cont_integrable)
open BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part136
open BstLean.Part137 hiding Bn
open BstLean.Part140

variable {N m : ℕ}

lemma cK143_nonneg (N m : ℕ) : 0 ≤ cK143 N m := by
  have hk0 : 0 ≤ kappa 0 := by rw [kappa_zero]; positivity
  unfold cK143
  positivity

/-- The constant of `t|h̄|²`: `√(cK143 N m/m)`. -/
noncomputable def cH143 (N m : ℕ) : ℝ := √(cK143 N m / (m : ℝ))

lemma cH143_nonneg (N m : ℕ) : 0 ≤ cH143 N m := Real.sqrt_nonneg _

/-- **Lemma H2(d), over the input and `θ`, sharper constant**:
`E_θ E_u (T(u) − γ q_N)² ≤ (γ·cH143 N m)²`. -/
theorem innerFluct143_joint (hN : 1 ≤ N) (hm : 1 ≤ m) :
    Integrable (fun p : (Fin N → ℝ) × HidParam N m => (Tn N m p.1 p.2 - 2 / (N : ℝ) * qN N) ^ 2)
        ((uniformSphere N).prod (hidGauss N m)) ∧
      ∫ p, (Tn N m p.1 p.2 - 2 / (N : ℝ) * qN N) ^ 2 ∂((uniformSphere N).prod (hidGauss N m)) ≤
        (2 / (N : ℝ) * cH143 N m) ^ 2 := by
  have := uniformSphere_isProbability N hN
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  obtain ⟨hint, -⟩ := innerFluct137_joint (m := m) hN hm
  obtain ⟨hEi, hEv⟩ := errK_mean143 (m := m) hN hm
  refine ⟨hint, ?_⟩
  rw [integral_prod_symm _ hint]
  calc ∫ θ, (∫ u, (Tn N m u θ - 2 / (N : ℝ) * qN N) ^ 2 ∂uniformSphere N) ∂hidGauss N m
      ≤ ∫ θ, (2 / (m : ℝ)) ^ 2 * errK θ ∂hidGauss N m :=
        integral_mono hint.integral_prod_right (hEi.const_mul _) fun θ => Tn_err hN hm θ
    _ = (2 / (m : ℝ)) ^ 2 * ∫ θ, errK θ ∂hidGauss N m := integral_const_mul _ _
    _ ≤ (2 / (m : ℝ)) ^ 2 * (((m : ℝ) / N) ^ 2 * cK143 N m / m) :=
        mul_le_mul_of_nonneg_left hEv (sq_nonneg _)
    _ = (2 / (N : ℝ) * cH143 N m) ^ 2 := by
        unfold cH143
        rw [mul_pow, Real.sq_sqrt (div_nonneg (cK143_nonneg N m) hm'.le)]
        field_simp

/-- `‖t|h̄|² − γq_N‖_{L²(θ)} ≤ γ·cH143 N m`. -/
theorem Hh_L2_143 (hN : 1 ≤ N) (hm : 1 ≤ m) :
    L2le (hidGauss N m) (fun θ => Hh N m θ - 2 / (N : ℝ) * qN N) (2 / (N : ℝ) * cH143 N m) := by
  have := uniformSphere_isProbability N hN
  obtain ⟨h1, h2⟩ := innerFluct143_joint (m := m) hN hm
  have hj : L2le ((uniformSphere N).prod (hidGauss N m))
      (fun p : (Fin N → ℝ) × HidParam N m => Tn N m p.1 p.2 - 2 / (N : ℝ) * qN N)
      (2 / (N : ℝ) * cH143 N m) :=
    ⟨(((measurable_Tn hN).sub_const _ :)).aestronglyMeasurable, h1, h2⟩
  refine hj.integral_left.congr_fun fun θ => ?_
  rw [integral_sub (sphere_cont_integrable hN (continuous_Tn_u θ)) (integrable_const _),
    Tn_mean hN]
  simp [Hh]

/-- The constant of the distance, sharper: `cB + 2·cHat2 + cH143`. -/
noncomputable def cDst143 (N m : ℕ) : ℝ := cB N m + 2 * cHat2 N m + cH143 N m

lemma cDst143_nonneg (N m : ℕ) : 0 ≤ cDst143 N m := by
  have := cB_nonneg N m
  have := cHat2_nonneg N m
  have := cH143_nonneg N m
  unfold cDst143
  linarith

/-- **The distance in `L²(θ)`**: `‖t|b̂ − h̄|² − γ(q_N − κ(q₁))‖₂ ≤ γ·cDst143 N m`. -/
theorem dist2_L2_143 (hN : 1 ≤ N) (hm : 1 ≤ m) :
    L2le (hidGauss N m) (fun θ => dist2 N m θ - 2 / (N : ℝ) * (qN N - kap1 N))
      (2 / (N : ℝ) * cDst143 N m) := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hγ : (0 : ℝ) ≤ 2 / (N : ℝ) := by positivity
  have hB := bhatNorm_L2 (m := m) hN hm
  have hX := (Xh_L2 (m := m) hN hm).const_mul (-2)
  have hH := Hh_L2_143 (m := m) hN hm
  have e2 : |(-2 : ℝ)| = 2 := by norm_num
  rw [e2] at hX
  have h1 := hB.add' hX (mul_nonneg hγ (cB_nonneg N m))
    (mul_nonneg (by norm_num) (mul_nonneg hγ (cHat2_nonneg N m)))
  have h2 := h1.add' hH
    (add_nonneg (mul_nonneg hγ (cB_nonneg N m))
      (mul_nonneg (by norm_num) (mul_nonneg hγ (cHat2_nonneg N m))))
    (mul_nonneg hγ (cH143_nonneg N m))
  refine (h2.congr_fun fun θ => ?_).congr_bound ?_
  · rw [dist2_eq]
    ring
  · unfold cDst143
    ring

/-- **The far event** (Chebyshev) from an `L²` bound of `dist2` with any constant `c`:
for `Xc > 8/25`, `Pr(t|b̂ − h̄|² > γ·Xc/N) ≤ (N·c)²/(Xc − 8/25)²`. -/
theorem distBad_of_L2 (hN : 1 ≤ N) {c : ℝ}
    (h : L2le (hidGauss N m) (fun θ => dist2 N m θ - 2 / (N : ℝ) * (qN N - kap1 N))
      (2 / (N : ℝ) * c)) {Xc : ℝ} (hXc : 8 / 25 < Xc) :
    (hidGauss N m).real {θ | 2 / (N : ℝ) * (Xc / (N : ℝ)) < dist2 N m θ} ≤
      ((N : ℝ) * c) ^ 2 / (Xc - 8 / 25) ^ 2 := by
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hγ : (0 : ℝ) < 2 / (N : ℝ) := by positivity
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
      (2 / (N : ℝ) * c) ^ 2 :=
    (mul_le_mul_of_nonneg_left hmono (sq_nonneg _)).trans (hmk.trans h.le)
  have hX0 : 0 < Xc - 8 / 25 := by linarith
  rw [le_div_iff₀ (by positivity)]
  have e : ε ^ 2 = (2 / (N : ℝ)) ^ 2 * ((Xc - 8 / 25) ^ 2 / (N : ℝ) ^ 2) := by
    rw [hε]; ring
  rw [e] at h6
  have hg2 : (0 : ℝ) < (2 / (N : ℝ)) ^ 2 := by positivity
  have h7 : (2 / (N : ℝ)) ^ 2 * ((hidGauss N m).real
        {θ | 2 / (N : ℝ) * (Xc / (N : ℝ)) < dist2 N m θ} * (Xc - 8 / 25) ^ 2) ≤
      (2 / (N : ℝ)) ^ 2 * (((N : ℝ) * c) ^ 2) := by
    have e1 : (2 / (N : ℝ)) ^ 2 * ((hidGauss N m).real
        {θ | 2 / (N : ℝ) * (Xc / (N : ℝ)) < dist2 N m θ} * (Xc - 8 / 25) ^ 2) =
        (N : ℝ) ^ 2 * ((2 / (N : ℝ)) ^ 2 * ((Xc - 8 / 25) ^ 2 / (N : ℝ) ^ 2) *
          (hidGauss N m).real {θ | 2 / (N : ℝ) * (Xc / (N : ℝ)) < dist2 N m θ}) := by
      field_simp
    have e2 : (2 / (N : ℝ)) ^ 2 * (((N : ℝ) * c) ^ 2) =
        (N : ℝ) ^ 2 * (2 / (N : ℝ) * c) ^ 2 := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left h6 (sq_nonneg _)
  exact le_of_mul_le_mul_left h7 hg2

/-! ## The widths of the Focus -/

/-- `n²/mW n ≤ 1/(128n)` for `n ≥ 16384`. -/
lemma nsq_div_mW_le128 {n : ℕ} (hn : 16384 ≤ n) :
    (n : ℝ) ^ 2 / (mW n : ℝ) ≤ 1 / (128 * (n : ℝ)) := by
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  refine ratio_le (n0 := n) (by omega) le_rfl (by positivity) ?_
  rw [div_pow, one_pow, mul_pow]
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (n : ℝ), mul_pos hnpos hnpos]

/-- `cH143² ≤ 8.3142/m` at `N ≥ 8192`, `m ≥ 10⁶`. -/
lemma cH143_sq_le (hN : 8192 ≤ N) (hm : 1000000 ≤ m) :
    cH143 N m ^ 2 ≤ 83142 / 10000 / (m : ℝ) := by
  have hm' : (1000000 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have h1 := cK143_le hN hm
  have h2 := cF2o_sq_le hm
  have e : cF2o m ^ 2 = (6 * (1 + 5 / (m : ℝ)) + (5 * kappa 0 + √6) ^ 2) / (m : ℝ) := by
    unfold cF2o
    rw [Real.sq_sqrt (by positivity)]
    ring
  rw [e, div_le_div_iff_of_pos_right hm0] at h2
  unfold cH143
  rw [Real.sq_sqrt (div_nonneg (cK143_nonneg N m) hm0.le)]
  refine div_le_div_of_nonneg_right ?_ hm0.le
  linarith

/-- `cDst143² ≤ 123.3/m` at the widths of the Focus. -/
lemma cDst143_sq_le {n : ℕ} (hn : 4096 ≤ n) :
    cDst143 (2 * n) (mW n) ^ 2 ≤ 1233 / 10 / (mW n : ℝ) := by
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
  have a3 := mul_sqrt_le hmpos (cH143_nonneg (2 * n) (mW n))
    (cH143_sq_le (N := 2 * n) (by omega) hmM) (by norm_num : (0 : ℝ) ≤ 2884 / 1000)
    (by norm_num)
  have hs : 0 < √(mW n : ℝ) := Real.sqrt_pos.mpr hmpos
  have h0 := cDst143_nonneg (2 * n) (mW n)
  have h1 : cDst143 (2 * n) (mW n) * √(mW n : ℝ) ≤ 11104 / 1000 := by
    unfold cDst143
    nlinarith
  have h2 : (cDst143 (2 * n) (mW n) * √(mW n : ℝ)) ^ 2 ≤ (11104 / 1000) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg h0 hs.le) h1 2
  rw [mul_pow, Real.sq_sqrt hmpos.le] at h2
  rw [le_div_iff₀ hmpos]
  nlinarith

/-- `Pr(t|b̂ − h̄|² > γ·Xc/N) ≤ 493.2·(n²/m_W)/(Xc − 8/25)²`. -/
theorem goodDist_prob143 {n : ℕ} (hn : 4096 ≤ n) {Xc : ℝ} (hXc : 8 / 25 < Xc) :
    (hidGauss (2 * n) (mW n)).real (goodDist n Xc)ᶜ ≤
      4932 / 10 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (Xc - 8 / 25) ^ 2 := by
  have hmM := mW_ge_million hn
  have hm : 1 ≤ mW n := by omega
  have hNcast : ((2 * n : ℕ) : ℝ) = 2 * (n : ℝ) := by push_cast; ring
  have hX0 : 0 < Xc - 8 / 25 := by linarith
  have e : (goodDist n Xc)ᶜ = {θ | 2 / ((2 * n : ℕ) : ℝ) * (Xc / ((2 * n : ℕ) : ℝ)) <
      dist2 (2 * n) (mW n) θ} := by
    ext θ
    simp [goodDist, not_le]
  rw [e]
  refine (distBad_of_L2 (N := 2 * n) (m := mW n) (by omega)
    (dist2_L2_143 (by omega) hm) hXc).trans ?_
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [hNcast, mul_pow]
  have a := mul_le_mul_of_nonneg_left (cDst143_sq_le hn) (sq_nonneg (2 * (n : ℝ)))
  have e1 : (2 * (n : ℝ)) ^ 2 * (1233 / 10 / (mW n : ℝ)) =
      4932 / 10 * ((n : ℝ) ^ 2 / (mW n : ℝ)) := by ring
  rw [e1] at a
  exact a

/-- The constant of the two events of the computed centre, `n ≥ 16384`. -/
noncomputable def cExtra143 : ℝ := 2238 / 100

/-- **The two events of the computed centre**, `n ≥ 16384`:
`Pr(goodDist n (3/4) fails) + Pr(goodT n (1/400000) fails) ≤ 22.38/n`. -/
theorem goodHatExtra143 {n : ℕ} (hn : 16384 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (goodDist n (3 / 4))ᶜ +
      (hidGauss (2 * n) (mW n)).real (goodT n (1 / 400000))ᶜ ≤ cExtra143 / (n : ℝ) := by
  have hn4 : 4096 ≤ n := by omega
  have hn' : (16384 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hρ := nsq_div_mW_le128 hn
  have h2 := goodDist_prob143 hn4 (Xc := 3 / 4) (by norm_num)
  have h3 := goodT_prob_sharp hn4 (dT := 1 / 400000) (by norm_num)
  have e1 : (1 : ℝ) / (128 * (n : ℝ)) = 1 / 128 / (n : ℝ) := by field_simp
  rw [e1] at hρ
  have b2 : 4932 / 10 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / (3 / 4 - 8 / 25) ^ 2 ≤
      2084 / 100 / (n : ℝ) := by
    rw [div_le_iff₀ (by norm_num)]
    have := mul_le_mul_of_nonneg_left hρ (by norm_num : (0 : ℝ) ≤ 4932 / 10)
    refine this.trans ?_
    have e4 : (4932 : ℝ) / 10 * (1 / 128 / (n : ℝ)) = 4932 / 10 / 128 / (n : ℝ) := by ring
    have e5 : (2084 : ℝ) / 100 / (n : ℝ) * (3 / 4 - 8 / 25) ^ 2 =
        2084 / 100 * (3 / 4 - 8 / 25) ^ 2 / (n : ℝ) := by ring
    rw [e4, e5]
    refine div_le_div_of_nonneg_right ?_ hnpos.le
    norm_num
  have b3 : 803 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) / ((n : ℝ) * (1 / 400000)) ≤
      154 / 100 / (n : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hnpos]
    have := mul_le_mul_of_nonneg_left hρ (by norm_num : (0 : ℝ) ≤ 803 / 100)
    have h5 : 803 / 100 * ((n : ℝ) ^ 2 / (mW n : ℝ)) * (n : ℝ) ≤ 803 / 100 * (1 / 128) := by
      have := mul_le_mul_of_nonneg_right this hnpos.le
      refine this.trans (le_of_eq ?_)
      field_simp
    refine h5.trans ?_
    nlinarith
  unfold cExtra143
  have e3 : (2238 : ℝ) / 100 / (n : ℝ) = 2084 / 100 / (n : ℝ) + 154 / 100 / (n : ℝ) := by ring
  rw [e3]
  exact add_le_add (h2.trans b2) (h3.trans b3)

/-- **The good hidden event for the computed centre**, `n ≥ 16384`:
`Pr(goodHat n fails) ≤ P143 + cExtra143/n = 0.000775 + 22.38/n`. -/
theorem goodHat_compl143 {n : ℕ} (hn : 16384 ≤ n) :
    (hidGauss (2 * n) (mW n)).real (goodHat n)ᶜ ≤ P143 + cExtra143 / (n : ℝ) := by
  have h1 := good136_prob143 (n := n) (by omega)
  have h23 := goodHatExtra143 hn
  have hsub : (goodHat n)ᶜ ⊆
      ((good136 n)ᶜ ∪ (goodDist n (3 / 4))ᶜ) ∪ (goodT n (1 / 400000))ᶜ := by
    intro θ hθ
    simp only [goodHat, Set.mem_compl_iff, Set.mem_inter_iff, not_and_or] at hθ
    simpa only [Set.mem_union, Set.mem_compl_iff] using hθ
  have h4 := (measureReal_mono (μ := hidGauss (2 * n) (mW n)) hsub (measure_ne_top _ _)).trans
    ((measureReal_union_le _ _).trans (add_le_add (measureReal_union_le _ _) le_rfl))
  linarith

end BstLean.Part143

open BstLean.Part143 in
#print axioms Hh_L2_143
open BstLean.Part143 in
#print axioms dist2_L2_143
open BstLean.Part143 in
#print axioms goodHatExtra143
open BstLean.Part143 in
#print axioms goodHat_compl143
