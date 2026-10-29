import BstLean.Part162LSp
import BstLean.Part162Sc
import BstLean.Part53Remez_Radial

/-!
# Part 162, item 1: Lemma LS of order `2q`, sharp form (the paper's constant)

Role: `delegations/statements/p162-spec.md`, item 1 ("the centred moment bound
`‖φ − E(φ | s)‖_{2p} ≤ c_p (n − 1 − 2p)^{−1/2}‖√(1 − s²)|P_lat∇φ|‖_{2p}` (lift to a Gaussian vector,
the rotation inequality, the inverse chi-square moment)"). Do not use `sorry`, `native_decide`
or `axiom`.

Route (the paper's): the 0-homogeneous lift `G(v) = H₁(v)/|v|`, cut off as
`g_ε(v) = H₁(v)/max(|v|, ε)` (Lipschitz with constant `2L/ε`); the `L^p` Poincaré inequality
(`poincare_p`) for `g_ε`; `|∇g_ε| ≤ √T/|v|` outside the ball (`gtr_grad_le`); radius and direction
are independent and `T` depends only on the direction (`gradSq_hom`); the negative radial moment
`E[|Z|^{−2q}; |Z| > ε] ≤ (k − 2q)^{−q}` (`trunc_invRad_le`, from the Gamma integral); the
small-ball bound `Pr(|Z| ≤ ε) ≤ (2ε)^k` (`smallBall_le`); and `ε → 0`.

* **`ls_mom_sharp`**: `‖G − EG‖_{2q} ≤ c_q (k − 2q)^{−1/2} ‖√T‖_{2q}` on `ℝ^k`, `2q < k`.
* **`ls_lat_mom_sharp`**: the same on a latitude sphere, `k = n − 1`.
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real Filter Topology Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 radF53 measurable_unitF measurable_radF)
open BstLean.Part53.RemezAux (gaussianRadialFactor gaussianRadialFactor_nonneg
  gaussian_radius_integral)
open BstLean.Part148 (EuLip)
open BstLean.Part151 (gradSq gradSq_le measurable_gradSq)
open BstLean.Part161 (momN momN_nonneg momN_pow mink4)

/-! ## The negative radial moments -/

lemma gamma_int (m : ℝ) (hm : -1 < m) :
    ∫ r in Ioi (0 : ℝ), r ^ m * Real.exp (-(1 / 2) * r ^ (2 : ℝ)) =
      (1 / 2 : ℝ) ^ (-(m + 1) / 2) * (1 / 2) * Real.Gamma ((m + 1) / 2) :=
  integral_rpow_mul_exp_neg_mul_rpow (by norm_num) hm (by norm_num)

lemma gamma_add_nat_ge {a : ℝ} (ha : 0 < a) (q : ℕ) :
    a ^ q * Real.Gamma a ≤ Real.Gamma (a + q) := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h1 : Real.Gamma (a + (q + 1 : ℕ)) = (a + q) * Real.Gamma (a + q) := by
      push_cast
      rw [← add_assoc, Real.Gamma_add_one (by positivity)]
    rw [h1, pow_succ]
    have hg := Real.Gamma_pos_of_pos ha
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    nlinarith [mul_le_mul_of_nonneg_left ih (by positivity : (0 : ℝ) ≤ a),
      mul_nonneg (mul_nonneg hq0 (pow_nonneg ha.le q)) hg.le]

variable {ι : Type} [Fintype ι]

lemma radF_eq_sqrt (Z : ι → ℝ) : radF53 Z = √(∑ i, Z i ^ 2) := rfl

/-- **The truncated negative radial moment**: `E[|Z|^{−2q}; |Z| > ε] ≤ (k − 2q)^{−q}` for
`2q < k` (the paper's `E|H|^{−2p} = ∏(n−1−2j)^{−1}`). -/
theorem trunc_invRad_le [Nonempty ι] {q : ℕ} (hq : 2 * q < Fintype.card ι) (ε : ℝ) :
    ∫ Z, (if ε < radF53 Z then (radF53 Z ^ (2 * q))⁻¹ else 0) ∂stdGauss ι ≤
      (((Fintype.card ι : ℝ) - 2 * q)⁻¹) ^ q := by
  set k := Fintype.card ι with hk
  have hk1 : 1 ≤ k := Fintype.card_pos
  set K := gaussianRadialFactor ι
  have hK : 0 ≤ K := gaussianRadialFactor_nonneg ι
  set Fe : ℝ → ℝ := fun r => if ε < r then (r ^ (2 * q))⁻¹ else 0 with hFe
  have hF := gaussian_radius_integral ι Fe
  have h1 := gaussian_radius_integral ι (fun _ => (1 : ℝ))
  beta_reduce at h1
  -- the radial integrals in `rpow` form
  have hkR : (2 * q : ℝ) < k := by exact_mod_cast hq
  set J₀ := ∫ r in Ioi (0 : ℝ), r ^ ((k : ℝ) - 1) * Real.exp (-(1 / 2) * r ^ (2 : ℝ))
  set J₁ := ∫ r in Ioi (0 : ℝ), r ^ ((k : ℝ) - 1 - 2 * q) * Real.exp (-(1 / 2) * r ^ (2 : ℝ))
  have eJ₀ : ∫ r in Ioi (0 : ℝ), r ^ (k - 1) * Real.exp (-r ^ 2 / 2) = J₀ := by
    refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
    rw [show ((k : ℝ) - 1) = ((k - 1 : ℕ) : ℝ) by rw [Nat.cast_sub hk1]; simp, Real.rpow_natCast,
      show r ^ (2 : ℝ) = r ^ 2 by norm_cast]
    ring_nf
  have hJ₀ : J₀ = (1 / 2 : ℝ) ^ (-((k : ℝ) - 1 + 1) / 2) * (1 / 2) * Real.Gamma (((k : ℝ) - 1 + 1) / 2) :=
    gamma_int _ (by linarith [(by exact_mod_cast hk1 : (1 : ℝ) ≤ k)])
  have hJ₁ : J₁ = (1 / 2 : ℝ) ^ (-((k : ℝ) - 1 - 2 * q + 1) / 2) * (1 / 2) *
      Real.Gamma (((k : ℝ) - 1 - 2 * q + 1) / 2) := gamma_int _ (by linarith)
  -- the truncated integrand is below the full one
  have hle : ∫ r in Ioi (0 : ℝ), r ^ (k - 1) * Real.exp (-r ^ 2 / 2) * Fe r ≤ J₁ := by
    have iJ₁ : IntegrableOn (fun r : ℝ => r ^ ((k : ℝ) - 1 - 2 * q) * Real.exp (-(1 / 2) * r ^ (2 : ℝ)))
        (Ioi 0) := by
      have := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 2) (s := (k : ℝ) - 1 - 2 * q)
        (b := 1 / 2) (by linarith) (by norm_num) (by norm_num)
      exact this
    have hpt : ∀ r ∈ Ioi (0 : ℝ), r ^ (k - 1) * Real.exp (-r ^ 2 / 2) * Fe r ≤
        r ^ ((k : ℝ) - 1 - 2 * q) * Real.exp (-(1 / 2) * r ^ (2 : ℝ)) := fun r hr => by
      have hr0 : 0 < r := hr
      have he : r ^ ((k : ℝ) - 1 - 2 * q) * Real.exp (-(1 / 2) * r ^ (2 : ℝ)) =
          r ^ (k - 1) * Real.exp (-r ^ 2 / 2) * (r ^ (2 * q))⁻¹ := by
        rw [Real.rpow_sub hr0, Real.rpow_sub hr0, Real.rpow_one,
          show r ^ (2 : ℝ) = r ^ 2 by norm_cast,
          show r ^ ((2 : ℝ) * q) = r ^ (2 * q) by rw [← Real.rpow_natCast]; push_cast; ring_nf,
          Real.rpow_natCast]
        rw [show r ^ (k - 1) = r ^ k / r by
          rw [eq_div_iff hr0.ne', ← pow_succ, Nat.sub_add_cancel hk1]]
        field_simp
      rw [he]
      simp only [hFe]
      split_ifs
      · exact le_rfl
      · have : 0 ≤ r ^ (k - 1) * Real.exp (-r ^ 2 / 2) * (r ^ (2 * q))⁻¹ := by positivity
        simpa using this
    have iL : IntegrableOn (fun r => r ^ (k - 1) * Real.exp (-r ^ 2 / 2) * Fe r) (Ioi 0) := by
      refine iJ₁.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioi fun r hr => ?_)
      · refine Measurable.aestronglyMeasurable ?_
        refine ((measurable_id.pow_const _).mul (by fun_prop)).mul ?_
        simp only [hFe]
        exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
          ((measurable_id.pow_const _).inv) measurable_const
      · rw [Real.norm_eq_abs, abs_of_nonneg]
        · exact hpt r hr
        · have hr0 : 0 < r := hr
          simp only [hFe]
          split_ifs <;> positivity
    exact setIntegral_mono_on iL iJ₁ measurableSet_Ioi hpt
  -- assemble
  have hE : ∫ Z, Fe (√(∑ i, Z i ^ 2)) ∂stdGauss ι ≤ K * J₁ := by
    rw [hF]; exact mul_le_mul_of_nonneg_left hle hK
  have hKJ : K * J₀ = 1 := by
    rw [← eJ₀]
    have e1 : ∫ _Z, (1 : ℝ) ∂stdGauss ι = 1 := by simp
    have e2 : ∫ r in Ioi (0 : ℝ), r ^ (k - 1) * Real.exp (-r ^ 2 / 2) * 1 =
        ∫ r in Ioi (0 : ℝ), r ^ (k - 1) * Real.exp (-r ^ 2 / 2) := by simp
    rw [e1, e2] at h1
    exact h1.symm
  set a := ((k : ℝ) - 2 * q) / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have hJ₁' : J₁ = (1 / 2 : ℝ) ^ (-a) * (1 / 2) * Real.Gamma a := by
    rw [hJ₁]; congr 2 <;> [congr 1; skip] <;> rw [ha] <;> ring
  have hJ₀' : J₀ = (1 / 2 : ℝ) ^ (-(a + q)) * (1 / 2) * Real.Gamma (a + q) := by
    rw [hJ₀]; congr 2 <;> [congr 1; skip] <;> rw [ha] <;> ring
  have hg := Real.Gamma_pos_of_pos ha0
  have hgq := Real.Gamma_pos_of_pos (by positivity : 0 < a + q)
  have hJ₀p : 0 < J₀ := by rw [hJ₀']; positivity
  have hKe : K = 1 / J₀ := by field_simp; linarith
  have hratio : K * J₁ = (2 : ℝ)⁻¹ ^ q * (Real.Gamma a / Real.Gamma (a + q)) := by
    rw [hKe, hJ₁', hJ₀']
    have h2 : (1 / 2 : ℝ) ^ (-a) = (1 / 2 : ℝ) ^ (-(a + q)) * (2 : ℝ)⁻¹ ^ q := by
      rw [show (2 : ℝ)⁻¹ ^ q = (1 / 2 : ℝ) ^ (q : ℝ) by rw [Real.rpow_natCast]; norm_num,
        ← Real.rpow_add (by norm_num)]
      congr 1; ring
    rw [h2]
    have : (0 : ℝ) < (1 / 2 : ℝ) ^ (-(a + q)) := by positivity
    field_simp
  calc ∫ Z, (if ε < radF53 Z then (radF53 Z ^ (2 * q))⁻¹ else 0) ∂stdGauss ι
      = ∫ Z, Fe (√(∑ i, Z i ^ 2)) ∂stdGauss ι := rfl
    _ ≤ K * J₁ := hE
    _ = (2 : ℝ)⁻¹ ^ q * (Real.Gamma a / Real.Gamma (a + q)) := hratio
    _ ≤ (2 : ℝ)⁻¹ ^ q * (a ^ q)⁻¹ := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [div_le_iff₀ hgq]
        have := gamma_add_nat_ge ha0 q
        rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
        linarith
    _ = (((k : ℝ) - 2 * q)⁻¹) ^ q := by
        rw [ha, ← inv_pow, ← mul_pow]
        congr 1
        have : (k : ℝ) - 2 * q ≠ 0 := by linarith
        field_simp

/-! ## Homogeneity of the gradient and the truncated lift -/

variable {H₁ : (ι → ℝ) → ℝ} {L : ℝ}

lemma fderiv_hom (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v) {t : ℝ}
    (ht : 0 < t) (v : ι → ℝ) : fderiv ℝ H₁ (t • v) = fderiv ℝ H₁ v := by
  have key : ∀ {s : ℝ} (hs : 0 < s) {w : ι → ℝ}, DifferentiableAt ℝ H₁ w →
      HasFDerivAt H₁ (fderiv ℝ H₁ w) (s • w) := fun {s} hs {w} hw => by
    have hfun : H₁ = fun z => s * H₁ (s⁻¹ • z) := funext fun z => by
      rw [hhom s⁻¹ z (inv_pos.mpr hs), ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
    have h1 : HasFDerivAt (fun z : ι → ℝ => s⁻¹ • z) (s⁻¹ • ContinuousLinearMap.id ℝ (ι → ℝ))
        (s • w) := (hasFDerivAt_id (s • w)).const_smul s⁻¹
    have h2 : HasFDerivAt H₁ (fderiv ℝ H₁ w) (s⁻¹ • s • w) := by
      rw [smul_smul, inv_mul_cancel₀ hs.ne', one_smul]; exact hw.hasFDerivAt
    have h3 := (h2.comp (s • w) h1).const_mul s
    have h4 : HasFDerivAt H₁ (s • (fderiv ℝ H₁ w).comp (s⁻¹ • ContinuousLinearMap.id ℝ (ι → ℝ)))
        (s • w) := by
      refine h3.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
      simp only [Function.comp]
      exact (congrFun hfun z)
    convert h4 using 1
    ext e
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
    field_simp
  by_cases hd : DifferentiableAt ℝ H₁ v
  · exact (key ht hd).fderiv
  · have hd' : ¬ DifferentiableAt ℝ H₁ (t • v) := fun h => by
      have := key (inv_pos.mpr ht) h
      rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at this
      exact hd this.differentiableAt
    rw [fderiv_zero_of_not_differentiableAt hd, fderiv_zero_of_not_differentiableAt hd']

lemma gradSq_hom [DecidableEq ι] (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v)
    {t : ℝ} (ht : 0 < t) (v : ι → ℝ) : gradSq H₁ (t • v) = gradSq H₁ v := by
  unfold gradSq; rw [fderiv_hom hhom ht]

/-- The truncated 0-homogeneous lift `g_ε(v) = H₁(v)/max(|v|, ε)`. -/
noncomputable def gtr (H₁ : (ι → ℝ) → ℝ) (ε : ℝ) (v : ι → ℝ) : ℝ := H₁ v / max (radF53 v) ε

lemma abs_H₁_le (hL : EuLip H₁ L) (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v)
    (v : ι → ℝ) : |H₁ v| ≤ L * radF53 v := by
  have h := hL v 0
  rw [hom_zero hhom, sub_zero] at h
  simpa [radF53] using h

lemma gtr_lip (hL0 : 0 ≤ L) (hL : EuLip H₁ L)
    (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v) {ε : ℝ} (hε : 0 < ε) :
    EuLip (gtr H₁ ε) (2 * L / ε) := by
  intro x y
  set d := √(∑ i, (x i - y i) ^ 2)
  have hd0 : 0 ≤ d := Real.sqrt_nonneg _
  set Mx := max (radF53 x) ε
  set My := max (radF53 y) ε
  have hMx : ε ≤ Mx := le_max_right _ _
  have hMy : ε ≤ My := le_max_right _ _
  have hMx0 : 0 < Mx := lt_of_lt_of_le hε hMx
  have hMy0 : 0 < My := lt_of_lt_of_le hε hMy
  have hry : radF53 y ≤ My := le_max_left _ _
  have hM : |My - Mx| ≤ d := by
    have h1 := radF_lip y x
    have e : √(∑ i, (y i - x i) ^ 2) = d := by
      congr 1; refine Finset.sum_congr rfl fun i _ => ?_; ring
    rw [e] at h1
    exact (abs_max_sub_max_le_abs _ _ _).trans h1
  have e : gtr H₁ ε x - gtr H₁ ε y = (H₁ x - H₁ y) / Mx + H₁ y * ((My - Mx) / (Mx * My)) := by
    unfold gtr; field_simp; ring
  rw [e]
  have t1 : |(H₁ x - H₁ y) / Mx| ≤ L * d / ε := by
    rw [abs_div, abs_of_pos hMx0]
    calc |H₁ x - H₁ y| / Mx ≤ L * d / Mx := div_le_div_of_nonneg_right (hL x y) hMx0.le
      _ ≤ L * d / ε := div_le_div_of_nonneg_left (by positivity) hε hMx
  have t2 : |H₁ y * ((My - Mx) / (Mx * My))| ≤ L * d / ε := by
    rw [abs_mul, abs_div, abs_of_pos (mul_pos hMx0 hMy0)]
    have h1 : |H₁ y| ≤ L * My := (abs_H₁_le hL hhom y).trans (mul_le_mul_of_nonneg_left hry hL0)
    calc |H₁ y| * (|My - Mx| / (Mx * My)) ≤ (L * My) * (d / (Mx * My)) :=
          mul_le_mul h1 (div_le_div_of_nonneg_right hM (by positivity)) (by positivity)
            (by positivity)
      _ = L * d / Mx := by field_simp
      _ ≤ L * d / ε := div_le_div_of_nonneg_left (by positivity) hε hMx
  calc |(H₁ x - H₁ y) / Mx + H₁ y * ((My - Mx) / (Mx * My))|
      ≤ |(H₁ x - H₁ y) / Mx| + |H₁ y * ((My - Mx) / (Mx * My))| := abs_add_le _ _
    _ ≤ L * d / ε + L * d / ε := add_le_add t1 t2
    _ = 2 * L / ε * d := by ring

/-- **The gradient of the truncated lift outside the ball**: for `|v| > ε`,
`|∇g_ε(v)| ≤ √T(v)/|v|`, `T = |∇H₁|² − G²`. -/
lemma gtr_grad_le [DecidableEq ι] (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v)
    {ε : ℝ} (hε : 0 < ε) {v : ι → ℝ} (hv : ε < radF53 v) :
    √(gradSq (gtr H₁ ε) v) ≤ √(gradSq H₁ v - H₁ (unitF53 v) ^ 2) / radF53 v := by
  have hr0 : 0 < radF53 v := lt_trans hε hv
  have hv0 : v ≠ 0 := fun h => by rw [h] at hr0; simp [radF53] at hr0
  have hcont : Continuous (radF53 (ι := ι)) := by unfold radF53; fun_prop
  have hloc : gtr H₁ ε =ᶠ[𝓝 v] fun w => H₁ w * (radF53 w)⁻¹ := by
    filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds hv)] with w hw
    unfold gtr
    rw [max_eq_left hw.le, div_eq_mul_inv]
  have hfd : fderiv ℝ (gtr H₁ ε) v = fderiv ℝ (fun w => H₁ w * (radF53 w)⁻¹) v := hloc.fderiv_eq
  have hR := hasFDerivAt_radF hv0
  have hI : HasFDerivAt (fun w => (radF53 w)⁻¹)
      ((-(radF53 v ^ 2)⁻¹) • ((1 / (2 * radF53 v)) • ∑ i, (2 * v i) • (ContinuousLinearMap.proj i :
        (ι → ℝ) →L[ℝ] ℝ))) v :=
    (hasDerivAt_inv hr0.ne').comp_hasFDerivAt v hR
  by_cases hd : DifferentiableAt ℝ H₁ v
  · have hM := hd.hasFDerivAt.mul hI
    have hfd2 : fderiv ℝ (fun w => H₁ w * (radF53 w)⁻¹) v =
        H₁ v • ((-(radF53 v ^ 2)⁻¹) • ((1 / (2 * radF53 v)) • ∑ i, (2 * v i) • (ContinuousLinearMap.proj i :
          (ι → ℝ) →L[ℝ] ℝ))) + (radF53 v)⁻¹ • fderiv ℝ H₁ v := hM.fderiv
    have hcomp : ∀ i, fderiv ℝ (gtr H₁ ε) v (Pi.single i 1) =
        fderiv ℝ H₁ v (Pi.single i 1) / radF53 v - H₁ v * v i / radF53 v ^ 3 := fun i => by
      rw [hfd, hfd2]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul',
        Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.single_apply, mul_ite,
        mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      field_simp
      ring
    have he : ∑ i, fderiv ℝ H₁ v (Pi.single i 1) * v i = H₁ v := by
      rw [← euler hhom hd, clm_apply_sum (fderiv ℝ H₁ v) v]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hs : ∑ i, v i ^ 2 = radF53 v ^ 2 := (radF_sq v).symm
    have hG : H₁ (unitF53 v) = H₁ v / radF53 v := by
      rw [hom_rad hhom v]; field_simp
    have hval : gradSq (gtr H₁ ε) v = (gradSq H₁ v - H₁ (unitF53 v) ^ 2) / radF53 v ^ 2 := by
      unfold gradSq
      simp_rw [hcomp]
      rw [hG]
      have e1 : ∑ i, (fderiv ℝ H₁ v (Pi.single i 1) / radF53 v - H₁ v * v i / radF53 v ^ 3) ^ 2 =
          (∑ i, fderiv ℝ H₁ v (Pi.single i 1) ^ 2) / radF53 v ^ 2 -
            2 * H₁ v / radF53 v ^ 4 * ∑ i, fderiv ℝ H₁ v (Pi.single i 1) * v i +
            H₁ v ^ 2 / radF53 v ^ 6 * ∑ i, v i ^ 2 := by
        rw [Finset.sum_div, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
          ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        field_simp
        ring
      rw [e1, he, hs]
      field_simp
      ring
    rw [hval, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hr0.le]
  · have hnd : ¬ DifferentiableAt ℝ (gtr H₁ ε) v := fun h => by
      apply hd
      have h2 : (fun w => gtr H₁ ε w * radF53 w) =ᶠ[𝓝 v] H₁ := by
        filter_upwards [hloc, hcont.continuousAt.eventually (lt_mem_nhds hv)] with w hw hw2
        rw [hw]
        have : radF53 w ≠ 0 := (lt_trans hε hw2).ne'
        field_simp
      exact (h.mul hR.differentiableAt).congr_of_eventuallyEq h2.symm
    unfold gradSq
    rw [fderiv_zero_of_not_differentiableAt hnd]
    simp only [ContinuousLinearMap.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero, Real.sqrt_zero]
    positivity

/-! ## The small ball -/

lemma gauss1_Icc_le {ε : ℝ} (hε : 0 ≤ ε) : (gaussianReal 0 1).real (Icc (-ε) ε) ≤ 2 * ε := by
  rw [gaussianReal_of_var_ne_zero 0 one_ne_zero, measureReal_def, withDensity_apply _ measurableSet_Icc]
  have hpdf : ∀ x, gaussianPDF 0 1 x ≤ 1 := fun x => by
    rw [gaussianPDF_def, ENNReal.ofReal_le_one, gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    have h1 : Real.exp (-x ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
    have h2 : (√(2 * π))⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]
      rw [show (1 : ℝ) = √1 by simp]
      exact Real.sqrt_le_sqrt (by linarith [Real.pi_gt_three])
    calc (√(2 * π))⁻¹ * Real.exp (-x ^ 2 / 2) ≤ 1 * 1 :=
          mul_le_mul h2 h1 (Real.exp_pos _).le zero_le_one
      _ = 1 := by ring
  have h : ∫⁻ x in Icc (-ε) ε, gaussianPDF 0 1 x ≤ ENNReal.ofReal (ε - -ε) := by
    calc ∫⁻ x in Icc (-ε) ε, gaussianPDF 0 1 x ≤ ∫⁻ _x in Icc (-ε) ε, 1 :=
          lintegral_mono fun x => hpdf x
      _ = ENNReal.ofReal (ε - -ε) := by
          rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, univ_inter,
            Real.volume_Icc, one_mul]
  have h2 : ENNReal.ofReal (ε - -ε) ≠ ⊤ := ENNReal.ofReal_ne_top
  calc (∫⁻ x in Icc (-ε) ε, gaussianPDF 0 1 x).toReal ≤ (ENNReal.ofReal (ε - -ε)).toReal :=
        ENNReal.toReal_mono h2 h
    _ = 2 * ε := by rw [ENNReal.toReal_ofReal (by linarith)]; ring

/-- **The small-ball bound**: `Pr(|Z| ≤ ε) ≤ (2ε)^k`. -/
lemma smallBall_le {ε : ℝ} (hε : 0 ≤ ε) :
    (stdGauss ι).real {v | radF53 v ≤ ε} ≤ (2 * ε) ^ Fintype.card ι := by
  have hsub : {v : ι → ℝ | radF53 v ≤ ε} ⊆ Set.pi univ (fun _ => Icc (-ε) ε) := by
    intro v hv i _
    have h1 : |v i| ≤ radF53 v := by
      rw [radF53, ← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun j => v j ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i))
    exact abs_le.mp (h1.trans hv)
  refine (measureReal_mono hsub).trans ?_
  unfold stdGauss
  rw [measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  simp only [Finset.prod_const, Finset.card_univ]
  refine pow_le_pow_left₀ ENNReal.toReal_nonneg ?_ _
  exact gauss1_Icc_le hε

/-! ## The sharp moment bound for one truncation level -/

lemma gtr_abs_le (hL0 : 0 ≤ L) (hL : EuLip H₁ L)
    (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v) {ε : ℝ} (hε : 0 < ε)
    (v : ι → ℝ) : |gtr H₁ ε v| ≤ L := by
  unfold gtr
  have hM : 0 < max (radF53 v) ε := lt_of_lt_of_le hε (le_max_right _ _)
  rw [abs_div, abs_of_pos hM, div_le_iff₀ hM]
  exact (abs_H₁_le hL hhom v).trans (mul_le_mul_of_nonneg_left (le_max_left _ _) hL0)

lemma gtr_eq_far (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v) {ε : ℝ}
    (hε : 0 < ε) {v : ι → ℝ} (hv : ε < radF53 v) : gtr H₁ ε v = H₁ (unitF53 v) := by
  unfold gtr
  have hr0 : 0 < radF53 v := lt_trans hε hv
  rw [max_eq_left hv.le, hom_rad hhom v]
  field_simp

/-- One truncation level: `‖G − EG‖_p ≤ ‖G − g_ε‖_p + ‖g_ε − Eg_ε‖_p + |Eg_ε − EG|` with the
small-ball bounds, and the Poincaré bound of `‖g_ε − Eg_ε‖_p`. -/
theorem ls_sharp_eps [DecidableEq ι] [Nonempty ι] (hL0 : 0 ≤ L) (hL : EuLip H₁ L)
    (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v) {q : ℕ} (hq : 1 ≤ q)
    (hqk : 2 * q < Fintype.card ι) {ε : ℝ} (hε : 0 < ε) :
    momN (stdGauss ι) (2 * q) (fun v => H₁ (unitF53 v) - ∫ w, H₁ (unitF53 w) ∂stdGauss ι) ≤
      2 * L * ((stdGauss ι).real {v | radF53 v ≤ ε}) ^ (((2 * q : ℕ) : ℝ)⁻¹) +
      cLS q * (momN (stdGauss ι) (2 * q) (fun v => √(gradSq H₁ v - H₁ (unitF53 v) ^ 2)) *
          (((Fintype.card ι : ℝ) - 2 * q)⁻¹) ^ ((2 : ℝ)⁻¹) +
        2 * L / ε * ((stdGauss ι).real {v | radF53 v ≤ ε}) ^ (((2 * q : ℕ) : ℝ)⁻¹)) +
      2 * L * (stdGauss ι).real {v | radF53 v ≤ ε} := by
  set γ := stdGauss ι with hγ
  have hp0 : 2 * q ≠ 0 := by omega
  have hc := hL.continuous hL0
  set G : (ι → ℝ) → ℝ := fun v => H₁ (unitF53 v) with hGd
  have mG : Measurable G := hc.measurable.comp measurable_unitF
  have bG : ∀ v, |G v| ≤ L := hom_unit_bound hL0 hL hhom
  set m := ∫ v, G v ∂γ with hm
  have hmL : |m| ≤ L := by
    rw [hm]; refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |G v| ∂γ ≤ ∫ _v, L ∂γ :=
          integral_mono (intB mG.abs (M := L) fun v => by rw [abs_abs]; exact bG v)
            (integrable_const _) bG
      _ = L := by simp
  set g := gtr H₁ ε with hgd
  have hgL := gtr_lip hL0 hL hhom hε
  have hgc : Continuous g := hgL.continuous (by positivity)
  have mg : Measurable g := hgc.measurable
  have bg : ∀ v, |g v| ≤ L := gtr_abs_le hL0 hL hhom hε
  set mε := ∫ v, g v ∂γ with hmε
  have hmεL : |mε| ≤ L := by
    rw [hmε]; refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |g v| ∂γ ≤ ∫ _v, L ∂γ :=
          integral_mono (intB mg.abs (M := L) fun v => by rw [abs_abs]; exact bg v)
            (integrable_const _) bg
      _ = L := by simp
  set S := {v : ι → ℝ | radF53 v ≤ ε} with hS
  have mS : MeasurableSet S := measurableSet_le measurable_radF measurable_const
  set β := γ.real S with hβ
  have hβ0 : 0 ≤ β := measureReal_nonneg
  set c := cLS q with hcd
  have hc0 : 0 ≤ c := cLS_nonneg q
  -- `|G − g| ≤ 2L·1_S`
  have hGg : ∀ v, |G v - g v| ≤ S.indicator (fun _ => 2 * L) v := fun v => by
    by_cases hv : v ∈ S
    · rw [Set.indicator_of_mem hv]
      exact (abs_sub _ _).trans (by linarith [bG v, bg v])
    · rw [Set.indicator_of_notMem hv]
      have hv' : ε < radF53 v := lt_of_not_ge hv
      rw [hgd, gtr_eq_far hhom hε hv', hGd]; simp
  have iInd : ∀ C : ℝ, Integrable (S.indicator (fun _ => C)) γ := fun C =>
    (integrable_const C).indicator mS
  have intInd : ∀ C : ℝ, ∫ v, S.indicator (fun _ => C) v ∂γ = β * C := fun C => by
    rw [integral_indicator mS, setIntegral_const, smul_eq_mul]
  -- Step 4: the mean shift
  have hb3 : |mε - m| ≤ 2 * L * β := by
    rw [hmε, hm, ← integral_sub (intB mg bg) (intB mG bG)]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ v, |g v - G v| ∂γ ≤ ∫ v, S.indicator (fun _ => 2 * L) v ∂γ :=
          integral_mono ((intB mg bg).sub (intB mG bG)).abs (iInd _)
            fun v => by rw [abs_sub_comm]; exact hGg v
      _ = 2 * L * β := by rw [intInd]; ring
  -- Step 1: Minkowski for `G − m = (G − g) + (g − mε) + (mε − m)`
  set X := momN γ (2 * q) (fun v => G v - m) with hX
  set b2 := momN γ (2 * q) (fun v => g v - mε) with hb2
  have hX0 : 0 ≤ X := momN_nonneg _ _ _
  have hb20 : 0 ≤ b2 := momN_nonneg _ _ _
  have hmk1 := mink4 γ (2 * q) (g1 := fun v => |G v - g v|) (g2 := fun v => |g v - mε|)
    (g3 := fun _ => |mε - m|) (g4 := fun _ => 0) (mG.sub mg).abs (mg.sub_const _).abs
    measurable_const measurable_const (fun v => abs_nonneg _) (fun v => abs_nonneg _)
    (fun _ => abs_nonneg _) (fun _ => le_rfl) (M := 2 * L)
    (fun v => (abs_sub _ _).trans (by linarith [bG v, bg v]))
    (fun v => (abs_sub _ _).trans (by linarith [bg v]))
    (fun _ => (abs_sub _ _).trans (by linarith)) (fun _ => by positivity)
    (b1 := 2 * L * β ^ (((2 * q : ℕ) : ℝ)⁻¹)) (b2 := b2) (b3 := |mε - m|) (b4 := 0)
    (by positivity) hb20 (abs_nonneg _) le_rfl
    (by
      rw [mul_pow, Real.rpow_inv_natCast_pow hβ0 hp0]
      calc ∫ v, |G v - g v| ^ (2 * q) ∂γ ≤ ∫ v, S.indicator (fun _ => (2 * L) ^ (2 * q)) v ∂γ := by
            refine integral_mono (intB ((mG.sub mg).abs.pow_const _) (M := (2 * L) ^ (2 * q))
              fun v => ?_) (iInd _) fun v => ?_
            · rw [abs_pow, abs_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by linarith [bG v, bg v])) _
            · by_cases hv : v ∈ S
              · have := hGg v
                rw [Set.indicator_of_mem hv] at this ⊢
                exact pow_le_pow_left₀ (abs_nonneg _) this _
              · have := hGg v
                rw [Set.indicator_of_notMem hv] at this ⊢
                have h0 : |G v - g v| = 0 := le_antisymm this (abs_nonneg _)
                rw [h0, zero_pow hp0]
        _ = (2 * L) ^ (2 * q) * β := by rw [intInd]; ring)
    (by rw [momN_pow γ hp0])
    (by simp)
    (by simp [zero_pow hp0])
  simp only [add_zero] at hmk1
  have hX1 : X ≤ 2 * L * β ^ (((2 * q : ℕ) : ℝ)⁻¹) + b2 + |mε - m| := by
    have hXp : X ^ (2 * q) ≤ (2 * L * β ^ (((2 * q : ℕ) : ℝ)⁻¹) + b2 + |mε - m|) ^ (2 * q) := by
      rw [hX, momN_pow γ hp0]
      refine le_trans (integral_mono (intB ((mG.sub_const _).abs.pow_const _)
        (M := (2 * L) ^ (2 * q)) fun v => ?_) (intB ((((mG.sub mg).abs.add (mg.sub_const _).abs).add
          measurable_const).pow_const _) (M := (2 * L + 2 * L + 2 * L) ^ (2 * q)) fun v => ?_)
          fun v => ?_) hmk1
      · rw [abs_pow, abs_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) ((abs_sub _ _).trans (by linarith [bG v])) _
      · show |(|G v - g v| + |g v - mε| + |mε - m|) ^ (2 * q)| ≤ (2 * L + 2 * L + 2 * L) ^ (2 * q)
        have h0 : 0 ≤ |G v - g v| + |g v - mε| + |mε - m| := by positivity
        have h1 : |G v - g v| ≤ 2 * L := (abs_sub _ _).trans (by linarith [bG v, bg v])
        have h2 : |g v - mε| ≤ 2 * L := (abs_sub _ _).trans (by linarith [bg v])
        have h3 : |mε - m| ≤ 2 * L := (abs_sub _ _).trans (by linarith)
        rw [abs_of_nonneg (pow_nonneg h0 _)]
        exact pow_le_pow_left₀ h0 (by linarith) _
      · refine pow_le_pow_left₀ (abs_nonneg _) ?_ _
        calc |G v - m| = |(G v - g v) + (g v - mε) + (mε - m)| := by ring_nf
          _ ≤ |G v - g v| + |g v - mε| + |mε - m| := abs_add_three _ _ _
    exact le_of_pow_le_pow_left₀ hp0 (by positivity) hXp
  -- Step 2: Poincaré for the truncated lift
  set Z := momN γ (2 * q) (fun v => √(gradSq g v)) with hZ
  have hZ0 : 0 ≤ Z := momN_nonneg _ _ _
  have hcp : c ^ (2 * q) = (π / 2) ^ (2 * q) * gmom (2 * q) := by
    rw [hcd, cLS, mul_pow, Real.rpow_inv_natCast_pow (gmom_nonneg _) hp0]
  have hb2Z : b2 ≤ c * Z := by
    have hP := poincare_p (by positivity : (0 : ℝ) ≤ 2 * L / ε) hgL (p := 2 * q) (by omega)
    have h1 : b2 ^ (2 * q) ≤ (c * Z) ^ (2 * q) := by
      rw [hb2, momN_pow γ hp0, mul_pow, hcp, hZ, momN_pow γ hp0]
      simp_rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      rw [mul_assoc]
      exact hP
    exact le_of_pow_le_pow_left₀ hp0 (by positivity) h1
  -- Step 3: the gradient of the truncated lift
  set T : (ι → ℝ) → ℝ := fun v => gradSq H₁ v - G v ^ 2 with hTd
  have mT : Measurable T := (measurable_gradSq H₁).sub (mG.pow_const 2)
  have bT : ∀ v, √(T v) ≤ L := fun v => by
    rw [show L = √(L ^ 2) from (Real.sqrt_sq hL0).symm]
    refine Real.sqrt_le_sqrt ?_
    have := gradSq_le hL0 hL v
    simp only [hTd]; nlinarith [sq_nonneg (G v)]
  set Y := momN γ (2 * q) (fun v => √(T v)) with hY
  have hY0 : 0 ≤ Y := momN_nonneg _ _ _
  set B' := (((Fintype.card ι : ℝ) - 2 * q)⁻¹) ^ ((2 : ℝ)⁻¹) with hB'
  have hkq : (0 : ℝ) < (Fintype.card ι : ℝ) - 2 * q := by
    have : (2 * q : ℝ) < Fintype.card ι := by exact_mod_cast hqk
    linarith
  have hB'0 : 0 ≤ B' := Real.rpow_nonneg (inv_nonneg.mpr hkq.le) _
  have hB'p : B' ^ (2 * q) = (((Fintype.card ι : ℝ) - 2 * q)⁻¹) ^ q := by
    rw [hB', pow_mul, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow,
      Real.sq_sqrt (inv_nonneg.mpr hkq.le)]
  set h1 : (ι → ℝ) → ℝ := fun v => if ε < radF53 v then √(T v) / radF53 v else 0 with hh1
  have mh1 : Measurable h1 :=
    Measurable.ite (measurableSet_lt measurable_const measurable_radF) (mT.sqrt.div measurable_radF)
      measurable_const
  have bh1 : ∀ v, 0 ≤ h1 v ∧ h1 v ≤ 2 * L / ε := fun v => by
    simp only [hh1]
    split_ifs with hv
    · have hr : 0 < radF53 v := lt_trans hε hv
      refine ⟨div_nonneg (Real.sqrt_nonneg _) hr.le, ?_⟩
      calc √(T v) / radF53 v ≤ L / ε := by
            rw [div_le_div_iff₀ hr hε]
            nlinarith [bT v, Real.sqrt_nonneg (T v)]
        _ ≤ 2 * L / ε := div_le_div_of_nonneg_right (by linarith) hε.le
    · exact ⟨le_rfl, by positivity⟩
  have hgr : ∀ v, √(gradSq g v) ≤ h1 v + S.indicator (fun _ => 2 * L / ε) v := fun v => by
    by_cases hv : ε < radF53 v
    · have hvS : v ∉ S := fun h => absurd h (not_le.mpr hv)
      simp only [hh1, if_pos hv, Set.indicator_of_notMem hvS, add_zero]
      exact gtr_grad_le hhom hε hv
    · have hvS : v ∈ S := le_of_not_gt hv
      simp only [hh1, if_neg hv, Set.indicator_of_mem hvS, zero_add]
      rw [show 2 * L / ε = √((2 * L / ε) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
      exact Real.sqrt_le_sqrt (gradSq_le (by positivity) hgL v)
  -- `∫ h1^{2q} ≤ (Y B')^{2q}`
  set F : (ι → ℝ) → ℝ := fun u => √(T u) ^ (2 * q) with hF
  set Gr : ℝ → ℝ := fun ρ => if ε < ρ then (ρ ^ (2 * q))⁻¹ else 0 with hGr
  have hpt : ∀ v, h1 v ^ (2 * q) = F (unitF53 v) * Gr (radF53 v) := fun v => by
    by_cases hv : ε < radF53 v
    · have hr : 0 < radF53 v := lt_trans hε hv
      have hv0 : v ≠ 0 := fun h => by rw [h] at hr; simp [radF53] at hr
      have hTu : T (unitF53 v) = T v := by
        simp only [hTd, hGd]
        rw [unitF_unitF hv0]
        congr 1
        have : unitF53 v = (radF53 v)⁻¹ • v := by unfold unitF53; rw [one_div]; rfl
        rw [this, gradSq_hom hhom (inv_pos.mpr hr)]
      simp only [hh1, hF, hGr, if_pos hv, hTu, div_pow]
      ring
    · simp only [hh1, hGr, if_neg hv, mul_zero, zero_pow hp0]
  have mF : Measurable F := mT.sqrt.pow_const _
  have mGr : Measurable Gr := Measurable.ite (measurableSet_lt measurable_const measurable_id)
    (measurable_id.pow_const _).inv measurable_const
  have hnz : ∀ᵐ v ∂γ, v ≠ 0 := by
    have h0 : γ {(0 : ι → ℝ)} = 0 :=
      BstLean.Part148.stdGauss_ac (measure_singleton (0 : ι → ℝ))
    rw [ae_iff]
    simpa using h0
  have hFu : ∫ v, F (unitF53 v) ∂γ = Y ^ (2 * q) := by
    rw [hY, momN_pow γ hp0]
    refine integral_congr_ae (hnz.mono fun v hv => ?_)
    simp only [hF, abs_of_nonneg (Real.sqrt_nonneg _)]
    congr 2
    simp only [hTd, hGd]
    rw [unitF_unitF hv]
    congr 1
    have hr : 0 < radF53 v := radF_pos hv
    have : unitF53 v = (radF53 v)⁻¹ • v := by unfold unitF53; rw [one_div]; rfl
    rw [this, gradSq_hom hhom (inv_pos.mpr hr)]
  have hI1 : ∫ v, h1 v ^ (2 * q) ∂γ ≤ (Y * B') ^ (2 * q) := by
    simp_rw [hpt]
    rw [polar_integral_mul F Gr mF mGr, hFu, mul_pow, hB'p]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hY0 _)
    exact trunc_invRad_le hqk ε
  have hmk2 := mink4 γ (2 * q) (g1 := h1) (g2 := S.indicator (fun _ => 2 * L / ε))
    (g3 := fun _ => 0) (g4 := fun _ => 0) mh1 (measurable_const.indicator mS) measurable_const
    measurable_const (fun v => (bh1 v).1)
    (fun v => by by_cases hv : v ∈ S <;> simp [hv]; positivity) (fun _ => le_rfl) (fun _ => le_rfl)
    (M := 2 * L / ε) (fun v => (bh1 v).2)
    (fun v => by by_cases hv : v ∈ S <;> simp [hv]; positivity)
    (fun _ => by positivity) (fun _ => by positivity)
    (b1 := Y * B') (b2 := 2 * L / ε * β ^ (((2 * q : ℕ) : ℝ)⁻¹)) (b3 := 0) (b4 := 0)
    (mul_nonneg hY0 hB'0) (by positivity) le_rfl le_rfl hI1
    (by
      rw [mul_pow, Real.rpow_inv_natCast_pow hβ0 hp0]
      have e : ∀ v, S.indicator (fun _ => 2 * L / ε) v ^ (2 * q) =
          S.indicator (fun _ => (2 * L / ε) ^ (2 * q)) v := fun v => by
        by_cases hv : v ∈ S <;> simp [hv, zero_pow hp0]
      simp_rw [e]
      rw [intInd]; ring_nf; exact le_rfl)
    (by simp [zero_pow hp0]) (by simp [zero_pow hp0])
  simp only [add_zero] at hmk2
  have hZ1 : Z ≤ Y * B' + 2 * L / ε * β ^ (((2 * q : ℕ) : ℝ)⁻¹) := by
    have h3 : Z ^ (2 * q) ≤ (Y * B' + 2 * L / ε * β ^ (((2 * q : ℕ) : ℝ)⁻¹)) ^ (2 * q) := by
      rw [hZ, momN_pow γ hp0]
      simp_rw [abs_of_nonneg (Real.sqrt_nonneg _)]
      refine le_trans (integral_mono (intB ((measurable_gradSq g).sqrt.pow_const _)
        (M := (2 * L / ε) ^ (2 * q)) fun v => ?_) (intB ((mh1.add
          (measurable_const.indicator mS)).pow_const _) (M := (2 * L / ε + 2 * L / ε) ^ (2 * q))
          fun v => ?_) fun v => ?_) hmk2
      · rw [abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _)]
        refine pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ _
        rw [show 2 * L / ε = √((2 * L / ε) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
        exact Real.sqrt_le_sqrt (gradSq_le (by positivity) hgL v)
      · have h0 : 0 ≤ h1 v + S.indicator (fun _ => 2 * L / ε) v := by
          have := (bh1 v).1
          by_cases hv : v ∈ S <;> simp [hv] <;> positivity
        have h2 : S.indicator (fun _ => 2 * L / ε) v ≤ 2 * L / ε := by
          by_cases hv : v ∈ S <;> simp [hv]; positivity
        show |(h1 v + S.indicator (fun _ => 2 * L / ε) v) ^ (2 * q)| ≤ _
        rw [abs_of_nonneg (pow_nonneg h0 _)]
        exact pow_le_pow_left₀ h0 (by linarith [(bh1 v).2]) _
      · exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (hgr v) _
    exact le_of_pow_le_pow_left₀ hp0 (by positivity) h3
  -- combine
  calc X ≤ 2 * L * β ^ (((2 * q : ℕ) : ℝ)⁻¹) + b2 + |mε - m| := hX1
    _ ≤ 2 * L * β ^ (((2 * q : ℕ) : ℝ)⁻¹) + c * (Y * B' + 2 * L / ε * β ^ (((2 * q : ℕ) : ℝ)⁻¹)) +
          2 * L * β := by
        gcongr
        exact hb2Z.trans (mul_le_mul_of_nonneg_left hZ1 hc0)


/-- **Lemma LS of order `2q`, sharp form (the paper's constant)**: for a Lipschitz positively
1-homogeneous `H₁` on `ℝ^k`, `2q < k`:
`‖G − EG‖_{2q} ≤ c_q·(k − 2q)^{−1/2}·‖√T‖_{2q}`, `G = H₁(Z/|Z|)`, `T = |∇H₁|² − G²`.
(Paper, Lemma `t7:p07:LS`: `c_p (∏_{j ≤ p}(n − 1 − 2j))^{−1/(2p)}`, which is at most
`c_p (n − 1 − 2p)^{−1/2}`.) -/
theorem ls_mom_sharp [DecidableEq ι] [Nonempty ι] (hL0 : 0 ≤ L) (hL : EuLip H₁ L)
    (hhom : ∀ (t : ℝ) (v : ι → ℝ), 0 < t → H₁ (t • v) = t * H₁ v) {q : ℕ} (hq : 1 ≤ q)
    (hqk : 2 * q < Fintype.card ι) :
    momN (stdGauss ι) (2 * q) (fun v => H₁ (unitF53 v) - ∫ w, H₁ (unitF53 w) ∂stdGauss ι) ≤
      cLS q * (momN (stdGauss ι) (2 * q) (fun v => √(gradSq H₁ v - H₁ (unitF53 v) ^ 2)) *
        (((Fintype.card ι : ℝ) - 2 * q)⁻¹) ^ ((2 : ℝ)⁻¹)) := by
  set X := momN (stdGauss ι) (2 * q) (fun v => H₁ (unitF53 v) - ∫ w, H₁ (unitF53 w) ∂stdGauss ι)
  set A := cLS q * (momN (stdGauss ι) (2 * q) (fun v => √(gradSq H₁ v - H₁ (unitF53 v) ^ 2)) *
        (((Fintype.card ι : ℝ) - 2 * q)⁻¹) ^ ((2 : ℝ)⁻¹))
  set k := Fintype.card ι
  set p := 2 * q
  set r : ℝ := ((p : ℕ) : ℝ)⁻¹ with hr
  have hp0 : (0 : ℝ) < p := by positivity
  have hr0 : 0 < r := inv_pos.mpr hp0
  have hc0 := cLS_nonneg q
  set C := 2 * L + cLS q * (2 * L * 2) + 2 * L with hC
  have hC0 : 0 ≤ C := by positivity
  have hkp : (p : ℝ) + 1 ≤ k := by
    have : p + 1 ≤ k := hqk
    exact_mod_cast this
  -- the bound at every level `0 < ε ≤ 1/2`
  have hlev : ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 → X ≤ A + C * (2 * ε) ^ r := fun ε hε hε2 => by
    have h := ls_sharp_eps hL0 hL hhom hq hqk hε
    set β := (stdGauss ι).real {v | radF53 v ≤ ε}
    have hβ0 : 0 ≤ β := measureReal_nonneg
    have hβ := smallBall_le (ι := ι) hε.le
    have h2e0 : 0 < 2 * ε := by positivity
    have h2e1 : 2 * ε ≤ 1 := by linarith
    -- `β^{1/p} ≤ (2ε)^{k/p} ≤ (2ε)·(2ε)^{1/p}` and `β ≤ (2ε)^{1/p}`
    have hβr : β ^ r ≤ (2 * ε) ^ ((k : ℝ) * r) := by
      calc β ^ r ≤ ((2 * ε) ^ k) ^ r := Real.rpow_le_rpow hβ0 hβ hr0.le
        _ = (2 * ε) ^ ((k : ℝ) * r) := by rw [← Real.rpow_natCast, ← Real.rpow_mul h2e0.le]
    have hkr : (k : ℝ) * r ≥ 1 + r := by
      rw [hr]; field_simp; linarith
    have h1 : (2 * ε) ^ ((k : ℝ) * r) ≤ (2 * ε) * (2 * ε) ^ r := by
      calc (2 * ε) ^ ((k : ℝ) * r) ≤ (2 * ε) ^ (1 + r) :=
            Real.rpow_le_rpow_of_exponent_ge h2e0 h2e1 hkr
        _ = (2 * ε) * (2 * ε) ^ r := by rw [Real.rpow_add h2e0, Real.rpow_one]
    have h2 : (2 * ε) * (2 * ε) ^ r ≤ (2 * ε) ^ r := by
      have := Real.rpow_nonneg h2e0.le r
      nlinarith
    have hβle : β ≤ (2 * ε) ^ r := by
      calc β ≤ (2 * ε) ^ k := hβ
        _ = (2 * ε) ^ ((k : ℝ)) := (Real.rpow_natCast _ _).symm
        _ ≤ (2 * ε) ^ r := Real.rpow_le_rpow_of_exponent_ge h2e0 h2e1 (by
            have : r ≤ 1 := by rw [hr]; exact inv_le_one_of_one_le₀ (by
              have : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by omega)
              linarith)
            have : (1 : ℝ) ≤ k := by exact_mod_cast (Fintype.card_pos : 0 < k)
            linarith)
    have hT1 : 2 * L * β ^ r ≤ 2 * L * (2 * ε) ^ r :=
      mul_le_mul_of_nonneg_left (hβr.trans (h1.trans h2)) (by positivity)
    have hT2 : 2 * L / ε * β ^ r ≤ 2 * L * 2 * (2 * ε) ^ r := by
      calc 2 * L / ε * β ^ r ≤ 2 * L / ε * ((2 * ε) * (2 * ε) ^ r) :=
            mul_le_mul_of_nonneg_left (hβr.trans h1) (by positivity)
        _ = 2 * L * 2 * (2 * ε) ^ r := by field_simp
    have hT3 : 2 * L * β ≤ 2 * L * (2 * ε) ^ r := mul_le_mul_of_nonneg_left hβle (by positivity)
    have hp' : ((2 * q : ℕ) : ℝ)⁻¹ = r := rfl
    rw [hp'] at h
    calc X ≤ 2 * L * β ^ r + cLS q * (momN (stdGauss ι) (2 * q)
            (fun v => √(gradSq H₁ v - H₁ (unitF53 v) ^ 2)) *
          (((k : ℝ) - 2 * q)⁻¹) ^ ((2 : ℝ)⁻¹) + 2 * L / ε * β ^ r) + 2 * L * β := h
      _ ≤ 2 * L * (2 * ε) ^ r + cLS q * (momN (stdGauss ι) (2 * q)
            (fun v => √(gradSq H₁ v - H₁ (unitF53 v) ^ 2)) *
          (((k : ℝ) - 2 * q)⁻¹) ^ ((2 : ℝ)⁻¹) + 2 * L * 2 * (2 * ε) ^ r) +
            2 * L * (2 * ε) ^ r := by gcongr
      _ = A + C * (2 * ε) ^ r := by rw [hC]; ring
  -- the limit `ε → 0`
  have hcont : ContinuousAt (fun ε : ℝ => A + C * (2 * ε) ^ r) 0 := by
    have h0 : ContinuousAt (fun y : ℝ => y ^ r) (2 * 0) :=
      Real.continuousAt_rpow_const _ _ (Or.inr hr0.le)
    exact continuousAt_const.add (continuousAt_const.mul
      (h0.comp (continuousAt_const.mul continuousAt_id)))
  have ht : Tendsto (fun ε : ℝ => A + C * (2 * ε) ^ r) (𝓝[>] 0) (𝓝 (A + C * (2 * 0) ^ r)) :=
    hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), X ≤ A + C * (2 * ε) ^ r := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 2 by norm_num)] with ε hε
    exact hlev ε hε.1 hε.2.le
  have := ge_of_tendsto ht hev
  rwa [mul_zero, Real.zero_rpow hr0.ne', mul_zero, add_zero] at this

open BstLean.Part161 (xLat) in
open BstLean.Part157 (Ret) in
/-- **Lemma LS of order `2q` on a latitude sphere, sharp form** (Lemma `t7:p07:LS` as stated):
`‖Φ(x) − E(Φ | s)‖_{2q} ≤ c_q (n − 1 − 2q)^{−1/2}·‖√T‖_{2q}` for `2q < n − 1`. -/
theorem ls_lat_mom_sharp {n : ℕ} (hn : 2 ≤ n) (c : Ret n) {s : ℝ} (hs : s ^ 2 ≤ 1)
    {Φ : (Fin n → ℝ) → ℝ} (hL0 : 0 ≤ L) (hL : EuLip Φ L)
    (hhom : ∀ (t : ℝ) (x : Fin n → ℝ), 0 < t → Φ (t • x) = t * Φ x) {q : ℕ} (hq : 1 ≤ q)
    (hqn : 2 * q < n - 1) :
    momN (stdGauss (Fin (n - 1))) (2 * q)
        (fun v => Φ (xLat c s (unitF53 v)) - ∫ w, Φ (xLat c s (unitF53 w)) ∂stdGauss (Fin (n - 1))) ≤
      cLS q * (momN (stdGauss (Fin (n - 1))) (2 * q)
        (fun v => √(gradSq (fun w => Φ (xLatH c s w)) v - Φ (xLat c s (unitF53 v)) ^ 2)) *
          (((n : ℝ) - 1 - 2 * q)⁻¹) ^ ((2 : ℝ)⁻¹)) := by
  have : Nonempty (Fin (n - 1)) := ⟨⟨0, by omega⟩⟩
  set H₁ : (Fin (n - 1) → ℝ) → ℝ := fun w => Φ (xLatH c s w) with hH₁
  have hHL : EuLip H₁ L := by
    intro v w
    refine (hL _ _).trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hL0)
    exact xLatH_dist (by omega) c hs v w
  have hHh : ∀ (t : ℝ) (v : Fin (n - 1) → ℝ), 0 < t → H₁ (t • v) = t * H₁ v := fun t v ht => by
    simp only [hH₁]; rw [xLatH_smul c s ht, hhom _ _ ht]
  have h := ls_mom_sharp hL0 hHL hHh hq (by rw [Fintype.card_fin]; exact hqn)
  have hnz : ∀ᵐ v ∂stdGauss (Fin (n - 1)), v ≠ 0 := by
    have h0 : stdGauss (Fin (n - 1)) {(0 : Fin (n - 1) → ℝ)} = 0 :=
      BstLean.Part148.stdGauss_ac (measure_singleton (0 : Fin (n - 1) → ℝ))
    rw [ae_iff]
    simpa using h0
  have hG : ∀ᵐ v ∂stdGauss (Fin (n - 1)), H₁ (unitF53 v) = Φ (xLat c s (unitF53 v)) := by
    filter_upwards [hnz] with v hv
    simp only [hH₁]
    rw [xLatH_eq, radF_unitF hv, unitF_unitF hv, one_smul]
  have hm : ∫ w, H₁ (unitF53 w) ∂stdGauss (Fin (n - 1)) =
      ∫ w, Φ (xLat c s (unitF53 w)) ∂stdGauss (Fin (n - 1)) := integral_congr_ae hG
  have e1 : momN (stdGauss (Fin (n - 1))) (2 * q)
      (fun v => H₁ (unitF53 v) - ∫ w, H₁ (unitF53 w) ∂stdGauss (Fin (n - 1))) =
      momN (stdGauss (Fin (n - 1))) (2 * q)
      (fun v => Φ (xLat c s (unitF53 v)) - ∫ w, Φ (xLat c s (unitF53 w)) ∂stdGauss (Fin (n - 1))) := by
    unfold momN; rw [hm]
    congr 1
    exact integral_congr_ae (hG.mono fun v hv => by beta_reduce; rw [hv])
  have e2 : momN (stdGauss (Fin (n - 1))) (2 * q)
      (fun v => √(gradSq H₁ v - H₁ (unitF53 v) ^ 2)) =
      momN (stdGauss (Fin (n - 1))) (2 * q)
      (fun v => √(gradSq (fun w => Φ (xLatH c s w)) v - Φ (xLat c s (unitF53 v)) ^ 2)) := by
    unfold momN
    congr 1
    exact integral_congr_ae (hG.mono fun v hv => by beta_reduce; rw [hv])
  have hc : ((Fintype.card (Fin (n - 1)) : ℕ) : ℝ) - 2 * q = (n : ℝ) - 1 - 2 * q := by
    rw [Fintype.card_fin, Nat.cast_sub (by omega)]; push_cast; ring
  rw [e1, e2, hc] at h
  exact h

end BstLean.Part162

open BstLean.Part162 in
#print axioms ls_mom_sharp
open BstLean.Part162 in
#print axioms ls_lat_mom_sharp
