import BstLean.Part206First
import BstLean.Part154NumA

/-! Scalar estimates for the first-layer mean energy. -/
namespace BstLean.Part211
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped Topology
open BstLean.Part137 (psiS psiS_nonneg)
open BstLean.Part153 (phiG PhiG psiG phiG_pos PhiG_pos PhiG_le_one)
open BstLean.Part154 (psiS_closed phiG_le_zero abs_mul_phiG_le)

lemma phi_zero_bound : phiG 0 ≤ 2 / 5 :=
  BstLean.Part154.phiG_bounds_NumA.2.1.trans (by norm_num)

lemma phi_one_bound : phiG 1 ≤ 1 / 4 :=
  BstLean.Part154.phiG_bounds_NumA.2.2.2.trans (by norm_num)

lemma psiG_upper (v : ℝ) : psiG v ≤ |v| + phiG 0 := by
  have h : v * PhiG v ≤ |v| := by
    rcases le_total 0 v with hv | hv
    · simpa [abs_of_nonneg hv] using mul_le_mul_of_nonneg_left (PhiG_le_one v) hv
    · have := mul_nonpos_of_nonpos_of_nonneg hv (PhiG_pos v).le
      linarith [abs_nonneg v]
  unfold psiG
  linarith [phiG_le_zero v]

lemma sq_mul_phi_bound (v : ℝ) : v ^ 2 * phiG v ≤ 2 / 5 := by
  have h := Real.add_one_le_exp (v ^ 2 / 2 - 1)
  have hprod : rexp (v ^ 2 / 2 - 1) * rexp (-(v ^ 2 / 2)) = (rexp 1)⁻¹ := by
    rw [← exp_add, ← exp_neg]
    congr 1
    ring
  have hmul := mul_le_mul_of_nonneg_right h (exp_pos (-(v ^ 2 / 2))).le
  rw [hprod] at hmul
  have hi : (rexp 1)⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ (exp_pos _) (by norm_num)]
    linarith [Real.exp_one_gt_d9]
  have hv : v ^ 2 * rexp (-(v ^ 2 / 2)) ≤ 1 := by linarith
  have hφ : phiG v = phiG 0 * rexp (-(v ^ 2 / 2)) := by
    unfold phiG
    simp
  rw [hφ]
  calc v ^ 2 * (phiG 0 * rexp (-(v ^ 2 / 2))) =
      phiG 0 * (v ^ 2 * rexp (-(v ^ 2 / 2))) := by ring
    _ ≤ phiG 0 * 1 := mul_le_mul_of_nonneg_left hv (phiG_pos 0).le
    _ ≤ 2 / 5 := by simpa using phi_zero_bound

lemma cube_mul_phi_bound (v : ℝ) : |v| ^ 3 * phiG v ≤ 3 / 5 := by
  have h := Real.add_one_le_exp (v ^ 2 / 3 - 1)
  have hh : v ^ 2 / 3 ≤ rexp (v ^ 2 / 3 - 1) := by linarith
  have hh3 := pow_le_pow_left₀ (by positivity : 0 ≤ v ^ 2 / 3) hh 3
  have he3 : rexp (v ^ 2 / 3 - 1) ^ 3 = rexp (v ^ 2 - 3) := by
    rw [← exp_nat_mul]
    congr 1
    ring
  rw [he3] at hh3
  have hmul := mul_le_mul_of_nonneg_right hh3 (exp_pos (-(v ^ 2))).le
  have he : rexp (v ^ 2 - 3) * rexp (-(v ^ 2)) = (rexp 1)⁻¹ ^ 3 := by
    rw [← exp_add, ← exp_neg, ← exp_nat_mul]
    congr 1
    ring
  rw [he] at hmul
  have hi : (rexp 1)⁻¹ ≤ 2 / 5 := by
    rw [inv_le_comm₀ (exp_pos _) (by norm_num)]
    linarith [Real.exp_one_gt_d9]
  have hi3 := pow_le_pow_left₀ (inv_nonneg.mpr (exp_pos 1).le) hi 3
  have hφ : phiG v = phiG 0 * rexp (-(v ^ 2 / 2)) := by unfold phiG; simp
  have he2 : rexp (-(v ^ 2 / 2)) ^ 2 = rexp (-(v ^ 2)) := by
    rw [← exp_nat_mul]
    congr 1
    ring
  have hφ2 : phiG 0 ^ 2 ≤ (2 / 5 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (phiG_pos 0).le phi_zero_bound 2
  have hv : v ^ 6 * rexp (-(v ^ 2)) ≤ 27 * (2 / 5 : ℝ) ^ 3 := by
    nlinarith only [hmul, hi3]
  have hsq : (|v| ^ 3 * phiG v) ^ 2 ≤ (3 / 5 : ℝ) ^ 2 := by
    rw [hφ, mul_pow, mul_pow, he2]
    have hav : (|v| ^ 3) ^ 2 = v ^ 6 := by
      rw [← pow_mul, show 3 * 2 = 2 * 3 from rfl, pow_mul, sq_abs]
      ring
    rw [hav]
    have h := mul_le_mul hφ2 hv (by positivity : 0 ≤ v ^ 6 * rexp (-(v ^ 2))) (by norm_num)
    nlinarith only [h]
  nlinarith [sq_nonneg (|v| ^ 3 * phiG v - 3 / 5)]

lemma psiS_scale_deriv (a : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t => psiS t a) (phiG (a / s)) s := by
  have hd : HasDerivAt (fun t : ℝ => a / t) (-a / s ^ 2) s := by
    convert (hasDerivAt_const s a).div (hasDerivAt_id s) hs.ne' using 1 <;>
      first | rfl | (dsimp; ring)
  have h := ((BstLean.Part153.hasDerivAt_PhiG (a / s)).comp s hd).const_mul a
  have h' := (hasDerivAt_id s).mul ((BstLean.Part153.hasDerivAt_phiG (a / s)).comp s hd)
  have h'' := h.add h'
  have he : a * (phiG (a / s) * (-a / s ^ 2)) +
      (1 * phiG (a / s) + s * (-(a / s) * phiG (a / s) * (-a / s ^ 2))) =
      phiG (a / s) := by field_simp; ring
  simp only [Function.comp_apply, id_eq, neg_mul] at h'' he
  rw [he] at h''
  apply h''.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hs] with t ht
  exact psiS_closed ht a

noncomputable def smoothSlope (a s : ℝ) : ℝ := 2 * psiS s a * phiG (a / s)

noncomputable def smoothCurvature (a s : ℝ) : ℝ :=
  2 * phiG (a / s) ^ 2 + 2 * (psiS s a / s) * (a / s) ^ 2 * phiG (a / s)

lemma smooth_square_deriv (a : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun t => psiS t a ^ 2) (smoothSlope a s) s := by
  convert (psiS_scale_deriv a hs).pow 2 using 1 <;> simp [smoothSlope]

lemma smoothSlope_deriv (a : ℝ) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (smoothSlope a) (smoothCurvature a s) s := by
  have hd : HasDerivAt (fun t : ℝ => a / t) (-a / s ^ 2) s := by
    convert (hasDerivAt_const s a).div (hasDerivAt_id s) hs.ne' using 1 <;>
      first | rfl | (dsimp; ring)
  have h := ((psiS_scale_deriv a hs).const_mul 2).mul
    ((BstLean.Part153.hasDerivAt_phiG (a / s)).comp s hd)
  convert h using 1
  · rfl
  · dsimp [smoothCurvature]
    field_simp <;> ring

lemma smoothSlope_bounds (a : ℝ) {s : ℝ} (hs : 0 < s) :
    0 ≤ smoothSlope a s ∧ smoothSlope a s ≤ s := by
  have hφ := (phiG_pos (a / s)).le
  have h0 := (phiG_pos 0).le
  have hp := mul_le_mul_of_nonneg_right (psiG_upper (a / s)) hφ
  have hv := (abs_mul_phiG_le (a / s)).trans phi_one_bound
  have hh := mul_le_mul ((phiG_le_zero (a / s)).trans phi_zero_bound)
    phi_zero_bound h0 (by norm_num : (0 : ℝ) ≤ 2 / 5)
  have hb : 2 * psiG (a / s) * phiG (a / s) ≤ 1 := by nlinarith
  unfold smoothSlope
  refine ⟨mul_nonneg (mul_nonneg (by norm_num) (psiS_nonneg s a)) hφ, ?_⟩
  rw [BstLean.Part153.psiS_scale hs, BstLean.Part153.psiS_one]
  nlinarith [mul_le_mul_of_nonneg_left hb hs.le]

lemma smoothCurvature_bounds (a : ℝ) {s : ℝ} (hs : 0 < s) :
    0 ≤ smoothCurvature a s ∧ smoothCurvature a s ≤ 2 := by
  have he : psiS s a / s = psiG (a / s) := by
    rw [BstLean.Part153.psiS_scale hs, BstLean.Part153.psiS_one]
    field_simp
  have hφ := (phiG_pos (a / s)).le
  have hp := mul_le_mul_of_nonneg_right (psiG_upper (a / s))
    (mul_nonneg (sq_nonneg (a / s)) hφ)
  have hc := cube_mul_phi_bound (a / s)
  have hsq := mul_le_mul phi_zero_bound (sq_mul_phi_bound (a / s))
    (by positivity : 0 ≤ (a / s) ^ 2 * phiG (a / s)) (by norm_num : (0 : ℝ) ≤ 2 / 5)
  have hh := pow_le_pow_left₀ hφ ((phiG_le_zero (a / s)).trans phi_zero_bound) 2
  have hab : |a / s| ^ 3 = |a / s| * (a / s) ^ 2 := by
    rw [pow_succ, sq_abs]
    ring
  rw [hab] at hc
  unfold smoothCurvature
  rw [he]
  refine ⟨add_nonneg (mul_nonneg (by norm_num) (sq_nonneg _))
    (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
      (BstLean.Part153.psiG_nonneg _)) (sq_nonneg _)) hφ), ?_⟩
  nlinarith only [hp, hc, hsq, hh]

lemma smooth_square_taylor_pos (a : ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    |psiS t a ^ 2 - psiS s a ^ 2 - smoothSlope a s * (t - s)| ≤ (t - s) ^ 2 := by
  let u : ℝ → ℝ := fun x => s + (t - s) * x
  have hu : ∀ x ∈ Icc (0 : ℝ) 1, 0 < u x := by
    intro x hx
    dsimp [u]
    nlinarith [mul_nonneg hs.le (sub_nonneg.mpr hx.2), mul_nonneg ht.le hx.1]
  have hd : ∀ x, HasDerivAt u (t - s) x := by
    intro x
    convert ((hasDerivAt_id x).const_mul (t - s)).const_add s using 1 <;>
      first | rfl | simp
  have h1 : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun x => psiS (u x) a ^ 2) (smoothSlope a (u x) * (t - s)) x :=
    fun x hx => (smooth_square_deriv a (hu x hx)).comp x (hd x)
  have h2 : ∀ x ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun x => smoothSlope a (u x) * (t - s))
        (smoothCurvature a (u x) * (t - s) ^ 2) x := by
    intro x hx
    convert ((smoothSlope_deriv a (hu x hx)).comp x (hd x)).mul_const (t - s) using 1
    · rfl
    · ring
  have hb : ∀ x ∈ Icc (0 : ℝ) 1,
      |smoothCurvature a (u x) * (t - s) ^ 2| ≤ 2 * (t - s) ^ 2 := by
    intro x hx
    rw [abs_of_nonneg (mul_nonneg (smoothCurvature_bounds a (hu x hx)).1 (sq_nonneg _))]
    exact mul_le_mul_of_nonneg_right (smoothCurvature_bounds a (hu x hx)).2 (sq_nonneg _)
  have h := BstLean.Part154.taylor2 h1 h2 hb
  simpa [u] using h

lemma psiS_continuous_scale (a : ℝ) : Continuous (fun s => psiS s a) := by
  have h : LipschitzWith 1 (fun s => psiS s a) := by
    apply LipschitzWith.of_dist_le_mul
    intro s t
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using
      BstLean.Part141.psiS_lip_s s t a
  exact h.continuous

theorem smooth_square_taylor (a : ℝ) {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    |psiS t a ^ 2 - psiS s a ^ 2 - smoothSlope a s * (t - s)| ≤ (t - s) ^ 2 := by
  rcases ht.eq_or_lt with ht | ht
  · subst t
    have hc : Continuous (fun t : ℝ =>
        |psiS t a ^ 2 - psiS s a ^ 2 - smoothSlope a s * (t - s)|) :=
      (((psiS_continuous_scale a).pow 2 |>.sub continuous_const).sub
        (continuous_const.mul (continuous_id.sub continuous_const))).abs
    have hc' : Continuous (fun t : ℝ => (t - s) ^ 2) := by fun_prop
    exact le_of_tendsto_of_tendsto
      (hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (hc'.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
      (show ∀ᶠ t : ℝ in 𝓝[>] 0,
        |psiS t a ^ 2 - psiS s a ^ 2 - smoothSlope a s * (t - s)| ≤ (t - s) ^ 2 from
        Filter.mem_of_superset self_mem_nhdsWithin fun t ht => smooth_square_taylor_pos a hs ht)
  · exact smooth_square_taylor_pos a hs ht

theorem psiS_homogeneous {r : ℝ} (hr : 0 ≤ r) (s a : ℝ) :
    psiS (r * s) (r * a) = r * psiS s a := by
  unfold psiS
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    dsimp only
    rw [show r * a + r * s * z = r * (a + s * z) by ring,
      BstLean.Part130.relu_mul_of_nonneg hr]

theorem psiS_square_bound (s a : ℝ) : psiS s a ^ 2 ≤ a ^ 2 + s ^ 2 := by
  have hi : Integrable (fun z : ℝ => (a + s * z) ^ 2) (gaussianReal 0 1) := by
    have h : MemLp (fun z : ℝ => a + s * z) 2 (gaussianReal 0 1) :=
      (memLp_const a).add ((memLp_id_gaussianReal 2).const_mul s)
    exact (memLp_two_iff_integrable_sq h.aestronglyMeasurable).mp h
  calc _ ≤ ∫ z, BstLean.Part130.relu (a + s * z) ^ 2 ∂gaussianReal 0 1 :=
        BstLean.Part137.psiS_sq_le s a
    _ ≤ ∫ z, (a + s * z) ^ 2 ∂gaussianReal 0 1 :=
        integral_mono (BstLean.Part137.integrable_relu_shift_sq a s) hi fun z =>
          BstLean.Part137.relu_sq_le _
    _ = _ := BstLean.Part150.int_affine_sq a s

#print axioms smooth_square_taylor
#print axioms psiS_homogeneous
#print axioms psiS_square_bound
end BstLean.Part211
