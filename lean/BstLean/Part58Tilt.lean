import BstLean.Part58Defs
import BstLean.Part56MomProg_Basic
import BstLean.Part50Laws
import BstLean.Part56MomProg_Sphere
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import BstLean.Part39BMarginal
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Part 58, wave 1: Lemmas Y1 and Y2, the one-dimensional tilt lemmas (source §4)

Specification: `delegations/answers/p58-spec-opus.md` §4.
Status: all three interface theorems are proved. `lemmaY1_58_of` uses Gibbs' inequality
`t E_t y ≥ log Z(t)` and `Z(t) ≥ e^{tb} U{y ≥ b}`. The tail proof uses Part 39's
complement-coordinate marginal and continuous cutoffs. The variance proof uses differentiation
under the integral, the mean value theorem, and Part 56's rotation invariance.
This file imports the frozen definitions and finished Parts 29–56, with no other Part 58 proof file.

Suggested route. The law of `y = (v·x)²` under `D_{t,v}` does not depend on the unit vector `v`
(rotation invariance of `uniformSphere`); its density is `∝ y^{−1/2}(1−y)^{(n−3)/2} e^{t y}`.
Put `Z(t) = E_U e^{t y}`. Then `log Z` is convex, `(log Z)' = E_t y`, `(log Z)'' = Var_t y`.
Y1: `E_t y ≥ log Z(t)/t`, `Z(t) ≥ e^{t b} U{y ≥ b}`, `U{y ≥ b} ≥ (1−b)^{(n−1)/2}/(n−1)`, `1 − b = 1/(2C)`.
Y2: `E_{Cn} y − E_{C'n} y = (C − C') n Var_{t*} y` for some `t*` (mean value theorem), and `0 ≤ E y ≤ 1`.
-/

namespace BstLean.Part58

open MeasureTheory BstLean.Cost
open scoped ENNReal Topology
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (Mono phiM phiSq contr trL frob Tens TSymm fval varU)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part48 (SBLevel)
open BstLean.Part53 (sg)
open BstLean.Part56 (UnitV lawRK kJ EV56 rk1)
open BstLean.Part50 (binghamA qA ZA)

lemma continuous_yv (v : Fin n → ℝ) : Continuous (fun x => yv v x) := by unfold yv; fun_prop

lemma yv_bound {v x : Fin n → ℝ} (hv : UnitV v) (hx : ∑ i, x i ^ 2 = 1) : 0 ≤ yv v x ∧ yv v x ≤ 1 := by
  refine ⟨by unfold yv; positivity, ?_⟩
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v x
  unfold yv; rw [show (∑ i, v i ^ 2) = 1 from hv, hx, one_mul] at this; exact this

/-- **Lemma Y1** from the uniform tail bound. -/
theorem lemmaY1_58_of (hT : LemmaTail58) : LemmaY1_58 := by
  intro n hn C hC t ht v hv
  have hn1 : 1 ≤ n := by omega
  have hU := BstLean.Part29.uniformSphere_isProbability n hn1
  have hsph := BstLean.Part29.uniformSphere_ae_sphere n
  have hC0 : 0 < C := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht
  set U := uniformSphere n with hUdef
  -- integrability on the sphere
  have hint : ∀ {f : (Fin n → ℝ) → ℝ}, Continuous f → Integrable f U := by
    intro f hf
    obtain ⟨M, hM⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
      (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
    apply Integrable.of_bound hf.aestronglyMeasurable M
    filter_upwards [hsph] with x hx
    apply hM
    apply Set.mem_image_of_mem
    constructor <;> intro i
    · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      rw [hx] at hi
      nlinarith [sq_nonneg (x i + 1)]
    · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
      rw [hx] at hi
      nlinarith [sq_nonneg (x i - 1)]
  have hq : ∀ x, qA (rk1 t v) x = t * yv v x := fun x => by
    rw [BstLean.Part56.MomProg.qA_rk1]; rfl
  set Zt := ZA n (rk1 t v) with hZt
  have hZe : Zt = ∫ x, Real.exp (t * yv v x) ∂U := by
    rw [hZt]; unfold ZA; congr 1; funext x; rw [hq]
  have hec : Continuous (fun x => Real.exp (t * yv v x)) := by
    exact Real.continuous_exp.comp (continuous_const.mul (continuous_yv v))
  have hZpos : 0 < Zt := by
    rw [hZe]
    rw [integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) (hint hec)]
    have : Function.support (fun x => Real.exp (t * yv v x)) = Set.univ := by
      ext x; simp [(Real.exp_pos _).ne']
    rw [this, measure_univ]; exact one_pos
  set ρ := fun x => Real.exp (t * yv v x) / Zt with hρ
  have hρc : Continuous ρ := hec.div_const _
  have hρpos : ∀ x, 0 < ρ x := fun x => div_pos (Real.exp_pos _) hZpos
  -- meanY as a ρ-weighted integral
  have hmean : meanY n t v = ∫ x, ρ x * yv v x ∂U := by
    unfold meanY lawRK binghamA
    rw [integral_withDensity_eq_integral_toReal_smul]
    · apply integral_congr_ae
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (by rw [hq]; exact (hρpos x).le), smul_eq_mul, hq]
    · have e : (fun x => Real.exp (qA (rk1 t v) x) / ZA n (rk1 t v)) = ρ := by
        funext x; rw [hq]
      have hm : Measurable (fun x => Real.exp (qA (rk1 t v) x) / ZA n (rk1 t v)) := by
        rw [e]; exact hρc.measurable
      exact hm.ennreal_ofReal
    · exact Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  have hρint : ∫ x, ρ x ∂U = 1 := by
    rw [hρ]; simp only
    rw [integral_div, ← hZe, div_self hZpos.ne']
  -- Gibbs: log Z ≤ t E y
  have hgibbs : Real.log Zt ≤ t * meanY n t v := by
    have hpt : ∀ x, ρ x - 1 ≤ ρ x * (t * yv v x - Real.log Zt) := by
      intro x
      have hl : Real.log (ρ x) = t * yv v x - Real.log Zt := by
        rw [hρ]; simp only
        rw [Real.log_div (Real.exp_pos _).ne' hZpos.ne', Real.log_exp]
      have h1 := Real.one_sub_inv_le_log_of_pos (hρpos x)
      rw [← hl]
      have := mul_le_mul_of_nonneg_left h1 (hρpos x).le
      rw [mul_sub, mul_one, mul_inv_cancel₀ (hρpos x).ne'] at this
      exact this
    have hI : ∫ x, (ρ x - 1) ∂U ≤ ∫ x, ρ x * (t * yv v x - Real.log Zt) ∂U :=
      integral_mono ((hint hρc).sub (integrable_const 1))
        (hint (hρc.mul ((continuous_const.mul (continuous_yv v)).sub continuous_const))) hpt
    rw [integral_sub (hint hρc) (integrable_const 1), hρint] at hI
    simp only [integral_const, probReal_univ, smul_eq_mul, mul_one, sub_self] at hI
    have e : ∀ x, ρ x * (t * yv v x - Real.log Zt) = t * (ρ x * yv v x) - Real.log Zt * ρ x :=
      fun x => by ring
    simp_rw [e] at hI
    have i1 : Integrable (fun x => t * (ρ x * yv v x)) U :=
      (hint (hρc.mul (continuous_yv v))).const_mul _
    have i2 : Integrable (fun x => Real.log Zt * ρ x) U := (hint hρc).const_mul _
    rw [integral_sub i1 i2, integral_const_mul, integral_const_mul, hρint, ← hmean] at hI
    linarith
  -- the tail
  set b := 1 - 1 / (2 * C) with hb
  have hb0 : 0 < b := by
    rw [hb]; have : 1 / (2 * C) < 1 := by rw [div_lt_one (by positivity)]; linarith
    linarith
  have hb1 : b < 1 := by rw [hb]; have : 0 < 1 / (2 * C) := by positivity
                         linarith
  set q := (1 - b) ^ (((n : ℝ) - 1) / 2) / ((n : ℝ) - 1) with hqdef
  have hn1' : (1 : ℝ) ≤ (n : ℝ) - 1 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hqpos : 0 < q := by rw [hqdef]; apply div_pos (Real.rpow_pos_of_pos (by linarith) _); linarith
  set S := {x : Fin n → ℝ | b ≤ yv v x} with hS
  have hSm : MeasurableSet S := measurableSet_le measurable_const (continuous_yv v).measurable
  have hSq : q ≤ U.real S := by
    have := hT n hn b hb0 hb1 v hv
    rw [measureReal_def]
    exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mp this
  have hZlow : Real.exp (t * b) * q ≤ Zt := by
    rw [hZe]
    have hind : ∀ x, S.indicator (fun _ => Real.exp (t * b)) x ≤ Real.exp (t * yv v x) := by
      intro x
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hx ht0.le)
      · rw [Set.indicator_of_notMem hx]; exact (Real.exp_pos _).le
    have hI := integral_mono ((integrable_const _).indicator hSm) (hint hec) hind
    rw [integral_indicator_const _ hSm, smul_eq_mul, mul_comm] at hI
    calc Real.exp (t * b) * q ≤ Real.exp (t * b) * U.real S :=
          mul_le_mul_of_nonneg_left hSq (Real.exp_pos _).le
      _ ≤ _ := by linarith
  -- combine
  have hlog : t * b + Real.log q ≤ Real.log Zt := by
    have := Real.log_le_log (by positivity) hZlow
    rwa [Real.log_mul (Real.exp_pos _).ne' hqpos.ne', Real.log_exp] at this
  have hlq : Real.log q = ((n : ℝ) - 1) / 2 * Real.log (1 - b) - Real.log ((n : ℝ) - 1) := by
    rw [hqdef, Real.log_div (Real.rpow_pos_of_pos (by linarith) _).ne' (by linarith),
      Real.log_rpow (by linarith)]
  have h1b : Real.log (1 - b) = - Real.log (2 * C) := by
    rw [hb, show (1 : ℝ) - (1 - 1 / (2 * C)) = (2 * C)⁻¹ by ring, Real.log_inv]
  have hm : b + Real.log q / t ≤ meanY n t v := by
    rw [add_div' _ _ _ ht0.ne', div_le_iff₀ ht0]; linarith
  have hl2 : 0 < Real.log (2 * C) := Real.log_pos (by linarith)
  have hA1 : ((n : ℝ) - 1) / 2 * Real.log (2 * C) / t ≤ Real.log (2 * C) / (2 * C) := by
    rw [div_le_div_iff₀ ht0 (by positivity)]
    have : ((n : ℝ) - 1) * C ≤ t := by nlinarith
    nlinarith
  have hA2 : Real.log ((n : ℝ) - 1) / t ≤ Real.log n / (C * n) := by
    have hl0 : 0 ≤ Real.log ((n : ℝ) - 1) := Real.log_nonneg hn1'
    have hle : Real.log ((n : ℝ) - 1) ≤ Real.log n := Real.log_le_log (by linarith) (by linarith)
    calc Real.log ((n : ℝ) - 1) / t ≤ Real.log ((n : ℝ) - 1) / (C * n) :=
          div_le_div_of_nonneg_left hl0 (by positivity) ht
      _ ≤ Real.log n / (C * n) := div_le_div_of_nonneg_right hle (by positivity)
  have hfinal : y0 C n ≤ b + Real.log q / t := by
    rw [hlq, h1b]
    unfold y0
    rw [hb]
    have e : (((n : ℝ) - 1) / 2 * -Real.log (2 * C) - Real.log ((n : ℝ) - 1)) / t =
        -(((n : ℝ) - 1) / 2 * Real.log (2 * C) / t) - Real.log ((n : ℝ) - 1) / t := by ring
    rw [e]; linarith
  linarith

private noncomputable def tiltJ (v : Fin n → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∫ x, yv v x ^ k * Real.exp (t * yv v x) ∂uniformSphere n

private lemma tiltJ_deriv (hn : 1 ≤ n) (v : Fin n → ℝ) (hv : UnitV v)
    (k : ℕ) (t : ℝ) : HasDerivAt (tiltJ v k) (tiltJ v (k + 1) t) t := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  let F := fun t x => yv v x ^ k * Real.exp (t * yv v x)
  let F' := fun t x => yv v x ^ (k + 1) * Real.exp (t * yv v x)
  have hcont (r : ℝ) : Continuous (F r) := by
    dsimp [F]; exact ((continuous_yv v).pow k).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_yv v)))
  have hd (x : Fin n → ℝ) (r : ℝ) : HasDerivAt (fun t => F t x) (F' r x) r := by
    convert (((hasDerivAt_id r).mul_const (yv v x)).exp).const_mul (yv v x ^ k) using 1 <;>
      dsimp [F, F']
    rw [pow_succ]; ring
  have hbound : ∀ᵐ x ∂uniformSphere n, ∀ r ∈ Metric.ball t 1,
      ‖F' r x‖ ≤ Real.exp (|t| + 1) := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    intro r hr
    obtain ⟨hy0, hy1⟩ := yv_bound hv hx
    have hp0 := pow_nonneg hy0 (k + 1)
    have hp1 : yv v x ^ (k + 1) ≤ 1 := pow_le_one₀ hy0 hy1
    have hr1 : |r - t| < 1 := by simpa [Real.dist_eq] using hr
    have hrle : r ≤ |t| + 1 := by
      have := le_abs_self t
      have := (abs_lt.mp hr1).2
      linarith
    have hre : r * yv v x ≤ |t| + 1 := by
      by_cases h : 0 ≤ r
      · exact (mul_le_mul_of_nonneg_left hy1 h).trans (by simpa using hrle)
      · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge h) hy0).trans (by positivity)
    dsimp [F']
    rw [abs_of_nonneg (mul_nonneg hp0 (Real.exp_pos _).le)]
    calc
      yv v x ^ (k + 1) * Real.exp (r * yv v x) ≤ Real.exp (r * yv v x) :=
        by nlinarith [Real.exp_pos (r * yv v x)]
      _ ≤ Real.exp (|t| + 1) := Real.exp_le_exp.mpr hre
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds t (by norm_num : (0 : ℝ) < 1))
    (Filter.Eventually.of_forall fun r => (hcont r).aestronglyMeasurable)
    (BstLean.Part56.MomProg.sphere_integrable hn (hcont t))
    (by dsimp [F']; unfold yv; fun_prop) hbound (integrable_const _)
    (Filter.Eventually.of_forall fun x r _ => hd x r)).2

private lemma tiltJ_pos (hn : 1 ≤ n) (v : Fin n → ℝ) (t : ℝ) : 0 < tiltJ v 0 t := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  simp only [tiltJ, pow_zero, one_mul]
  exact integral_exp_pos (BstLean.Part56.MomProg.sphere_integrable hn
    (Real.continuous_exp.comp (continuous_const.mul (continuous_yv v))))

private lemma tilt_integral (hn : 1 ≤ n) (v : Fin n → ℝ) (t : ℝ)
    (f : (Fin n → ℝ) → ℝ) :
    (∫ x, f x ∂lawRK n t v) =
      (∫ x, f x * Real.exp (t * yv v x) ∂uniformSphere n) / tiltJ v 0 t := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  unfold lawRK binghamA
  rw [integral_withDensity_eq_integral_toReal_smul]
  · have hz : 0 < ZA n (rk1 t v) := by
      unfold ZA
      exact integral_exp_pos (BstLean.Part56.MomProg.sphere_integrable hn (by
        unfold qA; fun_prop))
    simp_rw [ENNReal.toReal_ofReal (le_of_lt (div_pos (Real.exp_pos _) hz))]
    simp_rw [smul_eq_mul, BstLean.Part56.MomProg.qA_rk1]
    have he : ZA n (rk1 t v) = tiltJ v 0 t := by
      unfold ZA tiltJ yv
      simp_rw [BstLean.Part56.MomProg.qA_rk1, pow_zero, one_mul]
    rw [he, ← integral_div]
    apply integral_congr_ae
    filter_upwards with x
    unfold yv; ring
  · apply Measurable.ennreal_ofReal
    unfold qA; fun_prop
  · exact Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top

private lemma meanY_eq (hn : 1 ≤ n) (v : Fin n → ℝ) (t : ℝ) :
    meanY n t v = tiltJ v 1 t / tiltJ v 0 t := by
  rw [meanY, tilt_integral hn]
  simp [tiltJ]

private lemma varY_eq (hn : 1 ≤ n) (v : Fin n → ℝ) (t : ℝ) :
    varY n t v = tiltJ v 2 t / tiltJ v 0 t - (tiltJ v 1 t / tiltJ v 0 t) ^ 2 := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  rw [varY, varU, tilt_integral hn]
  change (∫ x, (yv v x - meanY n t v) ^ 2 * Real.exp (t * yv v x)
    ∂uniformSphere n) / tiltJ v 0 t = _
  have hi (k : ℕ) : Integrable (fun x => yv v x ^ k * Real.exp (t * yv v x))
      (uniformSphere n) := BstLean.Part56.MomProg.sphere_integrable hn (by unfold yv; fun_prop)
  have he (x : Fin n → ℝ) :
      (yv v x - meanY n t v) ^ 2 * Real.exp (t * yv v x) =
      yv v x ^ 2 * Real.exp (t * yv v x) -
        (2 * meanY n t v) * (yv v x ^ 1 * Real.exp (t * yv v x)) +
        meanY n t v ^ 2 * (yv v x ^ 0 * Real.exp (t * yv v x)) := by ring
  simp_rw [he]
  rw [integral_add (show Integrable (fun x => yv v x ^ 2 * Real.exp (t * yv v x) -
      (2 * meanY n t v) * (yv v x ^ 1 * Real.exp (t * yv v x))) (uniformSphere n)
      from (hi 2).sub ((hi 1).const_mul (2 * meanY n t v)))
    ((hi 0).const_mul (meanY n t v ^ 2)),
    integral_sub (hi 2) ((hi 1).const_mul (2 * meanY n t v)),
    integral_const_mul, integral_const_mul]
  change (tiltJ v 2 t - 2 * meanY n t v * tiltJ v 1 t +
    meanY n t v ^ 2 * tiltJ v 0 t) / tiltJ v 0 t = _
  rw [meanY_eq hn]
  field_simp [(tiltJ_pos hn v t).ne']
  ring

private lemma meanY_deriv (hn : 1 ≤ n) (v : Fin n → ℝ) (hv : UnitV v) (t : ℝ) :
    HasDerivAt (fun t => meanY n t v) (varY n t v) t := by
  simp_rw [meanY_eq hn]
  have hd := (tiltJ_deriv hn v hv 1 t).div (tiltJ_deriv hn v hv 0 t)
    (tiltJ_pos hn v t).ne'
  convert hd using 1
  rw [varY_eq hn]
  field_simp [(tiltJ_pos hn v t).ne']

private lemma meanY_bounds (hn : 1 ≤ n) (v : Fin n → ℝ) (hv : UnitV v) (t : ℝ) :
    0 ≤ meanY n t v ∧ meanY n t v ≤ 1 := by
  have hμ : SphLaw n (lawRK n t v) := (BstLean.Part50.binghamA_antipodal hn (rk1 t v)).1
  have := hμ.prob
  have hi : Integrable (yv v) (lawRK n t v) := by
    apply Integrable.of_bound (continuous_yv v).aestronglyMeasurable 1
    filter_upwards [hμ.sphere] with x hx
    have hb := yv_bound hv hx
    simpa [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2
  constructor
  · exact integral_nonneg (fun x => by unfold yv; positivity)
  · have h := integral_mono_ae hi (integrable_const (1 : ℝ))
      (hμ.sphere.mono fun x hx => (yv_bound hv hx).2)
    simpa [meanY] using h

private lemma sphere_yv_integral_eq (v w : Fin n → ℝ) (hv : UnitV v) (hw : UnitV w)
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ x, g (yv v x) ∂uniformSphere n) = ∫ x, g (yv w x) ∂uniformSphere n := by
  let V : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 v
  let W : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 w
  have hV : ‖V‖ = 1 := by
    have h : ‖V‖ ^ 2 = 1 := by simpa [V, EuclideanSpace.real_norm_sq_eq, UnitV] using hv
    nlinarith [norm_nonneg V]
  have hW : ‖W‖ = 1 := by
    have h : ‖W‖ ^ 2 = 1 := by simpa [W, EuclideanSpace.real_norm_sq_eq, UnitV] using hw
    nlinarith [norm_nonneg W]
  let R := (ℝ ∙ (V - W))ᗮ.reflection
  have hRV : R V = W := Submodule.reflection_sub (hV.trans hW.symm)
  have hRR (x) : R (R x) = x := R.symm_apply_apply x
  have hcoord (x : Fin n → ℝ) :
      yv w (WithLp.ofLp (R (WithLp.toLp 2 x))) = yv v x := by
    have h := R.inner_map_map V (WithLp.toLp 2 x)
    rw [hRV] at h
    unfold yv
    congr 1
    simpa [V, W, PiLp.inner_apply, mul_comm] using h
  have hm := BstLean.Part56.MomProg.uniformSphere_involution R hRR
  conv_rhs => rw [← hm]
  rw [integral_map (by fun_prop)
    ((show Continuous (fun x : Fin n → ℝ => g (yv w x)) from
      hg.comp (continuous_yv w)).aestronglyMeasurable)]
  simp only [hcoord]

private lemma tiltJ_unit_eq (v w : Fin n → ℝ) (hv : UnitV v) (hw : UnitV w)
    (k : ℕ) (t : ℝ) : tiltJ v k t = tiltJ w k t :=
  sphere_yv_integral_eq v w hv hw (fun y => y ^ k * Real.exp (t * y)) (by fun_prop)

private lemma sphere_complement_marginal (hn : 3 ≤ n) (v : Fin n → ℝ) (hv : UnitV v)
    (g : ℝ → ℝ) (hg : Continuous g) :
    (∫ x, g (1 - yv v x) ∂uniformSphere n) =
      (∫ z in (0 : ℝ)..1, g z * BstLean.Part39.wB n z) /
        ∫ z in (0 : ℝ)..1, BstLean.Part39.wB n z := by
  classical
  let i : Fin n := ⟨0, by omega⟩
  let w : Fin n → ℝ := fun j => if j = i then 1 else 0
  have hw : UnitV w := by simp [UnitV, w]
  rw [sphere_yv_integral_eq v w hv hw (fun y => g (1 - y)) (by fun_prop)]
  rw [← BstLean.Part39.sphere_t_marginal hn g hg]
  apply integral_congr_ae
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  have he := BstLean.Part39.qth_spike_sphere (n := n) 1 x hx
  have hq : BstLean.Part37.qth (BstLean.Part39.spikeθ 1) x = x i ^ 2 := by
    simp only [BstLean.Part37.qth, BstLean.Part39.spikeθ, ite_mul, one_mul, zero_mul]
    rw [Finset.sum_eq_single i]
    · simp [i]
    · intro j _ hji
      have hj : j.val ≠ 0 := fun h => hji (Fin.ext h)
      simp [hj]
    · simp
  rw [hq, one_mul] at he
  have hy : yv w x = x i ^ 2 := by simp [yv, w]
  rw [hy]
  congr 1
  linarith

private lemma wB_mass_le_two (hn : 3 ≤ n) :
    (∫ z in (0 : ℝ)..1, BstLean.Part39.wB n z) ≤ 2 := by
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hβ : 0 ≤ ((n : ℝ) - 3) / 2 := by linarith
  have hi : IntervalIntegrable (fun z : ℝ => (1 - z) ^ (-(1 / 2 : ℝ))) volume 0 1 := by
    simpa using ((intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
      (by norm_num : -1 < -(1 / 2 : ℝ))).comp_sub_left 1).symm
  have hm := intervalIntegral.integral_mono_on (a := (0 : ℝ)) (b := 1)
    (by norm_num) (BstLean.Part39.wB_integral_pos hn).1 hi (fun z hz => by
      unfold BstLean.Part39.wB
      have hpow : z ^ (((n : ℝ) - 3) / 2) ≤ 1 := Real.rpow_le_one hz.1 hz.2 hβ
      exact (mul_le_mul_of_nonneg_right hpow
        (Real.rpow_nonneg (by linarith [hz.2]) _)).trans_eq (one_mul _))
  calc
    _ ≤ ∫ z in (0 : ℝ)..1, (1 - z) ^ (-(1 / 2 : ℝ)) := hm
    _ = 2 := by
      rw [intervalIntegral.integral_comp_sub_left (fun z : ℝ => z ^ (-(1/2 : ℝ))) 1]
      norm_num [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1/2 : ℝ)))]

private lemma tail_lower_lt (hn : 3 ≤ n) (b : ℝ) (hb0 : 0 < b) (_hb1 : b < 1)
    (v : Fin n → ℝ) (hv : UnitV v) (r : ℝ) (hr0 : 0 < r) (hr : r < 1 - b) :
    r ^ (((n : ℝ) - 1) / 2) / ((n : ℝ) - 1) ≤
      (uniformSphere n).real {x | b ≤ yv v x} := by
  have hn1 : 1 ≤ n := by omega
  have := BstLean.Part29.uniformSphere_isProbability n hn1
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  let β : ℝ := ((n : ℝ) - 3) / 2
  have hβ : 0 ≤ β := by dsimp [β]; linarith
  let a : ℝ := 1 - b
  have ha : 0 < a := by dsimp [a]; linarith
  have hra : 0 < a - r := by dsimp [a]; linarith
  let φ : ℝ → ℝ := fun z => min 1 (max 0 ((a - z) / (a - r)))
  have hφ : Continuous φ := by dsimp [φ]; fun_prop
  have hφ0 (z : ℝ) : 0 ≤ φ z := le_min (by norm_num) (le_max_left _ _)
  have hφ1 (z : ℝ) : φ z ≤ 1 := min_le_left _ _
  have hφeq (z : ℝ) (hz : z ≤ r) : φ z = 1 := by
    apply min_eq_left
    apply le_trans _ (le_max_right _ _)
    rw [le_div_iff₀ hra]
    linarith
  have hφzero (z : ℝ) (hz : a ≤ z) : φ z = 0 := by
    have hd : (a - z) / (a - r) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hra.le
    simp [φ, max_eq_left hd]
  have hw := (BstLean.Part39.wB_integral_pos hn).1
  have hφw := hw.continuousOn_mul hφ.continuousOn
  have hr1 : r ≤ 1 := by dsimp [a] at hra; linarith
  have hφwr : IntervalIntegrable (fun z => φ z * BstLean.Part39.wB n z) volume 0 r :=
    hφw.mono_set (by
      rw [Set.uIcc_of_le hr0.le, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Set.Icc_subset_Icc le_rfl hr1)
  have hφwr1 : IntervalIntegrable (fun z => φ z * BstLean.Part39.wB n z) volume r 1 :=
    hφw.mono_set (by
      rw [Set.uIcc_of_le hr1, Set.uIcc_of_le (by norm_num : (0:ℝ) ≤ 1)]
      exact Set.Icc_subset_Icc hr0.le le_rfl)
  have hp : IntervalIntegrable (fun z : ℝ => z ^ β) volume 0 r :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hl : (∫ z in (0 : ℝ)..r, z ^ β) ≤
      ∫ z in (0 : ℝ)..r, φ z * BstLean.Part39.wB n z := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hr0.le hp hφwr
    intro z hz
    rw [hφeq z hz.2.le, one_mul]
    unfold BstLean.Part39.wB
    have hz1 : 0 < 1 - z := by linarith [hz.2]
    have hpow : 1 ≤ (1 - z) ^ (-(1 / 2 : ℝ)) :=
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos hz1 (by linarith [hz.1]) (by norm_num)
    simpa [β] using mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hz.1.le β)
  have hnneg : 0 ≤ ∫ z in r..(1 : ℝ), φ z * BstLean.Part39.wB n z := by
    apply intervalIntegral.integral_nonneg hr1
    intro z hz
    apply mul_nonneg (hφ0 z)
    unfold BstLean.Part39.wB
    exact mul_nonneg (Real.rpow_nonneg (by linarith [hz.1]) _)
      (Real.rpow_nonneg (by linarith [hz.2]) _)
  have hlow : r ^ (β + 1) / (β + 1) ≤ ∫ z in (0 : ℝ)..1, φ z * BstLean.Part39.wB n z := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hφwr hφwr1]
    have hi : (∫ z in (0 : ℝ)..r, z ^ β) = r ^ (β + 1) / (β + 1) := by
      rw [integral_rpow (Or.inl (by linarith : -1 < β)),
        Real.zero_rpow (by linarith : β + 1 ≠ 0), sub_zero]
    rw [hi] at hl
    linarith
  have hexp : (∫ x, φ (1 - yv v x) ∂uniformSphere n) ≤
      (uniformSphere n).real {x | b ≤ yv v x} := by
    let S := {x : Fin n → ℝ | b ≤ yv v x}
    have hS : MeasurableSet S := measurableSet_le measurable_const (continuous_yv v).measurable
    have hi : Integrable (fun x => φ (1 - yv v x)) (uniformSphere n) :=
      BstLean.Part56.MomProg.sphere_integrable hn1
        (hφ.comp (continuous_const.sub (continuous_yv v)))
    have hm := integral_mono hi ((integrable_const (1 : ℝ)).indicator hS) (fun x => by
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]; exact hφ1 _
      · rw [Set.indicator_of_notMem hx, hφzero]
        dsimp [S] at hx
        dsimp [a]; linarith)
    simpa [integral_indicator_const _ hS, S] using hm
  have hZ := (BstLean.Part39.wB_integral_pos hn).2
  have hZ2 := wB_mass_le_two hn
  rw [sphere_complement_marginal hn v hv φ hφ] at hexp
  calc
    r ^ (((n : ℝ) - 1) / 2) / ((n : ℝ) - 1) = (r ^ (β + 1) / (β + 1)) / 2 := by
      have he : β + 1 = ((n : ℝ) - 1) / 2 := by dsimp [β]; ring
      rw [he]
      field_simp [show (n : ℝ) - 1 ≠ 0 by linarith]
    _ ≤ (r ^ (β + 1) / (β + 1)) /
        (∫ z in (0 : ℝ)..1, BstLean.Part39.wB n z) :=
      div_le_div_of_nonneg_left (by positivity) hZ hZ2
    _ ≤ (∫ z in (0 : ℝ)..1, φ z * BstLean.Part39.wB n z) /
        (∫ z in (0 : ℝ)..1, BstLean.Part39.wB n z) := div_le_div_of_nonneg_right hlow hZ.le
    _ ≤ _ := hexp

/-- **Tail of `y` under the uniform law**. Route: the density of `s = v·x` under `U` is
`c_n (1 − s²)^{(n−3)/2}` with `c_n ≥ 1/2`; substitute `z = 1 − s²` (`ds ≥ dz/2`). -/
theorem lemmaTail58 : LemmaTail58 := by
  intro n hn b hb0 hb1 v hv
  have hn1 : 1 ≤ n := by omega
  have := BstLean.Part29.uniformSphere_isProbability n hn1
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have ha : 0 < 1 - b := by linarith
  have hc : Continuous (fun r : ℝ => r ^ (((n : ℝ) - 1) / 2) / ((n : ℝ) - 1)) :=
    (Real.continuous_rpow_const (by linarith)).div_const _
  have hbound : (1 - b) ^ (((n : ℝ) - 1) / 2) / ((n : ℝ) - 1) ≤
      (uniformSphere n).real {x | b ≤ yv v x} := by
    apply le_of_tendsto (hc.continuousAt.tendsto.mono_left
      (show 𝓝[Set.Iio (1 - b)] (1 - b) ≤ 𝓝 (1 - b) from nhdsWithin_le_nhds))
    filter_upwards [show ∀ᶠ r in 𝓝[Set.Iio (1 - b)] (1 - b), r < 1 - b from self_mem_nhdsWithin,
      (show ∀ᶠ r in 𝓝 (1 - b), 0 < r from Ioi_mem_nhds ha).filter_mono nhdsWithin_le_nhds]
      with r hr hr0
    exact tail_lower_lt hn b hb0 hb1 v hv r hr0 hr
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).mpr hbound

/-- **Lemma Y1**. -/
theorem lemmaY1_58 : LemmaY1_58 := lemmaY1_58_of lemmaTail58

/-- **Lemma Y2 (b)**. -/
theorem lemmaY2_58 : LemmaY2_58 := by
  intro n hn C' C _hC' hC
  have hn1 : 1 ≤ n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  let i : Fin n := ⟨0, by omega⟩
  let v : Fin n → ℝ := fun j => if j = i then 1 else 0
  have hv : UnitV v := by
    classical
    simp [UnitV, v]
  have hlt : C' * n < C * n := mul_lt_mul_of_pos_right hC hn0
  have hd := meanY_deriv hn1 v hv
  obtain ⟨t, ht, he⟩ := exists_hasDerivAt_eq_slope (fun r => meanY n r v)
    (fun r => varY n r v) hlt
    (continuousOn_of_forall_continuousAt fun r _ => (hd r).continuousAt)
    (fun r _ => hd r)
  refine ⟨t, ht.1.le, ht.2.le, ?_⟩
  intro w hw
  have hvw : varY n t w = varY n t v := by
    rw [varY_eq hn1, varY_eq hn1]
    simp_rw [tiltJ_unit_eq w v hw hv]
  rw [hvw, he]
  have hb := meanY_bounds hn1 v hv (C * n)
  have ha := meanY_bounds hn1 v hv (C' * n)
  have hden : 0 < C * n - C' * n := sub_pos.mpr hlt
  calc
    (meanY n (C * n) v - meanY n (C' * n) v) / (C * n - C' * n) ≤
        1 / (C * n - C' * n) := div_le_div_of_nonneg_right (by linarith) hden.le
    _ = 1 / ((C - C') * n) := by ring

end BstLean.Part58
