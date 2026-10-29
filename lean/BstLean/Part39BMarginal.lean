import BstLean.Part39BDefs
import BstLean.Part37Density
import BstLean.Part33Moments
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Topology.ContinuousMap.Weierstrass

/-!
# Part 39 Theorem B, wave 1: the law of `t = 1 − x₁²` under the uniform sphere

Specification: `delegations/answers/p39b-spec-opus.md`. Paper: Lemma BR, §1 of
`delegations/answers/omBR-opus-prover.md` (the `t`-density `p(t) ∝ t^β (1−t)^{−1/2} e^{−lam t}`).
Under `uniformSphere n`, `t` has density `∝ wB n t = t^{(n−3)/2} (1 − t)^{−1/2}` on `(0, 1)`.
Suggested route: Part 29's polar decomposition against the Gaussian weight
(`Part29Sphere.polar_homogeneous`), with `x = (s, √(1−s²) u)`; or the coordinate-moment formula
`E_U t^m` (Part 39's `Part39Series`) and a Weierstrass approximation of `φ` on `[0, 1]`.

Provers: replace each `sorry` by a proof. Do not edit `Part39BDefs.lean` or any statement in this
file, and do not use `native_decide` anywhere. Add no `axiom`.
-/

namespace BstLean.Part39

open MeasureTheory
open BstLean.Part29 (uniformSphere)
open BstLean.Part37 (qth bingham)

variable {n : ℕ}

/-- `∫₀¹ wB > 0`, and `wB` is integrable on `[0, 1]`. -/
theorem wB_integral_pos (hn : 3 ≤ n) :
    IntervalIntegrable (wB n) MeasureTheory.volume 0 1 ∧ 0 < ∫ t in (0 : ℝ)..1, wB n t := by
  have ha : 0 ≤ ((n : ℝ) - 3) / 2 := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hi : IntervalIntegrable (fun t : ℝ => (1 - t) ^ (-(1 / 2 : ℝ))) volume 0 1 := by
    simpa using ((intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := 1)
      (by norm_num : -1 < -(1 / 2 : ℝ))).comp_sub_left 1).symm
  have hw : IntervalIntegrable (wB n) volume 0 1 :=
    hi.continuousOn_mul (Real.continuous_rpow_const ha).continuousOn
  refine ⟨hw, intervalIntegral.intervalIntegral_pos_of_pos_on hw ?_ (by norm_num)⟩
  intro t ht
  exact mul_pos (Real.rpow_pos_of_pos ht.1 _) (Real.rpow_pos_of_pos (by linarith [ht.2]) _)

private lemma coord_moment (hn : 1 ≤ n) (i : Fin n) (m : ℕ) :
    (∫ x, (x i ^ 2) ^ m ∂uniformSphere n) = bU n m := by
  classical
  have hp : BstLean.Part29.gaussMom (2*m) =
      ∏ r ∈ Finset.range m, (2*(r:ℝ)+1) := by
    induction m with
    | zero => simp [BstLean.Part29.gaussMom]
    | succ m ih =>
      have he : Even (2*(m+1)) := ⟨m+1, by omega⟩
      have he' : Even (2*m) := ⟨m, by omega⟩
      simp only [BstLean.Part29.gaussMom, ite_eq_left he'] at ih
      rw [BstLean.Part29.gaussMom, ite_eq_left he,
        show 2*(m+1)-1 = 2*m+1 by omega, Nat.doubleFactorial_add_one]
      push_cast
      rw [Finset.prod_range_succ, ← ih]
      ring
  have hf : (∏ j : Fin n, BstLean.Part29.gaussMom
      (Finset.univ.filter fun _ : Fin (2*m) => i = j).card) =
      BstLean.Part29.gaussMom (2*m) := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro j hj hji
      simp [Ne.symm hji, BstLean.Part29.gaussMom]
    · simp
  have h := (BstLean.Part33.uniformSphere_prod n (2*m) hn).mom (2*m) le_rfl
    (fun _ => i)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Nat.mul_div_cancel_left _ (by omega : 0 < 2)] at h
  rw [hf, hp] at h
  simp_rw [← pow_mul]
  rw [h, bU, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro r hr
  have hd : (n : ℝ) + 2 * r ≠ 0 := by positivity
  have hd' : (n : ℝ)/2 + r ≠ 0 := by positivity
  apply (div_eq_div_iff hd hd').2
  ring

private lemma cont_integ (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f (uniformSphere n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

private lemma t_identity (hn : 1 ≤ n) (x : Fin n → ℝ)
    (hx : ∑ i, x i ^ 2 = 1) : tperp x = 1 - x ⟨0, by omega⟩ ^ 2 := by
  classical
  have he : tperp x + x ⟨0, by omega⟩ ^ 2 = ∑ i, x i ^ 2 := by
    have hs : (∑ i : Fin n, if i.val = 0 then x i ^ 2 else 0) =
        x ⟨0, by omega⟩ ^ 2 := by
      rw [Finset.sum_eq_single ⟨0, by omega⟩]
      · simp
      · intro j hj hji
        have hj0 : j.val ≠ 0 := fun h => hji (Fin.ext h)
        simp [hj0]
      · simp
    rw [← hs, tperp, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  rw [hx] at he
  linarith

private lemma real_beta (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t in (0 : ℝ)..1, t ^ (a - 1) * (1 - t) ^ (b - 1)) =
      Real.Gamma a * Real.Gamma b / Real.Gamma (a + b) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have he : (∫ t in (0 : ℝ)..1,
      ((t ^ (a - 1) * (1 - t) ^ (b - 1) : ℝ) : ℂ)) =
      Complex.betaIntegral (a : ℂ) (b : ℂ) := by
    unfold Complex.betaIntegral
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at ht
    rw [Complex.ofReal_mul, Complex.ofReal_cpow ht.1,
      Complex.ofReal_cpow (by linarith [ht.2])]
    push_cast
    rfl
  rw [he, Complex.betaIntegral_eq_Gamma_mul_div _ _ (by simpa using ha)
    (by simpa using hb)]
  simp only [← Complex.ofReal_add, Complex.Gamma_ofReal, Complex.ofReal_div,
    Complex.ofReal_mul]

private lemma beta_y_moment (hn : 3 ≤ n) (m : ℕ) :
    (∫ t in (0 : ℝ)..1, (1 - t) ^ m * wB n t) =
      (∫ t in (0 : ℝ)..1, wB n t) * bU n m := by
  let a : ℝ := ((n : ℝ) - 1) / 2
  have ha : 0 < a := by
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    dsimp [a]
    linarith
  have he (k : ℕ) : (∫ t in (0 : ℝ)..1, (1 - t) ^ k * wB n t) =
      Real.Gamma a * Real.Gamma ((k : ℝ) + 1 / 2) /
        Real.Gamma (a + ((k : ℝ) + 1 / 2)) := by
    rw [← real_beta a ((k : ℝ) + 1 / 2) ha (by positivity)]
    apply intervalIntegral.integral_congr_ae
    rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ 1 from by
      rw [ae_iff]
      simp] with t ht1
    intro ht
    dsimp [wB]
    have ht0 : 0 < 1 - t := by
      have : t < 1 := lt_of_le_of_ne ht.2 ht1
      linarith
    rw [show ((n : ℝ) - 3) / 2 = a - 1 by dsimp [a]; ring]
    rw [mul_left_comm, ← Real.rpow_natCast (1 - t) k,
      ← Real.rpow_add ht0]
    congr 2
    ring
  have hstep (k : ℕ) :
      (∫ t in (0 : ℝ)..1, (1 - t) ^ (k + 1) * wB n t) =
      ((k : ℝ) + 1 / 2) / ((n : ℝ) / 2 + k) *
        (∫ t in (0 : ℝ)..1, (1 - t) ^ k * wB n t) := by
    rw [he (k + 1), he k]
    push_cast
    rw [show (k : ℝ) + 1 + 1 / 2 = ((k : ℝ) + 1 / 2) + 1 by ring,
      show a + (((k : ℝ) + 1 / 2) + 1) = (a + ((k : ℝ) + 1 / 2)) + 1 by ring,
      Real.Gamma_add_one (by positivity : (k : ℝ) + 1 / 2 ≠ 0),
      Real.Gamma_add_one (ne_of_gt (by positivity : 0 < a + ((k : ℝ) + 1 / 2)))]
    have hd : a + ((k : ℝ) + 1 / 2) = (n : ℝ) / 2 + k := by dsimp [a]; ring
    rw [hd]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  induction m with
  | zero => simp [bU]
  | succ m ih =>
    rw [hstep, ih]
    simp only [bU, Finset.prod_range_succ]
    ring

private lemma continuous_tperp : Continuous (tperp : (Fin n → ℝ) → ℝ) := by
  classical
  unfold tperp
  apply continuous_finsetSum
  intro i hi
  split_ifs <;> fun_prop

private lemma polynomial_y (hn : 3 ≤ n) (p : Polynomial ℝ) :
    (∫ x, p.eval (1 - tperp x) ∂uniformSphere n) *
      (∫ t in (0 : ℝ)..1, wB n t) =
      ∫ t in (0 : ℝ)..1, p.eval (1 - t) * wB n t := by
  have hn1 : 1 ≤ n := by omega
  have hw := (wB_integral_pos hn).1
  have hc : Continuous (fun x : Fin n → ℝ => 1 - tperp x) :=
    continuous_const.sub continuous_tperp
  have hs (q : Polynomial ℝ) : Integrable (fun x => q.eval (1 - tperp x))
      (uniformSphere n) :=
    cont_integ hn1 (by simpa only [Function.comp_def] using q.continuous.comp hc)
  have hp (q : Polynomial ℝ) : Continuous (fun t : ℝ => q.eval (1 - t)) := by
    fun_prop
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp only [Polynomial.eval_add, add_mul]
    rw [integral_add (hs p) (hs q),
      intervalIntegral.integral_add (hw.continuousOn_mul (hp p).continuousOn)
        (hw.continuousOn_mul (hp q).continuousOn), add_mul, ihp, ihq]
  | monomial k c =>
    simp only [Polynomial.eval_monomial]
    rw [integral_const_mul]
    have hy : (∫ x, (1 - tperp x) ^ k ∂uniformSphere n) = bU n k := by
      calc
        _ = ∫ x, (x ⟨0, by omega⟩ ^ 2) ^ k ∂uniformSphere n := by
          apply integral_congr_ae
          filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
          rw [t_identity hn1 x hx]
          congr 1
          ring
        _ = _ := coord_moment hn1 _ k
    rw [hy]
    simp_rw [mul_assoc]
    rw [intervalIntegral.integral_const_mul, beta_y_moment hn]
    ring

/-- **The marginal of `t`.** For continuous `φ`,
  `E_U φ(t) = ∫₀¹ φ(t) wB(t) dt / ∫₀¹ wB(t) dt`. -/
theorem sphere_t_marginal (hn : 3 ≤ n) (φ : ℝ → ℝ) (hφ : Continuous φ) :
    ∫ x, φ (tperp x) ∂uniformSphere n =
      (∫ t in (0 : ℝ)..1, φ t * wB n t) / ∫ t in (0 : ℝ)..1, wB n t := by
  classical
  have hn1 : 1 ≤ n := by omega
  have := BstLean.Part29.uniformSphere_isProbability n hn1
  obtain ⟨hw, hz⟩ := wB_integral_pos hn
  let Z : ℝ := ∫ t in (0 : ℝ)..1, wB n t
  have hz' : 0 < Z := hz
  have hφs : Integrable (fun x => φ (tperp x)) (uniformSphere n) :=
    cont_integ hn1 (hφ.comp continuous_tperp)
  have hφw := hw.continuousOn_mul hφ.continuousOn
  have ht : ∀ᵐ x ∂uniformSphere n, tperp x ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
    constructor
    · unfold tperp
      apply Finset.sum_nonneg
      intro i hi
      split_ifs <;> positivity
    · rw [t_identity hn1 x hx]
      linarith [sq_nonneg (x ⟨0, by omega⟩)]
  apply (eq_div_iff hz.ne').2
  apply eq_of_forall_dist_le
  intro ε hε
  let δ : ℝ := ε / (2 * Z)
  have hδ : 0 < δ := div_pos hε (by positivity)
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1
    (fun y : ℝ => φ (1 - y)) (by fun_prop) δ hδ
  let q : ℝ → ℝ := fun t => p.eval (1 - t)
  have hq : Continuous q := by dsimp [q]; fun_prop
  have hnear (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : |φ t - q t| ≤ δ := by
    have h := hp (1 - t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
    rw [show 1 - (1 - t) = t by ring, abs_sub_comm] at h
    exact h.le
  have hqs : Integrable (fun x => q (tperp x)) (uniformSphere n) :=
    cont_integ hn1 (hq.comp continuous_tperp)
  have hqw := hw.continuousOn_mul hq.continuousOn
  have hpoly : (∫ x, q (tperp x) ∂uniformSphere n) * Z =
      ∫ t in (0 : ℝ)..1, q t * wB n t := polynomial_y hn p
  have hs : |(∫ x, φ (tperp x) ∂uniformSphere n) -
      (∫ x, q (tperp x) ∂uniformSphere n)| ≤ δ := by
    rw [← integral_sub hφs hqs]
    have h := MeasureTheory.norm_integral_le_of_norm_le_const
      (μ := uniformSphere n) (f := fun x => φ (tperp x) - q (tperp x))
      (ht.mono fun x hx => by simpa only [Real.norm_eq_abs] using hnear _ hx)
    simpa [Real.norm_eq_abs, measureReal_def] using h
  have hb : |(∫ t in (0 : ℝ)..1, φ t * wB n t) -
      (∫ t in (0 : ℝ)..1, q t * wB n t)| ≤ δ * Z := by
    rw [← intervalIntegral.integral_sub hφw hqw]
    have h := intervalIntegral.norm_integral_le_of_norm_le (a := (0 : ℝ)) (b := 1)
      (f := fun t => φ t * wB n t - q t * wB n t) (g := fun t => δ * wB n t)
      (by norm_num) (Filter.Eventually.of_forall fun t ht => by
        have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
        have hw0 : 0 ≤ wB n t := mul_nonneg
          (Real.rpow_nonneg ht'.1 _) (Real.rpow_nonneg (by linarith [ht'.2]) _)
        rw [← sub_mul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0]
        exact mul_le_mul_of_nonneg_right (hnear t ht') hw0) (hw.const_mul δ)
    simpa only [Real.norm_eq_abs, intervalIntegral.integral_const_mul] using h
  rw [Real.dist_eq]
  calc
    _ = |((∫ x, φ (tperp x) ∂uniformSphere n) -
        (∫ x, q (tperp x) ∂uniformSphere n)) * Z +
        ((∫ t in (0 : ℝ)..1, q t * wB n t) -
        (∫ t in (0 : ℝ)..1, φ t * wB n t))| := by rw [← hpoly]; congr 1; ring
    _ ≤ |((∫ x, φ (tperp x) ∂uniformSphere n) -
        (∫ x, q (tperp x) ∂uniformSphere n)) * Z| +
        |(∫ t in (0 : ℝ)..1, q t * wB n t) -
        (∫ t in (0 : ℝ)..1, φ t * wB n t)| := abs_add_le _ _
    _ ≤ δ * Z + δ * Z := by
      rw [abs_mul, abs_of_pos hz', abs_sub_comm
        (∫ t in (0 : ℝ)..1, q t * wB n t)]
      exact add_le_add (mul_le_mul_of_nonneg_right hs hz'.le) hb
    _ = ε := by dsimp [δ]; field_simp [ne_of_gt hz']; ring

/-- On the sphere, `q_θ(x) = lam (1 − t)` at `θ = lam e₁`. -/
theorem qth_spike_sphere (lam : ℝ) (x : Fin n → ℝ) (hx : ∑ i, x i ^ 2 = 1) :
    qth (spikeθ lam) x = lam * (1 - tperp x) := by
  classical
  have he : (∑ i : Fin n, (if i.val = 0 then lam else 0) * x i ^ 2) =
      lam * (∑ i : Fin n, if i.val = 0 then x i ^ 2 else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  have ht : (∑ i : Fin n, if i.val = 0 then x i ^ 2 else 0) + tperp x = 1 := by
    rw [tperp, ← Finset.sum_add_distrib, ← hx]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  change (∑ i : Fin n, (if i.val = 0 then lam else 0) * x i ^ 2) = _
  rw [he]
  congr 1
  linarith

end BstLean.Part39

#print axioms BstLean.Part39.sphere_t_marginal
#print axioms BstLean.Part39.wB_integral_pos
#print axioms BstLean.Part39.qth_spike_sphere
