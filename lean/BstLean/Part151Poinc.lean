import BstLean.Part107Poincare
import BstLean.Part148GC

/-!
# Part 151: the Gaussian Poincaré inequality with the constant `1` for a Lipschitz function

Role: the standard fact (G1) of `proofs/option-n/theorem5-03-inputs.tex` ("`Var f(X) ≤ E|∇f(X)|²`
for a Lipschitz `f`, gradient almost everywhere"). Part 107 has the inequality for a `C¹`
function (`poincare107_C1`). Here `f` is Lipschitz for the Euclidean norm (`EuLip f L` of
Part 148); the gradient is the Fréchet derivative `fderiv`, which exists almost everywhere
(Rademacher) and is `0` by convention where `f` is not differentiable.

Route: the small-angle rotation of Part 107 (`E (f(X_a) − f(X))² ≥ 2(1 − cos a)·Var f` by the
Gebelein inequality of Part 105, valid for every `f` in `L²`), with a new energy bound
`E (f(X_a) − f(X))² ≤ a²·E|∇f|²` for a Lipschitz `f` (`energy_lip`): the fundamental theorem of
calculus for the absolutely continuous function `θ ↦ f(X cos θ + Z sin θ)`, the Cauchy–Schwarz
inequality in `θ`, and, for each fixed `θ`, differentiability of `f` at the rotated point for
almost every `(X, Z)`.

* `gradSq f x = Σ_i (∂_i f(x))²`.
* **`poincare_lip`**: `Var f ≤ E gradSq f`.
* `poincare_lip_le`: `Var f ≤ E Γ` if `gradSq f ≤ Γ` almost everywhere; `poincare_lip_L`:
  `Var f ≤ L²`.
Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part151

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part48 (rotX rotY rot_preserving)
open BstLean.Part105
open BstLean.Part107
open BstLean.Part148 (EuLip en phiP phiP_lipschitz phiP_deriv_bound ii_of_bdd)

/-- The Cauchy–Schwarz inequality on `[0, a]` for an integrable function with integrable
square. -/
lemma cs_interval_ii (D : ℝ → ℝ) {a : ℝ} (ha : 0 ≤ a) (hD : IntervalIntegrable D volume 0 a)
    (hD2 : IntervalIntegrable (fun θ => D θ ^ 2) volume 0 a) :
    (∫ θ in (0 : ℝ)..a, D θ) ^ 2 ≤ a * ∫ θ in (0 : ℝ)..a, D θ ^ 2 := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0; simp
  set I := ∫ θ in (0 : ℝ)..a, D θ with hI
  set c := I / a with hc
  have h1 : 0 ≤ ∫ θ in (0 : ℝ)..a, (D θ - c) ^ 2 :=
    intervalIntegral.integral_nonneg ha (fun u _ => sq_nonneg _)
  have h2 : ∫ θ in (0 : ℝ)..a, (D θ - c) ^ 2 =
      (∫ θ in (0 : ℝ)..a, D θ ^ 2) - 2 * c * I + c ^ 2 * a := by
    have e : ∀ θ, (D θ - c) ^ 2 = D θ ^ 2 - 2 * c * D θ + c ^ 2 := fun θ => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
    · simp only [sub_zero, smul_eq_mul]; rw [← hI]; ring
    · exact hD2
    · exact hD.const_mul _
    · exact hD2.sub (hD.const_mul _)
    · exact intervalIntegrable_const
  rw [h2] at h1
  have h3 : c * a = I := by rw [hc]; field_simp
  have h4 : c ^ 2 * a = c * I := by rw [← h3]; ring
  have h5 : I ^ 2 = a * (c * I) := by rw [← h3]; ring
  rw [h5]
  have : c * I ≤ ∫ θ in (0 : ℝ)..a, D θ ^ 2 := by linarith
  exact mul_le_mul_of_nonneg_left this ha

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- `|∇f(x)|² = Σ_i (∂_i f(x))²` (`0` where `f` is not differentiable). -/
noncomputable def gradSq (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2

lemma gradSq_nonneg (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : 0 ≤ gradSq f x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma measurable_gradSq (f : (ι → ℝ) → ℝ) : Measurable (gradSq f) :=
  Finset.measurable_sum _ fun i _ =>
    (measurable_fderiv_apply_const ℝ f (Pi.single i 1)).pow_const 2

variable {f : (ι → ℝ) → ℝ} {L : ℝ}

/-- `|∇f|² ≤ L²` everywhere, for a Lipschitz `f`. -/
lemma gradSq_le (hL0 : 0 ≤ L) (hL : EuLip f L) (x : ι → ℝ) : gradSq f x ≤ L ^ 2 := by
  by_cases hx : DifferentiableAt ℝ f x
  · obtain ⟨g, hlin, hgg⟩ := hL.grad hL0 hx
    refine le_trans (le_of_eq ?_) hgg
    unfold gradSq
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hlin (Pi.single i 1)]
    simp [dotProduct, Pi.single_apply, sq]
  · unfold gradSq
    rw [fderiv_zero_of_not_differentiableAt hx]
    have e : ∑ i : ι, ((0 : (ι → ℝ) →L[ℝ] ℝ) (Pi.single i 1)) ^ 2 = 0 := by simp
    rw [e]
    positivity

lemma gradSq_integrable (hL0 : 0 ≤ L) (hL : EuLip f L) :
    Integrable (gradSq f) (stdGauss ι) := by
  refine Integrable.of_bound (measurable_gradSq f).aestronglyMeasurable (L ^ 2)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (gradSq_nonneg f x)]
  exact gradSq_le hL0 hL x

omit [DecidableEq ι] in
/-- A Lipschitz function is square-integrable under the standard Gaussian distribution. -/
lemma lip_memLp (hL0 : 0 ≤ L) (hL : EuLip f L) : MemLp f 2 (stdGauss ι) := by
  have hc := hL.continuous hL0
  rw [memLp_two_iff_integrable_sq hc.measurable.aestronglyMeasurable]
  have hdom : Integrable (fun x : ι → ℝ => 2 * f 0 ^ 2 + 2 * (L ^ 2 * ∑ i, x i * x i))
      (stdGauss ι) :=
    (integrable_const _).add (((integrable_finsetSum _ fun i _ =>
      gauss_pair_integrable107 i i).const_mul _).const_mul _)
  refine hdom.mono' (hc.measurable.pow_const 2).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h := hL x 0
  simp only [Pi.zero_apply, sub_zero] at h
  have hs : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : (f x - f 0) ^ 2 ≤ L ^ 2 * ∑ i, x i ^ 2 := by
    have h3 : (f x - f 0) ^ 2 ≤ (L * √(∑ i, x i ^ 2)) ^ 2 :=
      sq_le_sq' (by linarith [(abs_le.mp h).1]) (abs_le.mp h).2
    rwa [mul_pow, Real.sq_sqrt hs] at h3
  have e : ∑ i, x i * x i = ∑ i, x i ^ 2 := Finset.sum_congr rfl fun i _ => (sq _).symm
  rw [e]
  nlinarith [sq_nonneg (f x - 2 * f 0)]

/-! ## The energy bound along the rotation path -/

/-- The function along the path `θ ↦ cos θ·x + sin θ·z`. -/
noncomputable def psiP (f : (ι → ℝ) → ℝ) (p : (ι → ℝ) × (ι → ℝ)) (θ : ℝ) : ℝ :=
  f (rotX θ p.1 p.2)

omit [DecidableEq ι] [Fintype ι] in
lemma psiP_eq (f : (ι → ℝ) → ℝ) (p : (ι → ℝ) × (ι → ℝ)) : psiP f p = phiP f (p.2, p.1) := by
  funext θ
  unfold psiP phiP
  rw [rotX_eq107, add_comm]

omit [DecidableEq ι] in
lemma continuous_psiP (hL0 : 0 ≤ L) (hL : EuLip f L) :
    Continuous (Function.uncurry (psiP f)) := by
  have hc := hL.continuous hL0
  unfold psiP
  refine hc.comp ?_
  refine continuous_pi fun i => ?_
  simp only [rotX]
  fun_prop

/-- **The energy bound for a Lipschitz function**: `E (f(X_a) − f(X))² ≤ a²·E|∇f|²`. -/
theorem energy_lip (hL0 : 0 ≤ L) (hL : EuLip f L) {a : ℝ} (ha : 0 ≤ a) :
    ∫⁻ p, ENNReal.ofReal ((f (rotX a p.1 p.2) - f p.1) ^ 2) ∂(stdGauss ι).prod (stdGauss ι) ≤
      ENNReal.ofReal (a ^ 2 * ∫ x, gradSq f x ∂stdGauss ι) := by
  have hΓ := gradSq_integrable hL0 hL
  obtain ⟨hI, hK⟩ := gradPhi_lintegral_le107 f Set.univ (gradSq f) hΓ (fun _ _ => le_rfl)
    (Eventually.of_forall fun _ => Set.mem_univ _)
  have hΦ := measurable_gradPhi107 f
  have hdiff := hL.ae_diff hL0
  have mD : Measurable (fun w : ((ι → ℝ) × (ι → ℝ)) × ℝ => deriv (psiP f w.1) w.2) :=
    measurable_deriv_with_param (continuous_psiP hL0 hL)
  have mD2 : Measurable (fun w : ((ι → ℝ) × (ι → ℝ)) × ℝ =>
      ENNReal.ofReal (deriv (psiP f w.1) w.2 ^ 2)) :=
    ENNReal.measurable_ofReal.comp (mD.pow_const 2)
  -- the pointwise bound
  have hpt : ∀ p : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal ((f (rotX a p.1 p.2) - f p.1) ^ 2) ≤
      ENNReal.ofReal a * ∫⁻ θ in Set.Ioc 0 a, ENNReal.ofReal (deriv (psiP f p) θ ^ 2) := by
    intro p
    have hlip := phiP_lipschitz hL0 hL (p.2, p.1)
    rw [← psiP_eq] at hlip
    have hac : AbsolutelyContinuousOnInterval (psiP f p) 0 a :=
      hlip.lipschitzOnWith.absolutelyContinuousOnInterval
    have hftc := hac.integral_deriv_eq_sub
    have h0 : rotX 0 p.1 p.2 = p.1 := by rw [rotX_eq107]; simp
    have e0 : psiP f p a - psiP f p 0 = f (rotX a p.1 p.2) - f p.1 := by
      unfold psiP; rw [h0]
    rw [e0] at hftc
    have hb : ∀ θ, |deriv (psiP f p) θ| ≤
        (((L * √(Fintype.card ι)).toNNReal * (‖p.2‖₊ + ‖p.1‖₊) : ℝ≥0) : ℝ) := by
      intro θ
      have := phiP_deriv_bound hL0 hL (p.2, p.1) θ
      rwa [← psiP_eq] at this
    set C : ℝ := (((L * √(Fintype.card ι)).toNNReal * (‖p.2‖₊ + ‖p.1‖₊) : ℝ≥0) : ℝ) with hC
    have md : Measurable (deriv (psiP f p)) := measurable_deriv _
    have iD : IntervalIntegrable (deriv (psiP f p)) volume 0 a := ii_of_bdd md hb _ _
    have hb2 : ∀ θ, |deriv (psiP f p) θ ^ 2| ≤ C ^ 2 := fun θ => by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb θ) 2
    have iD2 : IntervalIntegrable (fun θ => deriv (psiP f p) θ ^ 2) volume 0 a :=
      ii_of_bdd (md.pow_const 2) hb2 _ _
    have hcs := cs_interval_ii (deriv (psiP f p)) ha iD iD2
    rw [hftc] at hcs
    refine (ENNReal.ofReal_le_ofReal hcs).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul ha, intervalIntegral.integral_of_le ha,
      ofReal_integral_eq_lintegral_ofReal iD2.1 (Eventually.of_forall fun θ => sq_nonneg _)]
  -- a fixed angle
  have hang : ∀ θ : ℝ, ∫⁻ p, ENNReal.ofReal (deriv (psiP f p) θ ^ 2)
      ∂(stdGauss ι).prod (stdGauss ι) =
      ∫⁻ q, gradPhi107 f q ∂(stdGauss ι).prod (stdGauss ι) := by
    intro θ
    have hR := rot_preserving (ι := ι) θ
    have h1 : ∀ᵐ q ∂((stdGauss ι).prod (stdGauss ι)), DifferentiableAt ℝ f q.1 :=
      Measure.quasiMeasurePreserving_fst.ae hdiff
    have h2 := hR.quasiMeasurePreserving.ae h1
    have hae : ∀ᵐ p ∂((stdGauss ι).prod (stdGauss ι)),
        ENNReal.ofReal (deriv (psiP f p) θ ^ 2) =
          gradPhi107 f (rotX θ p.1 p.2, rotY θ p.1 p.2) := by
      filter_upwards [h2] with p hp
      have hp' : DifferentiableAt ℝ f (rotX θ p.1 p.2) := hp
      have hd : HasDerivAt (psiP f p) (fderiv ℝ f (rotX θ p.1 p.2) (rotY θ p.1 p.2)) θ :=
        hp'.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_rotX107 p.1 p.2 θ)
      rw [hd.deriv]
      simp only [gradPhi107]
      rw [fderiv_apply_sum107]
    rw [lintegral_congr_ae hae]
    exact hR.lintegral_comp hΦ
  calc ∫⁻ p, ENNReal.ofReal ((f (rotX a p.1 p.2) - f p.1) ^ 2) ∂(stdGauss ι).prod (stdGauss ι)
      ≤ ∫⁻ p, ENNReal.ofReal a * (∫⁻ θ in Set.Ioc 0 a,
          ENNReal.ofReal (deriv (psiP f p) θ ^ 2)) ∂(stdGauss ι).prod (stdGauss ι) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal a * ∫⁻ p, (∫⁻ θ in Set.Ioc 0 a,
          ENNReal.ofReal (deriv (psiP f p) θ ^ 2)) ∂(stdGauss ι).prod (stdGauss ι) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal a * ∫⁻ θ in Set.Ioc 0 a, ∫⁻ p,
          ENNReal.ofReal (deriv (psiP f p) θ ^ 2) ∂(stdGauss ι).prod (stdGauss ι) := by
        rw [lintegral_lintegral_swap]
        exact mD2.aemeasurable
    _ = ENNReal.ofReal a * ∫⁻ _θ in Set.Ioc 0 a,
          ∫⁻ q, gradPhi107 f q ∂(stdGauss ι).prod (stdGauss ι) := by
        congr 2
        funext θ
        exact hang θ
    _ = ENNReal.ofReal a * ((∫⁻ q, gradPhi107 f q ∂(stdGauss ι).prod (stdGauss ι)) *
          ENNReal.ofReal a) := by
        simp
    _ ≤ ENNReal.ofReal a * (ENNReal.ofReal (∫ x, gradSq f x ∂stdGauss ι) * ENNReal.ofReal a) := by
        gcongr
    _ = ENNReal.ofReal (a ^ 2 * ∫ x, gradSq f x ∂stdGauss ι) := by
        rw [← ENNReal.ofReal_mul hI, ← ENNReal.ofReal_mul ha]
        congr 1
        ring

/-! ## The inequality -/

/-- `2 (1 − cos a)·Var f ≤ a²·E|∇f|²` for `0 ≤ a ≤ 1`. -/
lemma step_lip (hL0 : 0 ≤ L) (hL : EuLip f L) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    2 * (1 - Real.cos a) * ∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι ≤
      a ^ 2 * ∫ x, gradSq f x ∂stdGauss ι := by
  have hf2 := lip_memLp hL0 hL
  have hI : 0 ≤ ∫ x, gradSq f x ∂stdGauss ι := integral_nonneg fun x => gradSq_nonneg f x
  have hen := energy_lip hL0 hL ha
  have hpi : a ≤ Real.pi / 2 := by linarith [Real.pi_gt_three]
  have hcos : 0 ≤ Real.cos a := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hpi⟩
  have hsin : 0 ≤ Real.sin a :=
    Real.sin_nonneg_of_nonneg_of_le_pi ha (by linarith [Real.pi_gt_three])
  have hρ : |Real.cos a| ≤ 1 := Real.abs_cos_le_one a
  have hsC : sC (Real.cos a) = Real.sin a := by
    unfold sC
    rw [← Real.sin_sq_add_cos_sq a, add_sub_cancel_right, Real.sqrt_sq hsin]
  have hφ : ∀ w : (ι → ℝ) × (ι → ℝ),
      Real.cos a • w.1 + sC (Real.cos a) • w.2 = rotX a w.1 w.2 := fun w => by
    rw [hsC, rotX_eq107]
  have mp2 := ou_mp_snd (ι := ι) hρ
  have mp1 := ou_mp_fst (ι := ι)
  simp_rw [hφ] at mp2
  have hgeb := gebelein_L2 hρ hf2 hf2
  have hci := gebelein_L2_integrable hρ hf2 hf2
  simp_rw [hφ] at hgeb hci
  set V := ∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι with hV
  have hV0 : 0 ≤ V := integral_nonneg fun x => sq_nonneg _
  rw [mul_assoc, Real.mul_self_sqrt hV0, abs_of_nonneg hcos] at hgeb
  have hV' := var_eq107 f hf2
  rw [← hV] at hV'
  set m := ∫ y, f y ∂stdGauss ι
  set S := ∫ x, f x ^ 2 ∂stdGauss ι
  set C := ∫ w, f w.1 * f (rotX a w.1 w.2) ∂(stdGauss ι).prod (stdGauss ι)
  have hC : C ≤ m ^ 2 + Real.cos a * V := by
    have := (abs_le.mp hgeb).2
    nlinarith [this]
  have hsm : AEStronglyMeasurable (fun x => f x ^ 2) (stdGauss ι) :=
    hf2.integrable_sq.aestronglyMeasurable
  have A2 : ∫ w, f (rotX a w.1 w.2) ^ 2 ∂(stdGauss ι).prod (stdGauss ι) = S :=
    mp_integral_ae mp2 hsm
  have A1 : ∫ w : (ι → ℝ) × (ι → ℝ), f w.1 ^ 2 ∂(stdGauss ι).prod (stdGauss ι) = S :=
    mp_integral_ae mp1 hsm
  have i2 : Integrable (fun w : (ι → ℝ) × (ι → ℝ) => f (rotX a w.1 w.2) ^ 2)
      ((stdGauss ι).prod (stdGauss ι)) := (hf2.comp_measurePreserving mp2).integrable_sq
  have i1 : Integrable (fun w : (ι → ℝ) × (ι → ℝ) => f w.1 ^ 2)
      ((stdGauss ι).prod (stdGauss ι)) := (hf2.comp_measurePreserving mp1).integrable_sq
  have e : ∀ w : (ι → ℝ) × (ι → ℝ), (f (rotX a w.1 w.2) - f w.1) ^ 2 =
      f (rotX a w.1 w.2) ^ 2 + f w.1 ^ 2 - 2 * (f w.1 * f (rotX a w.1 w.2)) := fun w => by ring
  have hint : Integrable (fun w : (ι → ℝ) × (ι → ℝ) => (f (rotX a w.1 w.2) - f w.1) ^ 2)
      ((stdGauss ι).prod (stdGauss ι)) := by
    simp_rw [e]
    exact (i2.add i1).sub (hci.const_mul 2)
  have hD : ∫ w : (ι → ℝ) × (ι → ℝ), (f (rotX a w.1 w.2) - f w.1) ^ 2
      ∂(stdGauss ι).prod (stdGauss ι) = 2 * S - 2 * C := by
    simp_rw [e]
    have i12 : Integrable (fun w : (ι → ℝ) × (ι → ℝ) => f (rotX a w.1 w.2) ^ 2 + f w.1 ^ 2)
        ((stdGauss ι).prod (stdGauss ι)) := i2.add i1
    have i3 : Integrable (fun w : (ι → ℝ) × (ι → ℝ) => 2 * (f w.1 * f (rotX a w.1 w.2)))
        ((stdGauss ι).prod (stdGauss ι)) := hci.const_mul 2
    rw [integral_sub i12 i3, integral_add i2 i1, integral_const_mul, A1, A2]
    ring
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun w => sq_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg a) hI), hD] at hen
  nlinarith [hen, hC, hV']

/-- **The Gaussian Poincaré inequality with the constant `1` for a Lipschitz function**:
`Var f(X) ≤ E|∇f(X)|²`, `X` a standard Gaussian vector, `f` Lipschitz for the Euclidean norm;
`∇f` is the almost-everywhere derivative. -/
theorem poincare_lip (hL0 : 0 ≤ L) (hL : EuLip f L) :
    ∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι ≤
      ∫ x, ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2 ∂stdGauss ι := by
  set V := ∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι with hV
  have hI' : (∫ x, ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2 ∂stdGauss ι) =
      ∫ x, gradSq f x ∂stdGauss ι := rfl
  rw [hI']
  set I := ∫ x, gradSq f x ∂stdGauss ι with hI
  have hV0 : 0 ≤ V := integral_nonneg fun x => sq_nonneg _
  have ht : Tendsto (fun a : ℝ => (1 - 5 / 48 * a ^ 2) * V) (𝓝[>] 0) (𝓝 V) := by
    have hc : Continuous (fun a : ℝ => (1 - 5 / 48 * a ^ 2) * V) := by fun_prop
    have := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa using this
  refine le_of_tendsto ht ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with a ha
  have hs := step_lip hL0 hL ha.1.le ha.2.le
  rw [← hV, ← hI] at hs
  have hcb := (abs_le.mp (Real.cos_bound (x := a) (by rw [abs_of_pos ha.1]; exact ha.2.le))).2
  rw [abs_of_pos ha.1] at hcb
  have h2 : a ^ 2 * ((1 - 5 / 48 * a ^ 2) * V) ≤ a ^ 2 * I := by
    have : (a ^ 2 - 5 / 48 * a ^ 4) * V ≤ 2 * (1 - Real.cos a) * V :=
      mul_le_mul_of_nonneg_right (by linarith) hV0
    nlinarith [this, hs]
  exact le_of_mul_le_mul_left h2 (pow_pos ha.1 2)

/-- The Poincaré inequality with an almost-everywhere bound `Γ` of `|∇f|²`. -/
theorem poincare_lip_le (hL0 : 0 ≤ L) (hL : EuLip f L) {Γ : (ι → ℝ) → ℝ}
    (hΓ : Integrable Γ (stdGauss ι))
    (hb : ∀ᵐ x ∂stdGauss ι, ∑ i, (fderiv ℝ f x (Pi.single i 1)) ^ 2 ≤ Γ x) :
    ∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι ≤ ∫ x, Γ x ∂stdGauss ι :=
  (poincare_lip hL0 hL).trans (integral_mono_ae (gradSq_integrable hL0 hL) hΓ hb)

/-- `Var f(X) ≤ L²` for an `L`-Lipschitz function. -/
theorem poincare_lip_L (hL0 : 0 ≤ L) (hL : EuLip f L) :
    ∫ x, (f x - ∫ y, f y ∂stdGauss ι) ^ 2 ∂stdGauss ι ≤ L ^ 2 := by
  have h := poincare_lip_le hL0 hL (integrable_const (L ^ 2))
    (Eventually.of_forall fun x => gradSq_le hL0 hL x)
  simpa using h

end BstLean.Part151
