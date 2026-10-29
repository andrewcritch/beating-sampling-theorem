import BstLean.Part162LS
import BstLean.Part131Block

/-!
# Part 162, item 1: the Gaussian `L^p` Poincaré inequality (rotation form)

Role: `delegations/statements/p162-spec.md`, item 1 ("the rotation inequality of the paper").
Do not use `sorry`, `native_decide` or `axiom`.

Paper: `proofs/option-n/theorem7-07-mixture-fluctuation.tex`, proof of Lemma `t7:p07:LS`
("Rotate two independent Gaussian vectors along `H cos t + H' sin t` … Jensen in `H'` and
Minkowski along the path give `‖g − Eg‖_{2p} ≤ (π/2)ν_{2p}‖∇g‖_{2p}`"). Here Hölder (Jensen)
along the path is used instead of Minkowski; the constant is the same.

* `gmom p = E|g|^p` (`ν_p^p`); `gauss_dot_mom`: `E|⟨Z, v⟩|^p = E|g|^p |v|^p`.
* `pow_intervalIntegral_le`: `|∫₀^a D|^p ≤ a^{p−1}∫₀^a |D|^p`.
* `energy_p`: `E|f(X_a) − f(X)|^p ≤ a^p E|g|^p E|∇f|^p` (Lipschitz `f`).
* **`poincare_p`**: `E|f − Ef|^p ≤ (π/2)^p E|g|^p E|∇f|^p`.
-/

namespace BstLean.Part162

open MeasureTheory ProbabilityTheory Real Filter Topology
open scoped ENNReal NNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part148 (EuLip)

/-- The absolute moment `E|g|^p` of a standard Gaussian variable (`ν_p^p` in the paper). -/
noncomputable def gmom (p : ℕ) : ℝ := ∫ x, |x| ^ p ∂gaussianReal 0 1

lemma gmom_nonneg (p : ℕ) : 0 ≤ gmom p := integral_nonneg fun x => pow_nonneg (abs_nonneg x) p

variable {ι : Type} [Fintype ι]

/-- `E|⟨Z, v⟩|^p = E|g|^p·|v|^p` for a standard Gaussian vector `Z`. -/
lemma gauss_dot_mom (v : ι → ℝ) (p : ℕ) :
    ∫ y, |y ⬝ᵥ v| ^ p ∂stdGauss ι = gmom p * √(v ⬝ᵥ v) ^ p := by
  have hD : 0 ≤ v ⬝ᵥ v := by
    simp only [dotProduct]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h1 : ∫ y, |y ⬝ᵥ v| ^ p ∂stdGauss ι = ∫ x, |x| ^ p ∂gaussianReal 0 (v ⬝ᵥ v).toNNReal := by
    rw [← BstLean.Part131.stdGauss_dot v, integral_map (f := fun x : ℝ => |x| ^ p) (by fun_prop)
      (continuous_abs.pow p).aestronglyMeasurable]
  have h2 : gaussianReal 0 (v ⬝ᵥ v).toNNReal = (gaussianReal 0 1).map (√(v ⬝ᵥ v) * ·) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · ring
    · ext
      simp only [NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_one, mul_one, Real.coe_toNNReal _ hD]
      exact (Real.sq_sqrt hD).symm
  rw [h1, h2, integral_map (f := fun x : ℝ => |x| ^ p) (by fun_prop)
    (continuous_abs.pow p).aestronglyMeasurable]
  unfold gmom
  rw [mul_comm, ← integral_const_mul]
  congr 1; funext x
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow]

/-- Jensen on an interval: `|∫₀^a D|^p ≤ a^{p−1} ∫₀^a |D|^p`. -/
lemma pow_intervalIntegral_le {D : ℝ → ℝ} {a : ℝ} (ha : 0 ≤ a) {p : ℕ} (hp : 1 ≤ p)
    (hD : IntervalIntegrable D volume 0 a)
    (hDp : IntervalIntegrable (fun θ => |D θ| ^ p) volume 0 a) :
    |∫ θ in (0 : ℝ)..a, D θ| ^ p ≤ a ^ (p - 1) * ∫ θ in (0 : ℝ)..a, |D θ| ^ p := by
  rcases ha.eq_or_lt with h0 | hpos
  · subst h0; simp [zero_pow (by omega : p ≠ 0)]
  set μ : Measure ℝ := (ENNReal.ofReal a)⁻¹ • volume.restrict (Set.Ioc 0 a) with hμ
  have hvol : volume (Set.Ioc (0 : ℝ) a) = ENNReal.ofReal a := by simp
  have hP : IsProbabilityMeasure μ := by
    constructor
    rw [hμ, Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, hvol,
      smul_eq_mul, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hpos).ne' ENNReal.ofReal_ne_top]
  have hint : ∀ g : ℝ → ℝ, ∫ θ, g θ ∂μ = a⁻¹ * ∫ θ in (0 : ℝ)..a, g θ := fun g => by
    rw [hμ, integral_smul_measure, intervalIntegral.integral_of_le ha, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal ha, smul_eq_mul]
  have hi1 : Integrable (fun θ => |D θ|) μ := by
    rw [hμ]
    exact (hD.1.abs).smul_measure (by simp [hpos])
  have hip : Integrable (fun θ => |D θ| ^ p) μ := by
    rw [hμ]
    exact hDp.1.smul_measure (by simp [hpos])
  have hJ := (convexOn_pow p).map_integral_le (μ := μ) (f := fun θ => |D θ|)
    (continuous_pow p).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall fun θ => abs_nonneg (D θ)) hi1 hip
  rw [hint, hint] at hJ
  have habs : |∫ θ in (0 : ℝ)..a, D θ| ≤ ∫ θ in (0 : ℝ)..a, |D θ| :=
    intervalIntegral.abs_integral_le_integral_abs ha
  have h0 : 0 ≤ |∫ θ in (0 : ℝ)..a, D θ| := abs_nonneg _
  calc |∫ θ in (0 : ℝ)..a, D θ| ^ p ≤ (∫ θ in (0 : ℝ)..a, |D θ|) ^ p :=
        pow_le_pow_left₀ h0 habs p
    _ = a ^ p * (a⁻¹ * ∫ θ in (0 : ℝ)..a, |D θ|) ^ p := by
        rw [mul_pow, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hpos.ne', one_pow, one_mul]
    _ ≤ a ^ p * (a⁻¹ * ∫ θ in (0 : ℝ)..a, |D θ| ^ p) :=
        mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = a ^ (p - 1) * ∫ θ in (0 : ℝ)..a, |D θ| ^ p := by
        obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ]
        field_simp

section energy

open BstLean.Part48 (rotX rotY rot_preserving)
open BstLean.Part107
open BstLean.Part151 (gradSq gradSq_nonneg gradSq_le measurable_gradSq psiP psiP_eq continuous_psiP
  cs_interval_ii)
open BstLean.Part148 (phiP_lipschitz phiP_deriv_bound ii_of_bdd)

variable [DecidableEq ι] {f : (ι → ℝ) → ℝ} {L : ℝ}

/-- The `p`-th power of the directional derivative, as an extended nonnegative function of the
pair `(x, y)`. -/
noncomputable def gradPhiP (f : (ι → ℝ) → ℝ) (p : ℕ) (q : (ι → ℝ) × (ι → ℝ)) : ℝ≥0∞ :=
  ENNReal.ofReal (|∑ i, q.2 i * fderiv ℝ f q.1 (Pi.single i 1)| ^ p)

lemma measurable_gradPhiP (f : (ι → ℝ) → ℝ) (p : ℕ) : Measurable (gradPhiP f p) := by
  unfold gradPhiP
  refine ENNReal.measurable_ofReal.comp (Measurable.pow_const (Measurable.abs ?_) p)
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_pi_apply i).comp measurable_snd).mul
    ((measurable_fderiv_apply_const ℝ f (Pi.single i 1)).comp measurable_fst)

/-- `∫∫ |⟨∇f(x), y⟩|^p = E|g|^p ∫ |∇f|^p`. -/
lemma lintegral_gradPhiP (hL0 : 0 ≤ L) (hL : EuLip f L) (p : ℕ) :
    ∫⁻ q, gradPhiP f p q ∂(stdGauss ι).prod (stdGauss ι) =
      ENNReal.ofReal (gmom p * ∫ x, √(gradSq f x) ^ p ∂stdGauss ι) := by
  set g : (ι → ℝ) → ι → ℝ := fun x i => fderiv ℝ f x (Pi.single i 1) with hg
  have hgg : ∀ x, g x ⬝ᵥ g x = gradSq f x := fun x => by
    simp only [dotProduct, hg, gradSq, sq]
  have hin : ∀ x, ∫⁻ y, ENNReal.ofReal (|∑ i, y i * g x i| ^ p) ∂stdGauss ι =
      ENNReal.ofReal (gmom p * √(gradSq f x) ^ p) := fun x => by
    have hm : Measurable (fun y : ι → ℝ => |∑ i, y i * g x i| ^ p) := by fun_prop
    have hb : ∀ y : ι → ℝ, 0 ≤ |∑ i, y i * g x i| ^ p := fun y => pow_nonneg (abs_nonneg _) _
    have e : ∀ y : ι → ℝ, ∑ i, y i * g x i = y ⬝ᵥ g x := fun y => rfl
    have hint : Integrable (fun y : ι → ℝ => |∑ i, y i * g x i| ^ p) (stdGauss ι) := by
      have hi : Integrable (fun t : ℝ => |t| ^ p) (gaussianReal 0 (g x ⬝ᵥ g x).toNNReal) := by
        have h1 := (ProbabilityTheory.memLp_id_gaussianReal' (μ := 0)
          (v := (g x ⬝ᵥ g x).toNNReal) (p : ℝ≥0∞) (by simp)).integrable_norm_pow'
        simpa using h1
      rw [← BstLean.Part131.stdGauss_dot (g x)] at hi
      have h2 := (integrable_map_measure (g := fun t : ℝ => |t| ^ p)
        (continuous_abs.pow p).aestronglyMeasurable
        (by fun_prop : AEMeasurable (fun ξ : ι → ℝ => ξ ⬝ᵥ g x) (stdGauss ι))).mp hi
      exact h2
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hb)]
    congr 1
    simp_rw [e]
    rw [gauss_dot_mom, hgg]
  rw [lintegral_prod _ (measurable_gradPhiP f p).aemeasurable]
  have e2 : ∀ x, ∫⁻ y, gradPhiP f p (x, y) ∂stdGauss ι =
      ENNReal.ofReal (gmom p * √(gradSq f x) ^ p) := fun x => hin x
  rw [lintegral_congr e2]
  have hb : ∀ x, |gmom p * √(gradSq f x) ^ p| ≤ gmom p * L ^ p := fun x => by
    rw [abs_of_nonneg (by have := gmom_nonneg p; positivity)]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.sqrt_nonneg _) ?_ p) (gmom_nonneg p)
    rw [show L = √(L ^ 2) from (Real.sqrt_sq hL0).symm]
    exact Real.sqrt_le_sqrt (gradSq_le hL0 hL x)
  have hint : Integrable (fun x => gmom p * √(gradSq f x) ^ p) (stdGauss ι) :=
    Integrable.of_bound (((measurable_gradSq f).sqrt.pow_const p).const_mul _).aestronglyMeasurable
      _ (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hb x)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => by
    have := gmom_nonneg p; positivity), integral_const_mul]

/-- **The `L^p` energy bound along the rotation path**:
`E|f(X_a) − f(X)|^p ≤ a^p·E|g|^p·E|∇f|^p` for a Lipschitz `f` and `p ≥ 1`. -/
theorem energy_p (hL0 : 0 ≤ L) (hL : EuLip f L) {a : ℝ} (ha : 0 ≤ a) {p : ℕ} (hp : 1 ≤ p) :
    ∫⁻ q, ENNReal.ofReal (|f (rotX a q.1 q.2) - f q.1| ^ p) ∂(stdGauss ι).prod (stdGauss ι) ≤
      ENNReal.ofReal (a ^ p * (gmom p * ∫ x, √(gradSq f x) ^ p ∂stdGauss ι)) := by
  have hdiff := hL.ae_diff hL0
  have mD : Measurable (fun w : ((ι → ℝ) × (ι → ℝ)) × ℝ => deriv (psiP f w.1) w.2) :=
    measurable_deriv_with_param (continuous_psiP hL0 hL)
  have mDp : Measurable (fun w : ((ι → ℝ) × (ι → ℝ)) × ℝ =>
      ENNReal.ofReal (|deriv (psiP f w.1) w.2| ^ p)) :=
    ENNReal.measurable_ofReal.comp (mD.abs.pow_const p)
  have hI : 0 ≤ gmom p * ∫ x, √(gradSq f x) ^ p ∂stdGauss ι :=
    mul_nonneg (gmom_nonneg p) (integral_nonneg fun x => pow_nonneg (Real.sqrt_nonneg _) _)
  -- the pointwise bound
  have hpt : ∀ q : (ι → ℝ) × (ι → ℝ), ENNReal.ofReal (|f (rotX a q.1 q.2) - f q.1| ^ p) ≤
      ENNReal.ofReal (a ^ (p - 1)) *
        ∫⁻ θ in Set.Ioc 0 a, ENNReal.ofReal (|deriv (psiP f q) θ| ^ p) := by
    intro q
    have hlip := phiP_lipschitz hL0 hL (q.2, q.1)
    rw [← psiP_eq] at hlip
    have hac : AbsolutelyContinuousOnInterval (psiP f q) 0 a :=
      hlip.lipschitzOnWith.absolutelyContinuousOnInterval
    have hftc := hac.integral_deriv_eq_sub
    have h0 : rotX 0 q.1 q.2 = q.1 := by rw [rotX_eq107]; simp
    have e0 : psiP f q a - psiP f q 0 = f (rotX a q.1 q.2) - f q.1 := by
      unfold psiP; rw [h0]
    rw [e0] at hftc
    have hb : ∀ θ, |deriv (psiP f q) θ| ≤
        (((L * √(Fintype.card ι)).toNNReal * (‖q.2‖₊ + ‖q.1‖₊) : ℝ≥0) : ℝ) := by
      intro θ
      have := phiP_deriv_bound hL0 hL (q.2, q.1) θ
      rwa [← psiP_eq] at this
    set C : ℝ := (((L * √(Fintype.card ι)).toNNReal * (‖q.2‖₊ + ‖q.1‖₊) : ℝ≥0) : ℝ) with hC
    have md : Measurable (deriv (psiP f q)) := measurable_deriv _
    have iD : IntervalIntegrable (deriv (psiP f q)) volume 0 a := ii_of_bdd md hb _ _
    have hbp : ∀ θ, |(|deriv (psiP f q) θ| ^ p)| ≤ C ^ p := fun θ => by
      rw [abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) (hb θ) p
    have iDp : IntervalIntegrable (fun θ => |deriv (psiP f q) θ| ^ p) volume 0 a :=
      ii_of_bdd (md.abs.pow_const p) hbp _ _
    have hj := pow_intervalIntegral_le ha hp iD iDp
    rw [hftc] at hj
    refine (ENNReal.ofReal_le_ofReal hj).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (pow_nonneg ha _), intervalIntegral.integral_of_le ha,
      ofReal_integral_eq_lintegral_ofReal iDp.1
        (Filter.Eventually.of_forall fun θ => pow_nonneg (abs_nonneg _) _)]
  -- a fixed angle
  have hang : ∀ θ : ℝ, ∫⁻ q, ENNReal.ofReal (|deriv (psiP f q) θ| ^ p)
      ∂(stdGauss ι).prod (stdGauss ι) = ∫⁻ q, gradPhiP f p q ∂(stdGauss ι).prod (stdGauss ι) := by
    intro θ
    have hR := rot_preserving (ι := ι) θ
    have h1 : ∀ᵐ q ∂((stdGauss ι).prod (stdGauss ι)), DifferentiableAt ℝ f q.1 :=
      Measure.quasiMeasurePreserving_fst.ae hdiff
    have h2 := hR.quasiMeasurePreserving.ae h1
    have hae : ∀ᵐ q ∂((stdGauss ι).prod (stdGauss ι)),
        ENNReal.ofReal (|deriv (psiP f q) θ| ^ p) =
          gradPhiP f p (rotX θ q.1 q.2, rotY θ q.1 q.2) := by
      filter_upwards [h2] with q hq
      have hq' : DifferentiableAt ℝ f (rotX θ q.1 q.2) := hq
      have hd : HasDerivAt (psiP f q) (fderiv ℝ f (rotX θ q.1 q.2) (rotY θ q.1 q.2)) θ :=
        hq'.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_rotX107 q.1 q.2 θ)
      rw [hd.deriv]
      simp only [gradPhiP]
      rw [fderiv_apply_sum107]
    rw [lintegral_congr_ae hae]
    exact hR.lintegral_comp (measurable_gradPhiP f p)
  calc ∫⁻ q, ENNReal.ofReal (|f (rotX a q.1 q.2) - f q.1| ^ p) ∂(stdGauss ι).prod (stdGauss ι)
      ≤ ∫⁻ q, ENNReal.ofReal (a ^ (p - 1)) * (∫⁻ θ in Set.Ioc 0 a,
          ENNReal.ofReal (|deriv (psiP f q) θ| ^ p)) ∂(stdGauss ι).prod (stdGauss ι) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (a ^ (p - 1)) * ∫⁻ q, (∫⁻ θ in Set.Ioc 0 a,
          ENNReal.ofReal (|deriv (psiP f q) θ| ^ p)) ∂(stdGauss ι).prod (stdGauss ι) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (a ^ (p - 1)) * ∫⁻ θ in Set.Ioc 0 a, ∫⁻ q,
          ENNReal.ofReal (|deriv (psiP f q) θ| ^ p) ∂(stdGauss ι).prod (stdGauss ι) := by
        rw [lintegral_lintegral_swap]
        exact mDp.aemeasurable
    _ = ENNReal.ofReal (a ^ (p - 1)) * ∫⁻ _θ in Set.Ioc 0 a,
          ∫⁻ q, gradPhiP f p q ∂(stdGauss ι).prod (stdGauss ι) := by
        congr 2
        funext θ
        exact hang θ
    _ = ENNReal.ofReal (a ^ (p - 1)) * ((∫⁻ q, gradPhiP f p q ∂(stdGauss ι).prod (stdGauss ι)) *
          ENNReal.ofReal a) := by
        simp
    _ = ENNReal.ofReal (a ^ (p - 1)) * (ENNReal.ofReal (gmom p * ∫ x, √(gradSq f x) ^ p
          ∂stdGauss ι) * ENNReal.ofReal a) := by
        rw [lintegral_gradPhiP hL0 hL p]
    _ = ENNReal.ofReal (a ^ p * (gmom p * ∫ x, √(gradSq f x) ^ p ∂stdGauss ι)) := by
        rw [← ENNReal.ofReal_mul hI, ← ENNReal.ofReal_mul (pow_nonneg ha _)]
        congr 1
        obtain ⟨k, rfl⟩ : ∃ k, p = k + 1 := ⟨p - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ]
        ring

/-- Jensen for one point: `|f(x) − Ef|^p ≤ E|f(Y) − f(x)|^p` (extended form). -/
lemma ofReal_dev_le (hL0 : 0 ≤ L) (hL : EuLip f L) {p : ℕ} (hp : 1 ≤ p) (x : ι → ℝ) :
    ENNReal.ofReal (|f x - ∫ y, f y ∂stdGauss ι| ^ p) ≤
      ∫⁻ y, ENNReal.ofReal (|f y - f x| ^ p) ∂stdGauss ι := by
  have hfi : Integrable f (stdGauss ι) := (BstLean.Part151.lip_memLp hL0 hL).integrable one_le_two
  have hc := hL.continuous hL0
  have mg : Measurable (fun y => |f y - f x| ^ p) := (hc.measurable.sub_const _).abs.pow_const p
  by_cases hint : Integrable (fun y => |f y - f x| ^ p) (stdGauss ι)
  · rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun y => pow_nonneg (abs_nonneg _) _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have e : f x - ∫ y, f y ∂stdGauss ι = -∫ y, (f y - f x) ∂stdGauss ι := by
      rw [integral_sub hfi (integrable_const _)]; simp
    rw [e, abs_neg]
    have hg1 : Integrable (fun y => |f y - f x|) (stdGauss ι) := (hfi.sub (integrable_const _)).abs
    have hJ := (convexOn_pow p).map_integral_le (μ := stdGauss ι) (f := fun y => |f y - f x|)
      (continuous_pow p).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall fun y => Set.mem_Ici.mpr (abs_nonneg _)) hg1 hint
    calc |∫ y, (f y - f x) ∂stdGauss ι| ^ p ≤ (∫ y, |f y - f x| ∂stdGauss ι) ^ p :=
          pow_le_pow_left₀ (abs_nonneg _) (abs_integral_le_integral_abs) p
      _ ≤ ∫ y, |f y - f x| ^ p ∂stdGauss ι := hJ
  · have : ∫⁻ y, ENNReal.ofReal (|f y - f x| ^ p) ∂stdGauss ι = ⊤ := by
      by_contra hne
      exact hint ⟨mg.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall fun y => pow_nonneg (abs_nonneg _) _)).mpr
          (lt_top_iff_ne_top.mpr hne)⟩
    rw [this]; exact le_top

/-- **The Gaussian `L^p` Poincaré inequality (Pisier's rotation form)** for a Lipschitz `f` and
`p ≥ 1`: `E|f − Ef|^p ≤ (π/2)^p·E|g|^p·E|∇f|^p` (extended form). -/
theorem poincare_p_lint (hL0 : 0 ≤ L) (hL : EuLip f L) {p : ℕ} (hp : 1 ≤ p) :
    ∫⁻ x, ENNReal.ofReal (|f x - ∫ y, f y ∂stdGauss ι| ^ p) ∂stdGauss ι ≤
      ENNReal.ofReal ((π / 2) ^ p * (gmom p * ∫ x, √(gradSq f x) ^ p ∂stdGauss ι)) := by
  have hE := energy_p hL0 hL (le_of_lt (by positivity : (0 : ℝ) < π / 2)) hp
  have hrot : ∀ q : (ι → ℝ) × (ι → ℝ), rotX (π / 2) q.1 q.2 = q.2 := fun q => by
    rw [rotX_eq107]; simp
  simp_rw [hrot] at hE
  refine le_trans ?_ hE
  have hc := hL.continuous hL0
  have mF : Measurable (fun q : (ι → ℝ) × (ι → ℝ) => ENNReal.ofReal (|f q.2 - f q.1| ^ p)) :=
    ENNReal.measurable_ofReal.comp
      (((hc.measurable.comp measurable_snd).sub (hc.measurable.comp measurable_fst)).abs.pow_const p)
  rw [lintegral_prod _ mF.aemeasurable]
  exact lintegral_mono fun x => ofReal_dev_le hL0 hL hp x

/-- **The Gaussian `L^p` Poincaré inequality**, real form. -/
theorem poincare_p (hL0 : 0 ≤ L) (hL : EuLip f L) {p : ℕ} (hp : 1 ≤ p) :
    ∫ x, |f x - ∫ y, f y ∂stdGauss ι| ^ p ∂stdGauss ι ≤
      (π / 2) ^ p * (gmom p * ∫ x, √(gradSq f x) ^ p ∂stdGauss ι) := by
  have hR : 0 ≤ (π / 2) ^ p * (gmom p * ∫ x, √(gradSq f x) ^ p ∂stdGauss ι) := by
    have := gmom_nonneg p
    have : 0 ≤ ∫ x, √(gradSq f x) ^ p ∂stdGauss ι :=
      integral_nonneg fun x => pow_nonneg (Real.sqrt_nonneg _) _
    positivity
  by_cases hint : Integrable (fun x => |f x - ∫ y, f y ∂stdGauss ι| ^ p) (stdGauss ι)
  · have h := poincare_p_lint hL0 hL hp
    rw [← ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun x => pow_nonneg (abs_nonneg _) _)] at h
    exact (ENNReal.ofReal_le_ofReal_iff hR).mp h
  · rw [integral_undef hint]; exact hR

end energy

end BstLean.Part162

open BstLean.Part162 in
#print axioms poincare_p
