import BstLean.Part72Block
import BstLean.Part72Rank1
import BstLean.Part71QT1

/-!
# Part 72: two-subspace tilts `∝ exp(c‖Π_V x‖²)`, uniformly in `c`

Coordinates `Fin (b + r)`, `V` = the first `b` coordinates (a coordinate subspace).
`f1Tilt b r c` has density `exp(c·UV x)/Z` relative to `σ`, for any real `c` (the paper's
`c = αn`). By `block_split`, `xV/‖xV‖` and `xP/‖xP‖` are uniform on `S^{b−1}` and `S^{r−1}`
under every such tilt. Hence, for `b + r ≤ L·b` and `b + r ≤ L·r`, uniformly in `c`:

* `f1_mean_zero`: `E_μ x = 0`;
* `f1_dir`: `E_μ (w·x)² ≤ 2L/(b+r)` for every unit `w`;
* `f1_p4`: `E_μ p₄^q ≤ 2^q·(4q−1)!!·L^q/(b+r)^q` (Lemma S on each block);
* `f1_good`: `Good72 (b+r) d k μ (wF L) (Fov d (2L)) (2L)`, `wF L i = 4^i·(8i−1)!!·L^{2i}`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part72

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (uniformSphere)
open BstLean.Part40 (SphLaw)
open BstLean.Part41 (phiSq)
open BstLean.Part53 (c0 p4 unitF53 radF53)

variable {b r : ℕ}

/-- The normalizing constant `Z = E_σ exp(c·UV x)`. -/
noncomputable def f1Z (b r : ℕ) (c : ℝ) : ℝ := ∫ x, Real.exp (c * UV x) ∂uniformSphere (b + r)

/-- **The two-subspace tilt** `∝ exp(c‖Π_V x‖²)`, `V` the first `b` coordinates. -/
noncomputable def f1Tilt (b r : ℕ) (c : ℝ) : Measure (Fin (b + r) → ℝ) :=
  (uniformSphere (b + r)).withDensity (fun x => ENNReal.ofReal (Real.exp (c * UV x) / f1Z b r c))

private lemma cont_UV : Continuous (UV (b := b) (r := r)) := by
  unfold UV xV; fun_prop

private lemma UV_le_one {x : Fin (b + r) → ℝ} (hx : ∑ i, x i ^ 2 = 1) : UV x ≤ 1 := by
  have h := sum_split (fun t => t ^ 2) x
  have h2 : 0 ≤ ∑ j, xP x j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  unfold UV; linarith

private lemma UV_nonneg (x : Fin (b + r) → ℝ) : 0 ≤ UV x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma f1Z_pos (hbr : 1 ≤ b + r) (c : ℝ) : 0 < f1Z b r c := by
  have := BstLean.Part29.uniformSphere_isProbability (b + r) hbr
  have hσ := BstLean.Part71.unif_sph hbr
  have hc : Continuous (fun x : Fin (b + r) → ℝ => Real.exp (c * UV x)) := by
    have := cont_UV (b := b) (r := r); fun_prop
  have h : ∫ _x, Real.exp (-|c|) ∂uniformSphere (b + r) ≤ f1Z b r c := by
    apply integral_mono_ae (integrable_const _) (sphere_integrable hσ hc)
    filter_upwards [hσ.sphere] with x hx
    apply Real.exp_le_exp.mpr
    have h1 := UV_le_one hx
    have h0 := UV_nonneg x
    rcases le_or_gt 0 c with hc0 | hc0
    · rw [abs_of_nonneg hc0]; nlinarith
    · rw [abs_of_neg hc0]; nlinarith
  simp at h
  exact lt_of_lt_of_le (Real.exp_pos _) h

lemma f1_integral (hbr : 1 ≤ b + r) (c : ℝ) (f : (Fin (b + r) → ℝ) → ℝ) :
    ∫ x, f x ∂f1Tilt b r c =
      ∫ x, (Real.exp (c * UV x) / f1Z b r c) * f x ∂uniformSphere (b + r) := by
  have hZ := f1Z_pos (b := b) (r := r) hbr c
  have hm : Measurable (fun x : Fin (b + r) → ℝ => Real.exp (c * UV x) / f1Z b r c) := by
    have := cont_UV (b := b) (r := r); apply Continuous.measurable; fun_prop
  rw [f1Tilt, integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal (by simp)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (by positivity)]
  rfl

lemma f1_sph (hbr : 1 ≤ b + r) (c : ℝ) : SphLaw (b + r) (f1Tilt b r c) := by
  have := BstLean.Part29.uniformSphere_isProbability (b + r) hbr
  have hZ := f1Z_pos (b := b) (r := r) hbr c
  have hint : Integrable (fun x : Fin (b + r) → ℝ => Real.exp (c * UV x)) (uniformSphere (b + r)) :=
    sphere_integrable (BstLean.Part71.unif_sph hbr) (by have := cont_UV (b := b) (r := r); fun_prop)
  refine ⟨⟨?_⟩, ?_⟩
  · rw [f1Tilt, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal (hint.div_const _)
        (Filter.Eventually.of_forall (fun x => by simp only [Pi.zero_apply]; positivity)),
      integral_div]
    rw [show (∫ x, Real.exp (c * UV x) ∂uniformSphere (b + r)) = f1Z b r c from rfl,
      div_self hZ.ne']
    simp
  · exact (withDensity_absolutelyContinuous _ _).ae_le
      (BstLean.Part29.uniformSphere_ae_sphere (b + r))

private lemma neg_inv' (hn : 1 ≤ b + r) (F : (Fin (b + r) → ℝ) → ℝ) (hF : Continuous F) :
    ∫ x, F x ∂uniformSphere (b + r) = ∫ x, F (-x) ∂uniformSphere (b + r) := by
  have h := BstLean.Part56.MomProg.uniformSphere_involution (n := b + r)
    (LinearIsometryEquiv.neg ℝ) (fun x => by simp)
  have hf : (fun x : Fin (b + r) → ℝ =>
      WithLp.ofLp ((LinearIsometryEquiv.neg ℝ) (WithLp.toLp 2 x))) = fun x => -x := by
    funext x; simp
  rw [hf] at h
  conv_lhs => rw [← h]
  rw [integral_map (by fun_prop) hF.aestronglyMeasurable]

lemma f1_mean_zero (hbr : 1 ≤ b + r) (c : ℝ) (i : Fin (b + r)) :
    ∫ x, x i ∂f1Tilt b r c = 0 := by
  rw [f1_integral hbr c]
  set F : (Fin (b + r) → ℝ) → ℝ := fun x => (Real.exp (c * UV x) / f1Z b r c) * x i
  have hF : Continuous F := by have := cont_UV (b := b) (r := r); fun_prop
  have h := neg_inv' hbr F hF
  have hneg : ∀ x, F (-x) = -F x := by
    intro x
    simp only [F, UV, xV, Pi.neg_apply, neg_sq, mul_neg]
  simp_rw [hneg, integral_neg] at h
  change ∫ x, F x ∂uniformSphere (b + r) = 0
  linarith

/-- **The block directions are uniform under the tilt** (first block). -/
theorem f1_blockV (hb : 1 ≤ b) (c : ℝ) (G : (Fin b → ℝ) → ℝ) (hG : Continuous G)
    (hG0 : ∀ y, 0 ≤ G y) :
    ∫ x, G (unitF53 (xV x)) ∂f1Tilt b r c = ∫ y, G y ∂uniformSphere b := by
  have hbr : 1 ≤ b + r := by omega
  have hZ := f1Z_pos (b := b) (r := r) hbr c
  have hU := BstLean.Part53.measurable_unitF (ι := Fin b)
  have hGU : Measurable (fun x : Fin (b + r) → ℝ => G (unitF53 (xV x))) :=
    hG.measurable.comp (hU.comp measurable_xV)
  have hUVm : Measurable (UV (b := b) (r := r)) := cont_UV.measurable
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => hG0 _))
      hGU.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => hG0 _))
      hG.aestronglyMeasurable]
  congr 1
  rw [f1Tilt, lintegral_withDensity_eq_lintegral_mul _ (by
      apply Measurable.ennreal_ofReal; exact (Real.continuous_exp.measurable.comp
        (measurable_const.mul hUVm)).div_const _) hGU.ennreal_ofReal]
  have hsplit : ∀ x : Fin (b + r) → ℝ,
      (fun x => ENNReal.ofReal (Real.exp (c * UV x) / f1Z b r c)) x *
        ENNReal.ofReal (G (unitF53 (xV x))) =
      ENNReal.ofReal (1 / f1Z b r c) *
        ((fun s => ENNReal.ofReal (Real.exp (c * s))) (UV x) *
          (fun y => ENNReal.ofReal (G y)) (unitF53 (xV x))) := by
    intro x
    simp only
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  simp_rw [Pi.mul_apply, hsplit]
  have hW : Measurable (fun s : ℝ => ENNReal.ofReal (Real.exp (c * s))) := by fun_prop
  rw [lintegral_const_mul (ENNReal.ofReal (1 / f1Z b r c))
    (f := fun x => ENNReal.ofReal (Real.exp (c * UV x)) * ENNReal.ofReal (G (unitF53 (xV x))))
    ((hW.comp hUVm).mul (hG.measurable.ennreal_ofReal.comp (hU.comp measurable_xV)))]
  have hbs := block_split (b := b) (r := r) hb _ hW _ hG.measurable.ennreal_ofReal
  try simp only at hbs
  rw [hbs]
  have hZl : ∫⁻ x, ENNReal.ofReal (Real.exp (c * UV x)) ∂uniformSphere (b + r) =
      ENNReal.ofReal (f1Z b r c) := by
    rw [f1Z, ofReal_integral_eq_lintegral_ofReal
      (sphere_integrable (BstLean.Part71.unif_sph hbr) (by have := cont_UV (b := b) (r := r); fun_prop))
      (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))]
  rw [hZl, mul_comm, mul_assoc, ← ENNReal.ofReal_mul hZ.le, mul_one_div_cancel hZ.ne',
    ENNReal.ofReal_one, mul_one]

/-- **The block directions are uniform under the tilt** (second block). -/
theorem f1_blockP (hr : 1 ≤ r) (c : ℝ) (G : (Fin r → ℝ) → ℝ) (hG : Continuous G)
    (hG0 : ∀ y, 0 ≤ G y) :
    ∫ x, G (unitF53 (xP x)) ∂f1Tilt b r c = ∫ y, G y ∂uniformSphere r := by
  have hbr : 1 ≤ b + r := by omega
  have hZ := f1Z_pos (b := b) (r := r) hbr c
  have hU := BstLean.Part53.measurable_unitF (ι := Fin r)
  have hGU : Measurable (fun x : Fin (b + r) → ℝ => G (unitF53 (xP x))) :=
    hG.measurable.comp (hU.comp measurable_xP)
  have hUVm : Measurable (UV (b := b) (r := r)) := cont_UV.measurable
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => hG0 _))
      hGU.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (fun x => hG0 _))
      hG.aestronglyMeasurable]
  congr 1
  rw [f1Tilt, lintegral_withDensity_eq_lintegral_mul _ (by
      apply Measurable.ennreal_ofReal; exact (Real.continuous_exp.measurable.comp
        (measurable_const.mul hUVm)).div_const _) hGU.ennreal_ofReal]
  have hsplit : ∀ x : Fin (b + r) → ℝ,
      (fun x => ENNReal.ofReal (Real.exp (c * UV x) / f1Z b r c)) x *
        ENNReal.ofReal (G (unitF53 (xP x))) =
      ENNReal.ofReal (1 / f1Z b r c) *
        ((fun s => ENNReal.ofReal (Real.exp (c * s))) (UV x) *
          (fun y => ENNReal.ofReal (G y)) (unitF53 (xP x))) := by
    intro x
    simp only
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  simp_rw [Pi.mul_apply, hsplit]
  have hW : Measurable (fun s : ℝ => ENNReal.ofReal (Real.exp (c * s))) := by fun_prop
  rw [lintegral_const_mul (ENNReal.ofReal (1 / f1Z b r c))
    (f := fun x => ENNReal.ofReal (Real.exp (c * UV x)) * ENNReal.ofReal (G (unitF53 (xP x))))
    ((hW.comp hUVm).mul (hG.measurable.ennreal_ofReal.comp (hU.comp measurable_xP)))]
  have hbs := block_splitP (b := b) (r := r) hr _ hW _ hG.measurable.ennreal_ofReal
  try simp only at hbs
  rw [hbs]
  have hZl : ∫⁻ x, ENNReal.ofReal (Real.exp (c * UV x)) ∂uniformSphere (b + r) =
      ENNReal.ofReal (f1Z b r c) := by
    rw [f1Z, ofReal_integral_eq_lintegral_ofReal
      (sphere_integrable (BstLean.Part71.unif_sph hbr) (by have := cont_UV (b := b) (r := r); fun_prop))
      (Filter.Eventually.of_forall (fun x => (Real.exp_pos _).le))]
  rw [hZl, mul_comm, mul_assoc, ← ENNReal.ofReal_mul hZ.le, mul_one_div_cancel hZ.ne',
    ENNReal.ofReal_one, mul_one]

lemma rad_smul_unit {ι : Type} [Fintype ι] (z : ι → ℝ) : radF53 z • unitF53 z = z := by
  unfold radF53 unitF53
  rw [smul_smul]
  rcases eq_or_ne (Real.sqrt (∑ i, z i ^ 2)) 0 with h | h
  · have h0 : ∑ i, z i ^ 2 = 0 := le_antisymm (Real.sqrt_eq_zero'.mp h)
      (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    have hz : z = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (z i))).mp h0 i
        (Finset.mem_univ i)
      simpa using this
    subst hz; simp
  · rw [mul_one_div_cancel h, one_smul]

private lemma rad_sq {ι : Type} [Fintype ι] (z : ι → ℝ) : radF53 z ^ 2 = ∑ i, z i ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

private lemma rad_nonneg {ι : Type} [Fintype ι] (z : ι → ℝ) : 0 ≤ radF53 z := Real.sqrt_nonneg _

private lemma radV_le {x : Fin (b + r) → ℝ} (hx : ∑ i, x i ^ 2 = 1) : radF53 (xV x) ^ 2 ≤ 1 := by
  rw [rad_sq]
  have h := sum_split (fun t => t ^ 2) x
  have h2 : 0 ≤ ∑ j, xP x j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

private lemma radP_le {x : Fin (b + r) → ℝ} (hx : ∑ i, x i ^ 2 = 1) : radF53 (xP x) ^ 2 ≤ 1 := by
  rw [rad_sq]
  have h := sum_split (fun t => t ^ 2) x
  have h2 : 0 ≤ ∑ j, xV x j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  linarith

private lemma dot_unit {ι : Type} [Fintype ι] (w z : ι → ℝ) :
    ∑ j, w j * z j = radF53 z * ∑ j, w j * unitF53 z j := by
  conv_lhs => rw [← rad_smul_unit z]
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _; ring

private lemma sphere_dir_sq {m : ℕ} (hm : 1 ≤ m) (w : Fin m → ℝ) :
    ∫ y, (∑ j, w j * y j) ^ 2 ∂uniformSphere m = (∑ j, w j ^ 2) / m := by
  have h := BstLean.Part71.sphere_mean_qf hm (fun i j => w i * w j)
  have hq : ∀ y : Fin m → ℝ, BstLean.Part71.qf (fun i j => w i * w j) y = (∑ j, w j * y j) ^ 2 := by
    intro y
    unfold BstLean.Part71.qf
    rw [sq, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; ring
  simp_rw [hq] at h
  rw [h]
  congr 1
  simp [Matrix.trace, Matrix.diag, sq]

/-- **Directional second moments of the two-subspace tilt**, uniformly in `c`. -/
theorem f1_dir (hb : 1 ≤ b) (hr : 1 ≤ r) {L : ℝ} (hLb : ((b + r : ℕ) : ℝ) ≤ L * b)
    (hLr : ((b + r : ℕ) : ℝ) ≤ L * r) (c : ℝ) (w : Fin (b + r) → ℝ) (hw : ∑ i, w i ^ 2 = 1) :
    ∫ x, (∑ i, w i * x i) ^ 2 ∂f1Tilt b r c ≤ 2 * L / ((b + r : ℕ) : ℝ) := by
  have hbr : 1 ≤ b + r := by omega
  have hsph := f1_sph (b := b) (r := r) hbr c
  let := hsph.prob
  let wV : Fin b → ℝ := xV w
  let wP : Fin r → ℝ := xP w
  let GV : (Fin b → ℝ) → ℝ := fun y => (∑ j, wV j * y j) ^ 2
  let GP : (Fin r → ℝ) → ℝ := fun y => (∑ j, wP j * y j) ^ 2
  have hGV : Continuous GV := by fun_prop
  have hGP : Continuous GP := by fun_prop
  have hU1 := BstLean.Part53.measurable_unitF (ι := Fin b)
  have hpt : ∀ᵐ x ∂f1Tilt b r c, (∑ i, w i * x i) ^ 2 ≤
      2 * GV (unitF53 (xV x)) + 2 * GP (unitF53 (xP x)) := by
    filter_upwards [hsph.sphere] with x hx
    have hs : ∑ i, w i * x i = ∑ j, wV j * xV x j + ∑ j, wP j * xP x j := by
      rw [Fin.sum_univ_add]; rfl
    rw [hs, dot_unit wV (xV x), dot_unit wP (xP x)]
    have h1 := radV_le hx
    have h2 := radP_le hx
    simp only [GV, GP]
    set a := ∑ j, wV j * unitF53 (xV x) j
    set e := ∑ j, wP j * unitF53 (xP x) j
    have ha : radF53 (xV x) ^ 2 * a ^ 2 ≤ a ^ 2 := by nlinarith [sq_nonneg a]
    have he : radF53 (xP x) ^ 2 * e ^ 2 ≤ e ^ 2 := by nlinarith [sq_nonneg e]
    nlinarith [sq_nonneg (radF53 (xV x) * a - radF53 (xP x) * e)]
  have hiV : Integrable (fun x => GV (unitF53 (xV x))) (f1Tilt b r c) := by
    apply Integrable.of_bound (hGV.measurable.comp (hU1.comp measurable_xV)).aestronglyMeasurable
      (∑ j, wV j ^ 2)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases h0 : xV x = 0
    · simp [GV, h0, unitF53]; positivity
    · have hu : ∑ j, unitF53 (xV x) j ^ 2 = 1 := by
        unfold unitF53
        simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
        have hpos : 0 < ∑ j, xV x j ^ 2 := by
          by_contra hle
          apply h0
          funext j
          have h00 : ∑ j, xV x j ^ 2 = 0 := le_antisymm (not_lt.mp hle)
            (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
          have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (xV x i))).mp h00 j
            (Finset.mem_univ j)
          simpa using this
        rw [div_pow, one_pow, Real.sq_sqrt hpos.le]; field_simp
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ wV (unitF53 (xV x))
      rw [hu, mul_one] at this
      exact this
  have hiP : Integrable (fun x => GP (unitF53 (xP x))) (f1Tilt b r c) := by
    have hU2 := BstLean.Part53.measurable_unitF (ι := Fin r)
    apply Integrable.of_bound (hGP.measurable.comp (hU2.comp measurable_xP)).aestronglyMeasurable
      (∑ j, wP j ^ 2)
    filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases h0 : xP x = 0
    · simp [GP, h0, unitF53]; positivity
    · have hu : ∑ j, unitF53 (xP x) j ^ 2 = 1 := by
        unfold unitF53
        simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
        have hpos : 0 < ∑ j, xP x j ^ 2 := by
          by_contra hle
          apply h0
          funext j
          have h00 : ∑ j, xP x j ^ 2 = 0 := le_antisymm (not_lt.mp hle)
            (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
          have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (xP x i))).mp h00 j
            (Finset.mem_univ j)
          simpa using this
        rw [div_pow, one_pow, Real.sq_sqrt hpos.le]; field_simp
      have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ wP (unitF53 (xP x))
      rw [hu, mul_one] at this
      exact this
  have hwc : Continuous (fun x : Fin (b + r) → ℝ => (∑ i, w i * x i) ^ 2) := by fun_prop
  calc ∫ x, (∑ i, w i * x i) ^ 2 ∂f1Tilt b r c
      ≤ ∫ x, 2 * GV (unitF53 (xV x)) + 2 * GP (unitF53 (xP x)) ∂f1Tilt b r c :=
        integral_mono_ae (sphere_integrable hsph hwc) ((hiV.const_mul 2).add (hiP.const_mul 2)) hpt
    _ = 2 * (∑ j, wV j ^ 2) / b + 2 * (∑ j, wP j ^ 2) / r := by
        rw [integral_add (hiV.const_mul 2) (hiP.const_mul 2), integral_const_mul,
          integral_const_mul, f1_blockV hb c GV hGV (fun _ => sq_nonneg _),
          f1_blockP hr c GP hGP (fun _ => sq_nonneg _), sphere_dir_sq hb, sphere_dir_sq hr]
        ring
    _ ≤ 2 * (∑ j, wV j ^ 2) * (L / ((b + r : ℕ) : ℝ)) +
          2 * (∑ j, wP j ^ 2) * (L / ((b + r : ℕ) : ℝ)) := by
        have hbR : (0 : ℝ) < b := by exact_mod_cast hb
        have hrR : (0 : ℝ) < r := by exact_mod_cast hr
        have hnR : (0 : ℝ) < ((b + r : ℕ) : ℝ) := by exact_mod_cast hbr
        have e1 : 1 / (b : ℝ) ≤ L / ((b + r : ℕ) : ℝ) := by
          rw [div_le_div_iff₀ hbR hnR]; linarith
        have e2 : 1 / (r : ℝ) ≤ L / ((b + r : ℕ) : ℝ) := by
          rw [div_le_div_iff₀ hrR hnR]; linarith
        have s1 : 0 ≤ ∑ j, wV j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        have s2 : 0 ≤ ∑ j, wP j ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
        have k1 : 2 * (∑ j, wV j ^ 2) / (b : ℝ) = 2 * (∑ j, wV j ^ 2) * (1 / b) := by ring
        have k2 : 2 * (∑ j, wP j ^ 2) / (r : ℝ) = 2 * (∑ j, wP j ^ 2) * (1 / r) := by ring
        rw [k1, k2]
        exact add_le_add (mul_le_mul_of_nonneg_left e1 (by positivity))
          (mul_le_mul_of_nonneg_left e2 (by positivity))
    _ = 2 * L / ((b + r : ℕ) : ℝ) := by
        have hs := sum_split (fun t => t ^ 2) w
        try simp only at hs
        rw [hw] at hs
        have : ∑ j, wV j ^ 2 + ∑ j, wP j ^ 2 = 1 := hs.symm
        rw [← add_mul, ← mul_add, this]; ring

lemma unit_sq_le {ι : Type} [Fintype ι] (z : ι → ℝ) : ∑ j, unitF53 z j ^ 2 ≤ 1 := by
  unfold unitF53
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [div_pow, one_pow, Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  rcases eq_or_ne (∑ j, z j ^ 2) 0 with h | h
  · rw [h]; simp
  · rw [one_div_mul_cancel h]

lemma int_unit_comp {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ] {m : ℕ}
    (G : (Fin m → ℝ) → ℝ) (hG : Continuous G) (f : α → (Fin m → ℝ)) (hf : Measurable f) :
    Integrable (fun x => G (unitF53 (f x))) μ := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin m => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hG.norm.continuousOn
  apply Integrable.of_bound (hG.measurable.comp
    ((BstLean.Part53.measurable_unitF (ι := Fin m)).comp hf)).aestronglyMeasurable C
  filter_upwards [] with x
  apply hC
  apply Set.mem_image_of_mem
  have hs := unit_sq_le (f x)
  constructor <;> intro j <;> simp only [Function.comp_apply]
  · have hj := Finset.single_le_sum (fun i _ => sq_nonneg (unitF53 (f x) i)) (Finset.mem_univ j)
    nlinarith [sq_nonneg (unitF53 (f x) j + 1)]
  · have hj := Finset.single_le_sum (fun i _ => sq_nonneg (unitF53 (f x) i)) (Finset.mem_univ j)
    nlinarith [sq_nonneg (unitF53 (f x) j - 1)]

private lemma block_p4 {m : ℕ} (z : Fin m → ℝ) (hz : radF53 z ^ 2 ≤ 1) :
    ∑ j, z j ^ 4 ≤ p4 (unitF53 z) := by
  have hzu : ∀ j, z j = radF53 z * unitF53 z j := fun j => by
    have := congrFun (rad_smul_unit z) j
    simp only [Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  unfold p4
  simp_rw [hzu, mul_pow]
  rw [← Finset.mul_sum]
  have h4 : radF53 z ^ 4 ≤ 1 := by
    have : radF53 z ^ 4 = (radF53 z ^ 2) ^ 2 := by ring
    rw [this]; nlinarith [sq_nonneg (radF53 z)]
  have hs : 0 ≤ ∑ j, unitF53 z j ^ 4 := Finset.sum_nonneg (fun _ _ => by positivity)
  nlinarith

/-- **The `p₄` moments of the two-subspace tilt**, uniformly in `c`. -/
theorem f1_p4 (hb : 1 ≤ b) (hr : 1 ≤ r) {L : ℝ} (hLb : ((b + r : ℕ) : ℝ) ≤ L * b)
    (hLr : ((b + r : ℕ) : ℝ) ≤ L * r) (c : ℝ) (q : ℕ) (hq : 1 ≤ q) :
    ∫ x, p4 x ^ q ∂f1Tilt b r c ≤
      2 ^ q * ((4 * q - 1).doubleFactorial : ℝ) * L ^ q / ((b + r : ℕ) : ℝ) ^ q := by
  have hbr : 1 ≤ b + r := by omega
  have hsph := f1_sph (b := b) (r := r) hbr c
  let := hsph.prob
  let GV : (Fin b → ℝ) → ℝ := fun y => p4 y ^ q
  let GP : (Fin r → ℝ) → ℝ := fun y => p4 y ^ q
  have hGV : Continuous GV := by simp only [GV]; unfold p4; fun_prop
  have hGP : Continuous GP := by simp only [GP]; unfold p4; fun_prop
  have hp4n : ∀ {m : ℕ} (y : Fin m → ℝ), 0 ≤ p4 y := fun y => Finset.sum_nonneg (fun _ _ => by positivity)
  have hpt : ∀ᵐ x ∂f1Tilt b r c, p4 x ^ q ≤
      2 ^ (q - 1) * (GV (unitF53 (xV x)) + GP (unitF53 (xP x))) := by
    filter_upwards [hsph.sphere] with x hx
    have hs : p4 x = ∑ j, xV x j ^ 4 + ∑ j, xP x j ^ 4 := sum_split (fun t => t ^ 4) x
    have h1 := block_p4 (xV x) (radV_le hx)
    have h2 := block_p4 (xP x) (radP_le hx)
    have hle : p4 x ≤ p4 (unitF53 (xV x)) + p4 (unitF53 (xP x)) := by rw [hs]; linarith
    calc p4 x ^ q ≤ (p4 (unitF53 (xV x)) + p4 (unitF53 (xP x))) ^ q :=
          pow_le_pow_left₀ (hp4n x) hle q
      _ ≤ _ := add_pow_le (hp4n _) (hp4n _) q
  have hiV := int_unit_comp (μ := f1Tilt b r c) GV hGV xV measurable_xV
  have hiP := int_unit_comp (μ := f1Tilt b r c) GP hGP xP measurable_xP
  have hS := BstLean.Part53.lemmaS53
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hnR : (0 : ℝ) < ((b + r : ℕ) : ℝ) := by exact_mod_cast hbr
  have hL0 : 0 < L := by
    by_contra h; push Not at h
    have : L * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hbR.le
    linarith
  have e1 : 1 / (b : ℝ) ^ q ≤ L ^ q / ((b + r : ℕ) : ℝ) ^ q := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
    exact pow_le_pow_left₀ hnR.le hLb q
  have e2 : 1 / (r : ℝ) ^ q ≤ L ^ q / ((b + r : ℕ) : ℝ) ^ q := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← mul_pow]
    exact pow_le_pow_left₀ hnR.le hLr q
  have hD : (0 : ℝ) ≤ ((4 * q - 1).doubleFactorial : ℝ) := Nat.cast_nonneg _
  have hp4c : Continuous (fun x : Fin (b + r) → ℝ => p4 x ^ q) := by unfold p4; fun_prop
  calc ∫ x, p4 x ^ q ∂f1Tilt b r c
      ≤ ∫ x, 2 ^ (q - 1) * (GV (unitF53 (xV x)) + GP (unitF53 (xP x))) ∂f1Tilt b r c :=
        integral_mono_ae (sphere_integrable hsph hp4c) ((hiV.add hiP).const_mul _) hpt
    _ = 2 ^ (q - 1) * ((∫ y, p4 y ^ q ∂uniformSphere b) + ∫ y, p4 y ^ q ∂uniformSphere r) := by
        rw [integral_const_mul, integral_add hiV hiP,
          f1_blockV hb c GV hGV (fun y => pow_nonneg (hp4n y) q),
          f1_blockP hr c GP hGP (fun y => pow_nonneg (hp4n y) q)]
    _ ≤ 2 ^ (q - 1) * (((4 * q - 1).doubleFactorial : ℝ) / (b : ℝ) ^ q +
          ((4 * q - 1).doubleFactorial : ℝ) / (r : ℝ) ^ q) := by
        gcongr
        · exact hS b hb q hq
        · exact hS r hr q hq
    _ ≤ 2 ^ (q - 1) * (((4 * q - 1).doubleFactorial : ℝ) * (L ^ q / ((b + r : ℕ) : ℝ) ^ q) +
          ((4 * q - 1).doubleFactorial : ℝ) * (L ^ q / ((b + r : ℕ) : ℝ) ^ q)) := by
        rw [div_eq_mul_one_div _ ((b : ℝ) ^ q), div_eq_mul_one_div _ ((r : ℝ) ^ q)]
        gcongr
    _ = 2 ^ q * ((4 * q - 1).doubleFactorial : ℝ) * L ^ q / ((b + r : ℕ) : ℝ) ^ q := by
        obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
        simp only [Nat.add_sub_cancel, pow_succ]
        ring

/-- The trace-moment weight of the two-subspace tilt, `wF L i = 4^i·(8i−1)!!·L^{2i}`. -/
noncomputable def wF (L : ℝ) (i : ℕ) : ℝ := 4 ^ i * ((8 * i - 1).doubleFactorial : ℝ) * L ^ (2 * i)

/-- **The trace moments of the two-subspace tilt**, uniformly in `c`. -/
theorem f1_dev (hb : 1 ≤ b) (hr : 1 ≤ r) {L : ℝ} (hLb : ((b + r : ℕ) : ℝ) ≤ L * b)
    (hLr : ((b + r : ℕ) : ℝ) ≤ L * r) (c : ℝ) (d i : ℕ) (hi : 1 ≤ i) :
    ∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂f1Tilt b r c ≤
      wF L i * (d : ℝ) ^ (2 * i) / ((b + r : ℕ) : ℝ) ^ (2 * i) := by
  have hbr : 1 ≤ b + r := by omega
  have hsph := f1_sph (b := b) (r := r) hbr c
  let := hsph.prob
  have hU := BstLean.Part53.lemmaU53 d
  have hδc : Continuous (fun x : Fin (b + r) → ℝ => (phiSq d x - c0 d) ^ (2 * i)) :=
    (BstLean.Part53.FloorCorrection.phiSq_continuous.sub continuous_const).pow _
  have hp4c : Continuous (fun x : Fin (b + r) → ℝ => p4 x ^ (2 * i)) := by unfold p4; fun_prop
  have hmono : ∫ x, (phiSq d x - c0 d) ^ (2 * i) ∂f1Tilt b r c ≤
      ∫ x, (d : ℝ) ^ (2 * i) * p4 x ^ (2 * i) ∂f1Tilt b r c := by
    apply integral_mono_ae (sphere_integrable hsph hδc) (sphere_integrable hsph (by fun_prop))
    filter_upwards [hsph.sphere] with x hx
    obtain ⟨h0, h1⟩ := hU (b + r) x hx
    rw [← mul_pow]
    exact pow_le_pow_left₀ h0 h1 _
  rw [integral_const_mul] at hmono
  have hp := f1_p4 hb hr hLb hLr c (2 * i) (by omega)
  refine hmono.trans ((mul_le_mul_of_nonneg_left hp (by positivity)).trans (le_of_eq ?_))
  unfold wF
  rw [show 4 * (2 * i) - 1 = 8 * i - 1 by omega, pow_mul (2 : ℝ) 2 i]
  norm_num
  ring

/-- **Two-subspace tilts satisfy `Good72`**, uniformly in `c`, for every `d ≥ 1` and `k`. -/
theorem f1_good (hb : 1 ≤ b) (hr : 1 ≤ r) {L : ℝ} (hLb : ((b + r : ℕ) : ℝ) ≤ L * b)
    (hLr : ((b + r : ℕ) : ℝ) ≤ L * r) (c : ℝ) (d k : ℕ) (hd : 1 ≤ d) :
    Good72 (b + r) d k (f1Tilt b r c) (wF L) (Fov d (2 * L)) (2 * L) := by
  have hbr : 1 ≤ b + r := by omega
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hnR : (0 : ℝ) < ((b + r : ℕ) : ℝ) := by exact_mod_cast hbr
  have hL0 : 0 < L := by
    by_contra h; push Not at h
    have : L * b ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h hbR.le
    linarith
  apply good_of_ov (f1_sph hbr c) d k hd (wF L) (2 * L)
  · have : Mean (f1Tilt b r c) = 0 := by unfold Mean; simp [f1_mean_zero hbr c]
    rw [this]; positivity
  · intro w hw; exact f1_dir hb hr hLb hLr c w hw
  · intro i hi _; exact f1_dev hb hr hLb hLr c d i hi

end BstLean.Part72
