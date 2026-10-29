import BstLean.Part58Defs
import BstLean.Part56MomProg_Sphere
import BstLean.Part56PropD_Bingham

/-! Exact perpendicular moments for the axial approximation of `κ`. -/

namespace BstLean.Part58.Kappa

open MeasureTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part56

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

theorem sphere_linear_even {k : ℕ} (hk : 1 ≤ k) (a : Fin k → ℝ) (m : ℕ) :
    (∫ x, (∑ i, a i * x i) ^ (2 * m) ∂uniformSphere k) =
      (∑ i, a i ^ 2) ^ m * BstLean.Part29.gaussMom (2 * m) /
        BstLean.Part36.rhoD k m := by
  classical
  let R : ℝ := Real.sqrt (∑ i, a i ^ 2)
  have hR : R ^ 2 = ∑ i, a i ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)
  by_cases hzero : (∑ i, a i ^ 2) = 0
  · have ha : ∀ i, a i = 0 := by
      intro i
      have hi := Finset.single_le_sum (fun j _ => sq_nonneg (a j)) (Finset.mem_univ i)
      rw [hzero] at hi
      nlinarith [sq_nonneg (a i)]
    cases m with
    | zero =>
      let _ := BstLean.Part29.uniformSphere_isProbability k hk
      simp [BstLean.Part29.gaussMom, BstLean.Part36.rhoD]
    | succ m => simp [ha, hzero]
  · have hpos : 0 < ∑ i, a i ^ 2 := lt_of_le_of_ne
      (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hzero)
    have hRpos : 0 < R := Real.sqrt_pos.mpr hpos
    let v : Fin k → ℝ := fun i => a i / R
    have hv : UnitV v := by
      unfold UnitV
      simp only [v, div_pow, ← Finset.sum_div, ← hR]
      exact div_self (pow_ne_zero 2 hRpos.ne')
    have he (x : Fin k → ℝ) : (∑ i, a i * x i) = R * ∑ i, v i * x i := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      dsimp [v]
      field_simp
    simp_rw [he, mul_pow]
    rw [integral_const_mul, BstLean.Part56.MomProg.sphere_directional_moment hk v hv m]
    rw [show R ^ (2 * m) = (∑ i, a i ^ 2) ^ m by rw [pow_mul, hR]]
    ring

theorem sphere_linear_odd {k : ℕ} (a : Fin k → ℝ) (m : ℕ) :
    (∫ x, (∑ i, a i * x i) ^ (2 * m + 1) ∂uniformSphere k) = 0 := by
  let R : EuclideanSpace ℝ (Fin k) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin k) :=
    LinearIsometryEquiv.neg ℝ
  have hR : ∀ x, R (R x) = x := by intro x; simp [R]
  have hm := BstLean.Part56.MomProg.uniformSphere_involution R hR
  have h : (∫ x, (∑ i, a i * x i) ^ (2 * m + 1) ∂uniformSphere k) =
      -(∫ x, (∑ i, a i * x i) ^ (2 * m + 1) ∂uniformSphere k) := by
    conv_lhs => rw [← hm]
    rw [integral_map (by fun_prop)
      ((by fun_prop : Continuous (fun x : Fin k → ℝ => (∑ i, a i * x i) ^
        (2 * m + 1))).aestronglyMeasurable)]
    change (∫ x, (∑ i, a i * (-x i)) ^ (2 * m + 1) ∂uniformSphere k) = _
    simp only [mul_neg, Finset.sum_neg_distrib]
    have ho : Odd (2 * m + 1) := ⟨m, by omega⟩
    simp only [ho.neg_pow, integral_neg]
  linarith

variable {k : ℕ}

noncomputable def angularLaw
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1)))) :
    Measure (Fin (k + 1) → ℝ) := (uniformSphere k).map (tailReconstruct b)

noncomputable def rowTail
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (i : Fin (k + 1)) : Fin k → ℝ := fun l => b l.succ i

theorem tailReconstruct_linear
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (z : Fin k → ℝ) (i : Fin (k + 1)) :
    tailReconstruct b z i = ∑ l, rowTail b i l * z l := by
  have h := congrArg (fun q : EuclideanSpace ℝ (Fin (k + 1)) => q i)
    (b.sum_repr_symm (WithLp.toLp 2 (Fin.cons 0 z)))
  simp only [Fin.sum_univ_succ, Fin.cons_zero, zero_smul, zero_add,
    Fin.cons_succ] at h
  simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul] at h
  exact h.symm.trans (by apply Finset.sum_congr rfl; intro l hl; dsimp [rowTail]; ring)

theorem rowTail_sq
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (v : Fin (k + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v) (i : Fin (k + 1)) :
    (∑ l, rowTail b i l ^ 2) = 1 - v i ^ 2 := by
  have h := b.sum_sq_inner_right (EuclideanSpace.single i (1 : ℝ))
  simp only [EuclideanSpace.inner_single_right, star_trivial, one_mul,
    PiLp.norm_single, norm_one, one_pow, Fin.sum_univ_succ, hb] at h
  change v i ^ 2 + ∑ l, rowTail b i l ^ 2 = 1 at h
  linarith

theorem angular_coordinate_even (hk : 1 ≤ k)
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (v : Fin (k + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v)
    (i : Fin (k + 1)) (m : ℕ) :
    (∫ w, w i ^ (2 * m) ∂angularLaw b) =
      (1 - v i ^ 2) ^ m * BstLean.Part29.gaussMom (2 * m) /
        BstLean.Part36.rhoD k m := by
  rw [angularLaw, integral_map (by unfold tailReconstruct basisReconstruct; fun_prop)
    ((by fun_prop : Continuous (fun w : Fin (k + 1) → ℝ => w i ^ (2 * m))).aestronglyMeasurable)]
  simp_rw [tailReconstruct_linear]
  rw [sphere_linear_even hk, rowTail_sq b v hb]

theorem angular_coordinate_odd
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (i : Fin (k + 1)) (m : ℕ) :
    (∫ w, w i ^ (2 * m + 1) ∂angularLaw b) = 0 := by
  rw [angularLaw, integral_map (by unfold tailReconstruct basisReconstruct; fun_prop)
    ((by fun_prop : Continuous (fun w : Fin (k + 1) → ℝ => w i ^
      (2 * m + 1))).aestronglyMeasurable)]
  simp_rw [tailReconstruct_linear]
  exact sphere_linear_odd _ m

theorem angularLaw_sph (hk : 1 ≤ k)
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1)))) :
    BstLean.Part40.SphLaw (k + 1) (angularLaw b) := by
  let _ := BstLean.Part29.uniformSphere_isProbability k hk
  have hT : Measurable (tailReconstruct b) := by
    unfold tailReconstruct basisReconstruct
    fun_prop
  constructor
  · unfold angularLaw
    infer_instance
  · rw [angularLaw, ae_map_iff hT.aemeasurable (by
      exact measurableSet_eq_fun (by fun_prop) measurable_const)]
    filter_upwards [BstLean.Part29.uniformSphere_ae_sphere k] with z hz
    exact (tailReconstruct_sumsq b z).trans hz

theorem tailReconstruct_orthogonal
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (v : Fin (k + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v) (z : Fin k → ℝ) :
    (∑ i, v i * tailReconstruct b z i) = 0 := by
  have h : inner ℝ (b 0) (b.repr.symm (WithLp.toLp 2 (Fin.cons 0 z))) = 0 := by
    rw [← b.repr.inner_map_map, b.repr_self, b.repr.apply_symm_apply,
      EuclideanSpace.inner_single_left]
    simp
  simpa only [hb, tailReconstruct, basisReconstruct, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, mul_comm] using h

theorem angularLaw_orthogonal
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (v : Fin (k + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v) :
    ∀ᵐ w ∂angularLaw b, (∑ i, v i * w i) = 0 := by
  have hT : Measurable (tailReconstruct b) := by
    unfold tailReconstruct basisReconstruct
    fun_prop
  rw [angularLaw, ae_map_iff hT.aemeasurable (by
    exact measurableSet_eq_fun (by fun_prop) measurable_const)]
  exact ae_of_all _ (tailReconstruct_orthogonal b v hb)

theorem angular_coordinate_two (hk : 1 ≤ k)
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (v : Fin (k + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v) (i : Fin (k + 1)) :
    (∫ w, w i ^ 2 ∂angularLaw b) = (1 - v i ^ 2) / k := by
  have h := angular_coordinate_even hk b v hb i 1
  norm_num [BstLean.Part29.gaussMom, BstLean.Part36.rhoD] at h
  exact h

theorem angular_coordinate_four (hk : 1 ≤ k)
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (v : Fin (k + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v) (i : Fin (k + 1)) :
    (∫ w, w i ^ 4 ∂angularLaw b) = 3 * (1 - v i ^ 2) ^ 2 / ((k : ℝ) * (k + 2)) := by
  have h := angular_coordinate_even hk b v hb i 2
  norm_num [BstLean.Part29.gaussMom, BstLean.Part36.rhoD,
    Finset.prod_range_succ] at h
  rw [h]
  ring

theorem perpDir_law_eq (hk : 1 ≤ k)
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (v : Fin (k + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v) :
    (stdGauss (Fin (k + 1))).map (perpDir v) = angularLaw b := by
  apply Measure.ext_of_lintegral
  intro F hF
  have hP : Measurable (perpDir v) := by unfold perpDir; fun_prop
  have hT : Measurable (tailReconstruct b) := by unfold tailReconstruct basisReconstruct; fun_prop
  rw [angularLaw, lintegral_map hF hP, lintegral_map hF hT,
    perpDir_lintegral_tail b v hb F hF]
  exact (uniformSphere_lintegral_gauss k hk
    (fun z => F (tailReconstruct b z)) (hF.comp hT)).symm

noncomputable def axialPoint (v : Fin (k + 1) → ℝ)
    (p : (ℝ × (Fin k → ℝ)) × (Fin (k + 1) → ℝ)) : Fin (k + 1) → ℝ :=
  polarPoint v p.2 p.1.1 (BstLean.Part53.radF53 p.1.2)

theorem measurable_axialPoint (v : Fin (k + 1) → ℝ) : Measurable (axialPoint v) := by
  unfold axialPoint polarPoint axialS axialR BstLean.Part53.radF53
  fun_prop

theorem lawRK_eq_axial_angular_map (hk : 1 ≤ k)
    (b : OrthonormalBasis (Fin (k + 1)) ℝ (EuclideanSpace ℝ (Fin (k + 1))))
    (v : Fin (k + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v) (t : ℝ) :
    lawRK (k + 1) t v = ((axialMeasure t v).prod (angularLaw b)).map (axialPoint v) := by
  let _ := (angularLaw_sph hk b).prob
  let _ := axialMeasure_probability b v hb t
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lawRK_eq_polar_map b v hb t, lintegral_map hF (measurable_polarState v),
    lintegral_map hF (measurable_axialPoint v)]
  rw [lintegral_prod (fun p => F (polarState v p))
    (hF.comp (measurable_polarState v)).aemeasurable,
    lintegral_prod (fun p => F (axialPoint v p))
    (hF.comp (measurable_axialPoint v)).aemeasurable]
  apply lintegral_congr
  intro p
  have hFp : Measurable (fun w => F (axialPoint v (p, w))) := by
    exact hF.comp ((measurable_axialPoint v).comp (measurable_const.prodMk measurable_id))
  have hP : Measurable (perpDir v) := by unfold perpDir; fun_prop
  change (∫⁻ g, F (axialPoint v (p, perpDir v g)) ∂stdGauss (Fin (k + 1))) = _
  rw [← lintegral_map hFp hP, perpDir_law_eq hk b v hb]

end BstLean.Part58.Kappa
