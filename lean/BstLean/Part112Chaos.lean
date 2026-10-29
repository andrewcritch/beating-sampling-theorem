import BstLean.Part112Defs

/-!
# Part 112, helper `Chaos`: the first chaos is all of the part of order `c²`

`chaosLimit : ChaosLimit`. Route: the Cameron–Martin shift formula for the standard Gaussian on
`ι → ℝ` (`cm_integral`), the exact second moment of `e^{w·z − |w|²/2} − 1 − w·z`, the projection
inequality for `1, x_i`, and `∫ T_c h · x_i = c ∫ h · x_i` (rotation invariance).

No `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part112

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part105

section CM

variable {ι : Type} [Fintype ι]

/-- `w · z`. -/
noncomputable def dw (w z : ι → ℝ) : ℝ := ∑ i, w i * z i

/-- `|w|²`. -/
noncomputable def nsq (w : ι → ℝ) : ℝ := ∑ i, w i ^ 2

/-- The Cameron–Martin density `exp(w·z − |w|²/2)`. -/
noncomputable def rhoCM (w z : ι → ℝ) : ℝ := Real.exp (dw w z - nsq w / 2)

lemma rhoCM_prod (w z : ι → ℝ) :
    rhoCM w z = ∏ i, Real.exp (w i * z i - w i ^ 2 / 2) := by
  unfold rhoCM dw nsq
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.sum_sub_distrib, Finset.sum_div]

lemma measurable_dw (w : ι → ℝ) : Measurable (dw w) := by
  unfold dw
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).const_mul _

lemma measurable_rhoCM (w : ι → ℝ) : Measurable (rhoCM w) := by
  unfold rhoCM
  exact ((measurable_dw w).sub_const _).exp

lemma rhoCM_pos (w z : ι → ℝ) : 0 < rhoCM w z := Real.exp_pos _

lemma gauss1_shift (w : ℝ) :
    gaussianReal w 1 = (gaussianReal 0 1).withDensity
      (fun x => ENNReal.ofReal (Real.exp (w * x - w ^ 2 / 2))) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero, gaussianReal_of_var_ne_zero _ one_ne_zero,
    ← withDensity_mul _ (measurable_gaussianPDF 0 1) (by fun_prop)]
  congr 1
  funext x
  simp only [Pi.mul_apply, gaussianPDF_def]
  rw [← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  congr 1
  rw [gaussianPDFReal_def, gaussianPDFReal_def]
  simp only [NNReal.coe_one, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

lemma g1_int (w : ℝ) :
    Integrable (fun x : ℝ => Real.exp (w * x - w ^ 2 / 2)) (gaussianReal 0 1) := by
  simp_rw [Real.exp_sub]
  exact (integrable_exp_mul_gaussianReal w).div_const _

/-- **Cameron–Martin**, as an identity of measures. -/
lemma cm_measure (w : ι → ℝ) :
    (stdGauss ι).map (fun z => z + w) =
      (stdGauss ι).withDensity (fun z => ENNReal.ofReal (rhoCM w z)) := by
  classical
  unfold stdGauss
  have : ∀ i, SigmaFinite ((gaussianReal 0 1).map (fun x => x + w i)) := fun i => by
    rw [gaussianReal_map_add_const]; infer_instance
  have h1 : (Measure.pi fun _ : ι => gaussianReal 0 1).map (fun z => z + w) =
      Measure.pi (fun i => gaussianReal (w i) 1) := by
    have := Measure.pi_map_pi (μ := fun _ : ι => gaussianReal 0 1) (f := fun i x => x + w i)
      (fun i => by fun_prop)
    simp only [gaussianReal_map_add_const, zero_add] at this
    exact this
  rw [h1]
  refine Measure.pi_eq fun s hs => ?_
  set g : ι → ℝ → ℝ := fun i x => (s i).indicator (fun x => Real.exp (w i * x - w i ^ 2 / 2)) x
    with hg
  have hgi : ∀ i, Integrable (g i) (gaussianReal 0 1) := fun i => (g1_int (w i)).indicator (hs i)
  have hg0 : ∀ i x, 0 ≤ g i x := fun i x => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) _
  have hpt : ∀ z : ι → ℝ, (Set.univ.pi s).indicator (fun z => ENNReal.ofReal (rhoCM w z)) z =
      ENNReal.ofReal (∏ i, g i (z i)) := by
    intro z
    by_cases hz : z ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hz, rhoCM_prod]
      congr 1
      refine Finset.prod_congr rfl fun i _ => ?_
      simp only [hg]
      rw [Set.indicator_of_mem (hz i (Set.mem_univ i))]
    · rw [Set.indicator_of_notMem hz]
      simp only [Set.mem_univ_pi, not_forall] at hz
      obtain ⟨i, hi⟩ := hz
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hg, hi])]
      simp
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  simp_rw [hpt]
  rw [← ofReal_integral_eq_lintegral_ofReal (Integrable.fintype_prod hgi)
    (ae_of_all _ fun z => Finset.prod_nonneg fun i _ => hg0 i _),
    integral_fintype_prod_eq_prod, ENNReal.ofReal_prod_of_nonneg (fun i _ => integral_nonneg (hg0 i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ofReal_integral_eq_lintegral_ofReal (hgi i) (ae_of_all _ (hg0 i)), gauss1_shift (w i),
    withDensity_apply _ (hs i), ← lintegral_indicator (hs i)]
  refine lintegral_congr fun x => ?_
  simp only [hg]
  by_cases hx : x ∈ s i <;> simp [hx]

/-- **Cameron–Martin**, as an identity of integrals. -/
lemma cm_integral (w : ι → ℝ) (G : (ι → ℝ) → ℝ) (hG : Measurable G) :
    ∫ z, G (z + w) ∂stdGauss ι = ∫ z, rhoCM w z * G z ∂stdGauss ι := by
  have hm : Measurable (fun z : ι → ℝ => z + w) := measurable_id.add measurable_const
  rw [← integral_map hm.aemeasurable hG.aestronglyMeasurable, cm_measure,
    integral_withDensity_eq_integral_toReal_smul (measurable_rhoCM w).ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp [ENNReal.toReal_ofReal (rhoCM_pos w z).le]

end CM

/-! ## Moments -/

section Mom

variable {ι : Type} [Fintype ι]

lemma int_rho (w : ι → ℝ) : Integrable (rhoCM w) (stdGauss ι) := by
  have : rhoCM w = fun z : ι → ℝ => ∏ i, Real.exp (w i * z i - w i ^ 2 / 2) :=
    funext (rhoCM_prod w)
  rw [this]
  unfold stdGauss
  exact Integrable.fintype_prod (f := fun i x => Real.exp (w i * x - w i ^ 2 / 2))
    (fun i => g1_int (w i))

lemma dw_two (w z : ι → ℝ) : dw ((2 : ℝ) • w) z = 2 * dw w z := by
  simp only [dw, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma nsq_two (w : ι → ℝ) : nsq ((2 : ℝ) • w) = 4 * nsq w := by
  simp only [nsq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma rho_sq (w z : ι → ℝ) : rhoCM w z ^ 2 = Real.exp (nsq w) * rhoCM ((2 : ℝ) • w) z := by
  unfold rhoCM
  rw [dw_two, nsq_two, ← Real.exp_add, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma int_rho_sq (w : ι → ℝ) : Integrable (fun z => rhoCM w z ^ 2) (stdGauss ι) := by
  simp_rw [rho_sq]
  exact (int_rho _).const_mul _

lemma memLp_rho (w : ι → ℝ) : MemLp (rhoCM w) 2 (stdGauss ι) :=
  (memLp_two_iff_integrable_sq (measurable_rhoCM w).aestronglyMeasurable).2 (int_rho_sq w)

lemma memLp_coord (i : ι) : MemLp (fun z : ι → ℝ => z i) 2 (stdGauss ι) :=
  (memLp_two_iff_integrable_sq (measurable_pi_apply i).aestronglyMeasurable).2
    (BstLean.Part108.coordPow_int i 2)

lemma int_coord (i : ι) : Integrable (fun z : ι → ℝ => z i) (stdGauss ι) := by
  simpa using BstLean.Part108.coordPow_int i 1

lemma integral_coord (i : ι) : ∫ z : ι → ℝ, z i ∂stdGauss ι = 0 := by
  have := BstLean.Part108.coordPow_integral i 1
  simpa [BstLean.Part29.gaussMom] using this

lemma memLp_dw (w : ι → ℝ) : MemLp (dw w) 2 (stdGauss ι) := by
  unfold dw
  exact memLp_finsetSum _ fun i _ => (memLp_coord i).const_mul (w i)

lemma int_dw (w : ι → ℝ) : Integrable (dw w) (stdGauss ι) :=
  (memLp_dw w).integrable (by norm_num)

lemma integral_dw (w : ι → ℝ) : ∫ z, dw w z ∂stdGauss ι = 0 := by
  unfold dw
  rw [integral_finsetSum _ fun i _ => (int_coord i).const_mul (w i)]
  simp [integral_const_mul, integral_coord]

lemma integral_dw_mul (w v : ι → ℝ) : ∫ z, dw w z * dw v z ∂stdGauss ι = ∑ i, w i * v i := by
  classical
  have h := BstLean.Part107.wick2 (ι := ι) w v
  have e : ∀ a z : ι → ℝ, BstLean.Part107.lin a z = dw a z := fun a z => by
    simp only [BstLean.Part107.lin, dw]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  simp_rw [e] at h
  rw [h]
  rfl

lemma integral_dw_sq (w : ι → ℝ) : ∫ z, dw w z ^ 2 ∂stdGauss ι = nsq w := by
  have := integral_dw_mul w w
  simp_rw [← pow_two] at this
  exact this

lemma integral_rho (w : ι → ℝ) : ∫ z, rhoCM w z ∂stdGauss ι = 1 := by
  have := cm_integral w (fun _ => (1 : ℝ)) measurable_const
  simpa using this.symm

lemma dw_add (w z v : ι → ℝ) : dw w (z + v) = dw w z + dw w v := by
  simp only [dw, Pi.add_apply, mul_add, Finset.sum_add_distrib]

lemma dw_self (w : ι → ℝ) : dw w w = nsq w := by
  simp only [dw, nsq, pow_two]

lemma integral_rho_dw (w : ι → ℝ) : ∫ z, rhoCM w z * dw w z ∂stdGauss ι = nsq w := by
  rw [← cm_integral w (dw w) (measurable_dw w)]
  simp_rw [dw_add, dw_self]
  rw [integral_add (int_dw w) (integrable_const _), integral_dw]
  simp

/-- `q_w(z) = e^{w·z − |w|²/2} − 1 − w·z`. -/
noncomputable def qCM (w z : ι → ℝ) : ℝ := rhoCM w z - 1 - dw w z

lemma memLp_q (w : ι → ℝ) : MemLp (qCM w) 2 (stdGauss ι) :=
  ((memLp_rho w).sub (memLp_const 1)).sub (memLp_dw w)

lemma integral_q_sq (w : ι → ℝ) :
    ∫ z, qCM w z ^ 2 ∂stdGauss ι = Real.exp (nsq w) - 1 - nsq w := by
  have i1 := int_rho_sq w
  have i2 : Integrable (fun _ : ι → ℝ => (1 : ℝ)) (stdGauss ι) := integrable_const _
  have i3 : Integrable (fun z => dw w z ^ 2) (stdGauss ι) := (memLp_dw w).integrable_sq
  have i4 : Integrable (fun z => 2 * rhoCM w z) (stdGauss ι) := (int_rho w).const_mul 2
  have i5 : Integrable (fun z => 2 * (rhoCM w z * dw w z)) (stdGauss ι) :=
    ((memLp_rho w).integrable_mul (memLp_dw w)).const_mul 2
  have i6 : Integrable (fun z => 2 * dw w z) (stdGauss ι) := (int_dw w).const_mul 2
  have e : (fun z => qCM w z ^ 2) = fun z =>
      rhoCM w z ^ 2 + 1 + dw w z ^ 2 - 2 * rhoCM w z - 2 * (rhoCM w z * dw w z) + 2 * dw w z := by
    funext z; unfold qCM; ring
  have j2 : Integrable (fun z => rhoCM w z ^ 2 + 1) (stdGauss ι) := i1.add i2
  have j3 : Integrable (fun z => rhoCM w z ^ 2 + 1 + dw w z ^ 2) (stdGauss ι) := j2.add i3
  have j4 : Integrable (fun z => rhoCM w z ^ 2 + 1 + dw w z ^ 2 - 2 * rhoCM w z)
      (stdGauss ι) := j3.sub i4
  have j5 : Integrable (fun z => rhoCM w z ^ 2 + 1 + dw w z ^ 2 - 2 * rhoCM w z -
      2 * (rhoCM w z * dw w z)) (stdGauss ι) := j4.sub i5
  rw [e, integral_add j5 i6, integral_sub j4 i5, integral_sub j3 i4,
    integral_add j2 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_rho, integral_rho_dw, integral_dw, integral_dw_sq]
  simp_rw [rho_sq]
  rw [integral_const_mul, integral_rho]
  simp
  ring

end Mom

/-! ## The remainder, the projection inequality and the first-chaos coefficients of `T_c h` -/

section Main

variable {ι : Type} [Fintype ι]

lemma bm_memLp {G : (ι → ℝ) → ℝ} (hG : BM G) : MemLp G 2 (stdGauss ι) := by
  obtain ⟨M, hM⟩ := hG.bdd
  exact MemLp.of_bound hG.meas.aestronglyMeasurable M (ae_of_all _ fun x => by
    simpa [Real.norm_eq_abs] using hM x)

/-- The remainder after the terms of order `0` and `1` of the Cameron–Martin shift. -/
lemma shift_remainder {G : (ι → ℝ) → ℝ} (hG : Measurable G) {M : ℝ} (hM : ∀ x, |G x| ≤ M)
    (w : ι → ℝ) :
    (∫ z, G (z + w) ∂stdGauss ι - ∫ z, G z ∂stdGauss ι -
        ∑ i, w i * ∫ z, G z * z i ∂stdGauss ι) ^ 2 ≤
      M ^ 2 * (Real.exp (nsq w) - 1 - nsq w) := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  have bG : BM G := ⟨hG, M, hM⟩
  have mG := bm_memLp bG
  have iG : Integrable G (stdGauss ι) := bG.integrable _
  have iρG : Integrable (fun z => G z * rhoCM w z) (stdGauss ι) :=
    mG.integrable_mul (memLp_rho w)
  have iGd : Integrable (fun z => G z * dw w z) (stdGauss ι) :=
    mG.integrable_mul (memLp_dw w)
  have iGc : ∀ i, Integrable (fun z : ι → ℝ => G z * z i) (stdGauss ι) := fun i =>
    mG.integrable_mul (memLp_coord i)
  have h1 : ∫ z, G (z + w) ∂stdGauss ι = ∫ z, G z * rhoCM w z ∂stdGauss ι := by
    rw [cm_integral w G hG]
    exact integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  have h2 : ∑ i, w i * ∫ z, G z * z i ∂stdGauss ι = ∫ z, G z * dw w z ∂stdGauss ι := by
    have e : (fun z => G z * dw w z) = fun z => ∑ i, w i * (G z * z i) := by
      funext z
      simp only [dw, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, integral_finsetSum _ fun i _ => (iGc i).const_mul (w i)]
    simp_rw [integral_const_mul]
  have h3 : ∫ z, G (z + w) ∂stdGauss ι - ∫ z, G z ∂stdGauss ι -
      ∑ i, w i * ∫ z, G z * z i ∂stdGauss ι = ∫ z, G z * qCM w z ∂stdGauss ι := by
    have iρG' : Integrable (fun z => G z * rhoCM w z - G z) (stdGauss ι) := iρG.sub iG
    rw [h1, h2, ← integral_sub iρG iG, ← integral_sub iρG' iGd]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [qCM]
    ring
  rw [h3]
  have mq := memLp_q w
  have mqa : MemLp (fun z => |qCM w z|) 2 (stdGauss ι) := mq.abs
  have iqa : Integrable (fun z => |qCM w z|) (stdGauss ι) := mqa.integrable (by norm_num)
  have hv := variance_nonneg (fun z => |qCM w z|) (stdGauss ι)
  rw [variance_eq_sub mqa] at hv
  have hv' : (∫ z, |qCM w z| ∂stdGauss ι) ^ 2 ≤ ∫ z, qCM w z ^ 2 ∂stdGauss ι := by
    have e : ∫ z, ((fun z => |qCM w z|) ^ 2) z ∂stdGauss ι = ∫ z, qCM w z ^ 2 ∂stdGauss ι :=
      integral_congr_ae (ae_of_all _ fun z => by simp)
    rw [e] at hv
    linarith
  have h4 : |∫ z, G z * qCM w z ∂stdGauss ι| ≤ M * ∫ z, |qCM w z| ∂stdGauss ι := by
    refine (abs_integral_le_integral_abs).trans ?_
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg (ae_of_all _ fun z => abs_nonneg _) (iqa.const_mul M)
      (ae_of_all _ fun z => ?_)
    simp only [abs_mul]
    exact mul_le_mul_of_nonneg_right (hM z) (abs_nonneg _)
  have h5 : 0 ≤ ∫ z, |qCM w z| ∂stdGauss ι := integral_nonneg fun z => abs_nonneg _
  rw [← integral_q_sq w]
  calc (∫ z, G z * qCM w z ∂stdGauss ι) ^ 2 = |∫ z, G z * qCM w z ∂stdGauss ι| ^ 2 :=
        (sq_abs _).symm
    _ ≤ (M * ∫ z, |qCM w z| ∂stdGauss ι) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) h4 2
    _ = M ^ 2 * (∫ z, |qCM w z| ∂stdGauss ι) ^ 2 := by ring
    _ ≤ M ^ 2 * ∫ z, qCM w z ^ 2 ∂stdGauss ι := mul_le_mul_of_nonneg_left hv' (sq_nonneg M)

/-- The projection inequality for the functions `1`, `x_i`. -/
lemma proj_ineq {F : (ι → ℝ) → ℝ} (hF : BM F) (α : ℝ) (b : ι → ℝ) :
    ∫ x, F x ^ 2 ∂stdGauss ι - (∫ x, F x ∂stdGauss ι) ^ 2 -
        ∑ i, (∫ x, F x * x i ∂stdGauss ι) ^ 2 ≤
      ∫ x, (F x - α - dw b x) ^ 2 ∂stdGauss ι := by
  have mF := bm_memLp hF
  have iF : Integrable F (stdGauss ι) := hF.integrable _
  have iFc : ∀ i, Integrable (fun z : ι → ℝ => F z * z i) (stdGauss ι) := fun i =>
    mF.integrable_mul (memLp_coord i)
  have i1 : Integrable (fun z => F z ^ 2) (stdGauss ι) := mF.integrable_sq
  have i2 : Integrable (fun _ : ι → ℝ => α ^ 2) (stdGauss ι) := integrable_const _
  have i3 : Integrable (fun z => dw b z ^ 2) (stdGauss ι) := (memLp_dw b).integrable_sq
  have i4 : Integrable (fun z => (2 * α) * F z) (stdGauss ι) := iF.const_mul _
  have i5 : Integrable (fun z => 2 * (F z * dw b z)) (stdGauss ι) :=
    (mF.integrable_mul (memLp_dw b)).const_mul 2
  have i6 : Integrable (fun z => (2 * α) * dw b z) (stdGauss ι) := (int_dw b).const_mul _
  have e : (fun z => (F z - α - dw b z) ^ 2) = fun z =>
      F z ^ 2 + α ^ 2 + dw b z ^ 2 - (2 * α) * F z - 2 * (F z * dw b z) + (2 * α) * dw b z := by
    funext z; ring
  have j2 : Integrable (fun z => F z ^ 2 + α ^ 2) (stdGauss ι) := i1.add i2
  have j3 : Integrable (fun z => F z ^ 2 + α ^ 2 + dw b z ^ 2) (stdGauss ι) := j2.add i3
  have j4 : Integrable (fun z => F z ^ 2 + α ^ 2 + dw b z ^ 2 - (2 * α) * F z)
      (stdGauss ι) := j3.sub i4
  have j5 : Integrable (fun z => F z ^ 2 + α ^ 2 + dw b z ^ 2 - (2 * α) * F z -
      2 * (F z * dw b z)) (stdGauss ι) := j4.sub i5
  have hFd : ∫ z, F z * dw b z ∂stdGauss ι = ∑ i, b i * ∫ z, F z * z i ∂stdGauss ι := by
    have e' : (fun z => F z * dw b z) = fun z => ∑ i, b i * (F z * z i) := by
      funext z
      simp only [dw, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e', integral_finsetSum _ fun i _ => (iFc i).const_mul (b i)]
    simp_rw [integral_const_mul]
  rw [e, integral_add j5 i6, integral_sub j4 i5, integral_sub j3 i4,
    integral_add j2 i3, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_dw, integral_dw_sq, hFd]
  simp only [integral_const, probReal_univ, one_smul, mul_zero, add_zero]
  set m := ∫ x, F x ∂stdGauss ι
  set fc : ι → ℝ := fun i => ∫ x, F x * x i ∂stdGauss ι with hfc
  have hs : ∑ i, (b i - fc i) ^ 2 = nsq b - 2 * ∑ i, b i * fc i + ∑ i, fc i ^ 2 := by
    simp only [nsq, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hs0 : 0 ≤ ∑ i, (b i - fc i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith [sq_nonneg (α - m)]

/-- The first-chaos coefficients of `T_c h`: `∫ T_c h · x_i = c ∫ h · x_i`. -/
lemma Tou_coord {h : (ι → ℝ) → ℝ} (hh : BM h) {c : ℝ} (hc : |c| ≤ 1) (i : ι) :
    ∫ x, Tou c h x * x i ∂stdGauss ι = c * ∫ x, h x * x i ∂stdGauss ι := by
  have mh := bm_memLp hh
  have ihc : Integrable (fun z : ι → ℝ => h z * z i) (stdGauss ι) :=
    mh.integrable_mul (memLp_coord i)
  obtain ⟨M, hM⟩ := hh.bdd
  -- the left side as an integral over the pair
  have hcomb : BM (fun w : (ι → ℝ) × (ι → ℝ) => h (c • w.1 + sC c • w.2)) :=
    hh.comp (meas_comb c (sC c))
  have iL : Integrable (fun w : (ι → ℝ) × (ι → ℝ) => h (c • w.1 + sC c • w.2) * w.1 i)
      ((stdGauss ι).prod (stdGauss ι)) := by
    refine Integrable.bdd_mul (c := M) ((int_coord i).comp_fst (stdGauss ι))
      hcomb.meas.aestronglyMeasurable (ae_of_all _ fun w => ?_)
    simpa [Real.norm_eq_abs] using hM _
  have h1 : ∫ x, Tou c h x * x i ∂stdGauss ι =
      ∫ w, h (c • w.1 + sC c • w.2) * w.1 i ∂((stdGauss ι).prod (stdGauss ι)) := by
    rw [integral_prod _ iL]
    simp only [Tou, integral_mul_const]
  rw [h1]
  set θ := Real.arccos c with hθ
  have hcos : Real.cos θ = c := Real.cos_arccos (abs_le.mp hc).1 (abs_le.mp hc).2
  have hsin : Real.sin θ = sC c := by rw [hθ, Real.sin_arccos]; rfl
  have hmp := BstLean.Part48.rot_preserving (ι := ι) θ
  set H : (ι → ℝ) × (ι → ℝ) → ℝ := fun v => h v.1 * (c * v.1 i - sC c * v.2 i) with hH
  have hHm : Measurable H := by
    have h1 : Measurable (fun v : (ι → ℝ) × (ι → ℝ) => h v.1) := hh.meas.comp measurable_fst
    have h2 : Measurable (fun v : (ι → ℝ) × (ι → ℝ) => v.1 i) :=
      (measurable_pi_apply i).comp measurable_fst
    have h3 : Measurable (fun v : (ι → ℝ) × (ι → ℝ) => v.2 i) :=
      (measurable_pi_apply i).comp measurable_snd
    exact h1.mul ((h2.const_mul c).sub (h3.const_mul (sC c)))
  have key : ∀ w : (ι → ℝ) × (ι → ℝ), h (c • w.1 + sC c • w.2) * w.1 i =
      H (BstLean.Part48.rotX θ w.1 w.2, BstLean.Part48.rotY θ w.1 w.2) := by
    intro w
    simp only [hH]
    have e2 : BstLean.Part48.rotX θ w.1 w.2 = c • w.1 + sC c • w.2 := by
      funext j
      simp [BstLean.Part48.rotX, hcos, hsin]
    have e1 : c * BstLean.Part48.rotX θ w.1 w.2 i - sC c * BstLean.Part48.rotY θ w.1 w.2 i =
        w.1 i := by
      simp only [BstLean.Part48.rotX, BstLean.Part48.rotY, hcos, hsin]
      have := sC_sq hc
      linear_combination (w.1 i) * this
    rw [e1, e2]
  simp_rw [key]
  rw [mp_integral hmp H hHm]
  have iA : Integrable (fun v : (ι → ℝ) × (ι → ℝ) => c * (h v.1 * v.1 i))
      ((stdGauss ι).prod (stdGauss ι)) := (ihc.comp_fst (stdGauss ι)).const_mul c
  have iB : Integrable (fun v : (ι → ℝ) × (ι → ℝ) => sC c * (h v.1 * v.2 i))
      ((stdGauss ι).prod (stdGauss ι)) := by
    refine Integrable.const_mul ?_ _
    refine Integrable.bdd_mul (c := M) ((int_coord i).comp_snd (stdGauss ι))
      (hh.meas.comp measurable_fst).aestronglyMeasurable (ae_of_all _ fun w => ?_)
    simpa [Real.norm_eq_abs] using hM _
  have eH : H = fun v => c * (h v.1 * v.1 i) - sC c * (h v.1 * v.2 i) := by
    funext v; simp only [hH]; ring
  rw [eH, integral_sub iA iB, integral_const_mul, integral_const_mul,
    integral_fun_fst (fun x : ι → ℝ => h x * x i),
    integral_prod_mul (fun x : ι → ℝ => h x) (fun z : ι → ℝ => z i), integral_coord]
  simp

lemma exp_sq_int1 : Integrable (fun x : ℝ => Real.exp ((3 / 8) * x ^ 2)) (gaussianReal 0 1) := by
  rw [gaussianReal_of_var_ne_zero _ one_ne_zero,
    integrable_withDensity_iff (measurable_gaussianPDF 0 1)
      (ae_of_all _ fun x => by simp [gaussianPDF_def])]
  have e : (fun x : ℝ => Real.exp ((3 / 8) * x ^ 2) * (gaussianPDF 0 1 x).toReal) =
      fun x => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 8) * x ^ 2) := by
    funext x
    rw [gaussianPDF_def]
    simp only
    rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _), gaussianPDFReal_def]
    simp only [NNReal.coe_one, mul_one, sub_zero]
    rw [mul_comm, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [e]
  exact (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1 / 8)).const_mul _

lemma exp_sq_int : Integrable (fun x : ι → ℝ => Real.exp ((3 / 8) * nsq x)) (stdGauss ι) := by
  have e : (fun x : ι → ℝ => Real.exp ((3 / 8) * nsq x)) =
      fun x => ∏ i, Real.exp ((3 / 8) * x i ^ 2) := by
    funext x
    rw [← Real.exp_sum, nsq, Finset.mul_sum]
  rw [e]
  unfold stdGauss
  exact Integrable.fintype_prod (f := fun _ x => Real.exp ((3 / 8) * x ^ 2)) (fun _ => exp_sq_int1)

lemma exp_taylor2 {t : ℝ} (ht : 0 ≤ t) : Real.exp t - 1 - t ≤ t ^ 2 * Real.exp t := by
  have h1 : 1 - t ≤ Real.exp (-t) := by have := Real.add_one_le_exp (-t); linarith
  have h2 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have hp : 0 < Real.exp t := Real.exp_pos t
  -- e^t (1 - t) ≤ 1 and 1 ≤ e^t - ... 
  have h3 : Real.exp t * (1 - t) ≤ 1 := by nlinarith
  have h4 : Real.exp t - 1 ≤ t * Real.exp t := by nlinarith
  nlinarith

/-- **The first chaos is all of the part of order `c²`.** -/
theorem chaosLimit : ChaosLimit := by
  intro ι _ h hh
  obtain ⟨M, hM⟩ := hh.bdd
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0)
  set CE := ∫ x : ι → ℝ, Real.exp ((3 / 8) * nsq x) ∂stdGauss ι with hCE
  refine ⟨M ^ 2 * (16 / 9) * 1152 * CE, fun c hc0 hc1 => ?_⟩
  have hcabs : |c| ≤ 1 := by rw [abs_of_nonneg hc0]; linarith
  have hs2 : sC c ^ 2 = 1 - c ^ 2 := sC_sq hcabs
  have hc2 : c ^ 2 ≤ 1 / 4 := by nlinarith
  have hs2' : 3 / 4 ≤ sC c ^ 2 := by rw [hs2]; linarith
  have hs0 : 0 < sC c := lt_of_le_of_ne (sC_nonneg c) (fun h0 => by rw [← h0] at hs2'; norm_num at hs2')
  set s := sC c with hs
  set F := Tou c h with hF
  have bF : BM F := Tou_BM c hh
  set G : (ι → ℝ) → ℝ := fun y => h (s • y) with hG
  have mG : Measurable G := hh.meas.comp (measurable_const_smul s)
  have hGM : ∀ y, |G y| ≤ M := fun y => hM _
  set α := ∫ z, G z ∂stdGauss ι
  set b : ι → ℝ := fun i => (c / s) * ∫ z, G z * z i ∂stdGauss ι with hb
  -- step 4
  have hproj := proj_ineq bF α b
  have hNou : Nou c h = ∫ x, F x ^ 2 ∂stdGauss ι := rfl
  have hmean : ∫ x, F x ∂stdGauss ι = ∫ x, h x ∂stdGauss ι := integral_Tou hcabs hh
  have hco : ∑ i, (∫ x, F x * x i ∂stdGauss ι) ^ 2 =
      c ^ 2 * ∑ i, (∫ x, h x * x i ∂stdGauss ι) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Tou_coord hh hcabs i]; ring
  rw [hmean, hco, ← hNou] at hproj
  refine hproj.trans ?_
  -- pointwise bound of the remainder
  have ha : c ^ 2 / s ^ 2 ≤ (4 / 3) * c ^ 2 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg c]
  have ha0 : 0 ≤ c ^ 2 / s ^ 2 := by positivity
  have hpt : ∀ x : ι → ℝ, (F x - α - dw b x) ^ 2 ≤
      M ^ 2 * (16 / 9) * 1152 * c ^ 4 * Real.exp ((3 / 8) * nsq x) := by
    intro x
    set w : ι → ℝ := (c / s) • x with hw
    have e1 : F x = ∫ z, G (z + w) ∂stdGauss ι := by
      simp only [hF, Tou, hG]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp only
      congr 1
      funext j
      simp only [hw, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
    have e2 : dw b x = ∑ i, w i * ∫ z, G z * z i ∂stdGauss ι := by
      simp only [dw, hb, hw, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e3 : nsq w = c ^ 2 / s ^ 2 * nsq x := by
      simp only [nsq, hw, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    have hrem := shift_remainder mG hGM w
    rw [← e1, ← e2] at hrem
    refine hrem.trans ?_
    have hn0 : 0 ≤ nsq x := Finset.sum_nonneg fun i _ => sq_nonneg _
    set t := nsq w with ht
    have ht0 : 0 ≤ t := by rw [e3]; positivity
    have ht1 : t ≤ (4 / 3) * c ^ 2 * nsq x := by
      rw [e3]; exact mul_le_mul_of_nonneg_right ha hn0
    have ht2 : t ≤ nsq x / 3 := by nlinarith
    have hT := exp_taylor2 ht0
    have hexp : Real.exp t ≤ Real.exp (nsq x / 3) := Real.exp_le_exp.mpr ht2
    have hq := Real.quadratic_le_exp_of_nonneg (x := nsq x / 24) (by positivity)
    have hE : Real.exp ((3 / 8) * nsq x) = Real.exp (nsq x / 24) * Real.exp (nsq x / 3) := by
      rw [← Real.exp_add]; congr 1; ring
    have hpos3 : 0 < Real.exp (nsq x / 3) := Real.exp_pos _
    have hn2 : nsq x ^ 2 ≤ 1152 * Real.exp (nsq x / 24) := by nlinarith
    have ht4 : t ^ 2 ≤ (16 / 9) * c ^ 4 * nsq x ^ 2 := by
      have : t ^ 2 ≤ ((4 / 3) * c ^ 2 * nsq x) ^ 2 := pow_le_pow_left₀ ht0 ht1 2
      nlinarith
    have hc4 : 0 ≤ (16 / 9 : ℝ) * c ^ 4 := by positivity
    calc M ^ 2 * (Real.exp t - 1 - t) ≤ M ^ 2 * (t ^ 2 * Real.exp t) :=
          mul_le_mul_of_nonneg_left hT (sq_nonneg M)
      _ ≤ M ^ 2 * ((16 / 9) * c ^ 4 * nsq x ^ 2 * Real.exp (nsq x / 3)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg M)
          exact mul_le_mul ht4 hexp (Real.exp_pos _).le (by positivity)
      _ ≤ M ^ 2 * ((16 / 9) * c ^ 4 * (1152 * Real.exp (nsq x / 24)) * Real.exp (nsq x / 3)) := by
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg M)
          refine mul_le_mul_of_nonneg_right ?_ hpos3.le
          exact mul_le_mul_of_nonneg_left hn2 hc4
      _ = M ^ 2 * (16 / 9) * 1152 * c ^ 4 * Real.exp ((3 / 8) * nsq x) := by
          rw [hE]; ring
  have iL : Integrable (fun x => (F x - α - dw b x) ^ 2) (stdGauss ι) :=
    (((bm_memLp bF).sub (memLp_const α)).sub (memLp_dw b)).integrable_sq
  have hmono := integral_mono iL (exp_sq_int.const_mul (M ^ 2 * (16 / 9) * 1152 * c ^ 4)) hpt
  rw [integral_const_mul] at hmono
  refine hmono.trans (le_of_eq ?_)
  rw [← hCE]
  ring

end Main

#print axioms chaosLimit

end BstLean.Part112
