import BstLean.Part200Mean
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! Derivatives of the ReLU pair kernel, including both parallel endpoints. -/
namespace BstLean.Part209
open MeasureTheory ProbabilityTheory Real Matrix Filter Topology Set
open BstLean.Part130 BstLean.Part152 BstLean.Part153

noncomputable def kernelSlope (r : ℝ) : ℝ := (π - arccos r) / π

lemma continuous_kernelSlope : Continuous kernelSlope := by
  unfold kernelSlope
  fun_prop

lemma kappa_eq_zero_of_le {r : ℝ} (hr : r ≤ -1) : kappa r = 0 := by
  have hs : 1 - r ^ 2 ≤ 0 := by nlinarith
  simp [kappa, sqrt_eq_zero_of_nonpos hs, arccos_of_le_neg_one hr]

lemma kappa_eq_self_of_ge {r : ℝ} (hr : 1 ≤ r) : kappa r = r := by
  have hs : 1 - r ^ 2 ≤ 0 := by nlinarith
  simp [kappa, sqrt_eq_zero_of_nonpos hs, arccos_of_one_le hr, pi_ne_zero]

/-- The scalar kernel is differentiable at both endpoints as well as in the interior. -/
theorem hasDerivAt_kappa_all (r : ℝ) : HasDerivAt kappa (kernelSlope r) r := by
  have hdiff : DifferentiableOn ℝ kappa (Ioo (-1) 1) :=
    fun z hz => (hasDerivAt_kappa hz.1 hz.2).differentiableAt.differentiableWithinAt
  have hd : ∀ z ∈ Ioo (-1 : ℝ) 1, deriv kappa z = kernelSlope z :=
    fun z hz => (hasDerivAt_kappa hz.1 hz.2).deriv
  rcases lt_trichotomy r (-1) with hr | rfl | hr
  · have he : kappa =ᶠ[𝓝 r] fun _ => (0 : ℝ) := by
      filter_upwards [eventually_lt_nhds hr] with z hz
      exact kappa_eq_zero_of_le hz.le
    have hk : kernelSlope r = 0 := by simp [kernelSlope, arccos_of_le_neg_one hr.le]
    rw [hk]
    exact (hasDerivAt_const r 0).congr_of_eventuallyEq he
  · have hright : HasDerivWithinAt kappa (kernelSlope (-1)) (Ici (-1)) (-1) := by
      apply hasDerivWithinAt_Ici_of_tendsto_deriv hdiff
        continuous_kappa.continuousAt.continuousWithinAt
        (Ioo_mem_nhdsGT (by norm_num : (-1 : ℝ) < 1))
      apply (continuous_kernelSlope.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (-1 : ℝ) < 1)] with z hz
      exact (hd z hz).symm
    have hleft : HasDerivWithinAt kappa (kernelSlope (-1)) (Iic (-1)) (-1) := by
      have hk : kernelSlope (-1) = 0 := by simp [kernelSlope]
      rw [hk]
      apply (hasDerivAt_const (-1 : ℝ) (0 : ℝ)).hasDerivWithinAt.congr
      · exact fun z hz => kappa_eq_zero_of_le hz
      · exact kappa_neg_one
    exact (hleft.union hright).hasDerivAt (by simp)
  · rcases lt_trichotomy r 1 with hr1 | rfl | hr1
    · exact hasDerivAt_kappa hr hr1
    · have hleft : HasDerivWithinAt kappa (kernelSlope 1) (Iic 1) 1 := by
        apply hasDerivWithinAt_Iic_of_tendsto_deriv hdiff
          continuous_kappa.continuousAt.continuousWithinAt
          (Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1))
        apply (continuous_kernelSlope.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr'
        filter_upwards [Ioo_mem_nhdsLT (by norm_num : (-1 : ℝ) < 1)] with z hz
        exact (hd z hz).symm
      have hright : HasDerivWithinAt kappa (kernelSlope 1) (Ici 1) 1 := by
        have hk : kernelSlope 1 = 1 := by simp [kernelSlope, pi_ne_zero]
        rw [hk]
        apply (hasDerivAt_id (1 : ℝ)).hasDerivWithinAt.congr
        · exact fun z hz => kappa_eq_self_of_ge hz
        · exact kappa_one
      exact (hleft.union hright).hasDerivAt (by simp)
    · have he : kappa =ᶠ[𝓝 r] fun z => z := by
        filter_upwards [eventually_gt_nhds hr1] with z hz
        exact kappa_eq_self_of_ge hz.le
      have hk : kernelSlope r = 1 := by
        simp [kernelSlope, arccos_of_one_le hr1.le, pi_ne_zero]
      rw [hk]
      exact (hasDerivAt_id r).congr_of_eventuallyEq he

variable {d : ℕ}

lemma hasDerivAt_normSq_line (a u : Fin d → ℝ) :
    HasDerivAt (fun t : ℝ => normSq (a + t • u)) (2 * dotp a u) 0 := by
  have h : ∀ i : Fin d, HasDerivAt (fun t : ℝ => (a i + t * u i) ^ 2)
      (2 * a i * u i) 0 := by
    intro i
    convert (((hasDerivAt_id (0 : ℝ)).mul_const (u i)).const_add (a i)).pow 2 using 1
    · funext t; rfl
    · simp
  have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ => h i)
  convert hs using 1
  · funext t
    simp only [normSq, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
  · simp only [dotp, Finset.mul_sum, mul_assoc]

lemma hasDerivAt_nrm_line {a : Fin d → ℝ} (ha : a ≠ 0) (u : Fin d → ℝ) :
    HasDerivAt (fun t : ℝ => nrm (a + t • u)) (dotp a u / nrm a) 0 := by
  have hn : normSq a ≠ 0 := fun h => ha (normSq_eq_zero h)
  have h := (hasDerivAt_normSq_line a u).sqrt (by simpa using hn)
  have he : 2 * dotp a u / (2 * sqrt (normSq a)) = dotp a u / nrm a := by
    unfold nrm
    ring
  simpa only [zero_smul, add_zero, he, nrm] using h

noncomputable def pairCos (a b : Fin d → ℝ) : ℝ := dotp a b / (nrm a * nrm b)

/-- The vector formula has the zero-vector convention at the first input. -/
noncomputable def kernelVector (a b : Fin d → ℝ) : Fin d → ℝ :=
  if a = 0 then 0 else
    kernelSlope (pairCos a b) • b +
      (nrm b / nrm a * sqrt (1 - pairCos a b ^ 2) / π) • a

/-- The directional derivative formula includes nonzero parallel vectors. -/
theorem hasDerivAt_kernelPhi_line {a b : Fin d → ℝ} (ha : a ≠ 0) (u : Fin d → ℝ) :
    HasDerivAt (fun t : ℝ => kernelPhi (a + t • u) b)
      (dotp (kernelVector a b) u) 0 := by
  by_cases hb : b = 0
  · subst b
    simpa [kernelPhi, kernelVector, ha, nrm, normSq, dotp] using hasDerivAt_const (0 : ℝ) 0
  have hna : nrm a ≠ 0 := (BstLean.Part132.nrm_pos_of_ne
    (fun h => ha (normSq_eq_zero h))).ne'
  have hnb : nrm b ≠ 0 := (BstLean.Part132.nrm_pos_of_ne
    (fun h => hb (normSq_eq_zero h))).ne'
  have hn := (hasDerivAt_nrm_line ha u).mul_const (nrm b)
  have hd : HasDerivAt (fun t : ℝ => dotp (a + t • u) b) (dotp u b) 0 := by
    have hs := HasDerivAt.sum (u := Finset.univ) (fun i _ =>
      (((hasDerivAt_id (0 : ℝ)).mul_const (u i)).const_add (a i)).mul_const (b i))
    convert hs using 1
    · funext t
      simp [dotp, Finset.sum_apply]
    · simp [dotp]
  have hr := hd.div hn (by simpa using mul_ne_zero hna hnb)
  simp only [zero_smul, add_zero] at hr
  have hk := (hasDerivAt_kappa_all (pairCos (a + (0 : ℝ) • u) b)).comp 0 hr
  simp only [zero_smul, add_zero] at hk
  have h := hn.mul hk
  simp only [Function.comp_apply, Pi.div_apply, zero_smul, add_zero] at h
  convert h using 1
  · rfl
  · simp only [kernelVector, if_neg ha, dotp, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
    change kernelSlope (pairCos a b) * dotp b u +
      (nrm b / nrm a * sqrt (1 - pairCos a b ^ 2) / π) * dotp a u =
      dotp a u / nrm a * (nrm b * kappa (pairCos a b)) +
        nrm a * (nrm b * (kernelSlope (pairCos a b) *
          ((dotp u b * (nrm a * nrm b) - dotp a b * (dotp a u / nrm a * nrm b)) /
            (nrm a * nrm b) ^ 2)))
    have hab : dotp b u = dotp u b := by unfold dotp; apply Finset.sum_congr rfl; intros; ring
    rw [hab]
    have hkf : kappa (pairCos a b) = sqrt (1 - pairCos a b ^ 2) / π +
        pairCos a b * kernelSlope (pairCos a b) := by
      unfold kappa kernelSlope
      ring
    rw [hkf]
    have habr : dotp a b = pairCos a b * (nrm a * nrm b) := by
      unfold pairCos
      field_simp
    conv_rhs => rw [habr]
    field_simp [hna, hnb]
    <;> ring

end BstLean.Part209
