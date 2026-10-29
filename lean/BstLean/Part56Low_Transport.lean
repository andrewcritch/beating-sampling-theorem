import BstLean.Part56Low_Angular
import BstLean.Part53Floor_Energy

namespace BstLean.Part56.LowTransport

open MeasureTheory ProbabilityTheory BstLean.Part29 BstLean.Part53
open scoped ENNReal

lemma rankOne_normalizer_ge_one {n : ℕ} (hn : 1 ≤ n) (t : ℝ) (ht : 0 ≤ t)
    (v : Fin n → ℝ) : 1 ≤ BstLean.Part50.ZA n (rk1 t v) := by
  letI := BstLean.Part29.uniformSphere_isProbability n hn
  have hμ : BstLean.Part40.SphLaw n (uniformSphere n) :=
    ⟨inferInstance, BstLean.Part29.uniformSphere_ae_sphere n⟩
  have hc : Continuous (fun x : Fin n → ℝ => Real.exp (t * (∑ i, v i * x i) ^ 2)) := by
    fun_prop
  have hi := BstLean.Part53.FloorEnergy.sphere_cont_integrable hμ hc
  have h := integral_mono (integrable_const (1 : ℝ)) hi (fun x =>
    Real.one_le_exp_iff.mpr (mul_nonneg ht (sq_nonneg _)))
  simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, mul_one,
    BstLean.Part50.ZA, rk1_quadratic] using h

noncomputable def pairDirection {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (p : ℝ × (Fin m → ℝ)) : Fin (m + 1) → ℝ :=
  unitF53 (basisReconstruct b (Fin.cons p.1 p.2))

noncomputable def pairWeight {m : ℕ} (t : ℝ) (v : Fin (m + 1) → ℝ)
    (p : ℝ × (Fin m → ℝ)) : ℝ :=
  Real.exp (t * (axialS p.1 (radF53 p.2)) ^ 2) / BstLean.Part50.ZA (m + 1) (rk1 t v)

lemma pairDirection_measurable {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1)))) :
    Measurable (pairDirection b) := by
  unfold pairDirection
  simp_rw [basisReconstruct_eq_symm]
  exact BstLean.Part53.measurable_unitF.comp
    ((basisCoordinates b).symm.measurable.comp (by fun_prop))

lemma pairWeight_measurable {m : ℕ} (t : ℝ) (v : Fin (m + 1) → ℝ) :
    Measurable (pairWeight t v) := by
  unfold pairWeight axialS radF53
  fun_prop

lemma lawRK_pair_integral {m : ℕ}
    (b : OrthonormalBasis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (v : Fin (m + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v) (t : ℝ)
    (F : (Fin (m + 1) → ℝ) → ℝ) (hF : Measurable F) (hF0 : ∀ x, 0 ≤ F x)
    (hz : 0 ≤ BstLean.Part50.ZA (m + 1) (rk1 t v)) :
    (∫ x, F x ∂lawRK (m + 1) t v) =
      ∫ p, F (pairDirection b p) * pairWeight t v p
        ∂(gaussianReal 0 1).prod (stdGauss (Fin m)) := by
  have hw0 (p : ℝ × (Fin m → ℝ)) : 0 ≤ pairWeight t v p :=
    div_nonneg (Real.exp_pos _).le hz
  have hm := (hF.comp (pairDirection_measurable b)).mul (pairWeight_measurable t v)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hF0) hF.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun p =>
      mul_nonneg (hF0 _) (hw0 p))) hm.aestronglyMeasurable]
  congr 1
  rw [lawRK_lintegral_gauss (m + 1) (by omega) t v _ (hF.ennreal_ofReal)]
  have hwg : Measurable (fun g : Fin (m + 1) → ℝ => ENNReal.ofReal
      (Real.exp (t * (∑ i, v i * unitF53 g i) ^ 2) / BstLean.Part50.ZA (m + 1) (rk1 t v))) := by
    unfold unitF53
    fun_prop
  have hrot := basis_cons_lintegral b _ ((hF.ennreal_ofReal.comp BstLean.Part53.measurable_unitF).mul hwg)
  simp only [Pi.mul_apply, Function.comp_apply] at hrot
  rw [hrot]
  rw [lintegral_prod (fun p : ℝ × (Fin m → ℝ) =>
    ENNReal.ofReal (F (pairDirection b p) * pairWeight t v p)) hm.ennreal_ofReal.aemeasurable]
  apply lintegral_congr
  intro a
  apply lintegral_congr
  intro z
  rw [← basisReconstruct_eq_symm]
  rw [normalized_basis_axial b v hb a z]
  exact (ENNReal.ofReal_mul (hF0 _)).symm

lemma rankOne_moment_bound (m k : ℕ) (C L : ℝ) (hL : 0 < L)
    (t : ℝ) (ht : 0 ≤ t) (htC : t ≤ C * (m + 1))
    (v : Fin (m + 1) → ℝ) (hv : UnitV v) :
    ((4 * L + 1)⁻¹) ^ k *
      (1 - Real.exp (C * (m + 1)) * Real.sqrt 2 * ((Real.sqrt (1 + 2 * L))⁻¹) ^ m) ≤
      ∫ x, (1 - (∑ i, x i * v i) ^ 2) ^ k ∂lawRK (m + 1) t v := by
  obtain ⟨b, hb⟩ := unit_basis_exists (m + 1) (by omega) v hv
  have hb' : b 0 = WithLp.toLp 2 v := hb
  have hz := rankOne_normalizer_ge_one (by omega : 1 ≤ m + 1) t ht v
  have hz0 : 0 < BstLean.Part50.ZA (m + 1) (rk1 t v) := lt_of_lt_of_le zero_lt_one hz
  let w := pairWeight t v
  let W := Real.exp (C * (m + 1))
  have hw := pairWeight_measurable t v
  have hw0 (p : ℝ × (Fin m → ℝ)) : 0 ≤ w p := div_nonneg (Real.exp_pos _).le hz0.le
  have hy (p : ℝ × (Fin m → ℝ)) :
      0 ≤ 1 - (p.1 / Real.sqrt (p.1 ^ 2 + radF53 p.2 ^ 2)) ^ 2 ∧
      1 - (p.1 / Real.sqrt (p.1 ^ 2 + radF53 p.2 ^ 2)) ^ 2 ≤ 1 := by
    have h := abs_le.mp (axialS_abs_le_one p.1 (radF53 p.2))
    change -1 ≤ p.1 / Real.sqrt (p.1 ^ 2 + radF53 p.2 ^ 2) ∧
      p.1 / Real.sqrt (p.1 ^ 2 + radF53 p.2 ^ 2) ≤ 1 at h
    constructor <;> nlinarith [sq_nonneg (p.1 / Real.sqrt (p.1 ^ 2 + radF53 p.2 ^ 2))]
  have hwW (p : ℝ × (Fin m → ℝ)) : w p ≤ W := by
    have hs : t * (axialS p.1 (radF53 p.2)) ^ 2 ≤ C * (m + 1) := by
      have h := (hy p).1
      change 0 ≤ 1 - (axialS p.1 (radF53 p.2)) ^ 2 at h
      nlinarith
    exact (div_le_self (Real.exp_pos _).le hz).trans (Real.exp_le_exp.mpr hs)
  have hwi : Integrable w ((gaussianReal 0 1).prod (stdGauss (Fin m))) := by
    apply (integrable_const W).mono' hw.aestronglyMeasurable
    exact ae_of_all _ fun p => by rw [Real.norm_eq_abs, abs_of_nonneg (hw0 p)]; exact hwW p
  have hμ := (BstLean.Part50.binghamA_antipodal (by omega : 1 ≤ m + 1) (rk1 t v)).sph
  letI := hμ.prob
  letI : IsProbabilityMeasure (lawRK (m + 1) t v) := hμ.prob
  have hw1 : (∫ p, w p ∂(gaussianReal 0 1).prod (stdGauss (Fin m))) = 1 := by
    have h := lawRK_pair_integral b v hb' t (fun _ => 1) measurable_const (fun _ => zero_le_one) hz0.le
    simpa only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, smul_eq_mul, one_mul, mul_one] using h.symm
  have hpy : Measurable (fun p : ℝ × (Fin m → ℝ) =>
      w p * (1 - (p.1 / Real.sqrt (p.1 ^ 2 + radF53 p.2 ^ 2)) ^ 2) ^ k) := by
    dsimp only [w, pairWeight, radF53, axialS]
    fun_prop
  have hyi : Integrable (fun p : ℝ × (Fin m → ℝ) =>
      w p * (1 - (p.1 / Real.sqrt (p.1 ^ 2 + radF53 p.2 ^ 2)) ^ 2) ^ k)
      ((gaussianReal 0 1).prod (stdGauss (Fin m))) := by
    apply hwi.mono' hpy.aestronglyMeasurable
    exact ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 p) (pow_nonneg (hy p).1 k))]
      exact mul_le_of_le_one_right (hw0 p) (pow_le_one₀ (hy p).1 (hy p).2)
  have h := LowAngular.weighted_angular_lower m k L W hL (Real.exp_pos _).le w
    hw.stronglyMeasurable hw0 hwW hwi hw1 hyi
  let F : (Fin (m + 1) → ℝ) → ℝ := fun x => max 0 (1 - (∑ i, v i * x i) ^ 2) ^ k
  have hF : Measurable F := by dsimp only [F]; fun_prop
  have htrans := lawRK_pair_integral b v hb' t F hF (fun x => pow_nonneg (le_max_left _ _) _) hz0.le
  have he (p : ℝ × (Fin m → ℝ)) : F (pairDirection b p) =
      (1 - (p.1 / Real.sqrt (p.1 ^ 2 + radF53 p.2 ^ 2)) ^ 2) ^ k := by
    dsimp only [F, pairDirection]
    rw [normalized_basis_axial b v hb' p.1 p.2]
    change max 0 (1 - (p.1 / Real.sqrt (p.1 ^ 2 + radF53 p.2 ^ 2)) ^ 2) ^ k = _
    rw [max_eq_right (hy p).1]
  simp only [he, mul_comm _ (pairWeight t v _)] at htrans
  rw [← htrans] at h
  convert h using 1
  apply integral_congr_ae
  filter_upwards [hμ.sphere] with x hx
  have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x v
  change (∑ i, x i * v i) ^ 2 ≤ (∑ i, x i ^ 2) * ∑ i, v i ^ 2 at hs
  have hv' : (∑ i, v i ^ 2) = 1 := hv
  rw [hx, hv', one_mul] at hs
  dsimp only [F]
  simp only [mul_comm (v _) (x _)]
  rw [max_eq_right (by linarith)]


end BstLean.Part56.LowTransport
