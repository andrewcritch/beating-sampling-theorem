import BstLean.Part53Defs
import BstLean.Part48Var
import BstLean.Part41Error

namespace BstLean.Part53.T2Aux

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD)

noncomputable def radialPoly (n d : ℕ) (s : ℝ) :
    MvPolynomial (CoefIdxD n d) ℝ :=
  ∑ α, (MvPolynomial.C s * MvPolynomial.X α) ^ 2


private lemma radialPoly_eval (n d : ℕ) (s : ℝ) (Z : CoefIdxD n d → ℝ) :
    MvPolynomial.eval Z (radialPoly n d s) = ∑ α, (s • Z) α ^ 2 := by
  classical
  simp [radialPoly, Pi.smul_apply, smul_eq_mul]


private lemma gaussian_pow_integrable {ι : Type*} [Fintype ι]
    (P : MvPolynomial ι ℝ) (r : ℕ) :
    Integrable (fun z => (MvPolynomial.eval z P) ^ r) (stdGauss ι) := by
  simpa only [map_pow] using BstLean.Part48.gauss_poly_integrable (P ^ r)


private lemma radialPoly_moment (n d : ℕ) (s : ℝ) (r : ℕ) :
    ∫ Z, (MvPolynomial.eval Z (radialPoly n d s)) ^ r ∂stdGauss (CoefIdxD n d) =
      s ^ (2 * r) * BstLean.Part36.rhoD (Fintype.card (CoefIdxD n d)) r := by
  classical
  have hs (Z : CoefIdxD n d → ℝ) :
      Real.sqrt (∑ α, Z α ^ 2) ^ (2 * r) = (∑ α, Z α ^ 2) ^ r := by
    rw [pow_mul, Real.sq_sqrt (Finset.sum_nonneg fun α hα => sq_nonneg _)]
  have hm := BstLean.Part41.p1_gauss_norm_moment (ι := CoefIdxD n d) r
  simp_rw [hs] at hm
  have he (Z : CoefIdxD n d → ℝ) :
      (MvPolynomial.eval Z (radialPoly n d s)) ^ r =
        s ^ (2 * r) * (∑ α, Z α ^ 2) ^ r := by
    rw [radialPoly_eval]
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, pow_mul]
  simp_rw [he]
  rw [integral_const_mul, hm]

private lemma sg_sq (n d : ℕ) (hn : 1 ≤ n) : (sg n d) ^ 2 = 1 / DD n d := by
  have hD := BstLean.Part36.DD_pos (d := d) hn
  rw [sg, div_pow, one_pow, Real.sq_sqrt hD.le]

private lemma radial_centered_variance (n d : ℕ) (hn : 1 ≤ n) :
    ∫ Z, (MvPolynomial.eval Z (radialPoly n d (sg n d)) - 1) ^ 2
      ∂stdGauss (CoefIdxD n d) = 2 / DD n d := by
  classical
  let P := radialPoly n d (sg n d)
  have hD := BstLean.Part36.DD_pos (d := d) hn
  have h1 := radialPoly_moment n d (sg n d) 1
  have h2 := radialPoly_moment n d (sg n d) 2
  have hsg := sg_sq n d hn
  have hmean : ∫ Z, MvPolynomial.eval Z P ∂stdGauss (CoefIdxD n d) = 1 := by
    change (∫ Z, (MvPolynomial.eval Z P) ^ 1 ∂stdGauss (CoefIdxD n d)) =
      (sg n d) ^ (2 * 1) * BstLean.Part36.rhoD (DD n d) 1 at h1
    simpa [BstLean.Part36.rhoD, Finset.prod_range_succ, hsg, hD.ne'] using h1
  have hsecond : ∫ Z, (MvPolynomial.eval Z P) ^ 2 ∂stdGauss (CoefIdxD n d) =
      1 + 2 / DD n d := by
    rw [show (sg n d) ^ (2 * 2) = ((sg n d) ^ 2) ^ 2 by ring, hsg] at h2
    simp only [BstLean.Part36.rhoD, Finset.prod_range_succ, Finset.prod_range_zero,
      mul_one, Nat.cast_zero, Nat.cast_one, mul_zero, add_zero] at h2
    simp only [one_mul] at h2
    change (∫ Z, (MvPolynomial.eval Z P) ^ 2 ∂stdGauss (CoefIdxD n d)) =
      (1 / DD n d) ^ 2 * (DD n d * (DD n d + 2)) at h2
    rw [h2]
    field_simp
  have he (Z : CoefIdxD n d → ℝ) : (MvPolynomial.eval Z P - 1) ^ 2 =
      ((MvPolynomial.eval Z P) ^ 2 - 2 * MvPolynomial.eval Z P) + 1 := by ring
  change ∫ Z, (MvPolynomial.eval Z P - 1) ^ 2 ∂stdGauss (CoefIdxD n d) = _
  simp_rw [he]
  have hsub : Integrable (fun Z => (MvPolynomial.eval Z P) ^ 2 -
      2 * MvPolynomial.eval Z P) (stdGauss (CoefIdxD n d)) :=
    (gaussian_pow_integrable P 2).sub ((BstLean.Part48.gauss_poly_integrable P).const_mul 2)
  rw [integral_add hsub (integrable_const 1),
    integral_sub (gaussian_pow_integrable P 2)
      ((BstLean.Part48.gauss_poly_integrable P).const_mul 2),
    integral_const_mul, hmean, hsecond]
  simp
  ring


private lemma DD_ge_one (n d : ℕ) (hn : 1 ≤ n) : 1 ≤ DD n d := by
  rw [BstLean.Part36.DD_eq]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hc : (1 : ℝ) ≤ ((n + d).choose d : ℝ) := by
    exact_mod_cast (Nat.choose_pos (show d ≤ n + d by omega))
  nlinarith

private lemma normalized_radial_moment_succ (n d : ℕ) (hn : 1 ≤ n) (r : ℕ) :
    (∫ Z, (MvPolynomial.eval Z (radialPoly n d (sg n d))) ^ (r + 1)
      ∂stdGauss (CoefIdxD n d)) =
      (∫ Z, (MvPolynomial.eval Z (radialPoly n d (sg n d))) ^ r
        ∂stdGauss (CoefIdxD n d)) * (1 + 2 * (r : ℝ) / DD n d) := by
  have hD := BstLean.Part36.DD_pos (d := d) hn
  rw [radialPoly_moment, radialPoly_moment]
  change (sg n d) ^ (2 * (r + 1)) * BstLean.Part36.rhoD (DD n d) (r + 1) =
    ((sg n d) ^ (2 * r) * BstLean.Part36.rhoD (DD n d) r) *
      (1 + 2 * (r : ℝ) / DD n d)
  rw [show 2 * (r + 1) = 2 * r + 2 by omega, pow_add, sg_sq n d hn,
    BstLean.Part36.rhoD, Finset.prod_range_succ]
  unfold BstLean.Part36.rhoD
  field_simp

private lemma normalized_radial_moment_bound (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n d : ℕ), 1 ≤ n →
      1 ≤ (∫ Z, (MvPolynomial.eval Z (radialPoly n d (sg n d))) ^ r
        ∂stdGauss (CoefIdxD n d)) ∧
      (∫ Z, (MvPolynomial.eval Z (radialPoly n d (sg n d))) ^ r
        ∂stdGauss (CoefIdxD n d)) - 1 ≤ C / DD n d := by
  induction r with
  | zero =>
      refine ⟨0, le_rfl, fun n d hn => ?_⟩
      simp
  | succ r ih =>
      obtain ⟨C, hC, hbound⟩ := ih
      refine ⟨C * (1 + 2 * (r : ℝ)) + 2 * (r : ℝ), by positivity,
        fun n d hn => ?_⟩
      obtain ⟨hlo, hhi⟩ := hbound n d hn
      have hD := BstLean.Part36.DD_pos (d := d) hn
      have hD1 := DD_ge_one n d hn
      have hrD : 0 ≤ 2 * (r : ℝ) / DD n d := by positivity
      have hrDb : 2 * (r : ℝ) / DD n d ≤ 2 * (r : ℝ) := by
        apply (div_le_iff₀ hD).mpr
        nlinarith
      rw [normalized_radial_moment_succ n d hn r]
      constructor
      · nlinarith
      · calc
          _ = ((∫ Z, (MvPolynomial.eval Z (radialPoly n d (sg n d))) ^ r
              ∂stdGauss (CoefIdxD n d)) - 1) * (1 + 2 * (r : ℝ) / DD n d) +
                2 * (r : ℝ) / DD n d := by ring
          _ ≤ (C / DD n d) * (1 + 2 * (r : ℝ) / DD n d) +
                2 * (r : ℝ) / DD n d := by
            exact add_le_add (mul_le_mul_of_nonneg_right hhi
              (by positivity : 0 ≤ 1 + 2 * (r : ℝ) / DD n d)) le_rfl
          _ ≤ (C / DD n d) * (1 + 2 * (r : ℝ)) + 2 * (r : ℝ) / DD n d := by
            exact add_le_add (mul_le_mul_of_nonneg_left
              (by linarith : 1 + 2 * (r : ℝ) / DD n d ≤ 1 + 2 * (r : ℝ))
              (div_nonneg hC hD.le)) le_rfl
          _ = _ := by ring

lemma radial_power_variance_bound (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n d : ℕ), 1 ≤ n →
      (∫ Z, ((MvPolynomial.eval Z (radialPoly n d (sg n d))) ^ l - 1) ^ 2
        ∂stdGauss (CoefIdxD n d)) ≤ C / DD n d := by
  obtain ⟨C, hC, hbound⟩ := normalized_radial_moment_bound (2 * l)
  obtain ⟨Cl, hCl, hboundl⟩ := normalized_radial_moment_bound l
  refine ⟨C, hC, fun n d hn => ?_⟩
  let P := radialPoly n d (sg n d)
  have h2 := (hbound n d hn).2
  have h1 := (hboundl n d hn).1
  have he (Z : CoefIdxD n d → ℝ) : ((MvPolynomial.eval Z P) ^ l - 1) ^ 2 =
      ((MvPolynomial.eval Z P) ^ (2 * l) - 2 * (MvPolynomial.eval Z P) ^ l) + 1 := by
    rw [mul_comm 2 l, pow_mul]
    ring
  change (∫ Z, ((MvPolynomial.eval Z P) ^ l - 1) ^ 2
    ∂stdGauss (CoefIdxD n d)) ≤ _
  simp_rw [he]
  have hsub : Integrable (fun Z => (MvPolynomial.eval Z P) ^ (2 * l) -
      2 * (MvPolynomial.eval Z P) ^ l) (stdGauss (CoefIdxD n d)) :=
    (gaussian_pow_integrable P (2 * l)).sub ((gaussian_pow_integrable P l).const_mul 2)
  rw [integral_add hsub (integrable_const 1), integral_sub
      (gaussian_pow_integrable P (2 * l)) ((gaussian_pow_integrable P l).const_mul 2),
    integral_const_mul]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  dsimp [P]
  linarith


noncomputable def radialScale (n d : ℕ) (Z : CoefIdxD n d → ℝ) : ℝ :=
  Real.sqrt (∑ α, Z α ^ 2) / Real.sqrt (DD n d)

lemma radialScale_nonneg (n d : ℕ) (Z : CoefIdxD n d → ℝ) :
    0 ≤ radialScale n d Z := by
  exact div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

lemma sg_pow_even (n d j : ℕ) (hn : 1 ≤ n) :
    (sg n d) ^ (2 * j) = 1 / DD n d ^ j := by
  rw [pow_mul, sg_sq n d hn, div_pow, one_pow]

lemma radialScale_continuous (n d : ℕ) : Continuous (radialScale n d) := by
  unfold radialScale
  fun_prop

lemma radialScale_sq (n d : ℕ) (hn : 1 ≤ n) (Z : CoefIdxD n d → ℝ) :
    radialScale n d Z ^ 2 = MvPolynomial.eval Z (radialPoly n d (sg n d)) := by
  have hD := BstLean.Part36.DD_pos (d := d) hn
  rw [radialScale, div_pow, Real.sq_sqrt hD.le,
    Real.sq_sqrt (Finset.sum_nonneg fun α _ => sq_nonneg _), radialPoly_eval]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, sg_sq n d hn]
  ring

private lemma radius_power_difference_le (a : ℝ) (ha : 0 ≤ a) :
    (a - 1) ^ 2 ≤ (a ^ 2 - 1) ^ 2 := by
  have h := mul_nonneg (sq_nonneg (a - 1))
    (add_nonneg (sq_nonneg a) (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha))
  have hid : (a ^ 2 - 1) ^ 2 - (a - 1) ^ 2 = (a - 1) ^ 2 * (a ^ 2 + 2 * a) := by ring
  exact sub_nonneg.mp (hid ▸ h)

lemma radialScale_power_difference_le (n d j : ℕ) (hn : 1 ≤ n)
    (Z : CoefIdxD n d → ℝ) :
    (radialScale n d Z ^ j - 1) ^ 2 ≤
      (MvPolynomial.eval Z (radialPoly n d (sg n d)) ^ j - 1) ^ 2 := by
  have h := radius_power_difference_le (radialScale n d Z ^ j)
    (pow_nonneg (radialScale_nonneg n d Z) j)
  rw [← pow_mul, Nat.mul_comm j 2, pow_mul, radialScale_sq n d hn Z] at h
  exact h

/-- Both even and odd radius powers have a second-moment error of order `1 / DD`. -/
lemma radialScale_power_second_moment (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n d : ℕ), 1 ≤ n →
      Integrable (fun Z => (radialScale n d Z ^ j - 1) ^ 2)
        (stdGauss (CoefIdxD n d)) ∧
      (∫ Z, (radialScale n d Z ^ j - 1) ^ 2 ∂stdGauss (CoefIdxD n d)) ≤ C / DD n d := by
  obtain ⟨C, hC, hb⟩ := radial_power_variance_bound j
  refine ⟨C, hC, fun n d hn => ?_⟩
  have hi : Integrable (fun Z =>
      (MvPolynomial.eval Z (radialPoly n d (sg n d)) ^ j - 1) ^ 2)
      (stdGauss (CoefIdxD n d)) := by
    convert BstLean.Part48.gauss_poly_integrable
      ((radialPoly n d (sg n d) ^ j - 1) ^ 2) using 1
    funext Z
    simp
  have hc : Continuous (fun Z => (radialScale n d Z ^ j - 1) ^ 2) :=
    (((radialScale_continuous n d).pow j).sub continuous_const).pow 2
  have hdom := radialScale_power_difference_le n d j hn
  have hir : Integrable (fun Z => (radialScale n d Z ^ j - 1) ^ 2)
      (stdGauss (CoefIdxD n d)) := by
    apply hi.mono' hc.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun Z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact hdom Z
  exact ⟨hir, (integral_mono hir hi hdom).trans (hb n d hn)⟩

lemma radialScale_even_moment_ge_one (n d j : ℕ) (hn : 1 ≤ n) :
    1 ≤ ∫ Z, radialScale n d Z ^ (2 * j) ∂stdGauss (CoefIdxD n d) := by
  obtain ⟨C, hC, hb⟩ := normalized_radial_moment_bound j
  have he (Z : CoefIdxD n d → ℝ) : radialScale n d Z ^ (2 * j) =
      MvPolynomial.eval Z (radialPoly n d (sg n d)) ^ j := by
    rw [pow_mul, radialScale_sq n d hn Z]
  simp_rw [he]
  exact (hb n d hn).1

lemma radialScale_even_integrable (n d j : ℕ) (hn : 1 ≤ n) :
    Integrable (fun Z => radialScale n d Z ^ (2 * j)) (stdGauss (CoefIdxD n d)) := by
  have he (Z : CoefIdxD n d → ℝ) : radialScale n d Z ^ (2 * j) =
      MvPolynomial.eval Z (radialPoly n d (sg n d)) ^ j := by
    rw [pow_mul, radialScale_sq n d hn Z]
  simp_rw [he]
  exact gaussian_pow_integrable _ _

lemma radialScale_uniform_second_moment (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n d : ℕ), 1 ≤ n → ∀ j : ℕ, j ≤ k →
      Integrable (fun Z => (radialScale n d Z ^ j - 1) ^ 2)
        (stdGauss (CoefIdxD n d)) ∧
      (∫ Z, (radialScale n d Z ^ j - 1) ^ 2 ∂stdGauss (CoefIdxD n d)) ≤ C / DD n d := by
  classical
  let C := fun j => Classical.choose (radialScale_power_second_moment j)
  have hC (j : ℕ) : 0 ≤ C j := (Classical.choose_spec (radialScale_power_second_moment j)).1
  have hb (j n d : ℕ) (hn : 1 ≤ n) :=
    (Classical.choose_spec (radialScale_power_second_moment j)).2 n d hn
  refine ⟨∑ j ∈ Finset.range (k + 1), C j, Finset.sum_nonneg fun j _ => hC j,
    fun n d hn j hj => ?_⟩
  refine ⟨(hb j n d hn).1, (hb j n d hn).2.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (BstLean.Part36.DD_pos (d := d) hn).le
  exact Finset.single_le_sum (fun j _ => hC j) (Finset.mem_range.mpr (by omega))

end BstLean.Part53.T2Aux
