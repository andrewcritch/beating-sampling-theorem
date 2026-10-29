import BstLean.Part53T2_Radial

/-!
# Part 64: explicit radial constants (copy of `Part53T2_Radial` with the witnesses stated)

* `aR r`: `a₀ = 0`, `a_{r+1} = a_r (1 + 2r) + 2r`; `E (‖σZ‖²)^r − 1 ≤ a_r/𝒟`.
* `CR64 k = Σ_{j ≤ k} a_{2j}`; `radialScale_uniform_second_moment64`.

Do not use `native_decide` or `axiom`.
-/

namespace BstLean.Part64

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD)
open BstLean.Part53 (sg)
open BstLean.Part53.T2Aux (radialPoly radialScale radialScale_continuous radialScale_power_difference_le)

/-- The radial recursion `a₀ = 0`, `a_{r+1} = a_r (1 + 2r) + 2r`. -/
noncomputable def aR : ℕ → ℝ
  | 0 => 0
  | r + 1 => aR r * (1 + 2 * (r : ℝ)) + 2 * (r : ℝ)

lemma aR_nonneg (r : ℕ) : 0 ≤ aR r := by
  induction r with
  | zero => simp [aR]
  | succ r ih => simp only [aR]; positivity

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


private lemma normalized_radial_moment_bound64 (r : ℕ) :
    ∀ (n d : ℕ), 1 ≤ n →
      1 ≤ (∫ Z, (MvPolynomial.eval Z (radialPoly n d (sg n d))) ^ r
        ∂stdGauss (CoefIdxD n d)) ∧
      (∫ Z, (MvPolynomial.eval Z (radialPoly n d (sg n d))) ^ r
        ∂stdGauss (CoefIdxD n d)) - 1 ≤ aR r / DD n d := by
  induction r with
  | zero =>
      intro n d hn
      simp [aR]
  | succ r ih =>
      have hC := aR_nonneg r
      intro n d hn
      set C := aR r with hCdef
      have hstep : aR (r + 1) = C * (1 + 2 * (r : ℝ)) + 2 * (r : ℝ) := by simp only [aR, hCdef]
      rw [hstep]
      obtain ⟨hlo, hhi⟩ := ih n d hn
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

private lemma radial_power_variance_bound64 (l : ℕ) :
    ∀ (n d : ℕ), 1 ≤ n →
      (∫ Z, ((MvPolynomial.eval Z (radialPoly n d (sg n d))) ^ l - 1) ^ 2
        ∂stdGauss (CoefIdxD n d)) ≤ aR (2 * l) / DD n d := by
  have hbound := normalized_radial_moment_bound64 (2 * l)
  have hboundl := normalized_radial_moment_bound64 l
  intro n d hn
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

/-- Radius powers: second-moment error `≤ a_{2j}/𝒟`. -/
lemma radialScale_power_second_moment64 (j : ℕ) :
    ∀ (n d : ℕ), 1 ≤ n →
      Integrable (fun Z => (radialScale n d Z ^ j - 1) ^ 2)
        (stdGauss (CoefIdxD n d)) ∧
      (∫ Z, (radialScale n d Z ^ j - 1) ^ 2 ∂stdGauss (CoefIdxD n d)) ≤ aR (2 * j) / DD n d := by
  have hb := radial_power_variance_bound64 j
  intro n d hn
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

/-- The explicit radial constant `CR64 k = Σ_{j ≤ k} a_{2j}`. -/
noncomputable def CR64 (k : ℕ) : ℝ := ∑ j ∈ Finset.range (k + 1), aR (2 * j)

lemma CR64_nonneg (k : ℕ) : 0 ≤ CR64 k := Finset.sum_nonneg fun j _ => aR_nonneg _

lemma radialScale_uniform_second_moment64 (k : ℕ) :
    ∀ (n d : ℕ), 1 ≤ n → ∀ j : ℕ, j ≤ k →
      Integrable (fun Z => (radialScale n d Z ^ j - 1) ^ 2)
        (stdGauss (CoefIdxD n d)) ∧
      (∫ Z, (radialScale n d Z ^ j - 1) ^ 2 ∂stdGauss (CoefIdxD n d)) ≤ CR64 k / DD n d := by
  intro n d hn j hj
  have hb := radialScale_power_second_moment64 j n d hn
  refine ⟨hb.1, hb.2.trans ?_⟩
  apply div_le_div_of_nonneg_right _ (BstLean.Part36.DD_pos (d := d) hn).le
  exact Finset.single_le_sum (f := fun j => aR (2 * j)) (fun j _ => aR_nonneg _)
    (Finset.mem_range.mpr (by omega))

end BstLean.Part64
