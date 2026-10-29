import BstLean.Part86Defs
import BstLean.Part84Bonami
import BstLean.Part84Poly
import BstLean.Part57PropD_Null
import BstLean.Part33Euler
import BstLean.Part48Var

/-!
# Part 86: the slice reverse Hölder inequality (`SliceRHRK`)

* `sphere_rh`: for a polynomial `H` of total degree `≤ D` on `ℝ^k`, `k ≥ 1`, and `ω` uniform on the
  unit sphere (`ω = unitF53 z`, `z` standard Gaussian): `E H(ω)⁴ ≤ 8 · 9^D (E H(ω)²)²`.
  Proof: parity split, homogenization, polar independence, Bonami (`fourth84_nine`).
* `sliceRHRK`: the same on every slice `x = S v + R w` of `D_{t,v}`.
-/

namespace BstLean.Part86

open MeasureTheory MvPolynomial
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53 radF53)
open BstLean.Part56 (UnitV polarPoint perpDir axialR axialS tailReconstruct)

namespace SliceRH

variable {k : ℕ}

/-! ## Algebra: homogeneous polynomials -/

lemma hom_eval {b : ℕ} {φ : MvPolynomial (Fin k) ℝ} (hφ : φ.IsHomogeneous b) (r : ℝ)
    (z : Fin k → ℝ) : eval (r • z) φ = r ^ b * eval z φ := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have h := hφ.degree_eq_sum_deg_support hd
  have h2 : ∑ i ∈ d.support, d i = ∑ i, d i :=
    Finset.sum_subset (Finset.subset_univ _) (fun i _ hi => by simpa using hi)
  have : ∏ i, (r • z) i ^ d i = r ^ b * ∏ i, z i ^ d i := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum]
    rw [h, h2]
  rw [this]; ring

/-- `q = Σ X_i²`. -/
noncomputable def qS (k : ℕ) : MvPolynomial (Fin k) ℝ := ∑ i, X i ^ 2

lemma qS_eval (z : Fin k → ℝ) : eval z (qS k) = ∑ i, z i ^ 2 := by
  simp [qS]

lemma qS_deg : (qS k).totalDegree ≤ 2 := by
  unfold qS
  refine BstLean.Part84.totalDegree_finset_sum_le (fun i _ => ?_)
  exact (totalDegree_pow _ _).trans (by rw [totalDegree_X])

/-- The homogenization of the components `b ∈ S` of `H` to degree `N`. -/
noncomputable def hz (H : MvPolynomial (Fin k) ℝ) (S : Finset ℕ) (N : ℕ) :
    MvPolynomial (Fin k) ℝ :=
  ∑ b ∈ S, qS k ^ ((N - b) / 2) * homogeneousComponent b H

lemma hz_deg (H : MvPolynomial (Fin k) ℝ) (S : Finset ℕ) (N : ℕ)
    (hS : ∀ b ∈ S, 2 * ((N - b) / 2) + b = N) : (hz H S N).totalDegree ≤ N := by
  unfold hz
  refine BstLean.Part84.totalDegree_finset_sum_le (fun b hb => ?_)
  refine (totalDegree_mul _ _).trans ?_
  have h1 : (qS k ^ ((N - b) / 2)).totalDegree ≤ 2 * ((N - b) / 2) := by
    refine (totalDegree_pow _ _).trans ?_
    calc (N - b) / 2 * (qS k).totalDegree ≤ (N - b) / 2 * 2 := Nat.mul_le_mul_left _ qS_deg
      _ = 2 * ((N - b) / 2) := by ring
  have h2 : (homogeneousComponent b H).totalDegree ≤ b :=
    (homogeneousComponent_isHomogeneous b H).totalDegree_le
  have := hS b hb
  omega

lemma hz_hom (H : MvPolynomial (Fin k) ℝ) (S : Finset ℕ) (N : ℕ)
    (hS : ∀ b ∈ S, 2 * ((N - b) / 2) + b = N) (r : ℝ) (z : Fin k → ℝ) :
    eval (r • z) (hz H S N) = r ^ N * eval z (hz H S N) := by
  unfold hz
  simp only [map_sum, map_mul, map_pow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b hb => ?_
  rw [hom_eval (homogeneousComponent_isHomogeneous b H), qS_eval, qS_eval]
  have e : ∑ i, (r • z) i ^ 2 = r ^ 2 * ∑ i, z i ^ 2 := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]
  rw [e]
  have hN := hS b hb
  have hr : r ^ N = (r ^ 2) ^ ((N - b) / 2) * r ^ b := by
    rw [← pow_mul, ← pow_add, hN]
  rw [hr, mul_pow]
  ring

lemma hz_unit (H : MvPolynomial (Fin k) ℝ) (S : Finset ℕ) (N : ℕ) (z : Fin k → ℝ)
    (hz1 : ∑ i, z i ^ 2 = 1) :
    eval z (hz H S N) = ∑ b ∈ S, eval z (homogeneousComponent b H) := by
  unfold hz
  simp only [map_sum, map_mul, map_pow, qS_eval, hz1, one_pow, one_mul]

lemma sum_comp (H : MvPolynomial (Fin k) ℝ) (D : ℕ) (hH : H.totalDegree ≤ D) :
    ∑ b ∈ Finset.range (D + 1), homogeneousComponent b H = H := by
  conv_rhs => rw [← sum_homogeneousComponent H]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro b hb
    simp only [Finset.mem_range] at hb ⊢
    omega
  · intro b _ hb
    simp only [Finset.mem_range, not_lt] at hb
    have hlt : H.totalDegree < b := by omega
    exact homogeneousComponent_eq_zero b H hlt

/-! ## The unit vector -/

lemma unit_sumsq (z : Fin k → ℝ) (hz : z ≠ 0) : ∑ i, unitF53 z i ^ 2 = 1 := by
  have hs : 0 < ∑ i, z i ^ 2 := by
    have h00 : (0 : ℝ) ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (z i)
    rcases h00.lt_or_eq with h | h
    · exact h
    · exfalso; apply hz; funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (z i))).mp h.symm i
        (Finset.mem_univ i)
      simpa using this
  unfold unitF53
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [one_div, inv_pow, Real.sq_sqrt hs.le, inv_mul_cancel₀ hs.ne']

lemma unit_sumsq_le (z : Fin k → ℝ) : ∑ i, unitF53 z i ^ 2 ≤ 1 := by
  by_cases hz : z = 0
  · subst hz
    simp [unitF53]
  · exact (unit_sumsq z hz).le

lemma unit_mem (z : Fin k → ℝ) :
    unitF53 z ∈ Set.pi Set.univ (fun _ : Fin k => Set.Icc (-1 : ℝ) 1) := by
  intro i _
  have h1 : unitF53 z i ^ 2 ≤ 1 :=
    (Finset.single_le_sum (f := fun i => unitF53 z i ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ i)).trans (unit_sumsq_le z)
  have := abs_le_one_iff_mul_self_le_one.mpr (by nlinarith : unitF53 z i * unitF53 z i ≤ 1)
  exact abs_le.mp this

lemma unit_neg (z : Fin k → ℝ) : unitF53 (-z) = (-1 : ℝ) • unitF53 z := by
  unfold unitF53
  simp only [Pi.neg_apply, even_two, Even.neg_pow, smul_neg]
  ext i; simp

lemma int_unit (f : (Fin k → ℝ) → ℝ) (hf : Continuous f) :
    Integrable (fun z => f (unitF53 z)) (stdGauss (Fin k)) := by
  have hK : IsCompact (Set.pi Set.univ (fun _ : Fin k => Set.Icc (-1 : ℝ) 1)) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  refine Integrable.of_bound
    (hf.measurable.comp BstLean.Part53.measurable_unitF).aestronglyMeasurable C ?_
  exact Filter.Eventually.of_forall fun z => hC _ (unit_mem z)

/-! ## Polar factorization -/

lemma polar_fact (φ : ℝ → ℝ) (ψ : (Fin k → ℝ) → ℝ) (hφ : Measurable φ) (hψ : Measurable ψ)
    (hφ0 : ∀ ρ, 0 ≤ φ ρ) (hψ0 : ∀ ω, 0 ≤ ψ ω) :
    ∫ z, φ (radF53 z) * ψ (unitF53 z) ∂stdGauss (Fin k) =
      (∫ z, φ (radF53 z) ∂stdGauss (Fin k)) * ∫ z, ψ (unitF53 z) ∂stdGauss (Fin k) := by
  have hr := BstLean.Part53.measurable_radF (ι := Fin k)
  have hu := BstLean.Part53.measurable_unitF (ι := Fin k)
  rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z => mul_nonneg (hφ0 _) (hψ0 _))
      ((hφ.comp hr).mul (hψ.comp hu)).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => hφ0 _)
      (hφ.comp hr).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => hψ0 _)
      (hψ.comp hu).aestronglyMeasurable, ← ENNReal.toReal_mul]
  congr 1
  have hFm : Measurable (Function.uncurry
      (fun (ω : Fin k → ℝ) (ρ : ℝ) => ENNReal.ofReal (φ ρ) * ENNReal.ofReal (ψ ω))) :=
    (ENNReal.measurable_ofReal.comp (hφ.comp measurable_snd)).mul
      (ENNReal.measurable_ofReal.comp (hψ.comp measurable_fst))
  have h := BstLean.Part53.gauss_polar_gen
    (fun (ω : Fin k → ℝ) (ρ : ℝ) => ENNReal.ofReal (φ ρ) * ENNReal.ofReal (ψ ω)) hFm
  calc ∫⁻ z, ENNReal.ofReal (φ (radF53 z) * ψ (unitF53 z)) ∂stdGauss (Fin k)
      = ∫⁻ z, ENNReal.ofReal (φ (radF53 z)) * ENNReal.ofReal (ψ (unitF53 z))
          ∂stdGauss (Fin k) := by
        refine lintegral_congr fun z => ?_
        rw [ENNReal.ofReal_mul (hφ0 _)]
    _ = ∫⁻ z, ∫⁻ z', ENNReal.ofReal (φ (radF53 z')) * ENNReal.ofReal (ψ (unitF53 z))
          ∂stdGauss (Fin k) ∂stdGauss (Fin k) := h
    _ = ∫⁻ z, (∫⁻ z', ENNReal.ofReal (φ (radF53 z')) ∂stdGauss (Fin k)) *
          ENNReal.ofReal (ψ (unitF53 z)) ∂stdGauss (Fin k) := by
        refine lintegral_congr fun z => ?_
        have hm1 : Measurable (fun z' : Fin k → ℝ => ENNReal.ofReal (φ (radF53 z'))) :=
          ENNReal.measurable_ofReal.comp (hφ.comp hr)
        exact lintegral_mul_const _ hm1
    _ = _ := by
        have hm2 : Measurable (fun z : Fin k → ℝ => ENNReal.ofReal (ψ (unitF53 z))) :=
          ENNReal.measurable_ofReal.comp (hψ.comp hu)
        exact lintegral_const_mul _ hm2

/-! ## One parity class -/

lemma par_rh (hk : 1 ≤ k) (P : MvPolynomial (Fin k) ℝ) (N : ℕ) (hdeg : P.totalDegree ≤ N)
    (hom : ∀ (r : ℝ) (z : Fin k → ℝ), eval (r • z) P = r ^ N * eval z P) :
    ∫ z, (eval (unitF53 z) P) ^ 4 ∂stdGauss (Fin k) ≤
      9 ^ N * (∫ z, (eval (unitF53 z) P) ^ 2 ∂stdGauss (Fin k)) ^ 2 := by
  have hfac : ∀ z : Fin k → ℝ, eval z P = radF53 z ^ N * eval (unitF53 z) P := by
    intro z
    conv_lhs => rw [← BstLean.Part56.rad_smul_unit z]
    exact hom _ _
  have hcP : Continuous fun ω : Fin k → ℝ => eval ω P := continuous_eval P
  set a := ∫ z, (eval (unitF53 z) P) ^ 4 ∂stdGauss (Fin k) with ha
  set b := ∫ z, (eval (unitF53 z) P) ^ 2 ∂stdGauss (Fin k) with hb
  set R4 := ∫ z : Fin k → ℝ, (radF53 z ^ (2 * N)) ^ 2 ∂stdGauss (Fin k) with hR4
  set R2 := ∫ z : Fin k → ℝ, (radF53 z ^ N) ^ 2 ∂stdGauss (Fin k) with hR2
  have I4 : ∫ z, (eval z P) ^ 4 ∂stdGauss (Fin k) = R4 * a := by
    rw [hR4, ha, ← polar_fact (fun ρ => (ρ ^ (2 * N)) ^ 2) (fun ω => (eval ω P) ^ 4)
      (by fun_prop) (hcP.pow 4).measurable (fun _ => sq_nonneg _)
      (fun _ => by positivity)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hfac z]; ring
  have I2 : ∫ z, (eval z P) ^ 2 ∂stdGauss (Fin k) = R2 * b := by
    rw [hR2, hb, ← polar_fact (fun ρ => (ρ ^ N) ^ 2) (fun ω => (eval ω P) ^ 2)
      (by fun_prop) (hcP.pow 2).measurable (fun _ => sq_nonneg _)
      (fun _ => sq_nonneg _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [hfac z]; ring
  have hB := BstLean.Part84.fourth84_nine N (Fin k) P hdeg
  rw [I4, I2] at hB
  -- the radial moments
  have hrad : ∀ z : Fin k → ℝ, radF53 z ^ 2 = ∑ i, z i ^ 2 := fun z =>
    Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg (z i))
  have hf_eq : (fun z : Fin k → ℝ => (radF53 z ^ N) ^ 2) = fun z => eval z (qS k ^ N) := by
    funext z
    rw [map_pow, qS_eval, ← hrad]; ring
  have hf2_eq : (fun z : Fin k → ℝ => (radF53 z ^ (2 * N)) ^ 2) =
      fun z => eval z (qS k ^ (2 * N)) := by
    funext z
    rw [map_pow, qS_eval, ← hrad]; ring
  have hf : Integrable (fun z : Fin k → ℝ => (radF53 z ^ N) ^ 2) (stdGauss (Fin k)) := by
    rw [hf_eq]; exact BstLean.Part48.gauss_poly_integrable _
  have hf2 : Integrable (fun z : Fin k → ℝ => (radF53 z ^ (2 * N)) ^ 2) (stdGauss (Fin k)) := by
    rw [hf2_eq]; exact BstLean.Part48.gauss_poly_integrable _
  have hR : R2 ^ 2 ≤ R4 := by
    have h0 : 0 ≤ ∫ z : Fin k → ℝ, ((radF53 z ^ N) ^ 2 - R2) ^ 2 ∂stdGauss (Fin k) :=
      integral_nonneg fun z => sq_nonneg _
    have e : ∫ z : Fin k → ℝ, ((radF53 z ^ N) ^ 2 - R2) ^ 2 ∂stdGauss (Fin k) = R4 - R2 ^ 2 := by
      have e1 : (fun z : Fin k → ℝ => ((radF53 z ^ N) ^ 2 - R2) ^ 2) =
          fun z => (radF53 z ^ (2 * N)) ^ 2 - (2 * R2 * (radF53 z ^ N) ^ 2 - R2 ^ 2) := by
        funext z; ring
      have hl1 : Integrable (fun z : Fin k → ℝ => 2 * R2 * (radF53 z ^ N) ^ 2)
          (stdGauss (Fin k)) := hf.const_mul _
      have hl2 : Integrable (fun _ : Fin k → ℝ => R2 ^ 2) (stdGauss (Fin k)) :=
        integrable_const _
      have hl : Integrable (fun z : Fin k → ℝ => 2 * R2 * (radF53 z ^ N) ^ 2 - R2 ^ 2)
          (stdGauss (Fin k)) := hl1.sub hl2
      rw [e1, integral_sub hf2 hl, integral_sub hl1 hl2, integral_const_mul, integral_const]
      simp only [smul_eq_mul]
      rw [← hR4, ← hR2]; simp; ring
    linarith
  have hR2pos : 0 < R2 := by
    have h0 : 0 ≤ R2 := integral_nonneg fun z => sq_nonneg _
    rcases h0.lt_or_eq with h | h
    · exact h
    · exfalso
      have hz := (integral_eq_zero_iff_of_nonneg (fun z => sq_nonneg _) hf).mp h.symm
      have hne := BstLean.Part57.PropD57.gauss_ne_zero_ae k hk
      obtain ⟨z, hz1, hz2⟩ := (hz.and hne).exists
      have hs : ∑ i, z i ^ 2 ≠ 0 := by
        intro h0
        apply hz2; funext i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (z i))).mp h0 i
          (Finset.mem_univ i)
        simpa using this
      have hr : radF53 z ≠ 0 := by
        intro h0
        apply hs; rw [← hrad, h0]; ring
      exact pow_ne_zero 2 (pow_ne_zero N hr) hz1
  have hR4pos : 0 < R4 := lt_of_lt_of_le (by positivity) hR
  have h1 : R4 * a ≤ R4 * (9 ^ N * b ^ 2) := by
    calc R4 * a ≤ 9 ^ N * (R2 * b) ^ 2 := hB
      _ = R2 ^ 2 * (9 ^ N * b ^ 2) := by ring
      _ ≤ R4 * (9 ^ N * b ^ 2) := mul_le_mul_of_nonneg_right hR (by positivity)
  exact le_of_mul_le_mul_left h1 hR4pos

end SliceRH

open SliceRH

/-- **Reverse Hölder inequality on the sphere**: for a polynomial `H` of total degree `≤ D` on
`ℝ^k`, `k ≥ 1`, and the uniform direction `ω = z/‖z‖` (`z` standard Gaussian):
`E H(ω)⁴ ≤ 8 · 9^D (E H(ω)²)²`. -/
theorem sphere_rh (k D : ℕ) (hk : 1 ≤ k) (H : MvPolynomial (Fin k) ℝ) (hH : H.totalDegree ≤ D) :
    ∫ z, (eval (unitF53 z) H) ^ 4 ∂stdGauss (Fin k) ≤
      8 * 9 ^ D * (∫ z, (eval (unitF53 z) H) ^ 2 ∂stdGauss (Fin k)) ^ 2 := by
  by_cases hD : D = 0
  · subst hD
    have hC : H = C (H.coeff 0) := totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hH)
    rw [hC]
    simp only [eval_C, integral_const, smul_eq_mul, pow_zero, mul_one]
    simp
    nlinarith [sq_nonneg (H.coeff 0 ^ 2)]
  have hD1 : 1 ≤ D := Nat.one_le_iff_ne_zero.mpr hD
  set S0 := (Finset.range (D + 1)).filter (fun b => b % 2 = 0) with hS0
  set S1 := (Finset.range (D + 1)).filter (fun b => ¬ b % 2 = 0) with hS1
  set N0 := 2 * (D / 2) with hN0
  set N1 := 2 * ((D - 1) / 2) + 1 with hN1
  have c0 : ∀ b ∈ S0, 2 * ((N0 - b) / 2) + b = N0 := by
    intro b hb
    simp only [hS0, Finset.mem_filter, Finset.mem_range] at hb
    omega
  have c1 : ∀ b ∈ S1, 2 * ((N1 - b) / 2) + b = N1 := by
    intro b hb
    simp only [hS1, Finset.mem_filter, Finset.mem_range] at hb
    omega
  set P0 := hz H S0 N0 with hP0
  set P1 := hz H S1 N1 with hP1
  have r0 := par_rh hk P0 N0 (hz_deg H S0 N0 c0) (hz_hom H S0 N0 c0)
  have r1 := par_rh hk P1 N1 (hz_deg H S1 N1 c1) (hz_hom H S1 N1 c1)
  set u0 : (Fin k → ℝ) → ℝ := fun z => eval (unitF53 z) P0 with hu0
  set u1 : (Fin k → ℝ) → ℝ := fun z => eval (unitF53 z) P1 with hu1
  have hsplit : ∀ᵐ z ∂stdGauss (Fin k), eval (unitF53 z) H = u0 z + u1 z := by
    filter_upwards [BstLean.Part57.PropD57.gauss_ne_zero_ae k hk] with z hzne
    have h1 := unit_sumsq z hzne
    simp only [hu0, hu1, hP0, hP1]
    rw [hz_unit H S0 N0 _ h1, hz_unit H S1 N1 _ h1, hS0, hS1,
      Finset.sum_filter_add_sum_filter_not, ← map_sum, sum_comp H D hH]
  -- integrability
  have hc0 : Continuous fun ω : Fin k → ℝ => eval ω P0 := continuous_eval P0
  have hc1 : Continuous fun ω : Fin k → ℝ => eval ω P1 := continuous_eval P1
  have i04 : Integrable (fun z => u0 z ^ 4) (stdGauss (Fin k)) := int_unit _ (hc0.pow 4)
  have i14 : Integrable (fun z => u1 z ^ 4) (stdGauss (Fin k)) := int_unit _ (hc1.pow 4)
  have i02 : Integrable (fun z => u0 z ^ 2) (stdGauss (Fin k)) := int_unit _ (hc0.pow 2)
  have i12 : Integrable (fun z => u1 z ^ 2) (stdGauss (Fin k)) := int_unit _ (hc1.pow 2)
  have i01 : Integrable (fun z => u0 z * u1 z) (stdGauss (Fin k)) := int_unit _ (hc0.mul hc1)
  -- the cross term vanishes
  have hcross : ∫ z, u0 z * u1 z ∂stdGauss (Fin k) = 0 := by
    have hneg : ∀ z, u0 (-z) * u1 (-z) = -(u0 z * u1 z) := by
      intro z
      simp only [hu0, hu1, hP0, hP1, unit_neg, hz_hom H S0 N0 c0, hz_hom H S1 N1 c1]
      have e0 : (-1 : ℝ) ^ N0 = 1 := by rw [hN0, pow_mul]; norm_num
      have e1 : (-1 : ℝ) ^ N1 = -1 := by rw [hN1, pow_succ, pow_mul]; norm_num
      rw [e0, e1]; ring
    have hinv := BstLean.Part33.stdGauss_neg_invariant (ι := Fin k)
    have h := integral_map (μ := stdGauss (Fin k)) (φ := fun z : Fin k → ℝ => -z)
      measurable_neg.aemeasurable (f := fun z => u0 z * u1 z)
      (by rw [hinv]; exact i01.aestronglyMeasurable)
    rw [hinv] at h
    simp only [hneg, integral_neg] at h
    linarith
  have hA : ∫ z, (eval (unitF53 z) H) ^ 4 ∂stdGauss (Fin k) ≤
      8 * (∫ z, u0 z ^ 4 ∂stdGauss (Fin k) + ∫ z, u1 z ^ 4 ∂stdGauss (Fin k)) := by
    rw [← integral_add i04 i14, ← integral_const_mul]
    refine integral_mono_ae ?_ ((i04.add i14).const_mul 8) ?_
    · exact int_unit _ ((continuous_eval H).pow 4)
    · filter_upwards [hsplit] with z hz
      rw [hz]
      nlinarith [sq_nonneg (u0 z - u1 z), sq_nonneg (u0 z + u1 z),
        sq_nonneg (u0 z ^ 2 - u1 z ^ 2), sq_nonneg (u0 z * u1 z),
        mul_nonneg (sq_nonneg (u0 z - u1 z)) (sq_nonneg (u0 z + u1 z)),
        mul_nonneg (sq_nonneg (u0 z - u1 z)) (sq_nonneg (u0 z - u1 z))]
  have hBq : ∫ z, (eval (unitF53 z) H) ^ 2 ∂stdGauss (Fin k) =
      ∫ z, u0 z ^ 2 ∂stdGauss (Fin k) + ∫ z, u1 z ^ 2 ∂stdGauss (Fin k) := by
    have e : ∫ z, (eval (unitF53 z) H) ^ 2 ∂stdGauss (Fin k) =
        ∫ z, (u0 z ^ 2 + u1 z ^ 2) + 2 * (u0 z * u1 z) ∂stdGauss (Fin k) := by
      refine integral_congr_ae ?_
      filter_upwards [hsplit] with z hz
      rw [hz]; ring
    have i02p : Integrable (fun z => u0 z ^ 2 + u1 z ^ 2) (stdGauss (Fin k)) := i02.add i12
    have i01c : Integrable (fun z => 2 * (u0 z * u1 z)) (stdGauss (Fin k)) := i01.const_mul 2
    rw [e, integral_add i02p i01c, integral_add i02 i12, integral_const_mul, hcross]
    ring
  rw [hBq]
  set a0 := ∫ z, u0 z ^ 4 ∂stdGauss (Fin k)
  set a1 := ∫ z, u1 z ^ 4 ∂stdGauss (Fin k)
  set b0 := ∫ z, u0 z ^ 2 ∂stdGauss (Fin k)
  set b1 := ∫ z, u1 z ^ 2 ∂stdGauss (Fin k)
  have hb0 : 0 ≤ b0 := integral_nonneg fun z => sq_nonneg _
  have hb1 : 0 ≤ b1 := integral_nonneg fun z => sq_nonneg _
  have p0 : (9 : ℝ) ^ N0 ≤ 9 ^ D := pow_le_pow_right₀ (by norm_num) (by omega)
  have p1 : (9 : ℝ) ^ N1 ≤ 9 ^ D := pow_le_pow_right₀ (by norm_num) (by omega)
  have q0 : a0 ≤ 9 ^ D * b0 ^ 2 := r0.trans (mul_le_mul_of_nonneg_right p0 (sq_nonneg _))
  have q1 : a1 ≤ 9 ^ D * b1 ^ 2 := r1.trans (mul_le_mul_of_nonneg_right p1 (sq_nonneg _))
  have h9 : (0 : ℝ) < 9 ^ D := by positivity
  calc _ ≤ 8 * (a0 + a1) := hA
    _ ≤ 8 * (9 ^ D * b0 ^ 2 + 9 ^ D * b1 ^ 2) := by linarith
    _ ≤ 8 * 9 ^ D * (b0 + b1) ^ 2 := by nlinarith [mul_nonneg hb0 hb1]

/-! ## The slice -/

namespace SliceRH

variable {m : ℕ}

lemma tail_add (b : OrthonormalBasis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (z z' : Fin m → ℝ) :
    tailReconstruct b (z + z') = tailReconstruct b z + tailReconstruct b z' := by
  have h : Fin.cons (0 : ℝ) (z + z') = (Fin.cons 0 z + Fin.cons 0 z' : Fin (m + 1) → ℝ) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  exact (congrArg (BstLean.Part56.basisReconstruct b) h).trans
    (BstLean.Part56.basisReconstruct_add b _ _)

/-- `tailReconstruct b` as a linear map. -/
noncomputable def tailL (b : OrthonormalBasis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1)))) :
    (Fin m → ℝ) →ₗ[ℝ] (Fin (m + 1) → ℝ) where
  toFun := tailReconstruct b
  map_add' := tail_add b
  map_smul' := fun c z => BstLean.Part56.tailReconstruct_smul b c z

lemma tail_coord (b : OrthonormalBasis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (ω : Fin m → ℝ) (i : Fin (m + 1)) :
    tailReconstruct b ω i =
      ∑ j, ω j * tailReconstruct b (fun j' => if j = j' then 1 else 0) i := by
  have h := LinearMap.pi_apply_eq_sum_univ (tailL b) ω
  have h' := congrFun h i
  simpa [tailL] using h'

lemma perp_int (b : OrthonormalBasis (Fin (m + 1)) ℝ (EuclideanSpace ℝ (Fin (m + 1))))
    (v : Fin (m + 1) → ℝ) (hb : b 0 = WithLp.toLp 2 v) (f : (Fin (m + 1) → ℝ) → ℝ)
    (hf : Measurable f) (hf0 : ∀ w, 0 ≤ f w) :
    ∫ g, f (perpDir v g) ∂stdGauss (Fin (m + 1)) =
      ∫ z, f (tailReconstruct b (unitF53 z)) ∂stdGauss (Fin m) := by
  have hp : Measurable (perpDir v) := by unfold perpDir; fun_prop
  have ht : Measurable fun z : Fin m → ℝ => tailReconstruct b (unitF53 z) := by
    have : Measurable (tailReconstruct b) := by
      unfold tailReconstruct BstLean.Part56.basisReconstruct
      fun_prop
    exact this.comp BstLean.Part53.measurable_unitF
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun g => hf0 _)
      (hf.comp hp).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun g => hf0 _)
      (hf.comp ht).aestronglyMeasurable]
  congr 1
  exact BstLean.Part56.perpDir_lintegral_tail b v hb (fun w => ENNReal.ofReal (f w))
    (ENNReal.measurable_ofReal.comp hf)

end SliceRH

/-- **Slice reverse Hölder inequality for `D_{t,v}`.** -/
theorem sliceRHRK (m D : ℕ) (hm : 1 ≤ m) : SliceRHRK m D := by
  intro v hv a r Q hQ
  obtain ⟨b, hb⟩ := BstLean.Part56.unit_basis_exists (m + 1) (by omega) v hv
  have hb0 : b 0 = WithLp.toLp 2 v := hb
  set S := axialS a r
  set R := axialR a r
  set c : Fin (m + 1) → Fin m → ℝ :=
    fun i j => tailReconstruct b (fun j' => if j = j' then 1 else 0) i with hc
  set L : Fin (m + 1) → MvPolynomial (Fin m) ℝ :=
    fun i => C (S * v i) + ∑ j, C (R * c i j) * X j with hL
  have hLd : ∀ i, (L i).totalDegree ≤ 1 := by
    intro i
    refine (totalDegree_add _ _).trans (max_le (by rw [totalDegree_C]; omega) ?_)
    refine BstLean.Part84.totalDegree_finset_sum_le (fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]
  set Q' := aeval L Q with hQ'
  have hQ'd : Q'.totalDegree ≤ D := (BstLean.Part84.deg_aeval L hLd Q).trans hQ
  have hev : ∀ ω : Fin m → ℝ,
      eval (polarPoint v (tailReconstruct b ω) a r) Q = eval ω Q' := by
    intro ω
    rw [hQ', BstLean.Part84.eval_aeval']
    have hx : polarPoint v (tailReconstruct b ω) a r = fun i => eval ω (L i) := ?_
    · rw [hx]
    funext i
    simp only [hL, map_add, eval_C, map_sum, map_mul, eval_X, polarPoint, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul]
    rw [SliceRH.tail_coord b ω i, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hc]; ring
  have hcont : Continuous fun w : Fin (m + 1) → ℝ => eval (polarPoint v w a r) Q := by
    have : Continuous fun w : Fin (m + 1) → ℝ => polarPoint v w a r := by
      unfold polarPoint; fun_prop
    exact (continuous_eval Q).comp this
  have e4 := SliceRH.perp_int b v hb0 (fun w => (eval (polarPoint v w a r) Q) ^ 4)
    (hcont.pow 4).measurable (fun w => by positivity)
  have e2 := SliceRH.perp_int b v hb0 (fun w => (eval (polarPoint v w a r) Q) ^ 2)
    (hcont.pow 2).measurable (fun w => sq_nonneg _)
  simp only [hev] at e4 e2
  rw [e4, e2]
  exact sphere_rh m D hm Q' hQ'd

end BstLean.Part86

#print axioms BstLean.Part86.sphere_rh
#print axioms BstLean.Part86.sliceRHRK
