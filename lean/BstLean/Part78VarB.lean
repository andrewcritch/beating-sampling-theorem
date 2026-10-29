import BstLean.Part78Defs
import BstLean.Part62Kappa5
import BstLean.Part35Wick

/-!
# Part 78, variance bound, file B: Bessel bound, fourth moments, pointwise Hölder
-/

namespace BstLean.Part78

open MeasureTheory MvPolynomial ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part62 (KCrit γ5 γ5_nonneg E4_le_γ5 fourth_moment_kappa)
open BstLean.Part48 (gauss_poly_integrable)

set_option linter.unusedSectionVars false

/-! ### Degree 2 fourth moment -/

lemma kcrit5_2 : KCrit 2 5 γ5 := by
  refine ⟨by norm_num, γ5_nonneg, fun c hc => E4_le_γ5 c ?_, ?_⟩
  · have := Finset.mem_Icc.mp hc; exact Finset.mem_Icc.mpr ⟨this.1, by omega⟩
  · norm_num [Finset.sum_Icc_succ_top, γ5]

theorem fourth_moment_5_2 (ι : Type) [Fintype ι] (P : MvPolynomial ι ℝ) (hP : P.totalDegree ≤ 2) :
    ∫ z, (eval z P) ^ 4 ∂stdGauss ι ≤ 5 ^ 4 * (∫ z, (eval z P) ^ 2 ∂stdGauss ι) ^ 2 :=
  fourth_moment_kappa 2 5 γ5 kcrit5_2 ι P hP

lemma gpi78 {κ : Type*} [Fintype κ] (P : MvPolynomial κ ℝ) (r : ℕ) :
    Integrable (fun z => (eval z P) ^ r) (stdGauss κ) := by
  have := gauss_poly_integrable (P ^ r); simpa only [map_pow] using this

/-- Cauchy–Schwarz for Gaussian polynomials. -/
lemma poly_cs78 {κ : Type*} [Fintype κ] (U V : MvPolynomial κ ℝ) :
    (∫ z, eval z U * eval z V ∂stdGauss κ) ^ 2 ≤
      (∫ z, (eval z U) ^ 2 ∂stdGauss κ) * (∫ z, (eval z V) ^ 2 ∂stdGauss κ) := by
  have hUV : Integrable (fun z => eval z U * eval z V) (stdGauss κ) := by
    have := gauss_poly_integrable (U * V); simpa only [map_mul] using this
  have hquad (t : ℝ) : 0 ≤ (∫ z, (eval z U) ^ 2 ∂stdGauss κ) * (t * t) +
      (2 * ∫ z, eval z U * eval z V ∂stdGauss κ) * t +
      (∫ z, (eval z V) ^ 2 ∂stdGauss κ) := by
    have h : 0 ≤ ∫ z, (t * eval z U + eval z V) ^ 2 ∂stdGauss κ :=
      integral_nonneg fun z => sq_nonneg _
    have he : (fun z => (t * eval z U + eval z V) ^ 2) = fun z =>
        (t ^ 2 * (eval z U) ^ 2 + (2 * t) * (eval z U * eval z V)) +
          (eval z V) ^ 2 := by funext z; ring
    have i1 : Integrable (fun z => t ^ 2 * (eval z U) ^ 2) (stdGauss κ) :=
      (gpi78 U 2).const_mul _
    have i2 : Integrable (fun z => (2 * t) * (eval z U * eval z V))
      (stdGauss κ) := hUV.const_mul _
    have i12 : Integrable (fun z => t ^ 2 * (eval z U) ^ 2 +
      (2 * t) * (eval z U * eval z V)) (stdGauss κ) := i1.add i2
    rw [he, integral_add i12 (gpi78 V 2), integral_add i1 i2, integral_const_mul,
      integral_const_mul] at h
    nlinarith only [h]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith only [hd]

/-- Pointwise Hölder with the two fourth-moment bounds. -/
lemma holder_pt {κ : Type} [Fintype κ] (U T : MvPolynomial κ ℝ) (hU : U.totalDegree ≤ 2)
    (s1 : ℝ) (hs1 : 0 ≤ s1)
    (hT : ∫ z, (eval z T) ^ 4 ∂stdGauss κ ≤ s1 ^ 2 * (∫ z, (eval z T) ^ 2 ∂stdGauss κ) ^ 2) :
    ∫ z, (eval z U) ^ 2 * (eval z T) ^ 2 ∂stdGauss κ ≤
      25 * s1 * (∫ z, (eval z U) ^ 2 ∂stdGauss κ) * (∫ z, (eval z T) ^ 2 ∂stdGauss κ) := by
  have hcs := poly_cs78 (U ^ 2) (T ^ 2)
  simp only [map_pow] at hcs
  have hU4 := fourth_moment_5_2 κ U hU
  have e4 (P : MvPolynomial κ ℝ) : (fun z => ((eval z P) ^ 2) ^ 2) = fun z => (eval z P) ^ 4 := by
    funext z; ring
  rw [e4, e4] at hcs
  set A := ∫ z, (eval z U) ^ 2 * (eval z T) ^ 2 ∂stdGauss κ
  set u2 := ∫ z, (eval z U) ^ 2 ∂stdGauss κ
  set t2 := ∫ z, (eval z T) ^ 2 ∂stdGauss κ
  set u4 := ∫ z, (eval z U) ^ 4 ∂stdGauss κ
  set t4 := ∫ z, (eval z T) ^ 4 ∂stdGauss κ
  have hA0 : 0 ≤ A := integral_nonneg fun z => by positivity
  have hu2 : 0 ≤ u2 := integral_nonneg fun z => by positivity
  have ht2 : 0 ≤ t2 := integral_nonneg fun z => by positivity
  have hu4 : 0 ≤ u4 := integral_nonneg fun z => by positivity
  have ht4 : 0 ≤ t4 := integral_nonneg fun z => by positivity
  have hB0 : 0 ≤ 25 * s1 * u2 * t2 := by positivity
  have hsq : A ^ 2 ≤ (25 * s1 * u2 * t2) ^ 2 := by
    calc A ^ 2 ≤ u4 * t4 := hcs
      _ ≤ (5 ^ 4 * u2 ^ 2) * (s1 ^ 2 * t2 ^ 2) := mul_le_mul hU4 hT ht4 (by positivity)
      _ = (25 * s1 * u2 * t2) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ hA0 hB0 two_ne_zero).mp hsq

/-! ### Affine second moment -/

lemma coord_mean {ι : Type} [Fintype ι] (a : ι) : (∫ z, z a ∂stdGauss ι) = 0 := by
  classical
  have hw := BstLean.Part35.stdGauss_wick_step a 0 (Fin.elim0 : Fin 0 → ι)
  simpa using hw

lemma aff_second (hG : GaussLin) {ι : Type} [Fintype ι] (c0 : ℝ) (b : ι → ℝ) :
    ∫ u, (c0 + ∑ j, b j * u j) ^ 2 ∂stdGauss ι = c0 ^ 2 + ∑ j, b j ^ 2 := by
  obtain ⟨hi, hv⟩ := hG ι b b
  have hlin : Integrable (fun u : ι → ℝ => ∑ j, b j * u j) (stdGauss ι) := by
    have := gauss_poly_integrable (∑ j, C (b j) * X j : MvPolynomial ι ℝ)
    simpa using this
  have hmean : ∫ u, ∑ j, b j * u j ∂stdGauss ι = 0 := by
    have hc (j : ι) : Integrable (fun u : ι → ℝ => b j * u j) (stdGauss ι) := by
      have := gauss_poly_integrable (C (b j) * X j : MvPolynomial ι ℝ)
      simpa using this
    rw [integral_finsetSum _ fun j _ => hc j]
    simp [integral_const_mul, coord_mean]
  have he : (fun u : ι → ℝ => (c0 + ∑ j, b j * u j) ^ 2) = fun u =>
      (c0 ^ 2 + (2 * c0) * ∑ j, b j * u j) + (∑ j, b j * u j) * (∑ j, b j * u j) := by
    funext u; ring
  have i2 : Integrable (fun u : ι → ℝ => (2 * c0) * ∑ j, b j * u j) (stdGauss ι) :=
    hlin.const_mul _
  have i12 : Integrable (fun u : ι → ℝ => c0 ^ 2 + (2 * c0) * ∑ j, b j * u j) (stdGauss ι) :=
    (integrable_const _).add i2
  rw [he, integral_add i12 hi, integral_add (integrable_const _) i2, integral_const_mul, hmean, hv]
  simp [sq]

/-! ### Bessel with the feature operator bound -/

lemma continuous_pf {n : ℕ} (q : JJ n) : Continuous fun x : Fin n → ℝ => pf x q := by
  unfold pf BstLean.Part41.phiM BstLean.Part36.monoVal
  exact continuous_multiset_prod _ fun i _ => continuous_apply i

lemma sphere_cont_integrableB {n : ℕ} (hn : 1 ≤ n) {f : (Fin n → ℝ) → ℝ}
    (hf : Continuous f) : Integrable f (uniformSphere n) := by
  have := BstLean.Part29.uniformSphere_isProbability n hn
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Set.Icc (fun _ : Fin n => (-1 : ℝ))
    (fun _ => (1 : ℝ)))).bddAbove_image hf.norm.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [BstLean.Part29.uniformSphere_ae_sphere n] with x hx
  apply hC
  apply Set.mem_image_of_mem
  constructor <;> intro i
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i + 1)]
  · have hi := Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)
    rw [hx] at hi
    nlinarith [sq_nonneg (x i - 1)]

lemma bessel {n : ℕ} (hn : 1 ≤ n) (CF : ℝ) (hCF : 0 ≤ CF) (hF : FeatOp n CF)
    (r : (Fin n → ℝ) → ℝ) (hr : Continuous r) :
    ∑ q : JJ n, (∫ x, r x * pf x q ∂uniformSphere n) ^ 2 ≤
      CF / (n : ℝ) * ∫ x, r x ^ 2 ∂uniformSphere n := by
  set c : JJ n → ℝ := fun q => ∫ x, r x * pf x q ∂uniformSphere n with hc
  set g : (Fin n → ℝ) → ℝ := fun x => ∑ q, c q * pf x q with hg
  have hgc : Continuous g := continuous_finsetSum _ fun q _ => continuous_const.mul (continuous_pf q)
  set S := ∑ q : JJ n, c q ^ 2 with hS
  set R := ∫ x, r x ^ 2 ∂uniformSphere n with hR
  set lam := CF / (n : ℝ) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun q _ => sq_nonneg _
  have hrg : ∫ x, r x * g x ∂uniformSphere n = S := by
    have he : (fun x => r x * g x) = fun x => ∑ q, c q * (r x * pf x q) := by
      funext x; simp only [hg, Finset.mul_sum]; exact Finset.sum_congr rfl fun q _ => by ring
    have hi (q : JJ n) : Integrable (fun x => c q * (r x * pf x q)) (uniformSphere n) :=
      (sphere_cont_integrableB hn (hr.mul (continuous_pf q))).const_mul _
    rw [he, integral_finsetSum _ fun q _ => hi q]
    simp only [integral_const_mul, hS]
    exact Finset.sum_congr rfl fun q _ => by simp only [hc]; ring
  have hgg : ∫ x, g x ^ 2 ∂uniformSphere n ≤ lam * S := hF c
  have hquad (t : ℝ) : 0 ≤ t ^ 2 * (lam * S) - 2 * t * S + R := by
    have h : 0 ≤ ∫ x, (t * g x - r x) ^ 2 ∂uniformSphere n := integral_nonneg fun x => sq_nonneg _
    have he : (fun x => (t * g x - r x) ^ 2) = fun x =>
        (t ^ 2 * g x ^ 2 - (2 * t) * (r x * g x)) + r x ^ 2 := by funext x; ring
    have i1 : Integrable (fun x => t ^ 2 * g x ^ 2) (uniformSphere n) :=
      (sphere_cont_integrableB hn (hgc.pow 2)).const_mul _
    have i2 : Integrable (fun x => (2 * t) * (r x * g x)) (uniformSphere n) :=
      (sphere_cont_integrableB hn (hr.mul hgc)).const_mul _
    have i3 : Integrable (fun x => r x ^ 2) (uniformSphere n) :=
      sphere_cont_integrableB hn (hr.pow 2)
    have i12 : Integrable (fun x => t ^ 2 * g x ^ 2 - (2 * t) * (r x * g x)) (uniformSphere n) :=
      i1.sub i2
    rw [he, integral_add i12 i3, integral_sub i1 i2, integral_const_mul,
      integral_const_mul, hrg] at h
    nlinarith [sq_nonneg t]
  rcases hlam0.lt_or_eq with hpos | hzero
  · have h := hquad (1 / lam)
    have e : (1 / lam) ^ 2 * (lam * S) - 2 * (1 / lam) * S + R = R - S / lam := by
      field_simp; ring
    rw [e] at h
    have : S / lam ≤ R := by linarith
    rw [div_le_iff₀ hpos] at this
    linarith
  · rw [← hzero, zero_mul]
    by_contra hcon
    rw [not_le] at hcon
    have h := hquad ((R + 1) / (2 * S))
    rw [← hzero] at h
    have e : (R + 1) / (2 * S) * S = (R + 1) / 2 := by field_simp
    nlinarith

end BstLean.Part78
