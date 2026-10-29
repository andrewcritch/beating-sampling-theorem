import BstLean.Part59Defs
import BstLean.Part53Remez
import BstLean.Part59RPlus_Interval

/-!
# Part 59, wave 1: Lemma R+: the Remez step for nonnegative polynomials of degree `≤ 2k`

Specification: `delegations/answers/p59-spec-opus.md` §3.7. Source: `omDL2-opus-prover.md` §3.3,
Lemma R+ (with the Stirling endpoint density of `chDL1-codex.md` §1).

Suggested route.
* A real polynomial `q ≥ 0` on `ℝ` is `p₁² + p₂²` with `deg p_i ≤ deg q / 2` (factor over `ℂ`: real
  roots have even multiplicity, nonreal roots come in conjugate pairs; `q = |h|²` with `h ∈ ℂ[X]`,
  `p₁ = Re h`, `p₂ = Im h`). Check Mathlib first for a sum-of-two-squares lemma.
* Then apply Part 53's `lemmaR53 k` (`Part53Remez.lean`, finished) to `p₁` and `p₂` and add:
  `q(1) = p₁(1)² + p₂(1)² ≤ 2.5(k+1)² (E p₁(λ)² + E p₂(λ)²) = 2.5(k+1)² E q(λ)`. The last step needs
  integrability of `p_i(λ)²` under `stdGauss ι` (a polynomial in `‖Z‖`; Gaussian moments of every
  order are finite, as in `Part53Remez_Radial.lean`).
* Alternatively, redo Part 53's Nikolskii argument on `I = [1 − ω, 1 + ω]` directly for `q`.

Replace each `sorry` by a proof. Do not edit the statements or `Part59Defs.lean`. Do not use
`native_decide` or `axiom` anywhere. This file imports `Part59Defs` only; a prover may also import
finished files of Parts 29–58, but no other Part 59 wave-1 file. Name private helpers with the suffix
`59x` or make them `private`, so that `Part59Final` does not see a name clash.
-/

namespace BstLean.Part59

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM colM contr trL frob IsSymmT Tens TSymm fval Pn varU sdU heavyCount)
open BstLean.Part43 (BofQ varFQ)
open BstLean.Part53 (sg c0 aH g0 heatA fvA Ncirc LemmaR53 GaussPolar53)

variable {n d : ℕ}

private lemma radial_polynomial_sq_integrable59x (ι : Type) [Fintype ι]
    (p : Polynomial ℝ) :
    Integrable (fun Z =>
      (p.eval (Real.sqrt (∑ i, Z i ^ 2) / Real.sqrt (Fintype.card ι))) ^ 2)
      (stdGauss ι) := by
  classical
  let r : (ι → ℝ) → ℝ := fun Z =>
    Real.sqrt (∑ i, Z i ^ 2) / Real.sqrt (Fintype.card ι)
  have hr : Continuous r := by unfold r; fun_prop
  have hm (j : ℕ) : MemLp (fun Z => r Z ^ j) 2 (stdGauss ι) := by
    apply (memLp_two_iff_integrable_sq (hr.pow j).aestronglyMeasurable).2
    let P : MvPolynomial ι ℝ :=
      (∑ i : ι, MvPolynomial.X i ^ 2) ^ j *
        MvPolynomial.C ((Real.sqrt (Fintype.card ι) ^ j) ^ 2)⁻¹
    have he (Z : ι → ℝ) : (r Z ^ j) ^ 2 = MvPolynomial.eval Z P := by
      simp only [P, MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_sum,
        MvPolynomial.eval_X, MvPolynomial.eval_C]
      unfold r
      rw [div_pow, div_pow, ← pow_mul, mul_comm j 2, pow_mul,
        Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (Z i)))]
      exact div_eq_mul_inv _ _
    simpa only [← he, Pi.pow_apply] using BstLean.Part48.gauss_poly_integrable P
  have hp : MemLp (fun Z => p.eval (r Z)) 2 (stdGauss ι) := by
    simp_rw [Polynomial.eval_eq_sum_range]
    exact memLp_finsetSum _ (fun j _ => (hm j).const_mul (p.coeff j))
  exact hp.integrable_sq

private lemma radial_second_moment59x (ι : Type) [Fintype ι]
    (hι : 0 < Fintype.card ι) :
    ∫ Z, (Real.sqrt (∑ i, Z i ^ 2) / Real.sqrt (Fintype.card ι)) ^ 2
      ∂stdGauss ι = 1 := by
  classical
  have hi (i : ι) : Integrable (fun Z : ι → ℝ => Z i ^ 2) (stdGauss ι) := by
    convert BstLean.Part48.gauss_poly_integrable
      ((MvPolynomial.X i : MvPolynomial ι ℝ) ^ 2) using 1
    ext Z
    simp
  have hm (i : ι) : ∫ Z : ι → ℝ, Z i ^ 2 ∂stdGauss ι = 1 := by
    change ∫ Z : ι → ℝ, Z i ^ 2 ∂Measure.pi (fun _ => ProbabilityTheory.gaussianReal 0 1) = 1
    rw [integral_comp_eval (X := fun _ : ι => ℝ)
      (μ := fun _ : ι => ProbabilityTheory.gaussianReal 0 1)
      (i := i) (f := fun x : ℝ => x ^ 2) (by fun_prop)]
    rw [BstLean.Part29.gaussMom_eq]
    norm_num [BstLean.Part29.gaussMom]
  simp_rw [div_pow, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)),
    Real.sq_sqrt (show (0 : ℝ) ≤ Fintype.card ι by positivity)]
  rw [integral_div, integral_finsetSum _ (fun i _ => hi i)]
  simp_rw [hm]
  simp [ne_of_gt hι]

private lemma radial_polynomial_integrable59x (ι : Type) [Fintype ι]
    (p : Polynomial ℝ) :
    Integrable (fun Z => p.eval (Real.sqrt (∑ i, Z i ^ 2) /
      Real.sqrt (Fintype.card ι))) (stdGauss ι) := by
  have hc : Continuous (fun Z : ι → ℝ => p.eval (Real.sqrt (∑ i, Z i ^ 2) /
      Real.sqrt (Fintype.card ι))) := by fun_prop
  have hm := (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).2
    (radial_polynomial_sq_integrable59x ι p)
  exact hm.integrable (by norm_num)

private lemma lemmaRp59_zero : LemmaRp59 0 := by
  intro ι _ _ p hp hn
  rw [Polynomial.eq_C_of_natDegree_le_zero (show p.natDegree ≤ 0 by simpa using hp)]
  simp only [Polynomial.eval_C, integral_const, probReal_univ, one_smul, Nat.cast_zero]
  have h : 0 ≤ p.coeff 0 := by rw [Polynomial.coeff_zero_eq_eval_zero]; exact hn 0
  nlinarith

private lemma lemmaRp59_one : LemmaRp59 1 := by
  intro ι _ hι p hp hn
  classical
  let r : (ι → ℝ) → ℝ := fun Z =>
    Real.sqrt (∑ i, Z i ^ 2) / Real.sqrt (Fintype.card ι)
  have hi : Integrable r (stdGauss ι) := by
    simpa only [Polynomial.eval_X] using radial_polynomial_integrable59x ι Polynomial.X
  have hi2 : Integrable (fun Z => r Z ^ 2) (stdGauss ι) := by
    simpa only [Polynomial.eval_X] using radial_polynomial_sq_integrable59x ι Polynomial.X
  have hr2 : ∫ Z, r Z ^ 2 ∂stdGauss ι = 1 := radial_second_moment59x ι (by omega)
  have hr0 : 0 ≤ ∫ Z, r Z ∂stdGauss ι := integral_nonneg (fun Z => by dsimp [r]; positivity)
  have hr1 : ∫ Z, r Z ∂stdGauss ι ≤ 1 := by
    have hn : 0 ≤ ∫ Z, (r Z - 1) ^ 2 ∂stdGauss ι := integral_nonneg (fun Z => sq_nonneg _)
    have he (Z : ι → ℝ) : (r Z - 1) ^ 2 = r Z ^ 2 - 2 * r Z + 1 := by ring
    simp_rw [he] at hn
    rw [integral_add (f := fun Z => r Z ^ 2 - 2 * r Z) (g := fun _ => (1 : ℝ))
        (hi2.sub (hi.const_mul 2)) (integrable_const 1),
      integral_sub (f := fun Z => r Z ^ 2) (g := fun Z => 2 * r Z)
        hi2 (hi.const_mul 2), integral_const_mul, hr2] at hn
    simp only [integral_const, probReal_univ, one_smul] at hn
    linarith
  have he (t : ℝ) : p.eval t = p.coeff 2 * t ^ 2 + p.coeff 1 * t + p.coeff 0 := by
    rw [Polynomial.eval_eq_sum_range' (show p.natDegree < 3 by omega)]
    simp [Finset.sum_range_succ]; ring
  have hint : (∫ Z, p.eval (r Z) ∂stdGauss ι) =
      p.coeff 2 + p.coeff 1 * (∫ Z, r Z ∂stdGauss ι) + p.coeff 0 := by
    simp_rw [he]
    rw [integral_add (f := fun Z => p.coeff 2 * r Z ^ 2 + p.coeff 1 * r Z)
        (g := fun _ => p.coeff 0)
        ((hi2.const_mul _).add (hi.const_mul _)) (integrable_const _),
      integral_add (f := fun Z => p.coeff 2 * r Z ^ 2) (g := fun Z => p.coeff 1 * r Z)
        (hi2.const_mul _) (hi.const_mul _)]
    simp only [integral_const_mul, integral_const, probReal_univ, one_smul, hr2, mul_one]
  have h1 := hn 1
  have hm1 := hn (-1)
  rw [he] at h1 hm1
  norm_num at h1 hm1
  have hbound : p.eval 1 ≤ 2 * ∫ Z, p.eval (r Z) ∂stdGauss ι := by
    rw [he, hint]
    norm_num
    nlinarith [mul_nonneg hr0 h1, mul_nonneg (sub_nonneg.mpr hr1) hm1]
  have hnonneg : 0 ≤ ∫ Z, p.eval (r Z) ∂stdGauss ι := integral_nonneg (fun Z => hn _)
  simp only [Nat.cast_one]
  change p.eval 1 ≤ 5 / 2 * ((1 : ℝ) + 1) ^ 2 * ∫ Z, p.eval (r Z) ∂stdGauss ι
  nlinarith

open BstLean.Part53.RemezAux

private lemma radial_interval_comparison59x (ι : Type) [Fintype ι] (hQ : 1000 ≤ Fintype.card ι)
    (p : Polynomial ℝ) (hn : ∀ x : ℝ, 0 ≤ p.eval x)
    (hp : Integrable (fun Z => p.eval (Real.sqrt (∑ i, Z i ^ 2) /
      Real.sqrt (Fintype.card ι))) (stdGauss ι)) :
    (Real.sqrt (Fintype.card ι) / 5) *
      (∫ t in (1 - halfWidth (Fintype.card ι))..(1 + halfWidth (Fintype.card ι)), p.eval t) ≤
      ∫ Z, p.eval (Real.sqrt (∑ i, Z i ^ 2) / Real.sqrt (Fintype.card ι)) ∂stdGauss ι := by
  have : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  let Q := Fintype.card ι
  let w := halfWidth Q
  let A := normalizedRadialFactor ι
  have hQr : (1000 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hs : 30 ≤ Real.sqrt Q := (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num; linarith)
  have hw : 0 < w := by dsimp [w, halfWidth]; positivity
  have hw1 : w ≤ 1 / 60 := by
    dsimp [w, halfWidth]
    exact (div_le_div_iff₀ (by positivity) (by norm_num)).mpr (by linarith)
  have hsub : Set.Ioc (1 - w) (1 + w) ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    simp only [Set.mem_Ioc, Set.mem_Ioi] at ht ⊢
    linarith
  let f : ℝ → ℝ := fun t => A * radialWeight Q t * p.eval t
  have hi : IntegrableOn f (Set.Ioi 0) volume := by
    dsimp only [IntegrableOn, f]
    simp_rw [mul_assoc]
    exact (normalized_radius_integrable ι (fun t => p.eval t) hp).const_mul A
  have hmono : (Real.sqrt Q / 5) * (∫ t in Set.Ioc (1-w) (1+w), p.eval t) ≤
      ∫ t in Set.Ioc (1-w) (1+w), f t := by
    rw [← integral_const_mul]
    apply setIntegral_mono_on
      (p.continuous.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self |>.const_mul _)
      (hi.mono_set hsub) measurableSet_Ioc
    intro t ht
    have hlow := normalized_radialWeight_lower (q := (Q : ℝ)) hQr
      (normalizedRadialFactor_nonneg ι) (normalized_radius_mass ι)
      (show t ∈ Set.Icc (1 - halfWidth Q) (1 + halfWidth Q) from ⟨ht.1.le, ht.2⟩)
    exact mul_le_mul_of_nonneg_right hlow (hn t)
  have hbig : (∫ t in Set.Ioc (1-w) (1+w), f t) ≤ ∫ t in Set.Ioi (0 : ℝ), f t := by
    apply setIntegral_mono_set hi
      (Filter.Eventually.of_forall fun t => ?_) (Filter.Eventually.of_forall hsub)
    dsimp [f, A]
    exact mul_nonneg (mul_nonneg (normalizedRadialFactor_nonneg ι)
      (radialWeight_pos _ _).le) (hn t)
  rw [normalized_radius_integral ι (fun t => p.eval t)]
  rw [intervalIntegral.integral_of_le (by linarith : 1-w ≤ 1+w)]
  change (Real.sqrt Q / 5) * (∫ t in Set.Ioc (1-w) (1+w), p.eval t) ≤ _
  have he : (∫ t in Set.Ioi (0 : ℝ), f t) =
      A * ∫ t in Set.Ioi (0 : ℝ), radialWeight Q t * p.eval t := by
    simp only [f, mul_assoc, integral_const_mul]
  exact hmono.trans (hbig.trans_eq he)


/-- **Lemma R+.** -/
theorem lemmaRp59 (k : ℕ) : LemmaRp59 k := by
  by_cases hk : k = 0
  · subst k; exact lemmaRp59_zero
  by_cases hk1 : k = 1
  · subst k; exact lemmaRp59_one
  intro ι _ hQ p hp hn
  have hk2 : 2 ≤ k := by omega
  have hs : 0 < Real.sqrt (Fintype.card ι) := Real.sqrt_pos.mpr (by
    exact_mod_cast (show 0 < Fintype.card ι by omega))
  let w := halfWidth (Fintype.card ι)
  have hw : 0 < w := by dsimp [w, halfWidth]; positivity
  have hpoly := RPlusAux.affine_nonneg_bound59x p k hk2 hp hn 1 w hw
  have hrad := radial_interval_comparison59x ι hQ p hn
    (radial_polynomial_integrable59x ι p)
  have hcoef : ((k : ℝ) + 1) ^ 2 / (4 * w) =
      (5 / 2 * ((k : ℝ) + 1) ^ 2) * (Real.sqrt (Fintype.card ι) / 5) := by
    dsimp [w, halfWidth]
    field_simp
    ring
  rw [hcoef] at hpoly
  exact hpoly.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hrad (show 0 ≤ (5 / 2 : ℝ) * ((k : ℝ) + 1) ^ 2 by positivity))

end BstLean.Part59
