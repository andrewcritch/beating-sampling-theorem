import BstLean.Part53Defs
import BstLean.Part48Var
import BstLean.Part53Remez_Interval
import BstLean.Part53Remez_Radial

/-!
# Part 53, wave 1: Lemma R, the Remez step with the Stirling repair (§7 of the source; challenges
# D2 of `chDL1-opus` and §1 of `chDL1-codex`)

Specification: `delegations/answers/p53-spec-opus.md` §3.7.
Replace each `sorry` by a proof. Do not edit the statements. Do not use `native_decide` or `axiom`
anywhere. This file imports `Part53Defs` only (a prover may also import finished Part 29–52 files,
but no other Part 53 wave-1 file).

Suggested route.
* `λ = ‖Z‖/√Q`, `Q = |ι|`, has density `ρ_Q(t) = 2(Q/2)^{Q/2} t^{Q−1} e^{−Qt²/2}/Γ(Q/2)` (`t > 0`).
  Mathlib: `ProbabilityTheory.chiSquared`-type laws may be missing; derive the law of `‖Z‖²` from the
  product of Gaussians (`gammaPDFReal`), or avoid densities: bound `Pr(λ ∈ J)` from below for every
  subinterval `J` of `I = [1 − Q^{−1/2}, 1 + Q^{−1/2}]` by `0.2 √Q |J|`.
* Unimodality: the density on `I` is at least its value at the endpoints. Stirling with remainder
  (`Stirling.le_log_factorial_stirling`, `Real.Gamma` bounds): `ρ_Q(1 ± Q^{−1/2})/√Q ≥
  π^{−1/2} e^{−1−1/√1000} > 0.201` (`chDL1-codex` §1).
* Nikolskii on an interval: `sup_I p² ≤ ((k+1)²/(2ω)) ∫_I p²` for `deg p ≤ k` (Legendre Christoffel
  function at the endpoint: `Σ_{j≤k} (2j+1)/2 = (k+1)²/2`). Then `p(1)² ≤ sup_I p²` since `1 ∈ I`.
-/

namespace BstLean.Part53

open MeasureTheory BstLean.Cost
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part36 (CoefIdxD DD unitOfD mapMD)
open BstLean.Part41 (Mono phiM phiSq colM contr trL frob IsSymmT Tens TSymm fval In41 Pn heavyCount)
open BstLean.Part43 (BofQ varFQ)

variable {n d : ℕ}

private lemma radial_polynomial_sq_integrable (ι : Type) [Fintype ι]
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

private lemma lemmaR53_zero : LemmaR53 0 := by
  intro ι _ _ p hp
  rw [Polynomial.eq_C_of_natDegree_le_zero hp]
  simp only [Polynomial.eval_C, integral_const, probReal_univ, one_smul]
  norm_num
  nlinarith [sq_nonneg (p.coeff 0)]

private lemma radial_second_moment (ι : Type) [Fintype ι]
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

private lemma linear_eval_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (r : Ω → ℝ)
    (hr : MemLp r 2 μ) (hr0 : ∀ z, 0 ≤ r z) (hr2 : ∫ z, r z ^ 2 ∂μ = 1)
    (a b : ℝ) : (a + b) ^ 2 ≤ 2 * ∫ z, (a * r z + b) ^ 2 ∂μ := by
  have hi := hr.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hi2 := hr.integrable_sq
  have hmean0 : 0 ≤ ∫ z, r z ∂μ := integral_nonneg hr0
  have hmean1 : ∫ z, r z ∂μ ≤ 1 := by
    have hn : 0 ≤ ∫ z, (r z - 1) ^ 2 ∂μ := integral_nonneg (fun z => sq_nonneg _)
    have he (z : Ω) : (r z - 1) ^ 2 = r z ^ 2 - 2 * r z + 1 := by ring
    simp_rw [he] at hn
    rw [integral_add (f := fun z => r z ^ 2 - 2 * r z) (g := fun _ => (1 : ℝ))
        (hi2.sub (hi.const_mul 2)) (integrable_const 1),
      integral_sub (f := fun z => r z ^ 2) (g := fun z => 2 * r z)
        hi2 (hi.const_mul 2), integral_const_mul, hr2] at hn
    simp only [integral_const, probReal_univ, one_smul] at hn
    linarith
  have he (z : Ω) : (a * r z + b) ^ 2 =
      a ^ 2 * r z ^ 2 + (2 * a * b) * r z + b ^ 2 := by ring
  simp_rw [he]
  rw [integral_add (f := fun z => a ^ 2 * r z ^ 2 + (2 * a * b) * r z)
      (g := fun _ => b ^ 2)
      ((hi2.const_mul (a ^ 2)).add (hi.const_mul (2 * a * b))) (integrable_const (b ^ 2)),
    integral_add (f := fun z => a ^ 2 * r z ^ 2) (g := fun z => (2 * a * b) * r z)
      (hi2.const_mul (a ^ 2)) (hi.const_mul (2 * a * b))]
  simp only [integral_const_mul, integral_const, probReal_univ, one_smul, hr2, mul_one]
  nlinarith [mul_nonneg hmean0 (sq_nonneg (a + b)),
    mul_nonneg (sub_nonneg.mpr hmean1) (sq_nonneg (a - b))]

private lemma lemmaR53_one : LemmaR53 1 := by
  intro ι _ hι p hp
  let r : (ι → ℝ) → ℝ := fun Z =>
    Real.sqrt (∑ i, Z i ^ 2) / Real.sqrt (Fintype.card ι)
  have hc : Continuous r := by unfold r; fun_prop
  have hr : MemLp r 2 (stdGauss ι) := by
    apply (memLp_two_iff_integrable_sq hc.aestronglyMeasurable).2
    simpa only [Polynomial.eval_X] using radial_polynomial_sq_integrable ι Polynomial.X
  have he (t : ℝ) : p.eval t = p.coeff 1 * t + p.coeff 0 := by
    rw [Polynomial.eval_eq_sum_range' (show p.natDegree < 2 by omega)]
    simp [Finset.sum_range_succ, add_comm]
  have h := linear_eval_bound (stdGauss ι) r hr
    (fun Z => div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (radial_second_moment ι (by omega)) (p.coeff 1) (p.coeff 0)
  simp only [he, mul_one, Nat.cast_one]
  change (p.coeff 1 + p.coeff 0) ^ 2 ≤
    5 / 2 * ((1 : ℝ) + 1) ^ 2 * ∫ Z, (p.coeff 1 * r Z + p.coeff 0) ^ 2 ∂stdGauss ι
  have hint : 0 ≤ ∫ Z, (p.coeff 1 * r Z + p.coeff 0) ^ 2 ∂stdGauss ι :=
    integral_nonneg (fun Z => sq_nonneg _)
  nlinarith

/-- **Lemma R.** -/
theorem lemmaR53 (k : ℕ) : LemmaR53 k := by
  by_cases hk : k = 0
  · subst k
    exact lemmaR53_zero
  by_cases hk1 : k = 1
  · subst k
    exact lemmaR53_one
  intro ι _ hQ p hp
  have hk2 : 2 ≤ k := by omega
  have hs : 0 < Real.sqrt (Fintype.card ι) := Real.sqrt_pos.mpr (by
    exact_mod_cast (show 0 < Fintype.card ι by omega))
  let w := RemezAux.halfWidth (Fintype.card ι)
  have hw : 0 < w := by dsimp [w, RemezAux.halfWidth]; positivity
  have hpoly := RemezAux.affine_midpoint_sq_bound p k hk2 hp 1 w hw
  have hrad := RemezAux.radial_interval_comparison ι hQ p
    (radial_polynomial_sq_integrable ι p)
  have hcoef : ((k : ℝ) + 1) ^ 2 / (4 * w) =
      (5 / 2 * ((k : ℝ) + 1) ^ 2) * (Real.sqrt (Fintype.card ι) / 5) := by
    dsimp [w, RemezAux.halfWidth]
    field_simp
    <;> ring
  rw [hcoef] at hpoly
  exact hpoly.trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hrad (show 0 ≤ (5 / 2 : ℝ) * ((k : ℝ) + 1) ^ 2 by positivity))


end BstLean.Part53
