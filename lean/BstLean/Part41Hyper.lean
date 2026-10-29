import BstLean.Part41Defs

/-!
# Part 41, wave 1: Gaussian hypercontractivity (Bonami form) and Cantelli's inequality

Paper: Lemma `hyper` (at `q = 4`) and Lemma `cantelli` of `proofs/option-m/41-arbitrary-degree.tex`.
Specification: `delegations/answers/p41-spec-opus.md`. Do not use `native_decide` or `axiom` anywhere.

Suggested route for `bonami_gauss`: induction on the variables. Write `P = A + z_i B` with `A`, `B`
free of `z_i` (multilinearity), `deg B ≤ s − 1`. Then `E P⁴ = E A⁴ + 6 E A²B² + 3 E B⁴` (odd moments of
`z_i` vanish, `E z⁴ = 3`), and `E A²B² ≤ √(E A⁴ E B⁴)`; the induction gives `9^s`. `stdGauss ι` is a
product of `gaussianReal 0 1` (Part 29). Cantelli: Markov on `(X − E X + t)²` with `t = σ²/a`.
-/

namespace BstLean.Part41

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)

private lemma gaussian_polynomial_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial ι ℝ) :
    Integrable (fun z => MvPolynomial.eval z P) (stdGauss ι) := by
  classical
  conv in MvPolynomial.eval _ P => rw [P.as_sum]
  simp only [MvPolynomial.eval_sum]
  apply integrable_finsetSum
  intro m hm
  simp only [MvPolynomial.eval_monomial]
  have he (z : ι → ℝ) : m.prod (fun i e => z i ^ e) = ∏ i, z i ^ m i :=
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _)
  simp_rw [he]
  exact (Integrable.fintype_prod (f := fun i x => x ^ m i) (fun i =>
    integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x)
      (μ := gaussianReal 0 1) (by simp) _)).const_mul _

private lemma gaussian_polynomial_pow_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial ι ℝ) (r : ℕ) :
    Integrable (fun z => (MvPolynomial.eval z P) ^ r) (stdGauss ι) := by
  simpa only [MvPolynomial.eval_pow] using gaussian_polynomial_integrable (P ^ r)

private lemma integral_three {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {F G H : Ω → ℝ} (hF : Integrable F μ) (hG : Integrable G μ) (hH : Integrable H μ) :
    (∫ z, F z + G z + H z ∂μ) =
      (∫ z, F z ∂μ) + (∫ z, G z ∂μ) + (∫ z, H z ∂μ) := by
  exact (integral_add (hF.add hG) hH).trans
    (congrArg (fun r => r + ∫ z, H z ∂μ) (integral_add hF hG))

private noncomputable def splitP {ι : Type*} [DecidableEq ι]
    (P : MvPolynomial (Option ι) ℝ) (b : ℕ) : MvPolynomial ι ℝ :=
  ∑ m ∈ P.support.filter (fun m => m none = b), MvPolynomial.monomial m.some (P.coeff m)

private lemma splitP_ml {ι : Type*} [DecidableEq ι]
    (P : MvPolynomial (Option ι) ℝ)
    (hml : ∀ m ∈ P.support, ∀ i, m i ≤ 1) (b : ℕ) :
    ∀ m ∈ (splitP P b).support, ∀ i, m i ≤ 1 := by
  intro m hm i
  obtain ⟨u, hu, hmu⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
  have hmem : m = u.some := by
    have := MvPolynomial.support_monomial_subset hmu
    simpa using this
  subst m
  exact hml u (Finset.mem_filter.mp hu).1 (some i)

private lemma splitP_degree {ι : Type*} [DecidableEq ι]
    (P : MvPolynomial (Option ι) ℝ) (s b : ℕ) (hdeg : P.totalDegree ≤ s) :
    (splitP P b).totalDegree ≤ s - b := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  obtain ⟨hm, hb⟩ := Finset.mem_filter.mp hm
  apply (MvPolynomial.totalDegree_monomial_le _ _).trans
  have hsum := m.sum_option_index (fun _ k => k) (by simp) (by simp)
  have hle := (MvPolynomial.le_totalDegree hm).trans hdeg
  simp only [hb] at hsum
  simp only [Function.id_def]
  omega

private lemma splitP_eval {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial (Option ι) ℝ)
    (hml : ∀ m ∈ P.support, ∀ i, m i ≤ 1) (z : ι → ℝ) (x : ℝ) :
    MvPolynomial.eval (fun o => o.elim x z) P =
      MvPolynomial.eval z (splitP P 0) + x * MvPolynomial.eval z (splitP P 1) := by
  classical
  conv_lhs => rw [P.as_sum]
  simp only [MvPolynomial.eval_sum, splitP, MvPolynomial.eval_monomial,
    Finset.sum_filter, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  have hp := m.prod_option_index (fun o k => (o.elim x z) ^ k)
    (by simp) (by simp [pow_add])
  have hb : m none = 0 ∨ m none = 1 := by have := hml m hm none; omega
  rcases hb with hb | hb
  · simp [hb, hp, MvPolynomial.eval_monomial]
  · simp [hb, hp, MvPolynomial.eval_monomial]
    ring

private lemma affine_gaussian_moment (a b : ℝ) (r : ℕ) :
    (∫ x : ℝ, (a + x * b) ^ r ∂gaussianReal 0 1) =
      ∑ j ∈ Finset.range (r + 1),
        a ^ j * b ^ (r - j) * (r.choose j : ℝ) * BstLean.Part29.gaussMom (r - j) := by
  simp_rw [add_pow, mul_pow]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j hj
    have he (x : ℝ) : a ^ j * (x ^ (r - j) * b ^ (r - j)) * (r.choose j : ℝ) =
        (a ^ j * b ^ (r - j) * (r.choose j : ℝ)) * x ^ (r - j) := by ring
    simp_rw [he, integral_const_mul, BstLean.Part29.gaussMom_eq]
  · intro j hj
    exact ((integrable_pow_of_mem_interior_integrableExpSet (X := fun x : ℝ => x)
      (μ := gaussianReal 0 1) (by simp) (r - j)).mul_const (b ^ (r - j))).const_mul
        (a ^ j) |>.mul_const _

private lemma affine_gaussian_second (a b : ℝ) :
    (∫ x : ℝ, (a + x * b) ^ 2 ∂gaussianReal 0 1) = a ^ 2 + b ^ 2 := by
  rw [affine_gaussian_moment]
  norm_num [Finset.sum_range_succ, BstLean.Part29.gaussMom, Nat.choose]
  ring

private lemma affine_gaussian_fourth (a b : ℝ) :
    (∫ x : ℝ, (a + x * b) ^ 4 ∂gaussianReal 0 1) =
      a ^ 4 + 6 * (a ^ 2 * b ^ 2) + 3 * b ^ 4 := by
  rw [affine_gaussian_moment]
  norm_num [Finset.sum_range_succ, BstLean.Part29.gaussMom, Nat.choose]
  ring

private lemma gaussian_option_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial (Option ι) ℝ) (r : ℕ)
    (hml : ∀ m ∈ P.support, ∀ i, m i ≤ 1) :
    (∫ z, (MvPolynomial.eval z P) ^ r ∂stdGauss (Option ι)) =
      ∫ z, ∫ x : ℝ, (MvPolynomial.eval z (splitP P 0) +
        x * MvPolynomial.eval z (splitP P 1)) ^ r ∂gaussianReal 0 1 ∂stdGauss ι := by
  let e := (MeasurableEquiv.piOptionEquivProd (fun _ : Option ι => ℝ)).symm
  have hm : ((stdGauss ι).prod (gaussianReal 0 1)).map e = stdGauss (Option ι) :=
    Measure.pi_map_piOptionEquivProd (fun _ => gaussianReal 0 1)
  have hi := gaussian_polynomial_pow_integrable P r
  rw [← hm] at hi ⊢
  have hip := (integrable_map_equiv e _).mp hi
  change Integrable (fun p => (MvPolynomial.eval (e p) P) ^ r)
    ((stdGauss ι).prod (gaussianReal 0 1)) at hip
  rw [integral_map_equiv]
  rw [integral_prod _ hip]
  apply integral_congr_ae
  filter_upwards [] with z
  apply integral_congr_ae
  filter_upwards [] with x
  have he : e (z, x) = (fun o => o.elim x z) := by
    funext i
    cases i <;> rfl
  rw [he, splitP_eval P hml]

private lemma gaussian_polynomial_cs {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : MvPolynomial ι ℝ) :
    (∫ z, (MvPolynomial.eval z A) ^ 2 * (MvPolynomial.eval z B) ^ 2
      ∂stdGauss ι) ^ 2 ≤
      (∫ z, (MvPolynomial.eval z A) ^ 4 ∂stdGauss ι) *
      (∫ z, (MvPolynomial.eval z B) ^ 4 ∂stdGauss ι) := by
  have hcross : Integrable (fun z => (MvPolynomial.eval z A) ^ 2 *
      (MvPolynomial.eval z B) ^ 2) (stdGauss ι) := by
    convert gaussian_polynomial_integrable (A ^ 2 * B ^ 2) using 1
    ext z
    rw [map_mul, map_pow, map_pow]
  have hquad (t : ℝ) : 0 ≤
      (∫ z, (MvPolynomial.eval z A) ^ 4 ∂stdGauss ι) * (t * t) +
      (2 * ∫ z, (MvPolynomial.eval z A) ^ 2 * (MvPolynomial.eval z B) ^ 2
        ∂stdGauss ι) * t +
      (∫ z, (MvPolynomial.eval z B) ^ 4 ∂stdGauss ι) := by
    have h : 0 ≤ ∫ z, (t * (MvPolynomial.eval z A) ^ 2 +
        (MvPolynomial.eval z B) ^ 2) ^ 2 ∂stdGauss ι := integral_nonneg (fun z =>
      sq_nonneg (t * (MvPolynomial.eval z A) ^ 2 + (MvPolynomial.eval z B) ^ 2))
    have he : (fun z => (t * (MvPolynomial.eval z A) ^ 2 +
        (MvPolynomial.eval z B) ^ 2) ^ 2) = fun z =>
        (t ^ 2 * (MvPolynomial.eval z A) ^ 4 +
          (2 * t) * ((MvPolynomial.eval z A) ^ 2 * (MvPolynomial.eval z B) ^ 2)) +
            (MvPolynomial.eval z B) ^ 4 := by funext z; ring
    rw [he, integral_three ((gaussian_polynomial_pow_integrable A 4).const_mul (t ^ 2))
      (hcross.const_mul (2 * t)) (gaussian_polynomial_pow_integrable B 4),
      integral_const_mul, integral_const_mul] at h
    nlinarith only [h]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith only [hd]

private lemma bonami_arithmetic (K a b A4 B4 c : ℝ)
    (hK : 0 ≤ K) (ha : 0 ≤ a) (hb : 0 ≤ b) (_hA : 0 ≤ A4) (hB : 0 ≤ B4)
    (hc : 0 ≤ c) (hcs : c ^ 2 ≤ A4 * B4)
    (hAb : A4 ≤ 9 * K * a ^ 2) (hBb : B4 ≤ K * b ^ 2) :
    A4 + 6 * c + 3 * B4 ≤ 9 * K * (a + b) ^ 2 := by
  have hh := hcs.trans (mul_le_mul hAb hBb hB (by positivity))
  have hs : c ^ 2 ≤ (3 * K * a * b) ^ 2 := by nlinarith only [hh]
  have hcb : c ≤ 3 * K * a * b :=
    (sq_le_sq₀ hc (by positivity)).mp hs
  nlinarith [mul_nonneg hK (sq_nonneg b)]

private lemma gaussian_option_second {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial (Option ι) ℝ)
    (hml : ∀ m ∈ P.support, ∀ i, m i ≤ 1) :
    (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss (Option ι)) =
      (∫ z, (MvPolynomial.eval z (splitP P 0)) ^ 2 ∂stdGauss ι) +
      (∫ z, (MvPolynomial.eval z (splitP P 1)) ^ 2 ∂stdGauss ι) := by
  rw [gaussian_option_integral P 2 hml]
  simp_rw [affine_gaussian_second]
  exact integral_add (gaussian_polynomial_pow_integrable _ 2)
    (gaussian_polynomial_pow_integrable _ 2)

private lemma gaussian_option_fourth {ι : Type*} [Fintype ι] [DecidableEq ι]
    (P : MvPolynomial (Option ι) ℝ)
    (hml : ∀ m ∈ P.support, ∀ i, m i ≤ 1) :
    (∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss (Option ι)) =
      (∫ z, (MvPolynomial.eval z (splitP P 0)) ^ 4 ∂stdGauss ι) +
      6 * (∫ z, (MvPolynomial.eval z (splitP P 0)) ^ 2 *
        (MvPolynomial.eval z (splitP P 1)) ^ 2 ∂stdGauss ι) +
      3 * (∫ z, (MvPolynomial.eval z (splitP P 1)) ^ 4 ∂stdGauss ι) := by
  have hc : Integrable (fun z => (MvPolynomial.eval z (splitP P 0)) ^ 2 *
      (MvPolynomial.eval z (splitP P 1)) ^ 2) (stdGauss ι) := by
    convert gaussian_polynomial_integrable ((splitP P 0) ^ 2 * (splitP P 1) ^ 2) using 1
    ext z
    rw [map_mul, map_pow, map_pow]
  rw [gaussian_option_integral P 4 hml]
  simp_rw [affine_gaussian_fourth]
  rw [integral_three (gaussian_polynomial_pow_integrable (splitP P 0) 4)
    (hc.const_mul 6) ((gaussian_polynomial_pow_integrable (splitP P 1) 4).const_mul 3),
    integral_const_mul, integral_const_mul]

private lemma gaussian_rename_integral {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (P : MvPolynomial κ ℝ) (r : ℕ) :
    (∫ z, (MvPolynomial.eval z (MvPolynomial.rename e.symm P)) ^ r ∂stdGauss ι) =
      ∫ z, (MvPolynomial.eval z P) ^ r ∂stdGauss κ := by
  simp_rw [MvPolynomial.eval_rename]
  have hh := (measurePreserving_piCongrLeft (fun _ : κ => gaussianReal 0 1) e).integral_comp'
    (fun z => (MvPolynomial.eval z P) ^ r)
  have he (z : ι → ℝ) : MeasurableEquiv.piCongrLeft (fun _ : κ => ℝ) e z = z ∘ e.symm := by
    funext i
    obtain ⟨j, rfl⟩ := e.surjective i
    simp [MeasurableEquiv.piCongrLeft_apply_apply]
  simpa only [he, stdGauss] using hh

private lemma bonami_bound (ι : Type*) [Fintype ι] :
    ∀ [DecidableEq ι] (s : ℕ) (P : MvPolynomial ι ℝ),
      (∀ m ∈ P.support, ∀ i, m i ≤ 1) → P.totalDegree ≤ s →
      (∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι) ≤
        9 ^ s * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2 := by
  apply Fintype.induction_empty_option (P := fun ι =>
    ∀ [DecidableEq ι] (s : ℕ) (P : MvPolynomial ι ℝ),
      (∀ m ∈ P.support, ∀ i, m i ≤ 1) → P.totalDegree ≤ s →
      (∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι) ≤
        9 ^ s * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2)
  · intro α β instβ e ih instDec s P hml hdeg
    let : Fintype α := Fintype.ofEquiv β e.symm
    classical
    have hml' : ∀ m ∈ (MvPolynomial.rename e.symm P).support, ∀ i, m i ≤ 1 := by
      intro m hm i
      rw [MvPolynomial.support_rename_of_injective e.symm.injective] at hm
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hm
      simpa only [Finsupp.mapDomain_equiv_apply, Equiv.symm_symm] using hml u hu (e i)
    have hh := ih s (MvPolynomial.rename e.symm P) hml'
      ((MvPolynomial.totalDegree_rename_le _ _).trans hdeg)
    simpa only [gaussian_rename_integral] using hh
  · intro instDec s P hml hdeg
    have hp : P = MvPolynomial.C (P.coeff 0) := by
      ext m
      have hm : m = 0 := Subsingleton.elim _ _
      subst m
      simp
    rw [hp]
    simp only [MvPolynomial.eval_C, integral_const, probReal_univ, one_smul]
    exact le_of_eq (by ring) |>.trans
      (le_mul_of_one_le_left (sq_nonneg _) (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 9)))
  · intro α instα ih instDec s P hml hdeg
    classical
    by_cases hs : s = 0
    · have hp : P = MvPolynomial.C (P.coeff 0) :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (by omega)
      rw [hp]
      simp only [MvPolynomial.eval_C, integral_const, probReal_univ,
        one_smul, hs, pow_zero, one_mul]
      exact le_of_eq (by ring)
    · have hp : 9 ^ s = (9 : ℝ) * 9 ^ (s - 1) := by
        have he : s = (s - 1) + 1 := by omega
        conv_lhs => rw [he, pow_succ]
        ring
      rw [gaussian_option_fourth P hml, gaussian_option_second P hml, hp]
      apply bonami_arithmetic
      · positivity
      · exact integral_nonneg (fun _ => sq_nonneg _)
      · exact integral_nonneg (fun _ => sq_nonneg _)
      · exact integral_nonneg (fun _ => by positivity)
      · exact integral_nonneg (fun _ => by positivity)
      · exact integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
      · exact gaussian_polynomial_cs _ _
      · rw [← hp]
        exact ih s (splitP P 0) (splitP_ml P hml 0)
          (by simpa using splitP_degree P s 0 hdeg)
      · exact ih (s - 1) (splitP P 1) (splitP_ml P hml 1) (splitP_degree P s 1 hdeg)

/-- **Bonami's lemma for a finite Gaussian vector**: a multilinear polynomial `P` of degree `≤ s` in
independent standard Gaussians has `E P⁴ ≤ 9^s (E P²)²` (hypercontractivity at `q = 4`). -/
theorem bonami_gauss {ι : Type*} [Fintype ι] [DecidableEq ι] (s : ℕ) (P : MvPolynomial ι ℝ)
    (hml : ∀ m ∈ P.support, ∀ i, m i ≤ 1) (hdeg : P.totalDegree ≤ s) :
    Integrable (fun z => (MvPolynomial.eval z P) ^ 4) (stdGauss ι) ∧
    ∫ z, (MvPolynomial.eval z P) ^ 4 ∂stdGauss ι ≤
      9 ^ s * (∫ z, (MvPolynomial.eval z P) ^ 2 ∂stdGauss ι) ^ 2 := by
  refine ⟨gaussian_polynomial_pow_integrable P 4, ?_⟩
  exact bonami_bound ι s P hml hdeg

/-- **Cantelli's one-sided inequality**. -/
theorem cantelli {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (hX : MemLp X 2 P) (a : ℝ) (ha : 0 < a) :
    P {ω | X ω ≤ (∫ y, X y ∂P) - a} ≤ ENNReal.ofReal (variance X P / (variance X P + a ^ 2)) := by
  let v := variance X P
  let t := v / a
  let Y := fun ω => (∫ y, X y ∂P) - X ω + t
  have hv : 0 ≤ v := variance_nonneg X P
  have ht : 0 ≤ t := div_nonneg hv ha.le
  have hc : 0 < (a + t) ^ 2 := sq_pos_of_pos (by linarith)
  have hY : MemLp Y 2 P :=
    ((memLp_const _).sub hX).add (memLp_const _)
  have hmean : (∫ ω, Y ω ∂P) = t := by
    have hi : Integrable (fun ω => (∫ y, X y ∂P) - X ω) P :=
      (integrable_const _).sub (hX.integrable one_le_two)
    have hh := integral_add hi (integrable_const t)
    have hs := integral_sub (integrable_const (∫ y, X y ∂P))
      (hX.integrable one_le_two)
    change (∫ ω, Y ω ∂P) = (∫ ω, (∫ y, X y ∂P) - X ω ∂P) +
      (∫ _ : Ω, t ∂P) at hh
    rw [hh, hs]
    simp
  have hvar : variance Y P = v := by
    have hm : AEStronglyMeasurable (fun ω => (∫ y, X y ∂P) - X ω) P :=
      aestronglyMeasurable_const.sub hX.aestronglyMeasurable
    exact (variance_add_const hm t).trans
      (variance_const_sub hX.aestronglyMeasurable _)
  have hsecond : (∫ ω, Y ω ^ 2 ∂P) = v + t ^ 2 := by
    have hh := variance_eq_sub hY
    change variance Y P = (∫ ω, Y ω ^ 2 ∂P) - (∫ ω, Y ω ∂P) ^ 2 at hh
    rw [hvar, hmean] at hh
    linarith
  have hsub : {ω | X ω ≤ (∫ y, X y ∂P) - a} ⊆
      {ω | (a + t) ^ 2 ≤ Y ω ^ 2} := by
    intro ω hω
    have hh : a + t ≤ Y ω := by dsimp [Y]; dsimp at hω; linarith
    exact (sq_le_sq₀ (by linarith) (by linarith)).mpr hh
  have hm := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun ω => sq_nonneg (Y ω))) hY.integrable_sq
    ((a + t) ^ 2)
  have hb : P {ω | (a + t) ^ 2 ≤ Y ω ^ 2} ≤
      ENNReal.ofReal ((v + t ^ 2) / (a + t) ^ 2) := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top P _)]
    apply ENNReal.ofReal_le_ofReal
    apply (le_div_iff₀ hc).mpr
    rw [hsecond] at hm
    simpa [mul_comm, Measure.real] using hm
  have heq : (v + t ^ 2) / (a + t) ^ 2 = v / (v + a ^ 2) := by
    dsimp [t]
    have hd : v + a ^ 2 ≠ 0 := ne_of_gt (by positivity)
    have he : a + v / a ≠ 0 := ne_of_gt (by linarith [div_nonneg hv ha.le])
    field_simp
    ring
  exact (measure_mono hsub).trans (heq ▸ hb)

end BstLean.Part41
