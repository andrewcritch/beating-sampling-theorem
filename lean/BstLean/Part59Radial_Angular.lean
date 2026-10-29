import BstLean.Part59Radial_Algebra
import BstLean.Part53T2_Polar
import BstLean.Part45DegDrop

/-! # Part 59: angular variance transfer through Lemma R+ -/

namespace BstLean.Part59

open MeasureTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part36 (CoefIdxD DD mapMD unitOfD)
open BstLean.Part41 (Tens uJ contr varU sdU Pcal)
open BstLean.Part40 (SphLaw)
open BstLean.Part53 (fvA sg GaussPolar53)
open BstLean.Part53.T2Aux

variable {n d : ℕ}

private lemma ofReal_integral_le59x {α : Type*} [MeasurableSpace α]
    {ν : Measure α} {g : α → ℝ} (hg : ∀ x, 0 ≤ g x) :
    ENNReal.ofReal (∫ x, g x ∂ν) ≤ ∫⁻ x, ENNReal.ofReal (g x) ∂ν := by
  by_cases hi : Integrable g ν
  · rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hg)]
  · rw [integral_undef hi, ENNReal.ofReal_zero]; exact bot_le

private lemma fvA_positive59x (k : ℕ) (A : Tens n) (W : CoefIdxD n d → ℝ) (x : Fin n → ℝ) :
    fvA k A (mapMD W x) = A 0 default + ∑ j ∈ Finset.Icc 1 k, uJ A j W x := by
  classical
  unfold fvA
  rw [Finset.sum_range_succ', add_comm]
  rw [show Finset.Icc 1 k = Finset.Ico 1 (k + 1) by rfl, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel]
  congr 1
  · simp [contr]
  · apply Finset.sum_congr rfl
    intro j _
    rw [Nat.add_comm 1 j]
    rfl

private lemma variance_polynomial59x (μ : Measure (Fin n → ℝ)) (hμ : SphLaw n μ)
    (hn : 1 ≤ n) (k : ℕ) (A : Tens n) :
    ∃ Q : MvPolynomial (CoefIdxD n d) ℝ, Q.totalDegree ≤ 2 * k ∧
      ∀ W, MvPolynomial.eval W Q = varU μ (fun x => fvA k A (mapMD W x)) := by
  classical
  let := hμ.prob
  let S : Tens n := fun j w => Real.sqrt (DD n d) ^ j * A j w
  obtain ⟨Q, hdeg, heval⟩ := BstLean.Part45.var_poly45 (d := d) hμ k S
  refine ⟨Q, hdeg, fun W => ?_⟩
  have hD : Real.sqrt (DD n d) ≠ 0 := (Real.sqrt_pos.mpr (BstLean.Part36.DD_pos hn)).ne'
  have hp : Pcal k S W = fun x => ∑ j ∈ Finset.Icc 1 k, uJ A j W x := by
    funext x
    unfold Pcal
    apply Finset.sum_congr rfl
    intro j _
    have hs : uJ S j W x = Real.sqrt (DD n d) ^ j * uJ A j W x := by
      unfold uJ contr S
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    rw [hs]
    field_simp
  rw [heval, hp]
  have hi : MemLp (fun x => ∑ j ∈ Finset.Icc 1 k, uJ A j W x) 2 μ :=
    memLp_finsetSum _ (fun j _ => sphere_memLp hμ (continuous_u A j W))
  have hs := sd_shift (A 0 default) _ hi
  simp_rw [fvA_positive59x]
  have h0 : 0 ≤ varU μ (fun x => ∑ j ∈ Finset.Icc 1 k, uJ A j W x) :=
    integral_nonneg fun _ => sq_nonneg _
  have h1 : 0 ≤ varU μ (fun x => A 0 default + ∑ j ∈ Finset.Icc 1 k, uJ A j W x) :=
    integral_nonneg fun _ => sq_nonneg _
  change Real.sqrt _ = Real.sqrt _ at hs
  exact (Real.sqrt_inj h0 h1).mp hs.symm

private noncomputable def rayPoly59x {ι : Type} [Fintype ι]
    (Q : MvPolynomial ι ℝ) (W : ι → ℝ) : Polynomial ℝ :=
  ∑ e ∈ Q.support, Polynomial.C (Q.coeff e * ∏ i ∈ e.support, W i ^ e i) *
    Polynomial.X ^ (e.sum fun _ a => a)

private lemma rayPoly_degree59x {ι : Type} [Fintype ι]
    (Q : MvPolynomial ι ℝ) (W : ι → ℝ) :
    (rayPoly59x Q W).natDegree ≤ Q.totalDegree := by
  classical
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro e he
  exact (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (MvPolynomial.le_totalDegree he)

private lemma rayPoly_eval59x {ι : Type} [Fintype ι]
    (Q : MvPolynomial ι ℝ) (W : ι → ℝ) (l : ℝ) :
    (rayPoly59x Q W).eval l = MvPolynomial.eval (l • W) Q := by
  classical
  simp only [rayPoly59x, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, MvPolynomial.eval_eq]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
    ← Finset.prod_pow_eq_pow_sum, Finsupp.sum]
  ring

/-- Lemma R+ transfers the variance of an arbitrary coefficient family from Gaussian input
to its angular input. -/
lemma angular_variance59x (k : ℕ) (hRp : LemmaRp59 k) (hP : GaussPolar53)
    (μ : Measure (Fin n → ℝ)) (hμ : SphLaw n μ) (hn : 1 ≤ n)
    (hcard : 1000 ≤ Fintype.card (CoefIdxD n d)) (A : Tens n)
    (hi : Integrable (fun Z => varU μ (fun x => fvA k A (mapMD (sg n d • Z) x)))
      (stdGauss (CoefIdxD n d))) :
    (∫⁻ Z, ENNReal.ofReal (varU μ (fun x => fvA k A (mapMD (unitOfD Z) x)))
      ∂stdGauss (CoefIdxD n d)) ≤
      ENNReal.ofReal (5 / 2 * ((k : ℝ) + 1) ^ 2 *
        ∫ Z, varU μ (fun x => fvA k A (mapMD (sg n d • Z) x)) ∂stdGauss (CoefIdxD n d)) := by
  classical
  let := hμ.prob
  let R : ℝ := 5 / 2 * ((k : ℝ) + 1) ^ 2
  have hR : 0 ≤ R := by dsimp [R]; positivity
  let G := fun W : CoefIdxD n d → ℝ => varU μ (fun x => fvA k A (mapMD W x))
  have hG : Measurable G := variance_fvA_measurable59x μ k A
  have hG0 (W) : 0 ≤ G W := integral_nonneg fun _ => sq_nonneg _
  let F := fun W : CoefIdxD n d → ℝ => fun r : ℝ =>
    ENNReal.ofReal (R * G ((r / Real.sqrt (DD n d)) • W))
  have hFm : Measurable (Function.uncurry F) := by
    exact (measurable_const.mul (hG.comp ((measurable_snd.div_const _).smul measurable_fst))).ennreal_ofReal
  have hrad : Measurable (fun Z : CoefIdxD n d → ℝ => Real.sqrt (∑ i, Z i ^ 2)) := by
    fun_prop
  have hrem (Z : CoefIdxD n d → ℝ) :
      ENNReal.ofReal (G (unitOfD Z)) ≤
        ∫⁻ Z', F (unitOfD Z) (Real.sqrt (∑ i, Z' i ^ 2)) ∂stdGauss (CoefIdxD n d) := by
    obtain ⟨Q, hdeg, hQ⟩ := variance_polynomial59x μ hμ hn k A
    let q := rayPoly59x Q (unitOfD Z)
    have heval (l) : q.eval l = G (l • unitOfD Z) := by
      rw [rayPoly_eval59x, hQ]
    have hr := hRp (CoefIdxD n d) hcard q ((rayPoly_degree59x _ _).trans hdeg)
      (fun l => by rw [heval]; exact hG0 _)
    rw [heval, one_smul] at hr
    calc
      _ ≤ ENNReal.ofReal (R * ∫ Z', q.eval (Real.sqrt (∑ i, Z' i ^ 2) /
          Real.sqrt (Fintype.card (CoefIdxD n d))) ∂stdGauss (CoefIdxD n d)) :=
        ENNReal.ofReal_le_ofReal hr
      _ = ENNReal.ofReal (∫ Z', R * q.eval (Real.sqrt (∑ i, Z' i ^ 2) /
          Real.sqrt (Fintype.card (CoefIdxD n d))) ∂stdGauss (CoefIdxD n d)) := by
        rw [integral_const_mul]
      _ ≤ ∫⁻ Z', ENNReal.ofReal (R * q.eval (Real.sqrt (∑ i, Z' i ^ 2) /
          Real.sqrt (Fintype.card (CoefIdxD n d)))) ∂stdGauss (CoefIdxD n d) :=
        ofReal_integral_le59x (fun Z' => mul_nonneg hR (by rw [heval]; exact hG0 _))
      _ = _ := by
        apply lintegral_congr
        intro Z'
        rw [heval]
        rfl
  calc
    _ ≤ ∫⁻ Z, ∫⁻ Z', F (unitOfD Z) (Real.sqrt (∑ i, Z' i ^ 2))
        ∂stdGauss (CoefIdxD n d) ∂stdGauss (CoefIdxD n d) := lintegral_mono hrem
    _ = ∫⁻ Z, F (unitOfD Z) (Real.sqrt (∑ i, Z i ^ 2)) ∂stdGauss (CoefIdxD n d) :=
      (hP n d F hFm).symm
    _ = ∫⁻ Z, ENNReal.ofReal (R * G (sg n d • Z)) ∂stdGauss (CoefIdxD n d) := by
      apply lintegral_congr_ae
      filter_upwards [gauss_ae_nonzero (d := d) hn] with Z hZ
      change ENNReal.ofReal (R * G (radialScale n d Z • unitOfD Z)) = _
      rw [scale_unit Z hZ]
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hi.const_mul R)
        (Filter.Eventually.of_forall fun Z => mul_nonneg hR (hG0 _)), integral_const_mul]

end BstLean.Part59
