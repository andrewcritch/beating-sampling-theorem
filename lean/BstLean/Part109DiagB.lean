import BstLean.Part109Defs

/-!
# Part 109: Chebyshev for a diagonal Gaussian quadratic form, and the Gaussian tail of a linear
functional

`diagCheb109 : DiagCheb109`, `linTail109 : LinTail109` (statements in `Part109Defs.lean`).
-/

namespace BstLean.Part109

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

/-! ## Chebyshev, diagonal form -/

theorem diagCheb109 : DiagCheb109 := by
  intro ι _ lam t ht
  classical
  set g : ι → ℝ → ℝ := fun i x => lam i * (x ^ 2 - 1) with hg
  set X : ι → (ι → ℝ) → ℝ := fun i ξ => lam i * (ξ i ^ 2 - 1) with hX
  have hmp : ∀ i, MeasurePreserving (Function.eval i : (ι → ℝ) → ℝ) (stdGauss ι)
      (gaussianReal 0 1) := fun i => by
    unfold stdGauss
    exact measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i
  have hgm : ∀ i, Measurable (g i) := fun i => by simp only [hg]; fun_prop
  have hmem1 : ∀ i, MemLp (g i) 2 (gaussianReal 0 1) := fun i =>
    (BstLean.Part106.memLp_sq_gauss.sub (memLp_const 1)).const_mul (lam i)
  have hmem : ∀ i, MemLp (X i) 2 (stdGauss ι) := fun i =>
    (hmem1 i).comp_measurePreserving (hmp i)
  have hind : iIndepFun X (stdGauss ι) := by
    unfold stdGauss
    exact iIndepFun_pi (μ := fun _ : ι => gaussianReal 0 1) (X := g)
      (fun i => (hgm i).aemeasurable)
  have h2 : ∫ x : ℝ, x ^ 2 ∂gaussianReal 0 1 = 1 := by
    rw [BstLean.Part29.gaussMom_eq 2]
    norm_num [BstLean.Part29.gaussMom, Nat.doubleFactorial, Nat.even_iff]
  have hsqint : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
    BstLean.Part106.memLp_sq_gauss.integrable (by norm_num)
  have hvar1 : ∀ i, Var[g i; gaussianReal 0 1] = 2 * lam i ^ 2 := fun i => by
    have e : g i = fun x => lam i * ((fun x : ℝ => x ^ 2) x - 1) := rfl
    rw [e, variance_const_mul,
      variance_sub_const (X := fun x : ℝ => x ^ 2) (by fun_prop) 1,
      BstLean.Part106.var_sq_gauss]
    ring
  have hmean1 : ∀ i, ∫ x, g i x ∂gaussianReal 0 1 = 0 := fun i => by
    simp only [hg]
    rw [integral_const_mul, integral_sub hsqint (integrable_const _), h2]
    simp
  have hvar_i : ∀ i, Var[X i; stdGauss ι] = 2 * lam i ^ 2 := fun i => by
    have : X i = g i ∘ (Function.eval i) := rfl
    rw [this, ← variance_map (hgm i).aemeasurable (hmp i).measurable.aemeasurable, (hmp i).map_eq]
    exact hvar1 i
  have hmean_i : ∀ i, ∫ ξ, X i ξ ∂stdGauss ι = 0 := fun i => by
    have h := integral_map (μ := stdGauss ι) (φ := Function.eval i)
      (hmp i).measurable.aemeasurable (f := g i) (hgm i).aestronglyMeasurable
    rw [(hmp i).map_eq, hmean1 i] at h
    exact h.symm
  have hsum : (fun ξ : ι → ℝ => ∑ i, lam i * (ξ i ^ 2 - 1)) = ∑ i, X i := by
    funext ξ; simp [hX]
  have hvar : Var[fun ξ : ι → ℝ => ∑ i, lam i * (ξ i ^ 2 - 1); stdGauss ι] =
      2 * ∑ i, lam i ^ 2 := by
    rw [hsum, IndepFun.variance_sum (fun i _ => hmem i)
      (fun i _ j _ hij => hind.indepFun hij)]
    simp [hvar_i, Finset.mul_sum]
  have hmean : ∫ ξ : ι → ℝ, ∑ i, lam i * (ξ i ^ 2 - 1) ∂stdGauss ι = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hmem i).integrable (by norm_num))]
    exact Finset.sum_eq_zero fun i _ => hmean_i i
  have hm2 : MemLp (fun ξ : ι → ℝ => ∑ i, lam i * (ξ i ^ 2 - 1)) 2 (stdGauss ι) := by
    rw [hsum]
    exact memLp_finsetSum' _ (fun i _ => hmem i)
  have h := meas_ge_le_variance_div_sq hm2 ht
  rw [hmean, hvar] at h
  have hs0 : 0 ≤ ∑ i, lam i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsub : (stdGauss ι) {ξ | t ≤ ∑ i, lam i * (ξ i ^ 2 - 1)} ≤
      ENNReal.ofReal (2 * (∑ i, lam i ^ 2) / t ^ 2) := by
    refine le_trans (measure_mono ?_) h
    intro ξ hξ
    simp only [Set.mem_ofPred_eq, sub_zero] at hξ ⊢
    exact hξ.trans (le_abs_self _)
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hsub

/-! ## The Gaussian tail -/

/-- One dimension: `Pr(|x| > t) ≤ 2 e^{−t²/2}`. -/
lemma gauss_tail_one {t : ℝ} (ht : 0 ≤ t) :
    (gaussianReal 0 1).real {x : ℝ | t < |x|} ≤ 2 * Real.exp (-t ^ 2 / 2) := by
  have hmgf : ∀ s : ℝ, mgf id (gaussianReal 0 1) s = Real.exp (s ^ 2 / 2) := fun s => by
    rw [mgf_id_gaussianReal]
    simp
  have h1 := measure_ge_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) t ht
    (integrable_exp_mul_gaussianReal t)
  have h2 := measure_le_le_exp_mul_mgf (μ := gaussianReal 0 1) (X := id) (t := -t) (-t)
    (by linarith) (integrable_exp_mul_gaussianReal (-t))
  rw [hmgf, ← Real.exp_add] at h1 h2
  have e1 : -t * t + t ^ 2 / 2 = -t ^ 2 / 2 := by ring
  have e2 : - -t * -t + (-t) ^ 2 / 2 = -t ^ 2 / 2 := by ring
  rw [e1] at h1
  rw [e2] at h2
  have hsub : {x : ℝ | t < |x|} ⊆ {x : ℝ | t ≤ id x} ∪ {x : ℝ | id x ≤ -t} := by
    intro x hx
    simp only [Set.mem_ofPred_eq, Set.mem_union, id] at hx ⊢
    rcases lt_abs.1 hx with h | h
    · left; exact h.le
    · right; linarith
  calc (gaussianReal 0 1).real {x : ℝ | t < |x|}
      ≤ (gaussianReal 0 1).real ({x : ℝ | t ≤ id x} ∪ {x : ℝ | id x ≤ -t}) :=
        measureReal_mono hsub
    _ ≤ _ := (measureReal_union_le _ _).trans (by linarith)

theorem linTail109 : LinTail109 := by
  intro ι _ d t ht
  classical
  set s := Real.sqrt (∑ i, d i ^ 2) with hs
  have hs0 : 0 ≤ ∑ i, d i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  by_cases hz : s = 0
  · have : {ξ : ι → ℝ | t * s < |∑ i, d i * ξ i|} = ∅ := by
      ext ξ
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_lt, hz, mul_zero]
      have hd : ∀ i, d i = 0 := by
        have h0 : ∑ i, d i ^ 2 = 0 := (Real.sqrt_eq_zero hs0).1 hz
        intro i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (d i))).1 h0 i
          (Finset.mem_univ i)
        exact pow_eq_zero_iff (two_ne_zero) |>.1 this
      simp [hd]
    rw [this]
    simp
    positivity
  have hspos : 0 < s := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hz)
  set A : Matrix Unit ι ℝ := Matrix.of (fun _ i => d i) with hA
  set B : Matrix Unit Unit ℝ := Matrix.of (fun _ _ => s) with hB
  have hAB : A * A.transpose = B * B.transpose := by
    ext a b
    rw [Matrix.mul_apply, Matrix.mul_apply]
    simp only [Matrix.transpose_apply, hA, hB, Matrix.of_apply, Finset.univ_unique,
      Finset.sum_singleton]
    rw [← sq, hs, Real.sq_sqrt hs0]
    exact Finset.sum_congr rfl fun i _ => (sq (d i)).symm
  have hlaw := gaussLin105 ι Unit Unit A B hAB
  have hmA : Measurable (fun ξ : ι → ℝ => A.mulVec ξ) := by fun_prop
  have hmB : Measurable (fun ξ : Unit → ℝ => B.mulVec ξ) := by fun_prop
  have hS : MeasurableSet {v : Unit → ℝ | t * s < |v ()|} :=
    measurableSet_lt measurable_const (measurable_pi_apply ()).abs
  have e1 : (stdGauss ι).real {ξ | t * s < |∑ i, d i * ξ i|} =
      ((stdGauss ι).map (fun ξ => A.mulVec ξ)).real {v : Unit → ℝ | t * s < |v ()|} := by
    rw [map_measureReal_apply hmA hS]
    rfl
  rw [e1, hlaw, map_measureReal_apply hmB hS]
  have hmp : MeasurePreserving (Function.eval () : (Unit → ℝ) → ℝ) (stdGauss Unit)
      (gaussianReal 0 1) := by
    unfold stdGauss
    exact measurePreserving_eval (fun _ : Unit => gaussianReal 0 1) ()
  have hT : MeasurableSet {x : ℝ | t < |x|} := measurableSet_lt measurable_const measurable_abs
  have e2 : (fun ξ : Unit → ℝ => B.mulVec ξ) ⁻¹' {v : Unit → ℝ | t * s < |v ()|} =
      Function.eval () ⁻¹' {x : ℝ | t < |x|} := by
    ext ξ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Matrix.mulVec, dotProduct, hB, Matrix.of_apply,
      Finset.univ_unique, Finset.sum_singleton, Function.eval, abs_mul, abs_of_pos hspos]
    rw [mul_comm s, mul_lt_mul_iff_left₀ hspos]
  rw [e2, ← map_measureReal_apply hmp.measurable hT, hmp.map_eq]
  exact gauss_tail_one ht

end BstLean.Part109

#print axioms BstLean.Part109.diagCheb109
#print axioms BstLean.Part109.linTail109
