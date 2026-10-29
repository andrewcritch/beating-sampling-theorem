import BstLean.Part108Defs

/-!
# Part 108, Gaussian facts

* `gMom108`: values and bounds of `E|g|^{2j}`.
* `evalMom108`: the moments of `|A₁(x)|²` for the Gaussian version of `A`.
* `linLaw108`: the coefficients of degree 1 of the Gaussian version of `F`.
* `htailMom108`: the second moment of the terms of degree at least 2 of `F`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part108

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

/-! ## Moments of the squared norm -/

section Mom

variable {ι : Type} [Fintype ι]

lemma coordPow_int (i : ι) (r : ℕ) : Integrable (fun z : ι → ℝ => z i ^ r) (stdGauss ι) := by
  classical
  have h := BstLean.Part35.stdGauss_prod_integrable (ι := ι) r (fun _ => i)
  simpa using h

lemma coordPow_integral (i : ι) (r : ℕ) :
    ∫ z : ι → ℝ, z i ^ r ∂stdGauss ι = BstLean.Part29.gaussMom r := by
  have hmp : MeasurePreserving (Function.eval i : (ι → ℝ) → ℝ) (stdGauss ι)
      (gaussianReal 0 1) := by
    unfold stdGauss
    exact measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i
  rw [← BstLean.Part29.gaussMom_eq, ← hmp.map_eq]
  exact (integral_map hmp.measurable.aemeasurable
    (Measurable.aestronglyMeasurable (by fun_prop : Measurable fun x : ℝ => x ^ r))).symm

lemma powMean (z : ι → ℝ) (j : ℕ) :
    (∑ i, z i ^ 2) ^ (j + 1) ≤ (Fintype.card ι : ℝ) ^ j * ∑ i, z i ^ (2 * (j + 1)) := by
  rcases isEmpty_or_nonempty ι with h | h
  · simp
  · have hc : (0 : ℝ) < (Fintype.card ι : ℝ) ^ j := by
      have : 0 < Fintype.card ι := Fintype.card_pos
      positivity
    have h1 := pow_sum_div_card_le_sum_pow (s := (Finset.univ : Finset ι))
      (f := fun i => z i ^ 2) (fun i _ => sq_nonneg _) j
    rw [div_le_iff₀ (by simpa using hc)] at h1
    simp only [Finset.card_univ, ← pow_mul] at h1
    linarith

lemma normSqPow_int (j : ℕ) :
    Integrable (fun z : ι → ℝ => (∑ i, z i ^ 2) ^ j) (stdGauss ι) := by
  cases j with
  | zero => simp
  | succ j =>
    have hdom : Integrable (fun z : ι → ℝ =>
        (Fintype.card ι : ℝ) ^ j * ∑ i, z i ^ (2 * (j + 1))) (stdGauss ι) :=
      (integrable_finsetSum _ fun i _ => coordPow_int i _).const_mul _
    refine Integrable.mono' hdom (Measurable.aestronglyMeasurable (by fun_prop))
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    exact powMean z j

lemma normSqPow_le (j : ℕ) :
    ∫ z : ι → ℝ, (∑ i, z i ^ 2) ^ (j + 1) ∂stdGauss ι ≤
      (Fintype.card ι : ℝ) ^ j * ((Fintype.card ι : ℝ) * BstLean.Part29.gaussMom (2 * (j + 1))) := by
  have hdom : Integrable (fun z : ι → ℝ =>
      (Fintype.card ι : ℝ) ^ j * ∑ i, z i ^ (2 * (j + 1))) (stdGauss ι) :=
    (integrable_finsetSum _ fun i _ => coordPow_int i _).const_mul _
  refine le_trans (integral_mono (normSqPow_int (j + 1)) hdom fun z => powMean z j) ?_
  rw [integral_const_mul, integral_finsetSum _ fun i _ => coordPow_int i _]
  simp [coordPow_integral]

end Mom

lemma gaussMom_six : BstLean.Part29.gaussMom 6 = 15 := by
  unfold BstLean.Part29.gaussMom
  simp only [show Even 6 from by decide, ite_true]
  norm_num [Nat.doubleFactorial]

lemma gaussMom_eight : BstLean.Part29.gaussMom 8 = 105 := by
  unfold BstLean.Part29.gaussMom
  simp only [show Even 8 from by decide, ite_true]
  norm_num [Nat.doubleFactorial]

theorem gMom108 : GMom108 := by
  intro n _
  refine ⟨fun j => ?_, ?_, ?_, ?_⟩
  · unfold gmom
    exact integral_nonneg fun z => by positivity
  · unfold gmom
    have h := BstLean.Part107.normSq_mom2 (ι := Fin n)
    simpa using h
  · unfold gmom
    have h := normSqPow_le (ι := Fin n) 2
    rw [show 2 * (2 + 1) = 6 from rfl, gaussMom_six] at h
    simp only [Fintype.card_fin] at h
    linarith [h]
  · unfold gmom
    have h := normSqPow_le (ι := Fin n) 3
    rw [show 2 * (3 + 1) = 8 from rfl, gaussMom_eight] at h
    simp only [Fintype.card_fin] at h
    linarith [h]

/-! ## The distribution of `A₁(x)` -/

lemma kap_nonneg (dA : ℕ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ BstLean.Part107.kap dA t := by
  unfold BstLean.Part107.kap
  exact Finset.sum_nonneg fun j _ => pow_nonneg ht j

lemma dot_self_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ dot x x := by
  unfold dot
  exact Finset.sum_nonneg fun i _ => mul_self_nonneg _

/-- For every `x`: `A₁(x)` is `√(κ(|x|²))` times a standard Gaussian vector. -/
theorem evalLaw (n dA : ℕ) (x : Fin n → ℝ) :
    (bwGauss n n dA 1).map (fun A => bwEval A x) =
      (stdGauss (Fin n)).map
        (fun g => Real.sqrt (BstLean.Part107.kap dA (dot x x)) • g) := by
  classical
  set κ := BstLean.Part107.kap dA (dot x x) with hκ
  have hκ0 : 0 ≤ κ := kap_nonneg dA (dot_self_nonneg x)
  let A : Matrix (Fin n) (CoefIdx n n dA) ℝ := BstLean.Part107.rowMatAll 1 x
  let B : Matrix (Fin n) (Fin n) ℝ := Real.sqrt κ • 1
  have hAB : A * A.transpose = B * B.transpose := by
    simp only [A, B, BstLean.Part107.rowMatAll_mul_transpose, Matrix.transpose_smul,
      Matrix.transpose_one, Matrix.mul_smul, Matrix.mul_one, smul_smul,
      Real.mul_self_sqrt hκ0]
    congr 1
    rw [hκ]
    unfold BstLean.Part107.kap
    ring
  have hL : (fun c : CoefIdx n n dA → ℝ => bwEval c x) ∘
      (fun ξ : CoefIdx n n dA → ℝ => bwOfCoord ((1 : ℝ) • ξ)) = fun ξ => A.mulVec ξ := by
    funext ξ
    simp only [Function.comp_apply, BstLean.Part107.bwEval_eq_rowMatAll, A]
  have hR : (fun g : Fin n → ℝ => Real.sqrt κ • g) = fun g => B.mulVec g := by
    funext g
    simp only [B, Matrix.smul_mulVec, Matrix.one_mulVec]
  unfold bwGauss
  rw [Measure.map_map (BstLean.Part107.measurable_bwEval_vec x) (measurable_bwOfCoord_smul 1),
    hL, hR, gaussLin105 _ _ _ A B hAB]

theorem evalMom108 : EvalMom108 := by
  intro n dA x j
  set κ := BstLean.Part107.kap dA (dot x x) with hκ
  have hκ0 : 0 ≤ κ := kap_nonneg dA (dot_self_nonneg x)
  have hf : Measurable (fun y : Fin n → ℝ => ENNReal.ofReal ((∑ a, y a ^ 2) ^ j)) := by
    fun_prop
  have h1 : ∫⁻ A, ENNReal.ofReal ((∑ a, bwEval A x a ^ 2) ^ j) ∂bwGauss n n dA 1 =
      ∫⁻ y, ENNReal.ofReal ((∑ a, y a ^ 2) ^ j) ∂((bwGauss n n dA 1).map (fun A => bwEval A x)) :=
    (lintegral_map hf (BstLean.Part107.measurable_bwEval_vec x)).symm
  rw [h1, evalLaw, lintegral_map hf (measurable_const_smul _), ← hκ]
  have e : ∀ g : Fin n → ℝ, (∑ a, (Real.sqrt κ • g) a ^ 2) ^ j = κ ^ j * (∑ a, g a ^ 2) ^ j := by
    intro g
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, Real.sq_sqrt hκ0]
  simp_rw [e]
  rw [← ofReal_integral_eq_lintegral_ofReal ((normSqPow_int j).const_mul _)
    (Filter.Eventually.of_forall fun g => by positivity), integral_const_mul]
  rfl

/-! ## The coefficients of degree 1 of `F` -/

lemma mono1_inj {n d : ℕ} (hd : 1 ≤ d) {i i' : Fin n} (h : mono1 n d hd i = mono1 n d hd i') :
    i = i' := by
  have := congrArg (fun m : MonoIdx n d => m.2.val) h
  simpa [mono1] using this

theorem linLaw108 : LinLaw108 := by
  classical
  intro n dF hd
  let S : Matrix (Fin n) (CoefIdx n 1 dF) ℝ :=
    fun i c => if c = ((0 : Fin 1), mono1 n dF hd i) then 1 else 0
  have hSS : S * S.transpose = (1 : Matrix (Fin n) (Fin n) ℝ) * (1 : Matrix (Fin n) (Fin n) ℝ).transpose := by
    have hS : ∀ i c, S i c = if c = ((0 : Fin 1), mono1 n dF hd i) then 1 else 0 :=
      fun _ _ => rfl
    rw [Matrix.transpose_one, Matrix.mul_one]
    ext i i'
    rw [Matrix.mul_apply]
    rw [Finset.sum_eq_single ((0 : Fin 1), mono1 n dF hd i')
      (fun b _ hb => by rw [Matrix.transpose_apply, hS i' b]; simp [hb]) (by simp)]
    rw [Matrix.transpose_apply, hS i, hS i', Matrix.one_apply]
    by_cases h : i = i'
    · simp [h]
    · have : ¬ ((0 : Fin 1), mono1 n dF hd i') = ((0 : Fin 1), mono1 n dF hd i) := by
        intro hc
        exact h (mono1_inj hd (Prod.ext_iff.1 hc).2).symm
      simp [h, this]
  have hL : (linF hd) ∘ (fun ξ : CoefIdx n 1 dF → ℝ => bwOfCoord ((1 : ℝ) • ξ)) =
      fun ξ => S.mulVec ξ := by
    funext ξ i
    simp only [Function.comp_apply, linF, bwOfCoord, Pi.smul_apply, smul_eq_mul, one_mul,
      BstLean.Part106.bwWeight_mono1, Real.sqrt_one, div_one, Matrix.mulVec, dotProduct, S,
      ite_mul, zero_mul]
    rw [Finset.sum_ite_eq' Finset.univ ((0 : Fin 1), mono1 n dF hd i)]
    simp
  have hm : Measurable (linF (n := n) hd) :=
    measurable_pi_iff.2 fun i => measurable_pi_apply _
  have hid : (stdGauss (Fin n)).map (fun ξ => (1 : Matrix (Fin n) (Fin n) ℝ).mulVec ξ) =
      stdGauss (Fin n) := by
    simp only [Matrix.one_mulVec]
    exact Measure.map_id
  unfold bwGauss
  rw [Measure.map_map hm (measurable_bwOfCoord_smul 1), hL, gaussLin105 _ _ _ S 1 hSS, hid]

/-! ## The terms of degree at least 2 of `F` -/

lemma mixW_self {k q d : ℕ} (F : CoefIdx k q d → ℝ) : mixW F F = F := by
  funext i
  unfold mixW
  split_ifs <;> rfl

lemma Htail_eq {n dF : ℕ} (hd : 1 ≤ dF) (F : CoefIdx n 1 dF → ℝ) (y : Fin n → ℝ) :
    Htail hd F y = bwEval (mixW 0 F) y 0 := by
  have h1 := congrFun (bwEval_mix F F y) 0
  rw [mixW_self] at h1
  have h2 := BstLean.Part106.lowEval hd F y (0 : Fin 1)
  unfold Htail
  rw [h1, Pi.add_apply, h2]
  ring

lemma measurable_Htail {n dF : ℕ} (hd : 1 ≤ dF) (y : Fin n → ℝ) :
    Measurable (fun F : CoefIdx n 1 dF → ℝ => Htail hd F y) := by
  unfold Htail
  refine ((measurable_bwEval y 0).sub (measurable_pi_apply _)).sub ?_
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply _).mul_const _

theorem htailMom108 : HtailMom108 := by
  classical
  intro n dF hd y
  let a : CoefIdx n 1 dF → ℝ := fun c => rowMat (N := n) (n := 1) (d := dF) 1 y 0 c
  have hH : ∀ ξ : CoefIdx n 1 dF → ℝ,
      Htail hd (bwOfCoord ((1 : ℝ) • ξ)) y ^ 2 =
        BstLean.Part107.lin a ξ * BstLean.Part107.lin a ξ := by
    intro ξ
    rw [Htail_eq, bwEval_eq_rowMat, sq]
    have : (rowMat (N := n) (n := 1) (d := dF) 1 y).mulVec ξ 0 = BstLean.Part107.lin a ξ := by
      simp only [Matrix.mulVec, dotProduct, BstLean.Part107.lin, a]
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    rw [this]
  have hint : Integrable (fun ξ : CoefIdx n 1 dF → ℝ =>
      BstLean.Part107.lin a ξ * BstLean.Part107.lin a ξ) (stdGauss (CoefIdx n 1 dF)) := by
    simp_rw [BstLean.Part107.lin2_expand]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (BstLean.Part107.int2 i j).const_mul _
  have hip : BstLean.Part107.ip a a = ∑ j ∈ Finset.Icc 2 dF, dot y y ^ j := by
    have h := congrFun (congrFun
      (rowMat_mul_transpose (N := n) (n := 1) (d := dF) multinomial105 1 y y) 0) 0
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, Matrix.one_apply,
      ite_true, smul_eq_mul, mul_one, one_pow, one_mul] at h
    rw [← h]
    rfl
  unfold bwGauss
  rw [lintegral_map ((measurable_Htail hd y).pow_const 2).ennreal_ofReal
    (measurable_bwOfCoord_smul 1)]
  simp_rw [hH]
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun ξ => mul_self_nonneg _), BstLean.Part107.wick2, hip]

end BstLean.Part108

#print axioms BstLean.Part108.linLaw108
#print axioms BstLean.Part108.htailMom108
#print axioms BstLean.Part108.evalMom108
#print axioms BstLean.Part108.gMom108
