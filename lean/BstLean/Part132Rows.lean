import BstLean.Part130All

/-!
# Part 132, rows: the rows of a Gaussian matrix are independent and identically distributed

* `rows_indep`: functions of two different rows of a Gaussian matrix are independent.
* `rows_sum_sq`: `E (Σ_i f(row_i))² = m·E f² + m(m − 1)·(E f)²`.
* `layer_dot_relu_var`: `Var ⟨ReLU(M h), ReLU(M h′)⟩ ≤ (3/2)·m·v²·|h|²|h′|²`.

Do not use `sorry`, `native_decide` or `axiom`.
-/

namespace BstLean.Part132

open MeasureTheory ProbabilityTheory
open BstLean.Part29 (stdGauss)
open BstLean.Part130

variable {m k : ℕ}

/-- Functions of two different rows are independent (stated on the standard Gaussian of the
entries). -/
lemma rows_indep (v : ℝ) (f : (Fin k → ℝ) → ℝ) (hf : Measurable f) {i i' : Fin m}
    (hii : i ≠ i') :
    IndepFun (fun ξ : Fin m × Fin k → ℝ => f (fun j => Real.sqrt v * ξ (i, j)))
      (fun ξ : Fin m × Fin k → ℝ => f (fun j => Real.sqrt v * ξ (i', j)))
      (stdGauss (Fin m × Fin k)) := by
  classical
  have hI : iIndepFun (fun (p : Fin m × Fin k) (ξ : Fin m × Fin k → ℝ) => ξ p)
      (stdGauss (Fin m × Fin k)) := by
    unfold stdGauss
    exact iIndepFun_pi (μ := fun _ : Fin m × Fin k => gaussianReal 0 1) (X := fun _ => id)
      (fun _ => aemeasurable_id)
  let S : Fin m → Finset (Fin m × Fin k) := fun a => Finset.univ.image (fun j => (a, j))
  have hd : Disjoint (S i) (S i') := by
    rw [Finset.disjoint_left]
    intro p hp hp'
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at hp hp'
    obtain ⟨j, rfl⟩ := hp
    obtain ⟨j', hj'⟩ := hp'
    exact hii (Prod.mk.inj hj').1.symm
  have h := hI.indepFun_finset (S i) (S i') hd (fun p => measurable_pi_apply p)
  have hmem : ∀ (a : Fin m) (j : Fin k), (a, j) ∈ S a := fun a j =>
    Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  let φ : ∀ a : Fin m, (S a → ℝ) → ℝ :=
    fun a w => f (fun j => Real.sqrt v * w ⟨(a, j), hmem a j⟩)
  have hφ : ∀ a, Measurable (φ a) := fun a =>
    hf.comp (measurable_pi_iff.mpr fun j => measurable_const.mul (measurable_pi_apply _))
  exact h.comp (hφ i) (hφ i')

lemma row_integrable_iff (v : ℝ) (i : Fin m) {g : (Fin k → ℝ) → ℝ} (hg : Measurable g) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => g (rowOf i M)) (gaussMat m k v) ↔
      Integrable (fun ξ => g (Real.sqrt v • ξ)) (stdGauss (Fin k)) := by
  have h1 := integrable_map_measure (μ := gaussMat m k v) (f := rowOf i) (g := g)
    hg.aestronglyMeasurable (measurable_rowOf i).aemeasurable
  have h2 := integrable_map_measure (μ := stdGauss (Fin k)) (f := fun ξ => Real.sqrt v • ξ)
    (g := g) hg.aestronglyMeasurable (measurable_const_smul _).aemeasurable
  rw [gaussMat_row] at h1
  exact h1.symm.trans h2

lemma row_integral (v : ℝ) (i : Fin m) {g : (Fin k → ℝ) → ℝ} (hg : Measurable g) :
    ∫ M, g (rowOf i M) ∂gaussMat m k v = ∫ ξ, g (Real.sqrt v • ξ) ∂stdGauss (Fin k) := by
  rw [← integral_map (measurable_rowOf i).aemeasurable hg.aestronglyMeasurable, gaussMat_row,
    integral_map (measurable_const_smul _).aemeasurable hg.aestronglyMeasurable]

/-- The mean of a product of functions of two different rows. -/
lemma rows_mul (v : ℝ) (f : (Fin k → ℝ) → ℝ) (hf : Measurable f)
    (hf1 : Integrable (fun ξ => f (Real.sqrt v • ξ)) (stdGauss (Fin k))) {i i' : Fin m}
    (hii : i ≠ i') :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => f (rowOf i M) * f (rowOf i' M))
      (gaussMat m k v) ∧
    ∫ M, f (rowOf i M) * f (rowOf i' M) ∂gaussMat m k v =
      (∫ ξ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k)) ^ 2 := by
  have hind := rows_indep (m := m) v f hf hii
  have hT : Measurable (fun ξ : Fin m × Fin k → ℝ =>
      (Matrix.of fun i j => Real.sqrt v * ξ (i, j) : Matrix (Fin m) (Fin k) ℝ)) :=
    measurable_ofFlat _
  have hm : ∀ a : Fin m, Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => f (rowOf a M)) :=
    fun a => hf.comp (measurable_rowOf a)
  have hY : ∀ a : Fin m, Integrable
      (fun ξ : Fin m × Fin k → ℝ => f (fun j => Real.sqrt v * ξ (a, j)))
      (stdGauss (Fin m × Fin k)) := by
    intro a
    have h0 := (row_integrable_iff (m := m) v a hf).mpr hf1
    unfold gaussMat at h0
    exact (integrable_map_measure (hm a).aestronglyMeasurable hT.aemeasurable).mp h0
  have hYi : ∀ a : Fin m, ∫ ξ : Fin m × Fin k → ℝ, f (fun j => Real.sqrt v * ξ (a, j))
      ∂stdGauss (Fin m × Fin k) = ∫ ξ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k) := by
    intro a
    rw [← row_integral (m := m) v a hf]
    unfold gaussMat
    rw [integral_map hT.aemeasurable (hm a).aestronglyMeasurable]
    rfl
  have hmm : Measurable (fun M : Matrix (Fin m) (Fin k) ℝ => f (rowOf i M) * f (rowOf i' M)) :=
    (hm i).mul (hm i')
  constructor
  · unfold gaussMat
    exact (integrable_map_measure hmm.aestronglyMeasurable hT.aemeasurable).mpr
      (hind.integrable_mul (hY i) (hY i'))
  · unfold gaussMat
    rw [integral_map hT.aemeasurable hmm.aestronglyMeasurable]
    have h := hind.integral_mul_eq_mul_integral (hY i).aestronglyMeasurable
      (hY i').aestronglyMeasurable
    rw [hYi, hYi] at h
    rw [sq, ← h]
    rfl

/-- Second moment of a sum of one function of each (independent) row. -/
theorem rows_sum_sq {m k : ℕ} (v : ℝ) (f : (Fin k → ℝ) → ℝ) (hf : Measurable f)
    (hf2 : Integrable (fun ξ => f (Real.sqrt v • ξ) ^ 2) (stdGauss (Fin k))) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => (∑ i, f (rowOf i M)) ^ 2) (gaussMat m k v) ∧
    ∫ M, (∑ i, f (rowOf i M)) ^ 2 ∂gaussMat m k v =
      (m : ℝ) * ∫ ξ, f (Real.sqrt v • ξ) ^ 2 ∂stdGauss (Fin k) +
      (m : ℝ) * ((m : ℝ) - 1) * (∫ ξ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k)) ^ 2 := by
  classical
  have hfs : Measurable (fun ξ : Fin k → ℝ => f (Real.sqrt v • ξ)) :=
    hf.comp (measurable_const_smul _)
  have hf1 : Integrable (fun ξ => f (Real.sqrt v • ξ)) (stdGauss (Fin k)) :=
    ((memLp_two_iff_integrable_sq hfs.aestronglyMeasurable).mpr hf2).integrable one_le_two
  have hsq : Measurable (fun w : Fin k → ℝ => f w ^ 2) := hf.pow_const 2
  have hint : ∀ i j : Fin m, Integrable
      (fun M : Matrix (Fin m) (Fin k) ℝ => f (rowOf i M) * f (rowOf j M)) (gaussMat m k v) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      have := (row_integrable_iff (m := m) v i hsq).mpr hf2
      simpa [sq] using this
    · exact (rows_mul v f hf hf1 hij).1
  have key : ∀ i j : Fin m, ∫ M, f (rowOf i M) * f (rowOf j M) ∂gaussMat m k v =
      if i = j then ∫ ξ, f (Real.sqrt v • ξ) ^ 2 ∂stdGauss (Fin k)
      else (∫ ξ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k)) ^ 2 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simp only [↓reduceIte]
      have := row_integral (m := m) v i hsq
      simpa [sq] using this
    · simp only [hij, ↓reduceIte]
      exact (rows_mul v f hf hf1 hij).2
  have hexp : (fun M : Matrix (Fin m) (Fin k) ℝ => (∑ i, f (rowOf i M)) ^ 2) =
      fun M => ∑ i, ∑ j, f (rowOf i M) * f (rowOf j M) := by
    funext M; rw [sq, Finset.sum_mul_sum]
  rw [hexp]
  refine ⟨integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j, ?_⟩
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp_rw [integral_finsetSum _ fun j _ => hint _ j]
  simp_rw [key]
  set E2 := ∫ ξ, f (Real.sqrt v • ξ) ^ 2 ∂stdGauss (Fin k) with hE2
  set E1 := ∫ ξ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k) with hE1
  have e : ∀ i : Fin m, ∑ j : Fin m, (if i = j then E2 else E1 ^ 2) =
      E2 + ((m : ℝ) - 1) * E1 ^ 2 := by
    intro i
    have : ∀ j : Fin m, (if i = j then E2 else E1 ^ 2) =
        E1 ^ 2 + if i = j then (E2 - E1 ^ 2) else 0 := by
      intro j; split_ifs <;> ring
    simp_rw [this]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      Finset.mem_univ, ite_true]
    ring
  simp_rw [e]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The variance of the layer inner product: `Var ⟨ReLU(M h), ReLU(M h′)⟩ ≤ (3/2)·m·v²·|h|²|h′|²`. -/
theorem layer_dot_relu_var {m k : ℕ} {v : ℝ} (hv : 0 ≤ v) (h h' : Fin k → ℝ) :
    Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) - (m : ℝ) / 2 * (v * kernelPhi h h')) ^ 2)
      (gaussMat m k v) ∧
    ∫ M, (dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) - (m : ℝ) / 2 * (v * kernelPhi h h')) ^ 2
      ∂gaussMat m k v ≤ 3 / 2 * (m : ℝ) * v ^ 2 * normSq h * normSq h' := by
  let f : (Fin k → ℝ) → ℝ := fun w => relu (∑ j, w j * h j) * relu (∑ j, w j * h' j)
  have hf : Measurable f :=
    (measurable_relu.comp (Finset.measurable_sum _ fun j _ =>
      (measurable_pi_apply j).mul_const _)).mul
    (measurable_relu.comp (Finset.measurable_sum _ fun j _ => (measurable_pi_apply j).mul_const _))
  -- a matrix with one row
  let R : (Fin k → ℝ) → Matrix (Fin 1) (Fin k) ℝ → ℝ := fun g M => normSq (reluV (M.mulVec g))
  have hR : ∀ (g : Fin k → ℝ) (M : Matrix (Fin 1) (Fin k) ℝ),
      R g M = relu (∑ j, M 0 j * g j) ^ 2 := by
    intro g M
    change ∑ i : Fin 1, relu ((M.mulVec g) i) ^ 2 = _
    rw [Fin.sum_univ_one]
    rfl
  have hRm : ∀ g : Fin k → ℝ, Measurable (R g) := fun g =>
    measurable_normSq.comp (measurable_reluV.comp (measurable_mulVec_right g))
  have hR0 : ∀ (g : Fin k → ℝ) (M : Matrix (Fin 1) (Fin k) ℝ), 0 ≤ R g M :=
    fun g M => normSq_nonneg _
  have four : ∀ g : Fin k → ℝ, Integrable (fun M => R g M ^ 2) (gaussMat 1 k v) ∧
      ∫ M, R g M ^ 2 ∂gaussMat 1 k v = 3 / 2 * (v * normSq g) ^ 2 := by
    intro g
    have h4 := layer_relu_four (m := 1) hv g
    refine ⟨h4.1, ?_⟩
    rw [h4.2]
    norm_num
  have key : (fun M : Matrix (Fin 1) (Fin k) ℝ => f (rowOf 0 M) ^ 2) =
      fun M => R h M * R h' M := by
    funext M
    rw [hR, hR]
    simp only [f, rowOf]
    ring
  have hRR : Integrable (fun M => R h M * R h' M) (gaussMat 1 k v) := by
    refine Integrable.mono' ((four h).1.add (four h').1)
      ((hRm h).mul (hRm h')).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun M => ?_
    rw [Real.norm_eq_abs, abs_le]
    simp only [Pi.add_apply]
    constructor <;> nlinarith [sq_nonneg (R h M - R h' M), sq_nonneg (R h M + R h' M)]
  have hzero : ∀ g : Fin k → ℝ, normSq g = 0 → ∀ M : Matrix (Fin 1) (Fin k) ℝ, R g M = 0 := by
    intro g hg M
    rw [hR, normSq_eq_zero hg]
    simp [relu]
  have hbound : ∫ M, R h M * R h' M ∂gaussMat 1 k v ≤ 3 / 2 * v ^ 2 * normSq h * normSq h' := by
    by_cases hN : normSq h = 0
    · have : ∀ M : Matrix (Fin 1) (Fin k) ℝ, R h M * R h' M = 0 := by
        intro M; rw [hzero h hN M, zero_mul]
      simp_rw [this]
      simp [hN]
    by_cases hN' : normSq h' = 0
    · have : ∀ M : Matrix (Fin 1) (Fin k) ℝ, R h M * R h' M = 0 := by
        intro M; rw [hzero h' hN' M, mul_zero]
      simp_rw [this]
      simp [hN']
    have hp : 0 < normSq h := lt_of_le_of_ne (normSq_nonneg h) (Ne.symm hN)
    have hp' : 0 < normSq h' := lt_of_le_of_ne (normSq_nonneg h') (Ne.symm hN')
    have hi2 : Integrable (fun M => (normSq h' ^ 2 * R h M ^ 2 + normSq h ^ 2 * R h' M ^ 2) /
        (2 * normSq h * normSq h')) (gaussMat 1 k v) :=
      (((four h).1.const_mul _).add ((four h').1.const_mul _)).div_const _
    calc ∫ M, R h M * R h' M ∂gaussMat 1 k v
        ≤ ∫ M, (normSq h' ^ 2 * R h M ^ 2 + normSq h ^ 2 * R h' M ^ 2) /
            (2 * normSq h * normSq h') ∂gaussMat 1 k v := by
          refine integral_mono hRR hi2 fun M => ?_
          rw [le_div_iff₀ (by positivity)]
          nlinarith [sq_nonneg (normSq h' * R h M - normSq h * R h' M)]
      _ = 3 / 2 * v ^ 2 * normSq h * normSq h' := by
          rw [integral_div, integral_add ((four h).1.const_mul _) ((four h').1.const_mul _),
            integral_const_mul, integral_const_mul, (four h).2, (four h').2]
          field_simp
          ring
  have hf2 : Integrable (fun ξ => f (Real.sqrt v • ξ) ^ 2) (stdGauss (Fin k)) := by
    refine (row_integrable_iff (m := 1) v (0 : Fin 1) (hf.pow_const 2)).mp ?_
    have := hRR
    rw [← key] at this
    exact this
  have hE2 : ∫ ξ, f (Real.sqrt v • ξ) ^ 2 ∂stdGauss (Fin k) ≤
      3 / 2 * v ^ 2 * normSq h * normSq h' := by
    have e : ∫ ξ, f (Real.sqrt v • ξ) ^ 2 ∂stdGauss (Fin k) =
        ∫ M, R h M * R h' M ∂gaussMat 1 k v := by
      rw [← key]
      exact (row_integral (m := 1) v (0 : Fin 1) (hf.pow_const 2)).symm
    rw [e]
    exact hbound
  have ha : ∫ ξ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k) = v * kernelPhi h h' / 2 := by
    have e := row_integral (m := 1) v (0 : Fin 1) hf
    have r := row_formula (m := 1) hv h h' 0
    change 2 * ∫ M, f (rowOf 0 M) ∂gaussMat 1 k v = _ at r
    rw [e] at r
    unfold kernelPhi dotp
    linarith
  have S := rows_sum_sq (m := m) v f hf hf2
  have L := layer_dot_relu (m := m) hv h h'
  have hsum : ∀ M : Matrix (Fin m) (Fin k) ℝ,
      dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) = ∑ i, f (rowOf i M) := fun M => rfl
  set c := (m : ℝ) / 2 * (v * kernelPhi h h') with hc
  set a := ∫ ξ, f (Real.sqrt v • ξ) ∂stdGauss (Fin k) with haa
  set E2 := ∫ ξ, f (Real.sqrt v • ξ) ^ 2 ∂stdGauss (Fin k) with hE2d
  have hca : c = (m : ℝ) * a := by rw [hc, ha]; ring
  have hexp : (fun M : Matrix (Fin m) (Fin k) ℝ =>
      (dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) - c) ^ 2) =
      fun M => (∑ i, f (rowOf i M)) ^ 2 -
        2 * c * dotp (reluV (M.mulVec h)) (reluV (M.mulVec h')) + c ^ 2 := by
    funext M
    rw [← hsum M]
    ring
  rw [hexp]
  have i2 : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ =>
      2 * c * dotp (reluV (M.mulVec h)) (reluV (M.mulVec h'))) (gaussMat m k v) :=
    L.1.const_mul (2 * c)
  have i1 : Integrable (fun M : Matrix (Fin m) (Fin k) ℝ => (∑ i, f (rowOf i M)) ^ 2 -
      2 * c * dotp (reluV (M.mulVec h)) (reluV (M.mulVec h'))) (gaussMat m k v) := S.1.sub i2
  refine ⟨i1.add (integrable_const _), ?_⟩
  rw [integral_add i1 (integrable_const _), integral_sub S.1 i2,
    integral_const_mul, L.2, S.2, integral_const]
  have hu : (gaussMat m k v).real Set.univ = 1 := by simp
  rw [hu, one_smul]
  rw [hca]
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have h1 : (m : ℝ) * E2 ≤ (m : ℝ) * (3 / 2 * v ^ 2 * normSq h * normSq h') :=
    mul_le_mul_of_nonneg_left hE2 hm0
  have h2 : 0 ≤ (m : ℝ) * a ^ 2 := mul_nonneg hm0 (sq_nonneg a)
  nlinarith [h1, h2]

end BstLean.Part132

open BstLean.Part132 in
#print axioms rows_sum_sq
open BstLean.Part132 in
#print axioms layer_dot_relu_var
