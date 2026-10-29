import BstLean.Part107Defs

/-!
# Part 107, the pair distribution of a Gaussian `W` (all degrees): `twoPoint107`, `onePoint107`
-/

namespace BstLean.Part107

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open BstLean.Part29 (stdGauss uniformSphere)
open BstLean.Part105

section PairLaw

variable {N n d : ℕ}

/-- The matrix of `ξ ↦ W(u)`, `W` with Gaussian coordinates `σ ξ` (all degrees). -/
noncomputable def rowMatAll (σ : ℝ) (u : Fin N → ℝ) : Matrix (Fin n) (CoefIdx N n d) ℝ :=
  fun a i => if a = i.1 then σ * monoVal u i.2 / Real.sqrt (bwWeight i.2) else 0

lemma bwEval_eq_rowMatAll (σ : ℝ) (u : Fin N → ℝ) (ξ : CoefIdx N n d → ℝ) :
    bwEval (bwOfCoord (σ • ξ)) u = (rowMatAll σ u).mulVec ξ := by
  funext a
  simp only [bwEval, bwOfCoord, Matrix.mulVec, dotProduct, rowMatAll, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [ite_true, Pi.smul_apply, smul_eq_mul]
  ring

lemma rowMatAll_mul_transpose (σ : ℝ) (u u' : Fin N → ℝ) :
    (rowMatAll (N := N) (n := n) (d := d) σ u) *
        (rowMatAll (N := N) (n := n) (d := d) σ u').transpose =
      (σ ^ 2 * ∑ j ∈ Finset.range (d + 1), dot u u' ^ j) • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  classical
  ext a a'
  simp only [Matrix.mul_apply, Matrix.transpose_apply, rowMatAll, Fintype.sum_prod_type,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
  by_cases h : a = a'
  · subst h
    simp only [ite_true, mul_one]
    have key : ∀ m : MonoIdx N d,
        (σ * monoVal u m / Real.sqrt (bwWeight m)) *
          (σ * monoVal u' m / Real.sqrt (bwWeight m)) =
        ∑ j ∈ Finset.range (d + 1),
          if m.deg = j then σ ^ 2 * (monoVal u m * monoVal u' m / bwWeight m) else 0 := by
      intro m
      rw [Finset.sum_ite_eq]
      have hmem : m.deg ∈ Finset.range (d + 1) := Finset.mem_range.2 m.1.isLt
      simp only [hmem, ite_true]
      have hw := Real.mul_self_sqrt (bwWeight_nonneg m)
      rw [div_mul_div_comm, hw]
      ring
    simp_rw [key]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← multinomial105 N d u u' j (Nat.lt_succ_iff.mp (Finset.mem_range.1 hj)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> simp
  · have h' : ¬ a' = a := fun hc => h hc.symm
    simp [h, h']

lemma measurable_bwEval_vec (u : Fin N → ℝ) :
    Measurable (fun c : CoefIdx N n d → ℝ => bwEval c u) :=
  measurable_pi_iff.2 fun a => measurable_bwEval u a

lemma abs_rW_le_one (d : ℕ) (t : ℝ) (ht : |t| ≤ 1) : |rW d t| ≤ 1 := by
  unfold rW
  have hd : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  rw [abs_div, abs_of_pos hd, div_le_one hd]
  calc |∑ j ∈ Finset.range (d + 1), t ^ j| ≤ ∑ j ∈ Finset.range (d + 1), |t ^ j| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range (d + 1), (1 : ℝ) :=
        Finset.sum_le_sum fun j _ => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg t) ht
    _ = (d : ℝ) + 1 := by simp

/-- The pair distribution of the Gaussian version of `W` (all degrees). -/
theorem pairLaw107 (N n d : ℕ) (σ : ℝ) (u u' : Fin N → ℝ) (hu : dot u u = 1)
    (hu' : dot u' u' = 1) :
    (bwGauss N n d σ).map (fun c => (bwEval c u, bwEval c u')) =
      ((stdGauss (Fin n)).prod (stdGauss (Fin n))).map
        (fun p => ((Real.sqrt ((d : ℝ) + 1) * σ) • p.1,
          (Real.sqrt ((d : ℝ) + 1) * σ) •
            (rW d (dot u u') • p.1 + sC (rW d (dot u u')) • p.2))) := by
  classical
  have hd1 : (0 : ℝ) < (d : ℝ) + 1 := by positivity
  have hρ1 := abs_rW_le_one d (dot u u') (abs_dot_le_one u u' hu hu')
  have hsumρ : ∑ j ∈ Finset.range (d + 1), dot u u' ^ j = ((d : ℝ) + 1) * rW d (dot u u') := by
    unfold rW
    field_simp
  generalize rW d (dot u u') = ρ at hρ1 hsumρ ⊢
  generalize hτ : Real.sqrt ((d : ℝ) + 1) * σ = τ
  have hss : sC ρ * sC ρ = 1 - ρ ^ 2 := by
    have := sC_sq hρ1
    nlinarith
  generalize sC ρ = s at hss ⊢
  have hττ : τ * τ = σ ^ 2 * ((d : ℝ) + 1) := by
    rw [← hτ]
    have := Real.mul_self_sqrt hd1.le
    nlinarith
  have hsum1 : ∑ j ∈ Finset.range (d + 1), (1 : ℝ) ^ j = (d : ℝ) + 1 := by simp
  let e := MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin n => ℝ)
  let A : Matrix (Fin n ⊕ Fin n) (CoefIdx N n d) ℝ :=
    Matrix.fromRows (rowMatAll σ u) (rowMatAll σ u')
  let B : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℝ :=
    Matrix.fromBlocks (τ • 1) 0 ((τ * ρ) • 1) ((τ * s) • 1)
  have hAB : A * A.transpose = B * B.transpose := by
    simp only [A, B, Matrix.transpose_fromRows, Matrix.fromRows_mul_fromCols,
      rowMatAll_mul_transpose, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      hu, hu', dot_comm' u' u, hsum1, hsumρ]
    simp only [Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_zero,
      Matrix.mul_smul, Matrix.mul_one, Matrix.mul_zero, smul_zero,
      add_zero, smul_smul, ← add_smul]
    congr 2
    · rw [hττ]
    · rw [show τ * ρ * τ = τ * τ * ρ by ring, hττ]; ring
    · rw [show τ * (τ * ρ) = τ * τ * ρ by ring, hττ]; ring
    · rw [show τ * ρ * (τ * ρ) + τ * s * (τ * s) = τ * τ * (ρ ^ 2 + s * s) by ring, hττ, hss]
      ring
  have hL : (fun c : CoefIdx N n d → ℝ => (bwEval c u, bwEval c u')) ∘
      (fun ξ : CoefIdx N n d → ℝ => bwOfCoord (σ • ξ)) = e ∘ (fun ξ => A.mulVec ξ) := by
    funext ξ
    simp only [Function.comp_apply, bwEval_eq_rowMatAll, A, Matrix.fromRows_mulVec]
    rfl
  have hR : (fun p : (Fin n → ℝ) × (Fin n → ℝ) => (τ • p.1, τ • (ρ • p.1 + s • p.2))) ∘ e =
      e ∘ (fun ξ => B.mulVec ξ) := by
    funext ξ
    simp only [Function.comp_apply, B, Matrix.fromBlocks_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.zero_mulVec, add_zero]
    refine Prod.ext ?_ ?_
    · rfl
    · funext a
      simp [e, MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, mul_add, mul_assoc]
  have hprod : (stdGauss (Fin n)).prod (stdGauss (Fin n)) = (stdGauss (Fin n ⊕ Fin n)).map e :=
    ((measurePreserving_sumPiEquivProdPi
      (fun _ : Fin n ⊕ Fin n => gaussianReal 0 1)).map_eq).symm
  have hmF : Measurable (fun c : CoefIdx N n d → ℝ => (bwEval c u, bwEval c u')) :=
    (measurable_bwEval_vec u).prodMk (measurable_bwEval_vec u')
  unfold bwGauss
  rw [Measure.map_map hmF (measurable_bwOfCoord_smul σ), hL, hprod,
    Measure.map_map (by fun_prop) e.measurable, hR,
    ← Measure.map_map e.measurable (by fun_prop), ← Measure.map_map e.measurable (by fun_prop),
    gaussLin105 _ _ _ A B hAB]

end PairLaw

/-! ## Scaling -/

lemma sphProj_smul {n : ℕ} (τ : ℝ) (y : Fin n → ℝ) :
    sphProj (τ • y) = (τ / |τ|) • sphProj y := by
  unfold sphProj
  have h : Real.sqrt (∑ i, (τ • y) i ^ 2) = |τ| * Real.sqrt (∑ i, y i ^ 2) := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg τ), Real.sqrt_sq_eq_abs]
  rw [h, smul_smul, smul_smul]
  congr 1
  rw [one_div, mul_inv, one_div]
  ring

lemma cosA_smul {n : ℕ} {τ : ℝ} (hτ : τ ≠ 0) (g g' : Fin n → ℝ) :
    cosA (τ • g) (τ • g') = cosA g g' := by
  unfold cosA
  rw [sphProj_smul, sphProj_smul]
  unfold dot
  simp only [Pi.smul_apply, smul_eq_mul]
  have h : τ / |τ| * (τ / |τ|) = 1 := by
    rw [div_mul_div_comm, abs_mul_abs_self]
    exact div_self (mul_self_ne_zero.2 hτ)
  calc ∑ i, τ / |τ| * sphProj g i * (τ / |τ| * sphProj g' i)
      = ∑ i, (τ / |τ| * (τ / |τ|)) * (sphProj g i * sphProj g' i) :=
        Finset.sum_congr rfl fun i _ => by ring
    _ = _ := by simp [h]

lemma measurable_cosA {n : ℕ} :
    Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => cosA q.1 q.2) := by
  unfold cosA
  exact measurable_dot2.comp
    ((measurable_sphProj.comp measurable_fst).prodMk (measurable_sphProj.comp measurable_snd))

theorem twoPoint107 : TwoPoint107 := by
  intro N n d σ u u' ψ hσ hu hu' hψ
  have hτ : Real.sqrt ((d : ℝ) + 1) * σ ≠ 0 :=
    mul_ne_zero (Real.sqrt_ne_zero'.2 (by positivity)) hσ
  have hmF : Measurable (fun c : CoefIdx N n d → ℝ => (bwEval c u, bwEval c u')) :=
    (measurable_bwEval_vec u).prodMk (measurable_bwEval_vec u')
  have hG : Measurable (fun q : (Fin n → ℝ) × (Fin n → ℝ) => ψ (cosA q.1 q.2)) :=
    hψ.comp measurable_cosA
  have h1 : ∫ c, ψ (cosA (bwEval c u) (bwEval c u')) ∂bwGauss N n d σ =
      ∫ q, ψ (cosA q.1 q.2) ∂(bwGauss N n d σ).map (fun c => (bwEval c u, bwEval c u')) :=
    (integral_map hmF.aemeasurable hG.aestronglyMeasurable).symm
  have hmR : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      ((Real.sqrt ((d : ℝ) + 1) * σ) • p.1,
        (Real.sqrt ((d : ℝ) + 1) * σ) •
          (rW d (dot u u') • p.1 + sC (rW d (dot u u')) • p.2))) := by
    fun_prop
  rw [h1, pairLaw107 N n d σ u u' hu hu', integral_map hmR.aemeasurable hG.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [aR]
  rw [cosA_smul hτ]

theorem onePoint107 (hZ : NonZero107) : OnePoint107 := by
  intro N n d σ u hn hσ hu
  have hτ : Real.sqrt ((d : ℝ) + 1) * σ ≠ 0 :=
    mul_ne_zero (Real.sqrt_ne_zero'.2 (by positivity)) hσ
  have hmF : Measurable (fun c : CoefIdx N n d → ℝ => (bwEval c u, bwEval c u)) :=
    (measurable_bwEval_vec u).prodMk (measurable_bwEval_vec u)
  have hmR : Measurable (fun p : (Fin n → ℝ) × (Fin n → ℝ) =>
      ((Real.sqrt ((d : ℝ) + 1) * σ) • p.1,
        (Real.sqrt ((d : ℝ) + 1) * σ) •
          (rW d (dot u u) • p.1 + sC (rW d (dot u u)) • p.2))) := by
    fun_prop
  have hS : MeasurableSet {q : (Fin n → ℝ) × (Fin n → ℝ) | q.1 ≠ 0} :=
    (measurable_fst (measurableSet_singleton (0 : Fin n → ℝ))).compl
  have h2 : ∀ᵐ q ∂(bwGauss N n d σ).map (fun c => (bwEval c u, bwEval c u)), q.1 ≠ 0 := by
    rw [pairLaw107 N n d σ u u hu hu, ae_map_iff hmR.aemeasurable hS]
    have h3 : ∀ᵐ p ∂(stdGauss (Fin n)).prod (stdGauss (Fin n)), p.1 ≠ 0 :=
      (measurePreserving_fst (μ := stdGauss (Fin n)) (ν := stdGauss (Fin n))).quasiMeasurePreserving.ae
        (hZ n hn)
    filter_upwards [h3] with p hp
    exact smul_ne_zero hτ hp
  exact (ae_map_iff hmF.aemeasurable hS).1 h2

#print axioms twoPoint107
#print axioms onePoint107

end BstLean.Part107
