import BstLean.Part233RowLip

/-! The matrix distance has no extra square root of the row count. -/
namespace BstLean.Part233
open MeasureTheory ProbabilityTheory Real Set Matrix
open BstLean.Part29 BstLean.Part130 BstLean.Part136 BstLean.Part137 BstLean.Part205
open BstLean.Part133
open BstLean.Part153 (nrm nrm_sq nrm_nonneg abs_nrm_sub_le)
open BstLean.Part148 (EuLip)

/-- A row Lipschitz bound gives the same constant for the norm of all rows. -/
theorem row_norm_lipschitz {a b : ℕ} {d : (Fin b → ℝ) → ℝ} {L c : ℝ}
    (hL0 : 0 ≤ L) (hc : 0 ≤ c) (hL : EuLip d L) :
    EuLip (fun ξ : Fin a × Fin b → ℝ => c * nrm (fun i => d (fun j => ξ (i, j))))
      (c * L) := by
  intro ξ η
  have hv : nrm ((fun i => d (fun j => ξ (i, j))) -
      (fun i => d (fun j => η (i, j)))) ≤
      L * √(∑ p, (ξ p - η p) ^ 2) := by
    have hs : normSq ((fun i => d (fun j => ξ (i, j))) -
        (fun i => d (fun j => η (i, j)))) ≤
        L ^ 2 * (∑ p, (ξ p - η p) ^ 2) := by
      rw [Fintype.sum_prod_type, Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have h := hL (fun j => ξ (i, j)) (fun j => η (i, j))
      have hp := pow_le_pow_left₀ (abs_nonneg _) h 2
      rw [sq_abs, mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at hp
      exact hp
    have hr := Real.sqrt_le_sqrt hs
    rw [Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq hL0] at hr
    exact hr
  rw [← mul_sub, abs_mul, abs_of_nonneg hc]
  exact (mul_le_mul_of_nonneg_left
    ((abs_nrm_sub_le _ _).trans hv) hc).trans_eq (by ring)

noncomputable def standardDistanceRoot {N m : ℕ}
    (M₁ : Matrix (Fin m) (Fin N) ℝ) (Ξ : Fin m × Fin m → ℝ) : ℝ :=
  2 / (m : ℝ) * nrm (fun i =>
    rowMean (fun u => reluV (M₁.mulVec u)) (fun j => Ξ (i, j)) -
      rowSmooth (h1bar M₁) (worldSigma M₁) (fun j => Ξ (i, j)))

theorem standardDistanceRoot_lipschitz {N m : ℕ} (hN : 1 ≤ N)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    EuLip (standardDistanceRoot M₁)
      ((√(firstQ M₁) + nrm (h1bar M₁)) / (m : ℝ)) := by
  have h := row_norm_lipschitz (a := m)
    (div_nonneg (add_nonneg (sqrt_nonneg _) (nrm_nonneg _)) (by norm_num))
    (by positivity : 0 ≤ 2 / (m : ℝ))
    (world_row_lipschitz hN M₁ (worldSigma M₁))
  have he : 2 / (m : ℝ) * ((√(firstQ M₁) + nrm (h1bar M₁)) / 2) =
      (√(firstQ M₁) + nrm (h1bar M₁)) / (m : ℝ) := by ring
  rw [he] at h
  exact h

/-- The root is the square root of the exact source distance on standardized matrices. -/
theorem standardDistanceRoot_sq {N m : ℕ} (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) (Ξ : Fin m × Fin m → ℝ) :
    standardDistanceRoot M₁ Ξ ^ 2 = BstLean.Part140.dist2 N m
      (M₁, fun i j => √(2 / (m : ℝ)) * Ξ (i, j)) := by
  rw [dist2_standard_rows hm]
  unfold standardDistanceRoot
  rw [mul_pow, nrm_sq]
  unfold normSq
  ring

theorem standardDistanceRoot_second_moment {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) :
    Integrable (fun Ξ => standardDistanceRoot M₁ Ξ ^ 2) (stdGauss (Fin m × Fin m)) ∧
      (∫ Ξ, standardDistanceRoot M₁ Ξ ^ 2 ∂stdGauss (Fin m × Fin m)) =
        2 / (m : ℝ) * worldDelta M₁ := by
  obtain ⟨hi, he⟩ := exact_conditional_distance_paper hN hm M₁
  have hd : Measurable (fun M₂ => BstLean.Part140.dist2 N m (M₁, M₂)) :=
    (BstLean.Part140.measurable_dist2 hN).comp
      (measurable_const.prodMk measurable_id)
  have hscale : Measurable
      (fun Ξ : Fin m × Fin m → ℝ => Matrix.of fun i j => √(2 / (m : ℝ)) * Ξ (i, j)) :=
    by fun_prop
  have hi' : Integrable (fun Ξ : Fin m × Fin m → ℝ => BstLean.Part140.dist2 N m
      (M₁, Matrix.of fun i j => √(2 / (m : ℝ)) * Ξ (i, j)))
      (stdGauss (Fin m × Fin m)) :=
    (integrable_map_measure (μ := stdGauss (Fin m × Fin m))
      hd.aestronglyMeasurable hscale.aemeasurable).mp hi
  have he' : (∫ M₂, BstLean.Part140.dist2 N m (M₁, M₂)
      ∂gaussMat m m (2 / (m : ℝ))) =
      ∫ Ξ : Fin m × Fin m → ℝ, BstLean.Part140.dist2 N m
        (M₁, Matrix.of fun i j => √(2 / (m : ℝ)) * Ξ (i, j))
          ∂stdGauss (Fin m × Fin m) :=
    integral_map (μ := stdGauss (Fin m × Fin m))
      hscale.aemeasurable hd.aestronglyMeasurable
  have hfun : (fun Ξ => standardDistanceRoot M₁ Ξ ^ 2) =
      (fun Ξ : Fin m × Fin m → ℝ => BstLean.Part140.dist2 N m
        (M₁, Matrix.of fun i j => √(2 / (m : ℝ)) * Ξ (i, j))) :=
    funext (standardDistanceRoot_sq hm M₁)
  rw [hfun]
  exact ⟨hi', he'.symm.trans he⟩

/-- Jensen supplies the root mean from the exact conditional squared distance. -/
theorem standardDistanceRoot_mean {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) {B : ℝ}
    (hB : 0 ≤ B) (hmean : 2 / (m : ℝ) * worldDelta M₁ ≤ B ^ 2) :
    (∫ Ξ, standardDistanceRoot M₁ Ξ ∂stdGauss (Fin m × Fin m)) ≤ B := by
  obtain ⟨hi, he⟩ := standardDistanceRoot_second_moment hN hm M₁
  have hj := sq_integral_le hi
  rw [he] at hj
  nlinarith

/-- The upper tail integrates the complete standardized second matrix. -/
theorem standardDistanceRoot_tail {N m : ℕ} (hN : 1 ≤ N)
    (M₁ : Matrix (Fin m) (Fin N) ℝ) {M a : ℝ}
    (hmean : ∫ Ξ, standardDistanceRoot M₁ Ξ ∂stdGauss (Fin m × Fin m) ≤ M)
    (hgap : M ≤ a) :
    (stdGauss (Fin m × Fin m)).real {Ξ | a < standardDistanceRoot M₁ Ξ} ≤
      exp (-(a - M) ^ 2 /
        (2 * ((√(firstQ M₁) + nrm (h1bar M₁)) / (m : ℝ)) ^ 2)) := by
  have h := BstLean.Part152.gaussConc_upper_sharp
    (div_nonneg (add_nonneg (sqrt_nonneg _) (nrm_nonneg _)) (Nat.cast_nonneg m))
    (standardDistanceRoot_lipschitz hN M₁) (sub_nonneg.mpr hgap)
  exact (measureReal_mono (fun Ξ hΞ => by
    change a < standardDistanceRoot M₁ Ξ at hΞ
    change (∫ η, standardDistanceRoot M₁ η ∂stdGauss (Fin m × Fin m)) +
      (a - M) ≤ standardDistanceRoot M₁ Ξ
    linarith) (measure_ne_top _ _)).trans h

end BstLean.Part233
#print axioms BstLean.Part233.row_norm_lipschitz
#print axioms BstLean.Part233.standardDistanceRoot_lipschitz
#print axioms BstLean.Part233.standardDistanceRoot_sq
#print axioms BstLean.Part233.standardDistanceRoot_second_moment
#print axioms BstLean.Part233.standardDistanceRoot_mean
#print axioms BstLean.Part233.standardDistanceRoot_tail
