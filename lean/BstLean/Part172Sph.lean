import BstLean.Part171All

/-!
# Part 172 (file `Sph`): the second moment of a direction on the sphere

No proof is left open; no `native_decide` or `axiom` is used.

* **`sg_sph_mom2`**: for `w = V/|V|`, `V` standard Gaussian in `ℝ^d`,
  `E⟨p, w⟩² = |p|²/d`.
-/

namespace BstLean.Part172

open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part130 (normSq)
open BstLean.Part53 (unitF53 measurable_unitF)
open BstLean.Part73 (IsOrth)

variable {d : ℕ}

/-- `Q(p) = E⟨p, w⟩²`. -/
noncomputable def sg_Q (p : Fin d → ℝ) : ℝ :=
  ∫ v, (∑ k, p k * unitF53 v k) ^ 2 ∂stdGauss (Fin d)

lemma sg_unit_sumsq (z : Fin d → ℝ) (hz : z ≠ 0) : ∑ i, unitF53 z i ^ 2 = 1 := by
  have hs : 0 < ∑ i, z i ^ 2 := by
    have h00 : (0 : ℝ) ≤ ∑ i, z i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (z i)
    rcases h00.lt_or_eq with h | h
    · exact h
    · exfalso; apply hz; funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (z i))).mp h.symm i
        (Finset.mem_univ i)
      simpa using this
  unfold unitF53
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
  rw [one_div, inv_pow, Real.sq_sqrt hs.le, inv_mul_cancel₀ hs.ne']

lemma sg_unit_sumsq_le (z : Fin d → ℝ) : ∑ i, unitF53 z i ^ 2 ≤ 1 := by
  by_cases hz : z = 0
  · subst hz; simp [unitF53]
  · exact (sg_unit_sumsq z hz).le

lemma sg_dot_sq_le (p w : Fin d → ℝ) : (∑ k, p k * w k) ^ 2 ≤ normSq p * ∑ k, w k ^ 2 := by
  unfold normSq
  exact Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma sg_meas_dot (p : Fin d → ℝ) :
    Measurable (fun v : Fin d → ℝ => (∑ k, p k * unitF53 v k) ^ 2) :=
  (Finset.measurable_sum _ fun k _ =>
    measurable_const.mul ((measurable_pi_apply k).comp measurable_unitF)).pow_const 2

lemma sg_int_dot (p : Fin d → ℝ) :
    Integrable (fun v : Fin d → ℝ => (∑ k, p k * unitF53 v k) ^ 2) (stdGauss (Fin d)) := by
  refine Integrable.mono' (integrable_const (normSq p)) (sg_meas_dot p).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h0 : 0 ≤ normSq p := Finset.sum_nonneg fun i _ => sq_nonneg _
  calc _ ≤ normSq p * ∑ k, unitF53 v k ^ 2 := sg_dot_sq_le _ _
    _ ≤ normSq p * 1 := mul_le_mul_of_nonneg_left (sg_unit_sumsq_le v) h0
    _ = normSq p := mul_one _

lemma sg_Q_orth (O : Matrix (Fin d) (Fin d) ℝ) (hO : IsOrth O) (p : Fin d → ℝ) :
    sg_Q (O.transpose.mulVec p) = sg_Q p := by
  unfold sg_Q
  have h := BstLean.Part137.stdGauss_rot_integral O hO (sg_meas_dot p)
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only
  rw [BstLean.Part73.unitF_orth hO]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

lemma sg_Q_smul (t : ℝ) (p : Fin d → ℝ) : sg_Q (t • p) = t ^ 2 * sg_Q p := by
  unfold sg_Q
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← mul_pow, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring

lemma sg_Q_unit (hd : 1 ≤ d) {p : Fin d → ℝ} (hp : normSq p = 1) :
    sg_Q p = sg_Q (Pi.single (⟨0, by omega⟩ : Fin d) 1) := by
  classical
  have he : normSq (Pi.single (⟨0, by omega⟩ : Fin d) (1 : ℝ)) = 1 := by
    unfold normSq
    rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin d)]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  obtain ⟨O, hO, hOe⟩ := BstLean.Part137.exists_orth_map hd hp he
  have h := sg_Q_orth O.transpose hO.t (Pi.single (⟨0, by omega⟩ : Fin d) 1)
  rw [Matrix.transpose_transpose, hOe] at h
  exact h

lemma sg_ae_ne (hd : 1 ≤ d) : ∀ᵐ v ∂stdGauss (Fin d), v ≠ 0 := by
  have h0 := BstLean.Part168.stdGauss_zero hd
  rw [ae_iff]
  simpa using h0

/-- **`E⟨p, w⟩² = |p|²/d`.** -/
theorem sg_sph_mom2 (hd : 1 ≤ d) (p : Fin d → ℝ) :
    ∫ v, (∑ k, p k * unitF53 v k) ^ 2 ∂stdGauss (Fin d) = normSq p / d := by
  classical
  set e : Fin d → ℝ := Pi.single (⟨0, by omega⟩ : Fin d) 1
  have hsingle : ∀ j : Fin d, sg_Q (Pi.single j 1) = sg_Q e := fun j => by
    apply sg_Q_unit hd
    unfold normSq
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · simp
  have hsum : ∑ j : Fin d, sg_Q (Pi.single j 1) = 1 := by
    unfold sg_Q
    rw [← integral_finsetSum _ fun j _ => sg_int_dot _]
    have : ∀ᵐ v ∂stdGauss (Fin d),
        ∑ j : Fin d, (∑ k, (Pi.single j (1 : ℝ) : Fin d → ℝ) k * unitF53 v k) ^ 2 = 1 := by
      filter_upwards [sg_ae_ne hd] with v hv
      refine (Finset.sum_congr rfl fun j _ => ?_).trans (sg_unit_sumsq v hv)
      congr 1
      rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [hb]
      · simp
    rw [integral_congr_ae this]; simp
  simp_rw [hsingle] at hsum
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hQe : sg_Q e = 1 / d := by field_simp; linarith
  show sg_Q p = _
  by_cases hp : normSq p = 0
  · have : p = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (p i))).mp hp i
        (Finset.mem_univ i)
      simpa using this
    subst this
    rw [hp]; unfold sg_Q; simp
  · have hp0 : 0 < normSq p := lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hp)
    set r := √(normSq p)
    have hr : 0 < r := Real.sqrt_pos.mpr hp0
    have hpu : p = r • (r⁻¹ • p) := by rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hu : normSq (r⁻¹ • p) = 1 := by
      unfold normSq
      simp only [Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum]
      rw [inv_pow, Real.sq_sqrt hp0.le]; exact inv_mul_cancel₀ hp
    rw [show sg_Q p = sg_Q (r • (r⁻¹ • p)) from by rw [← hpu], sg_Q_smul, sg_Q_unit hd hu, hQe,
      Real.sq_sqrt hp0.le]
    ring

end BstLean.Part172
