import BstLean.Part56Defs

/-! Algebraic identities for the anchor projection. -/

namespace BstLean.Part56.Orth

open MeasureTheory
open scoped ENNReal
open BstLean.Part36 (CoefIdxD monoVal)
open BstLean.Part41 (Mono phiM)
open BstLean.Part53 (linZ)

variable {n d : ℕ}

private lemma block_product (j l : ℕ) (v : Fin n → ℝ) (p : Mono n d)
    (h : j ≠ l) : phiB d j v p * phiB d l v p = 0 := by
  unfold phiB
  split_ifs <;> simp_all

/-- Distinct degree blocks are orthogonal. -/
theorem blocks_orthogonal (j l : ℕ) (v : Fin n → ℝ) (h : j ≠ l) :
    (∑ p : Mono n d, phiB d j v p * phiB d l v p) = 0 := by
  classical
  exact Finset.sum_eq_zero (fun p _ => block_product j l v p h)

/-- Every degree block has a strictly positive squared norm at a unit vector. -/
theorem block_norm_pos (v : Fin n → ℝ) (hv : UnitV v) (j : ℕ) (hj : j ≤ d) :
    0 < kJ d j v v := by
  classical
  obtain ⟨a, ha⟩ : ∃ a : Fin n, v a ≠ 0 := by
    by_contra h
    push Not at h
    have hz : (∑ a, v a ^ 2) = 0 := by simp [h]
    unfold UnitV at hv
    linarith
  let p : Mono n d := ⟨⟨j, by omega⟩, ⟨Multiset.replicate j a, by simp⟩⟩
  have hp : phiB d j v p = v a ^ j := by
    simp [phiB, p, phiM, monoVal]
  unfold kJ
  have hle := Finset.single_le_sum
    (fun q (_ : q ∈ (Finset.univ : Finset (Mono n d))) =>
      mul_self_nonneg (phiB d j v q)) (Finset.mem_univ p)
  rw [hp] at hle
  exact lt_of_lt_of_le (mul_self_pos.mpr (pow_ne_zero _ ha)) hle

/-- The variance parameter of the residual Gaussian is nonnegative. -/
theorem residual_variance_nonneg (v : Fin n → ℝ) (hv : UnitV v) (x : Fin n → ℝ) :
    0 ≤ tauR d v x := by
  classical
  unfold tauR KR
  apply Finset.sum_nonneg
  intro j hj
  have hjd : j ≤ d := (Finset.mem_Icc.mp hj).2
  have hpos := block_norm_pos v hv j hjd
  have hcs : kJ d j x v ^ 2 ≤ kJ d j x x * kJ d j v v := by
    simpa only [kJ, pow_two] using Finset.sum_mul_sq_le_sq_mul_sq
      Finset.univ (phiB d j x) (phiB d j v)
  apply sub_nonneg.mpr
  apply (div_le_iff₀ hpos).mpr
  simpa only [pow_two] using hcs

/-- The projection preserves each anchor. -/
theorem anchor_projection (v : Fin n → ℝ) (hv : UnitV v)
    (Z : CoefIdxD n d → ℝ) (j : ℕ) (hj : j ≤ d) :
    ancRK (projA v Z) v j = ancRK Z v j := by
  classical
  funext a
  let A : ℕ → ℝ := fun l => ∑ p : Mono n d, phiB d l v p * Z ⟨p.1, (p.2, a)⟩
  change (∑ p : Mono n d, (∑ l ∈ Finset.range (d + 1),
    phiB d l v p / kJ d l v v * A l) * phiB d j v p) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  have ht (l : ℕ) :
      (∑ p : Mono n d, (phiB d l v p / kJ d l v v * A l) * phiB d j v p) =
      (∑ p : Mono n d, phiB d l v p * phiB d j v p) / kJ d l v v * A l := by
    simp_rw [show ∀ p : Mono n d,
      (phiB d l v p / kJ d l v v * A l) * phiB d j v p =
      (phiB d l v p * phiB d j v p) / kJ d l v v * A l by intro p; ring]
    rw [← Finset.sum_mul, ← Finset.sum_div]
  simp_rw [ht]
  rw [Finset.sum_eq_single j]
  · rw [show (∑ p : Mono n d, phiB d j v p * phiB d j v p) = kJ d j v v from rfl,
      div_self (ne_of_gt (block_norm_pos v hv j hj)), one_mul]
    change A j = ∑ p : Mono n d, Z ⟨p.1, (p.2, a)⟩ * phiB d j v p
    simp [A, mul_comm]
  · intro l hl hlj
    rw [blocks_orthogonal l j v hlj, zero_div, zero_mul]
  · intro h
    exact (h (Finset.mem_range.mpr (by omega))).elim

/-- Each anchor is linear in the coefficient array. -/
theorem anchor_add (v : Fin n → ℝ) (Z W : CoefIdxD n d → ℝ) (j : ℕ) :
    ancRK (Z + W) v j = ancRK Z v j + ancRK W v j := by
  classical
  funext a
  simp [ancRK, linZ, BstLean.Part41.colM, add_mul, Finset.sum_add_distrib]

theorem anchor_sub (v : Fin n → ℝ) (Z W : CoefIdxD n d → ℝ) (j : ℕ) :
    ancRK (Z - W) v j = ancRK Z v j - ancRK W v j := by
  classical
  funext a
  simp [ancRK, linZ, BstLean.Part41.colM, sub_mul, Finset.sum_sub_distrib]

theorem anchor_smul (v : Fin n → ℝ) (s : ℝ) (Z : CoefIdxD n d → ℝ) (j : ℕ) :
    ancRK (s • Z) v j = s • ancRK Z v j := by
  classical
  funext a
  simp [ancRK, linZ, BstLean.Part41.colM, mul_assoc, Finset.mul_sum]

/-- Resampling the residual leaves the anchors unchanged. -/
theorem anchor_resampling (v : Fin n → ℝ) (hv : UnitV v)
    (Z W : CoefIdxD n d → ℝ) (j : ℕ) (hj : j ≤ d) :
    ancRK (projA v Z + (W - projA v W)) v j = ancRK Z v j := by
  rw [anchor_add, anchor_sub, anchor_projection v hv Z j hj,
    anchor_projection v hv W j hj, sub_self, add_zero]

/-- Evaluating the projected coefficient array gives the conditional mean. -/
theorem projected_value (v x : Fin n → ℝ) (Z : CoefIdxD n d → ℝ) :
    linZ (projA v Z) (fun p : Mono n d => phiM x p) = mux Z v x := by
  classical
  funext a
  let A : ℕ → ℝ := fun j => ∑ p : Mono n d, phiB d j v p * Z ⟨p.1, (p.2, a)⟩
  change (∑ p : Mono n d, (∑ j ∈ Finset.range (d + 1),
    phiB d j v p / kJ d j v v * A j) * phiM x p) = _
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mux, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro j hj
  have ht (p : Mono n d) : phiB d j v p * phiM x p =
      phiB d j x p * phiB d j v p := by
    unfold phiB
    split_ifs <;> ring
  simp_rw [show ∀ p : Mono n d,
    (phiB d j v p / kJ d j v v * A j) * phiM x p =
    (phiB d j v p * phiM x p) / kJ d j v v * A j by intro p; ring,
    ht]
  rw [← Finset.sum_mul, ← Finset.sum_div]
  change kJ d j x v / kJ d j v v * A j = _
  congr 1
  simp [A, ancRK, linZ, BstLean.Part41.colM, mul_comm]

/-- The projection is continuous in the coefficient array. -/
theorem projection_continuous (v : Fin n → ℝ) : Continuous (projA (d := d) v) := by
  classical
  apply continuous_pi
  intro a
  unfold projA
  apply continuous_finsetSum
  intro j hj
  apply continuous_const.mul
  apply continuous_finsetSum
  intro p hp
  exact continuous_const.mul (continuous_apply _)

/-- The split interface identifies the law of residual resampling. -/
theorem resampling_measurePreserving (hS : PropSplit56 d) (v : Fin n → ℝ) (hv : UnitV v) :
    MeasureTheory.MeasurePreserving
      (fun p : (CoefIdxD n d → ℝ) × (CoefIdxD n d → ℝ) =>
        projA v p.1 + (p.2 - projA v p.2))
      ((BstLean.Part29.stdGauss (CoefIdxD n d)).prod
        (BstLean.Part29.stdGauss (CoefIdxD n d)))
      (BstLean.Part29.stdGauss (CoefIdxD n d)) := by
  classical
  let f := fun p : (CoefIdxD n d → ℝ) × (CoefIdxD n d → ℝ) =>
    projA v p.1 + (p.2 - projA v p.2)
  have hf : Measurable f := ((projection_continuous v).comp continuous_fst |>.add
    (continuous_snd.sub ((projection_continuous v).comp continuous_snd))).measurable
  refine ⟨hf, ?_⟩
  apply MeasureTheory.Measure.ext
  intro s hs
  rw [MeasureTheory.Measure.map_apply hf hs]
  have hi := hS n v hv (s.indicator (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hs)
  have hp : Measurable (fun p => s.indicator (fun _ => (1 : ℝ≥0∞)) (f p)) :=
    (measurable_const.indicator hs).comp hf
  have hprod := MeasureTheory.lintegral_prod
    (μ := BstLean.Part29.stdGauss (CoefIdxD n d))
    (ν := BstLean.Part29.stdGauss (CoefIdxD n d)) _ hp.aemeasurable
  have hset : (fun p => s.indicator (fun _ => (1 : ℝ≥0∞)) (f p)) =
      (f ⁻¹' s).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext p
    simp [Set.indicator_apply]
  rw [hset] at hprod
  change (∫⁻ p, (f ⁻¹' s).indicator 1 p ∂
    (BstLean.Part29.stdGauss (CoefIdxD n d)).prod
      (BstLean.Part29.stdGauss (CoefIdxD n d))) = _ at hprod
  rw [MeasureTheory.lintegral_indicator_one (hf hs)] at hprod
  rw [MeasureTheory.lintegral_indicator_const hs, one_mul] at hi
  exact hprod.trans hi.symm

end BstLean.Part56.Orth
