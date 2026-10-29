import BstLean.Part218WishartTrace
import BstLean.Part214FirstLayer

/-! The Wishart trace payment uses the actual He-scaled first-layer distribution. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part130 BstLean.Part132 BstLean.Part133 BstLean.Part214

lemma gaussMat_scale (m N : ℕ) (v : ℝ) :
    MeasurePreserving (fun M : Matrix (Fin m) (Fin N) ℝ => √v • M)
      (gaussMat m N 1) (gaussMat m N v) := by
  refine ⟨by fun_prop, ?_⟩
  unfold gaussMat
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext ξ
  ext i j
  simp

lemma measurable_wishartTrace (N m : ℕ) : Measurable (wishartTrace N m) := by
  have he : wishartTrace N m = fun M => ∑ i, ∑ j, dotp (M j) (M i) ^ 2 :=
    funext (wishartTrace_entries N m)
  rw [he]
  unfold dotp
  fun_prop

lemma wishartTrace_smul (N m : ℕ) (a : ℝ) (M : Matrix (Fin m) (Fin N) ℝ) :
    wishartTrace N m (a • M) = a ^ 4 * wishartTrace N m M := by
  rw [wishartTrace_entries, wishartTrace_entries]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have he : dotp ((a • M) j) ((a • M) i) = a ^ 2 * dotp (M j) (M i) := by
    unfold dotp
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  rw [he]
  ring

noncomputable def paperTrace (N m : ℕ) (M : Matrix (Fin m) (Fin N) ℝ) : ℝ :=
  (N : ℝ) ^ 2 / 4 * wishartTrace N m M

noncomputable def traceVariance (N m : ℕ) : ℝ :=
  (2 * (m : ℝ) * ((m : ℝ) - 1) * (2 * (N : ℝ) ^ 2 + 6 * N) +
    8 * N * (m : ℝ) * ((m : ℝ) - 1) * ((m : ℝ) - 2)) +
  8 * (m : ℝ) * N * (N + 2) * (N + 3) +
  2 * (8 * (m : ℝ) * ((m : ℝ) - 1) * N * (N + 2))

lemma paperTrace_scale {N m : ℕ} (hN : 1 ≤ N) (M : Matrix (Fin m) (Fin N) ℝ) :
    paperTrace N m (√(2 / (N : ℝ)) • M) = wishartTrace N m M := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  unfold paperTrace
  rw [wishartTrace_smul, show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
    sq_sqrt (by positivity : 0 ≤ 2 / (N : ℝ))]
  field_simp
  ring

/-- Both trace moments have a concrete first-layer supply. -/
theorem paperTrace_moments {N m : ℕ} (hN : 1 ≤ N) :
    Integrable (paperTrace N m) (gaussMat m N (2 / (N : ℝ))) ∧
    (∫ M, paperTrace N m M ∂gaussMat m N (2 / (N : ℝ))) =
      (m : ℝ) * N * (m + N + 1) ∧
    Integrable (fun M => (paperTrace N m M - (m : ℝ) * N * (m + N + 1)) ^ 2)
      (gaussMat m N (2 / (N : ℝ))) ∧
    (∫ M, (paperTrace N m M - (m : ℝ) * N * (m + N + 1)) ^ 2
      ∂gaussMat m N (2 / (N : ℝ))) = traceVariance N m := by
  let c : ℝ := (m : ℝ) * N * (m + N + 1)
  have mp := gaussMat_scale m N (2 / (N : ℝ))
  have mf : Measurable (paperTrace N m) := (measurable_wishartTrace N m).const_mul _
  have iT : MemLp (wishartTrace N m) 2 (gaussMat m N 1) :=
    (wishartOff_memLp N m).add (diagonal_memLp hN)
  have iC : Integrable (fun M => (wishartTrace N m M - c) ^ 2) (gaussMat m N 1) :=
    (iT.sub (memLp_const c)).integrable_sq
  have transfer : ∀ (f : ℝ → ℝ), Measurable f →
      (∫ M, f (paperTrace N m M) ∂gaussMat m N (2 / (N : ℝ))) =
        ∫ M, f (wishartTrace N m M) ∂gaussMat m N 1 := by
    intro f hf
    rw [← mp.map_eq, integral_map mp.measurable.aemeasurable (show Measurable (fun M => f (paperTrace N m M)) from hf.comp mf).aestronglyMeasurable]
    simp_rw [paperTrace_scale hN]
  have itransfer : ∀ (f : ℝ → ℝ), Measurable f →
      Integrable (fun M => f (wishartTrace N m M)) (gaussMat m N 1) →
      Integrable (fun M => f (paperTrace N m M)) (gaussMat m N (2 / (N : ℝ))) := by
    intro f hf hi
    rw [← mp.map_eq]
    apply (integrable_map_measure (show Measurable (fun M => f (paperTrace N m M)) from hf.comp mf).aestronglyMeasurable mp.measurable.aemeasurable).mpr
    change Integrable (fun M : Matrix (Fin m) (Fin N) ℝ =>
      f (paperTrace N m (√(2 / (N : ℝ)) • M))) (gaussMat m N 1)
    simp_rw [paperTrace_scale hN]
    exact hi
  refine ⟨itransfer id measurable_id (iT.integrable one_le_two),
    (transfer id measurable_id).trans (wishartTrace_mean hN),
    itransfer (fun x => (x - c) ^ 2) (by fun_prop) iC, ?_⟩
  rw [transfer (fun x => (x - c) ^ 2) (by fun_prop)]
  have h := wishartTrace_variance (m := m) hN
  rw [variance_eq_integral (measurable_wishartTrace N m).aemeasurable, wishartTrace_mean hN] at h
  exact h

theorem paperTrace_upper_charge {N m : ℕ} (hN : 1 ≤ N) (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 < ε) :
    (gaussMat m N (2 / (N : ℝ))).real
      {M | (1 + ε) * ((m : ℝ) * N * (m + N + 1)) < paperTrace N m M} ≤
      traceVariance N m / (ε * ((m : ℝ) * N * (m + N + 1))) ^ 2 := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : 0 < (m : ℝ) * N * (m + N + 1) := by positivity
  have hr : (m : ℝ) * N * (m + N + 1) <
      (1 + ε) * ((m : ℝ) * N * (m + N + 1)) := by nlinarith [mul_pos hε hc]
  have h := paperTrace_moments (m := m) hN
  have he : (1 + ε) * ((m : ℝ) * N * (m + N + 1)) - (m : ℝ) * N * (m + N + 1) =
      ε * ((m : ℝ) * N * (m + N + 1)) := by ring
  simpa only [he] using upper_tail_of_mean_bound h.2.2.1 h.2.2.2.le (le_refl _) hr

end BstLean.Part218
#print axioms BstLean.Part218.paperTrace_moments
#print axioms BstLean.Part218.paperTrace_upper_charge
