import BstLean.Part218Direction
import BstLean.Part159Q1
import BstLean.Part214FirstLayer

/-! The directional Markov payment has an explicit positive mean. -/
namespace BstLean.Part218
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 BstLean.Part130 BstLean.Part133 BstLean.Part137 BstLean.Part214

noncomputable def directionMean (N m : ℕ) : ℝ :=
  2 * m * cN N ^ 2 * (N + 2) / (N : ℝ) ^ 2 * (1 - 2 * N * cN N ^ 2)

lemma directionMean_pos {N m : ℕ} (hN : 2 ≤ N) (hm : 1 ≤ m) : 0 < directionMean N m := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hn1 : 0 < (N : ℝ) - 1 := by linarith
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hw := BstLean.Part159.cN_sq_window hN
  have hr := (BstLean.Part159.rN_window hN).2
  have hc : 0 < cN N ^ 2 := lt_of_lt_of_le (by positivity) hw.1
  have hb : (N : ℝ) / (π * (N - 1)) < 1 := by
    apply (div_lt_one (by positivity : 0 < π * ((N : ℝ) - 1))).mpr
    nlinarith [pi_gt_three]
  have hpos : 0 < 1 - 2 * N * cN N ^ 2 := by linarith
  unfold directionMean
  positivity

lemma worldDirection_measurable {N m : ℕ} (hN : 1 ≤ N) :
    Measurable (worldDirection (N := N) (m := m)) := by
  have := uniformSphere_isProbability N hN
  have hm : Measurable (fun p : Matrix (Fin m) (Fin N) ℝ × (Fin N → ℝ) =>
      (∑ i, h1bar p.1 i * centeredFirst p.1 i p.2) ^ 2) := by
    apply Measurable.pow_const
    apply Finset.measurable_sum
    intro i _
    have hb : Measurable (fun p : Matrix (Fin m) (Fin N) ℝ × (Fin N → ℝ) => h1bar p.1 i) :=
      ((measurable_pi_apply i).comp (measurable_h1bar hN)).comp measurable_fst
    apply hb.mul
    unfold centeredFirst reluV Matrix.mulVec dotProduct relu
    exact (by fun_prop : Measurable (fun p : Matrix (Fin m) (Fin N) ℝ × (Fin N → ℝ) =>
      max 0 (∑ j, p.1 i j * p.2 j))).sub hb
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

theorem worldDirection_charge {N m : ℕ} (hN : 2 ≤ N) (hm : 1 ≤ m) {p : ℝ} (hp : 0 < p) :
    (gaussMat m N (2 / (N : ℝ))).real
      {M | directionMean N m / p < worldDirection M} ≤ p := by
  have h := worldDirection_mean (N := N) (m := m) (by omega) hm
  exact nonnegative_mean_charge _ (fun M => centeredGram_nonneg M (h1bar M)) h.1
    (directionMean_pos hN hm) hp h.2.le

end BstLean.Part218
#print axioms BstLean.Part218.worldDirection_charge
