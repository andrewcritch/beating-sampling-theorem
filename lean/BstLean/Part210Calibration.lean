import BstLean.Part210Scalar

/-! S07: calibration on arbitrary measurable subsets, without normalization. -/
namespace BstLean.Part210
open MeasureTheory ProbabilityTheory Real
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part159
open BstLean.Part133 (L2le)
open BstLean.Part136 (hidGauss mW_ge_million)
open BstLean.Part140 (kap1)

/-- The dimension-dependent calibration numerator in P10f. -/
noncomputable def Rnew (n : ℕ) : ℝ :=
  501 / 1000 / √(n : ℝ) + 406 / 10 ^ 7 * √(mW n : ℝ) / (n : ℝ) ^ 2

/-- The sharp bound holds for every measurable subset of the scalar window. -/
theorem restricted_calibration_raw {n : ℕ} (hn : 4096 ≤ n)
    {G : Set (WHid n)} (mG : MeasurableSet G) (hG : G ⊆ goodS n) :
    L2le (hidGauss (2 * n) (mW n))
      (G.indicator fun θ => qOf n (ccP n) θ - 1)
      (501 / 1000 * √(1 / ((n : ℝ) * (mW n : ℝ))) +
        406 / 10 ^ 7 / (n : ℝ) ^ 2) := by
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hmpos : (0 : ℝ) < mW n := by exact_mod_cast hm
  have hS := SWp_L2 (n := n) (by omega) hm
  have he : √(2 / (((2 * n : ℕ) : ℝ) * (mW n : ℝ))) =
      √(1 / ((n : ℝ) * (mW n : ℝ))) := by
    congr 1
    push_cast
    field_simp
  rw [he] at hS
  have mS : Measurable (fun θ : WHid n => |SWp θ / 2 - 1|) :=
    ((measurable_SWp.div_const 2).sub_const 1).abs
  have hSa := L2le.of_abs_le mS.aestronglyMeasurable hS
    (fun θ => by rw [abs_abs])
  have h1 := hSa.const_mul_nonneg (c := 501 / 1000) (by norm_num)
  let c : ℝ := 203 / 100 * |kapT n - kap1 (2 * n)|
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have h2 := L2le.const (μ := hidGauss (2 * n) (mW n)) c
  have h3 := h1.add' h2 (by positivity) (abs_nonneg _)
  have mq : Measurable (G.indicator fun θ => qOf n (ccP n) θ - 1) :=
    ((measurable_qOf measurable_ccP).sub_const 1).indicator mG
  have h4 : L2le (hidGauss (2 * n) (mW n))
      (G.indicator fun θ => qOf n (ccP n) θ - 1)
      (501 / 1000 * √(1 / ((n : ℝ) * (mW n : ℝ))) + |c|) := by
    refine L2le.of_abs_le mq.aestronglyMeasurable h3 fun θ => ?_
    refine le_trans ?_ (le_abs_self _)
    by_cases hθ : θ ∈ G
    · rw [Set.indicator_of_mem hθ]
      exact pap_q_error hn (hG hθ)
    · rw [Set.indicator_of_notMem hθ, abs_zero]
      exact add_nonneg (by positivity) hc
  refine h4.mono (by positivity) ?_
  rw [abs_of_nonneg hc]
  have hk := BstLean.Part201.kapT_close_strong hn
  have hb := mul_le_mul_of_nonneg_left hk (show (0 : ℝ) ≤ 203 / 100 by norm_num)
  dsimp [c]
  convert add_le_add_left hb (501 / 1000 * √(1 / ((n : ℝ) * (mW n : ℝ)))) using 1 <;> ring

/-- P10f qLtwo, with the exact integer width and the paper numerator. -/
theorem restricted_calibration {n : ℕ} (hn : 4096 ≤ n)
    {G : Set (WHid n)} (mG : MeasurableSet G) (hG : G ⊆ goodS n) :
    L2le (hidGauss (2 * n) (mW n))
      (G.indicator fun θ => qOf n (ccP n) θ - 1) (Rnew n / √(mW n : ℝ)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm : 1 ≤ mW n := by have := mW_ge_million hn; omega
  have hmpos : (0 : ℝ) < mW n := by exact_mod_cast hm
  have hsN : 0 < √(n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hsM : 0 < √(mW n : ℝ) := Real.sqrt_pos.mpr hmpos
  refine (restricted_calibration_raw hn mG hG).congr_bound ?_
  unfold Rnew
  rw [Real.sqrt_div (by norm_num), Real.sqrt_one, Real.sqrt_mul hnpos.le]
  field_simp
  <;> ring

/-- The source World event is a measurable admissible restriction. -/
theorem pap_qL2 {n : ℕ} (hn : 4096 ≤ n) :
    L2le (hidGauss (2 * n) (mW n))
      ((GPap n).indicator fun θ => qOf n (ccP n) θ - 1) (Rnew n / √(mW n : ℝ)) :=
  restricted_calibration hn (measurableSet_GPap (by omega)) (fun _ h => h.1.2)

end BstLean.Part210
#print axioms BstLean.Part210.restricted_calibration_raw
#print axioms BstLean.Part210.restricted_calibration
#print axioms BstLean.Part210.pap_qL2
