import BstLean.Part292GatedChi

/-! A fixed gate deficit and two monotone chi-square inequalities suffice on the whole band. -/
namespace BstLean.Part292
open MeasureTheory ProbabilityTheory Real Matrix
open BstLean.Part130 BstLean.Part152

theorem trace_dimension {n : ℕ} (hn : 8000 ≤ n) :
    (2400000000 : ℝ) ≤ (mA n : ℝ)*(n-1 : ℕ) := by
  have h1 : (64000000 : ℝ) ≤ mA n := by
    exact_mod_cast (show 64000000 ≤ mA n by unfold mA; nlinarith)
  have h2 : (7999 : ℝ) ≤ (n-1 : ℕ) := by exact_mod_cast (show 7999 ≤ n-1 by omega)
  nlinarith [mul_le_mul h1 h2 (by norm_num) (Nat.cast_nonneg (mA n))]

theorem trace_lower_threshold {T : ℝ} (hT : 2400000000 ≤ T) :
    (999/2000 : ℝ)*T ≤ (1599/3200 : ℝ)*T-2*sqrt ((1599/3200 : ℝ)*T*12) := by
  have hT0 : 0 ≤ T := by linarith
  have hs : sqrt ((1599/3200 : ℝ)*T*12) ≤ T/20000 := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [mul_nonneg hT0 (show 0 ≤ T-2400000000 by linarith)]
  linarith

theorem trace_upper_threshold {T : ℝ} (hT : 2400000000 ≤ T) :
    T+2*sqrt (T*18)+2*18 ≤ (1001/1000 : ℝ)*T := by
  have hT0 : 0 ≤ T := by linarith
  have hs : sqrt (T*18) ≤ T/2500 := by
    apply sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [mul_nonneg hT0 (show 0 ≤ T-112500000 by linarith)]
  linarith

theorem activeEnergy_band {n : ℕ} (hn : 8000 ≤ n) :
    ((BstLean.Part29.stdGauss (Fin (mA n))).prod (gaussMat (mA n) (n-1) 1)).real
      {p | activeEnergy p.1 p.2 < (999/2000 : ℝ)*(mA n : ℝ)*(n-1 : ℕ)} ≤
      2*exp (-12) := by
  have hT := trace_dimension hn
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have he : (n-1 : ℕ)*( ((1/2 : ℝ)-1/3200)*(mA n : ℝ)) =
      (1599/3200 : ℝ)*((mA n : ℝ)*(n-1 : ℕ)) := by ring
  have h := gated_chi_lower (m := mA n) (d := n-1) (η := 1/3200) (x := 12)
    (by omega) (by norm_num) (by norm_num) (by rw [he]; linarith) (by rw [he]; linarith)
  rw [he] at h
  have hpay : exp (-2*(1/3200 : ℝ)^2*(mA n : ℝ)) ≤ exp (-12) := by
    apply exp_le_exp.mpr
    simp only [mA, Nat.cast_pow]
    nlinarith
  apply (measureReal_mono ?_).trans (h.trans ?_)
  · intro p hp
    simp only [Set.mem_setOf_eq, mul_assoc] at hp ⊢
    exact hp.trans_le (by simpa only [mul_assoc] using trace_lower_threshold hT)
  · linarith

theorem matrix_chi_upper {m d : ℕ} {x : ℝ} (hx : 0 ≤ x) :
    (gaussMat m d 1).real {G | (m : ℝ)*d+2*sqrt ((m : ℝ)*d*x)+2*x <
      ∑ i, normSq (G i)} ≤ exp (-x) := by
  have h := chiSq_upper_LM (ι := Fin m × Fin d) hx
  unfold gaussMat
  rw [map_measureReal_apply (by fun_prop)
    (measurableSet_lt measurable_const (by unfold normSq; fun_prop))]
  apply le_trans (measureReal_mono ?_) h
  intro G hG
  simp only [Set.mem_preimage, Set.mem_setOf_eq, sqrt_one, one_mul, Matrix.of_apply] at hG
  simp only [Set.mem_setOf_eq, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul]
  simpa only [normSq, Fintype.sum_prod_type, Matrix.of_apply] using hG.le

theorem totalEnergy_band {n : ℕ} (hn : 8000 ≤ n) :
    (gaussMat (mA n) (n-1) 1).real
      {G | (1001/1000 : ℝ)*(mA n : ℝ)*(n-1 : ℕ) < ∑ i, normSq (G i)} ≤ exp (-18) := by
  apply (measureReal_mono ?_).trans (matrix_chi_upper (by norm_num : (0 : ℝ) ≤ 18))
  intro G hG
  simp only [Set.mem_setOf_eq] at hG ⊢
  exact (trace_upper_threshold (trace_dimension hn)).trans_lt
    (by simpa only [mul_assoc] using hG)

end BstLean.Part292
