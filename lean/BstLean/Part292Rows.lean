import BstLean.Part221SharpSphere1664
import BstLean.Part221ChiRadius
import BstLean.Part223Maximum

/-! All-row bounds. At order 1664 the exact Gaussian radial moment and
arithmetic mean bound avoid a numerical tail integral on the low band. -/
namespace BstLean.Part292
open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (radF53 measurable_radF)
open BstLean.Part130 BstLean.Part167 BstLean.Part212

theorem maximum_even_moment {m d : ℕ} (hm : 0 < m) (hd : 1 ≤ d) (j : ℕ) :
    (∫⁻ G, ENNReal.ofReal (Mx hm G ^ (2 * j))
      ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d))) ≤
      ENNReal.ofReal ((m : ℝ) * radialProduct d j) := by
  have hpt (G : Fin m → Fin d → ℝ) : ENNReal.ofReal (Mx hm G ^ (2 * j)) ≤
      ∑ i, ENNReal.ofReal (radF53 (G i) ^ (2 * j)) := by
    have hn (i : Fin m) (_ : i ∈ Finset.univ) : 0 ≤ radF53 (G i) ^ (2 * j) :=
      pow_nonneg (show 0 ≤ radF53 (G i) from sqrt_nonneg _) _
    rw [← ENNReal.ofReal_sum_of_nonneg hn]
    exact ENNReal.ofReal_le_ofReal (Mx_pow_le hm G _)
  have hf : Measurable (fun g : Fin d → ℝ =>
      ENNReal.ofReal (radF53 g ^ (2 * j))) :=
    (measurable_radF.pow_const _).ennreal_ofReal
  refine (lintegral_mono hpt).trans_eq ?_
  have hmi (i : Fin m) : Measurable (fun G : Fin m → Fin d → ℝ =>
      ENNReal.ofReal (radF53 (G i) ^ (2 * j))) := hf.comp (measurable_pi_apply i)
  rw [lintegral_finsetSum _ (fun i _ => hmi i)]
  have he (i : Fin m) : (∫⁻ G, ENNReal.ofReal (radF53 (G i) ^ (2 * j))
      ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d))) =
      ENNReal.ofReal (radialProduct d j) := by
    rw [(measurePreserving_eval (fun _ : Fin m => stdGauss (Fin d)) i).lintegral_comp hf]
    exact radius_even_lintegral d j hd
  simp_rw [he]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg m)]

/-- A small rational power absorbs the entire row count on the band. -/
theorem row_count_power : (11882 : ℝ) ^ 2 ≤ (1023 / 1000 : ℝ) ^ 832 := by
  have h : (427 / 100 : ℝ) ≤ (1023 / 1000 : ℝ) ^ 64 := by norm_num
  calc
    (11882 : ℝ) ^ 2 ≤ (427 / 100 : ℝ) ^ 13 := by norm_num
    _ ≤ ((1023 / 1000 : ℝ) ^ 64) ^ 13 := pow_le_pow_left₀ (by norm_num) h 13
    _ = _ := by rw [← pow_mul]

theorem maximum_moment1664_band {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882)
    (hm : 0 < mA n) :
    (∫⁻ G, ENNReal.ofReal (Mx hm G ^ 1664)
      ∂Measure.pi (fun _ : Fin (mA n) => stdGauss (Fin (n - 2)))) ≤
      ENNReal.ofReal (((11291 / 10000 : ℝ) * n) ^ 832) := by
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR' : (n : ℝ) ≤ 11882 := by exact_mod_cast hn'
  have hd : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := by
    rw [Nat.cast_sub (by omega : 2 ≤ n)]; norm_num
  have hp := BstLean.Part221.radialProduct832_le_mean (d := n - 2) (by omega)
  rw [hd] at hp
  have hm' : (mA n : ℝ) ≤ (1023 / 1000 : ℝ) ^ 832 := by
    calc (mA n : ℝ) = (n : ℝ) ^ 2 := by simp [mA]
      _ ≤ (11882 : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnR' 2
      _ ≤ _ := row_count_power
  have hbase : (1023 / 1000 : ℝ) * ((n : ℝ) - 2 + 831) ≤ 11291 / 10000 * n := by
    linarith
  have h := maximum_even_moment hm (by omega : 1 ≤ n - 2) 832
  apply h.trans (ENNReal.ofReal_le_ofReal ?_)
  calc (mA n : ℝ) * radialProduct (n - 2) 832 ≤
      (1023 / 1000 : ℝ) ^ 832 * ((n : ℝ) - 2 + 831) ^ 832 :=
        mul_le_mul hm' hp (radialProduct_pos (by omega) 832).le (by positivity)
    _ = ((1023 / 1000 : ℝ) * ((n : ℝ) - 2 + 831)) ^ 832 := (mul_pow _ _ _).symm
    _ ≤ _ := pow_le_pow_left₀ (mul_nonneg (by norm_num) (by linarith)) hbase _

/-- The all-row Chernoff bound uses all rows, with no half-gate factor. -/
theorem maximum_chernoff {m d : ℕ} (hm : 0 < m) (hd : 1 ≤ d)
    {a : ℝ} (ha : 0 < a) (ha2 : (d : ℝ) < a ^ 2) :
    (Measure.pi (fun _ : Fin m => stdGauss (Fin d))).real
      {G | a < Mx hm G} ≤ (m : ℝ) * exp (-BstLean.Part221.chiRadiusRate d a) := by
  have he : {G : Fin m → Fin d → ℝ | a < Mx hm G} =
      ⋃ i, {G | a < radF53 (G i)} := by
    ext G
    simp only [mem_setOf_eq, mem_iUnion, Mx, Finset.lt_sup'_iff, Finset.mem_univ, true_and]
  rw [he]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  calc
    (∑ i : Fin m, (Measure.pi (fun _ : Fin m => stdGauss (Fin d))).real
      {G | a < radF53 (G i)}) ≤ ∑ _i : Fin m, exp (-BstLean.Part221.chiRadiusRate d a) := by
      apply Finset.sum_le_sum
      intro i _
      have heval := (measurePreserving_eval (fun _ : Fin m => stdGauss (Fin d)) i).measure_preimage
        (s := {g | a < radF53 g})
        (measurableSet_lt measurable_const measurable_radF).nullMeasurableSet
      have hr := congrArg ENNReal.toReal heval
      change (Measure.pi (fun _ : Fin m => stdGauss (Fin d))).real
        {G | a < radF53 (G i)} = (stdGauss (Fin d)).real {g | a < radF53 g} at hr
      rw [hr]
      exact BstLean.Part221.gaussian_radius_chernoff hd ha ha2
    _ = _ := by simp

end BstLean.Part292

/-- info: 'BstLean.Part292.maximum_moment1664_band' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part292.maximum_moment1664_band

/-- info: 'BstLean.Part292.maximum_chernoff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part292.maximum_chernoff
