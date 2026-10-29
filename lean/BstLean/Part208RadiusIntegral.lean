import BstLean.Part208Laplace

/-! Part 208: a noncentral inverse-radius integral bound. -/
namespace BstLean.Part208
open MeasureTheory ProbabilityTheory Real Filter Topology Set
open scoped ENNReal

noncomputable def radiusKernel (n : ℕ) (v z t : ℝ) : ℝ :=
  (1 + 2 * t * v) ^ (-(n : ℝ) / 2) * exp (-(t * z / (1 + 2 * t * v)))

/-- A derivative majorant retains the noncentrality `z`. -/
theorem radiusKernel_lintegral_le {n : ℕ} (hn : 4 < n) {v z : ℝ}
    (hv : 0 < v) (hz : 0 ≤ z) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (radiusKernel n v z t) ≤
      ENNReal.ofReal (1 / (((n : ℝ) - 4) * v + z)) := by
  have hnR : (4 : ℝ) < n := by exact_mod_cast hn
  let p : ℝ := 2 - (n : ℝ) / 2
  let C : ℝ := ((n : ℝ) - 4) * v + z
  have hC : 0 < C := by dsimp [C]; positivity
  let b : ℝ → ℝ := fun t => 1 + 2 * t * v
  let g : ℝ → ℝ := fun t => -(b t ^ p * exp (-(t * z / b t))) / C
  let d : ℝ → ℝ := fun t => radiusKernel n v z t * (((n : ℝ) - 4) * v * b t + z) / C
  have hb : ∀ t, 0 ≤ t → 0 < b t := by intro t ht; dsimp [b]; positivity
  have hd : ∀ t ∈ Ici (0 : ℝ), HasDerivAt g (d t) t := by
    intro t ht
    have hb0 := hb t ht
    have hb' : HasDerivAt b (2 * v) t := by
      simpa [b, mul_assoc, mul_left_comm, mul_comm] using
        ((hasDerivAt_id t).const_mul (2 * v)).const_add 1
    have he := (((hasDerivAt_id t).mul_const z).div hb' hb0.ne').neg.exp
    have hg := (((hb'.rpow_const (p := p) (Or.inl hb0.ne')).mul he).neg).div_const C
    convert hg using 1 <;> dsimp [g, d, radiusKernel]
    have hp1 : b t ^ (p - 1) = b t ^ (-(n : ℝ) / 2) * b t := by
      calc
        _ = b t ^ (-(n : ℝ) / 2 + 1) := by congr 1; dsimp [p]; ring
        _ = _ := by rw [Real.rpow_add hb0, Real.rpow_one]
    have hp2 : b t ^ p = b t ^ (-(n : ℝ) / 2) * b t ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hb0]
      congr 1
      dsimp [p]
      ring
    rw [hp1, hp2]
    dsimp [p]
    field_simp [hb0.ne', hC.ne']
    dsimp [b]
    ring
  have hd0 : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ d t := by
    intro t ht
    dsimp [d, radiusKernel]
    have := hb t (le_of_lt ht)
    positivity
  have hg0 : Tendsto g atTop (𝓝 0) := by
    have hbt : Tendsto b atTop atTop := by
      simpa [b, mul_assoc, mul_left_comm, mul_comm] using
        tendsto_atTop_add_const_left _ 1
          ((tendsto_id (x := (atTop : Filter ℝ))).const_mul_atTop (by positivity : 0 < 2 * v))
    have hpow : Tendsto (fun t => b t ^ p) atTop (𝓝 0) := by
      have h := (tendsto_rpow_neg_atTop (y := (n : ℝ) / 2 - 2) (by linarith)).comp hbt
      convert h using 1
      ext t
      congr 1
      dsimp [p]
      ring
    have hprod : Tendsto (fun t => b t ^ p * exp (-(t * z / b t))) atTop (𝓝 0) := by
      apply squeeze_zero' _ _ hpow
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        exact mul_nonneg (rpow_nonneg (hb t ht).le _) (exp_pos _).le
      · filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
        have he : exp (-(t * z / b t)) ≤ 1 := by
          rw [exp_le_one_iff]
          exact neg_nonpos.mpr (div_nonneg (mul_nonneg ht hz) (hb t ht).le)
        simpa using mul_le_mul_of_nonneg_left he (rpow_nonneg (hb t ht).le p)
    simpa [g] using hprod.neg.div_const C
  have hdi := integrableOn_Ioi_deriv_of_nonneg' hd hd0 hg0
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' hd hd0 hg0
  calc
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (radiusKernel n v z t)
      ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (d t) := by
        apply setLIntegral_mono' measurableSet_Ioi
        intro t ht
        apply ENNReal.ofReal_le_ofReal
        have hk : 0 ≤ radiusKernel n v z t := by
          dsimp [radiusKernel]; exact mul_nonneg (rpow_nonneg (hb t ht.le).le _) (exp_pos _).le
        have hc : C ≤ ((n : ℝ) - 4) * v * b t + z := by
          dsimp [C, b]
          nlinarith [mul_nonneg (by linarith : 0 ≤ (n : ℝ) - 4) hv.le,
            mul_nonneg ht.le hv.le]
        dsimp [d]
        rw [le_div_iff₀ hC]
        exact mul_le_mul_of_nonneg_left hc hk
    _ = ENNReal.ofReal (1 / C) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hdi
        ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => hd0 t ht), hval]
      congr 1
      simp [g, b]
      ring

end BstLean.Part208
