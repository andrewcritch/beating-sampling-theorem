import BstLean.Part167Max

namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (radF53 measurable_radF)
open BstLean.Part167 (Mx Mx_nonneg Mx_pow_le measurable_Mx young_pow)
variable {m d : ℕ}

theorem max_moment160 (hm : 0 < m) {q : ℕ} (hq : 1 ≤ q) :
    ∫⁻ G, ENNReal.ofReal (Mx hm G ^ 160) ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)) ≤
      ENNReal.ofReal ((m : ℝ) ^ ((1 : ℝ) / q) * ((d : ℝ) + 160 * q) ^ 80) := by
  set Q := Measure.pi (fun _ : Fin m => stdGauss (Fin d))
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  set K : ℝ := (m : ℝ) ^ ((1 : ℝ) / q) * ((d : ℝ) + 160 * q) ^ 80 with hK
  have hK0 : 0 < K := by
    have : 0 < (d : ℝ) + 160 * q := by positivity
    positivity
  have hKq : K ^ q = m * ((d : ℝ) + 160 * q) ^ (80 * q) := by
    rw [hK, mul_pow, ← Real.rpow_natCast ((m : ℝ) ^ ((1 : ℝ) / q)), ← Real.rpow_mul (by positivity),
      one_div, inv_mul_cancel₀ (by positivity), Real.rpow_one, ← pow_mul]
  -- the high moment
  have hhigh : ∫⁻ G, ENNReal.ofReal ((Mx hm G ^ 160) ^ q) ∂Q ≤ ENNReal.ofReal (K ^ q) := by
    have hpt : ∀ G : Fin m → Fin d → ℝ, ENNReal.ofReal ((Mx hm G ^ 160) ^ q) ≤
        ∑ i, ENNReal.ofReal ((∑ j, G i j ^ 2) ^ (80 * q)) := by
      intro G
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
      apply ENNReal.ofReal_le_ofReal
      rw [← pow_mul]
      refine (Mx_pow_le hm G (160 * q)).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show 160 * q = 2 * (80 * q) by ring, pow_mul, BstLean.Part162.radF_sq]
    refine (lintegral_mono hpt).trans ?_
    have hmi : ∀ i : Fin m, Measurable (fun G : Fin m → Fin d → ℝ =>
        ENNReal.ofReal ((∑ j, G i j ^ 2) ^ (80 * q))) := fun i =>
      ENNReal.measurable_ofReal.comp ((Finset.measurable_sum _ fun j _ =>
        ((measurable_pi_apply j).comp (measurable_pi_apply i)).pow_const 2).pow_const _)
    rw [lintegral_finsetSum _ (fun i _ => hmi i)]
    have hrow : ∀ i : Fin m, ∫⁻ G, ENNReal.ofReal ((∑ j, G i j ^ 2) ^ (80 * q)) ∂Q ≤
        ENNReal.ofReal (((d : ℝ) + 2 * (80 * q : ℕ)) ^ (80 * q)) := by
      intro i
      have hmp := MeasureTheory.measurePreserving_eval (fun _ : Fin m => stdGauss (Fin d)) i
      have hf : Measurable (fun g : Fin d → ℝ => ENNReal.ofReal ((∑ j, g j ^ 2) ^ (80 * q))) :=
        ENNReal.measurable_ofReal.comp ((Finset.measurable_sum _ fun j _ =>
          (measurable_pi_apply j).pow_const 2).pow_const _)
      have := hmp.lintegral_comp hf
      simp only [Function.eval] at this
      rw [this]
      have h := BstLean.Part166.chi_mom (ι := Fin d) (80 * q)
      simpa using h
    calc ∑ i : Fin m, ∫⁻ G, ENNReal.ofReal ((∑ j, G i j ^ 2) ^ (80 * q)) ∂Q
        ≤ ∑ _i : Fin m, ENNReal.ofReal (((d : ℝ) + 2 * (80 * q : ℕ)) ^ (80 * q)) :=
          Finset.sum_le_sum fun i _ => hrow i
      _ = ENNReal.ofReal (K ^ q) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hKq,
            ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          congr 2; push_cast; ring
  -- Young
  have hpt : ∀ G : Fin m → Fin d → ℝ, ENNReal.ofReal (Mx hm G ^ 160) ≤
      ENNReal.ofReal (1 / (q * K ^ (q - 1))) * ENNReal.ofReal ((Mx hm G ^ 160) ^ q) +
        ENNReal.ofReal ((1 - 1 / q) * K) := by
    intro G
    have h1 : 0 ≤ 1 - 1 / (q : ℝ) := by
      rw [sub_nonneg, div_le_one (by positivity)]; exact hqR
    rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
      (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have := young_pow (pow_nonneg (Mx_nonneg hm G) 160) hK0 hq
    rw [div_eq_mul_one_div] at this
    linarith
  refine (lintegral_mono hpt).trans ?_
  have hmeas : Measurable (fun G : Fin m → Fin d → ℝ => ENNReal.ofReal ((Mx hm G ^ 160) ^ q)) :=
    ENNReal.measurable_ofReal.comp (((measurable_Mx hm).pow_const 160).pow_const q)
  rw [lintegral_add_right _ measurable_const, lintegral_const_mul _ hmeas, lintegral_const,
    measure_univ, mul_one]
  have h1 : 0 ≤ 1 - 1 / (q : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]; exact hqR
  calc ENNReal.ofReal (1 / (q * K ^ (q - 1))) * ∫⁻ G, ENNReal.ofReal ((Mx hm G ^ 160) ^ q) ∂Q +
        ENNReal.ofReal ((1 - 1 / q) * K)
      ≤ ENNReal.ofReal (1 / (q * K ^ (q - 1))) * ENNReal.ofReal (K ^ q) +
          ENNReal.ofReal ((1 - 1 / q) * K) := by gcongr
    _ = ENNReal.ofReal K := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
          (by positivity)]
        congr 1
        obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
        simp only [Nat.add_sub_cancel]
        rw [pow_succ]
        push_cast
        field_simp
        ring

end BstLean.Part212
