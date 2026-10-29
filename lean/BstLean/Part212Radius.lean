import BstLean.Part41Error
import BstLean.Part162Dir

/-! Exact Gaussian radius moments and the direction sum with the exact coefficient. -/
namespace BstLean.Part212
open MeasureTheory ProbabilityTheory Real
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (radF53 unitF53)

/-- The unnormalized Gaussian radial product. -/
noncomputable def radialProduct (d j : ℕ) : ℝ :=
  ∏ i ∈ Finset.range j, ((d : ℝ) + 2 * i)

theorem radius_even (d j : ℕ) :
    ∫ g, radF53 g ^ (2 * j) ∂stdGauss (Fin d) = radialProduct d j := by
  simpa [radF53, radialProduct, BstLean.Part36.rhoD] using
    (BstLean.Part41.p1_gauss_norm_moment (ι := Fin d) j)

theorem radius_even_lintegral (d j : ℕ) (hd : 1 ≤ d) :
    ∫⁻ g, ENNReal.ofReal (radF53 g ^ (2 * j)) ∂stdGauss (Fin d) =
      ENNReal.ofReal (radialProduct d j) := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  rw [← ofReal_integral_eq_lintegral_ofReal (BstLean.Part162.integrable_radF_pow _)
    (ae_of_all _ fun g => pow_nonneg (Real.sqrt_nonneg _) _), radius_even]

theorem radialProduct_pos {d : ℕ} (hd : 1 ≤ d) (j : ℕ) :
    0 < radialProduct d j := by
  unfold radialProduct
  apply Finset.prod_pos
  intro i _
  have : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  positivity

theorem radialProduct_succ (d j : ℕ) :
    radialProduct d (j + 1) = radialProduct d j * ((d : ℝ) + 2 * j) := by
  exact Finset.prod_range_succ _ _

theorem radius_mean_lower {d : ℕ} (hd : 2 ≤ d) :
    √((d : ℝ) - 1) ≤ ∫ g, radF53 g ∂stdGauss (Fin d) := by
  have : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  have h := BstLean.Part162.sq_mean_radF_ge (d := d)
  have h0 : 0 ≤ ∫ g, radF53 g ∂stdGauss (Fin d) :=
    integral_nonneg fun _ => Real.sqrt_nonneg _
  rw [← Real.sqrt_sq h0]
  exact Real.sqrt_le_sqrt h

/-- The exact radius coefficient for order `2j`. -/
noncomputable def exactRadius (d j : ℕ) : ℝ :=
  radialProduct d j ^ (1 / (2 * (j : ℝ))) / √((d : ℝ) - 1)

theorem exactRadius_pow {d j : ℕ} (hd : 2 ≤ d) (hj : 1 ≤ j) :
    exactRadius d j ^ (2 * j) = radialProduct d j / ((d : ℝ) - 1) ^ j := by
  have hP := (radialProduct_pos (by omega : 1 ≤ d) j).le
  have hj0 : (j : ℝ) ≠ 0 := by exact_mod_cast (show j ≠ 0 by omega)
  unfold exactRadius
  rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hP]
  have he : 1 / (2 * (j : ℝ)) * (↑(2 * j) : ℝ) = 1 := by
    push_cast; field_simp
  rw [he, Real.rpow_one]
  rw [pow_mul, Real.sq_sqrt]
  have : (2 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

/-- Independent directions represented by normalized independent Gaussian rows. -/
theorem direction_sum_exact {d m j : ℕ} (hd : 2 ≤ d) (hm : 1 ≤ m) (hj : 1 ≤ j)
    (c : Fin m → ℝ) :
    ∫ G, radF53 (∑ i, c i • unitF53 (G i)) ^ (2 * j)
        ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)) ≤
      exactRadius d j ^ (2 * j) * radF53 c ^ (2 * j) := by
  have h := BstLean.Part162.dirsum_le_sqrt hm hd c (k := 2 * j) (by omega)
  rw [radius_even, pow_mul, Real.sq_sqrt] at h
  · rw [exactRadius_pow hd hj]; exact h
  · have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith

theorem radius_order160 (d : ℕ) :
    ∫ g, radF53 g ^ 160 ∂stdGauss (Fin d) = radialProduct d 80 :=
  radius_even d 80

theorem direction_sum_order160 {d m : ℕ} (hd : 2 ≤ d) (hm : 1 ≤ m)
    (c : Fin m → ℝ) :
    ∫ G, radF53 (∑ i, c i • unitF53 (G i)) ^ 160
        ∂Measure.pi (fun _ : Fin m => stdGauss (Fin d)) ≤
      exactRadius d 80 ^ 160 * radF53 c ^ 160 :=
  direction_sum_exact (j := 80) hd hm (by norm_num) c

theorem direction_sum_norm {d m j : ℕ} (hd : 2 ≤ d) (hm : 1 ≤ m) (hj : 1 ≤ j)
    (c : Fin m → ℝ) :
    BstLean.Part161.momN (Measure.pi (fun _ : Fin m => stdGauss (Fin d))) (2 * j)
      (fun G => radF53 (∑ i, c i • unitF53 (G i))) ≤ exactRadius d j * radF53 c := by
  have h0 : 0 ≤ exactRadius d j * radF53 c := by
    unfold exactRadius
    exact mul_nonneg (div_nonneg
      (Real.rpow_nonneg (radialProduct_pos (by omega : 1 ≤ d) j).le _)
      (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  apply le_of_pow_le_pow_left₀ (by omega : 2 * j ≠ 0) h0
  rw [BstLean.Part161.momN_pow _ (by omega), mul_pow]
  simpa only [abs_of_nonneg (BstLean.Part162.radF_nonneg _)] using
    direction_sum_exact hd hm hj c

/-- A uniform coefficient bound covers the full frontier interval. -/
theorem exactRadius_order160_frontier {n : ℕ} (hn : 8000 ≤ n) :
    exactRadius (n - 2) 80 ≤ 101 / 100 := by
  have hd : 2 ≤ n - 2 := by omega
  have hdR : (7998 : ℝ) ≤ (n - 2 : ℕ) := by exact_mod_cast (show 7998 ≤ n - 2 by omega)
  have hP : radialProduct (n - 2) 80 ≤ ((n - 2 : ℕ) + (158 : ℝ)) ^ 80 := by
    unfold radialProduct
    calc (∏ i ∈ Finset.range 80, ((n - 2 : ℕ) + 2 * (i : ℝ)))
        ≤ ∏ _i ∈ Finset.range 80, ((n - 2 : ℕ) + (158 : ℝ)) := by
          apply Finset.prod_le_prod₀
          · intro i _; positivity
          · intro i hi
            have hiR : (i : ℝ) ≤ 79 := by
              exact_mod_cast (show i ≤ 79 by have := Finset.mem_range.mp hi; omega)
            linarith
      _ = _ := by simp
  have hratio : ((n - 2 : ℕ) + (158 : ℝ)) / ((n - 2 : ℕ) - (1 : ℝ)) ≤
      (101 / 100 : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have h0 : 0 ≤ exactRadius (n - 2) 80 := by
    unfold exactRadius
    exact div_nonneg (Real.rpow_nonneg (radialProduct_pos (by omega : 1 ≤ n - 2) 80).le _)
      (Real.sqrt_nonneg _)
  apply le_of_pow_le_pow_left₀ (by norm_num : (160 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 101 / 100)
  rw [show (160 : ℕ) = 2 * 80 by norm_num, exactRadius_pow hd (by norm_num)]
  calc radialProduct (n - 2) 80 / ((n - 2 : ℕ) - (1 : ℝ)) ^ 80
      ≤ ((n - 2 : ℕ) + (158 : ℝ)) ^ 80 / ((n - 2 : ℕ) - (1 : ℝ)) ^ 80 :=
        div_le_div_of_nonneg_right hP (pow_nonneg (by linarith) 80)
    _ = (((n - 2 : ℕ) + (158 : ℝ)) / ((n - 2 : ℕ) - (1 : ℝ))) ^ 80 := by rw [div_pow]
    _ ≤ ((101 / 100 : ℝ) ^ 2) ^ 80 :=
      pow_le_pow_left₀ (div_nonneg (by linarith) (by linarith)) hratio _
    _ = _ := by rw [← pow_mul]
end BstLean.Part212
