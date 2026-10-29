import BstLean.Part289Constants

/-! The existing table-root allowance remains sufficient with the lower floor.
The table-error caps are explicit hypotheses, independent of any per-row certificate. -/
namespace BstLean.Part289
open Real BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part272
variable {n : ℕ}

theorem paper_small_parameter (hn : 1 ≤ n) :
    0 ≤ (1 / 10 ^ 45 : ℝ) / (n : ℝ) ^ 5 ∧
      ((1 / 10 ^ 45 : ℝ) / (n : ℝ) ^ 5) * (n : ℝ) ^ 3 ≤ 1 / 10 ^ 45 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  refine ⟨by positivity, ?_⟩
  have he : ((1 / 10 ^ 45 : ℝ) / (n : ℝ) ^ 5) * (n : ℝ) ^ 3 =
      (1 / 10 ^ 45 : ℝ) * (1 / (n : ℝ) ^ 2) := by field_simp
  rw [he]
  exact mul_le_of_le_one_right (by positivity)
    (div_le_one_of_le₀ (one_le_pow₀ hnR) (by positivity))

theorem small_table_numeric (hn : 1 ≤ n) {u χ : ℝ} (hu0 : 0 ≤ u)
    (hu : u * (n : ℝ) ^ 3 ≤ 1 / 10 ^ 45) (hχ : χ ≤ n) :
    √((n : ℝ) * (1650 * u * n ^ 2) ^ 2 + 3 * χ * n * (8 * u * n) ^ 2) ≤ 1 / 10 ^ 20 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by positivity
  have h5 : (n : ℝ) ^ 5 ≤ (n : ℝ) ^ 6 := pow_le_pow_right₀ hnR (by norm_num)
  have h4 : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 6 := pow_le_pow_right₀ hnR (by norm_num)
  have hχterm : 3 * χ * n * (8 * u * n) ^ 2 ≤ 192 * u ^ 2 * (n : ℝ) ^ 4 := by
    have h := mul_le_mul_of_nonneg_right hχ
      (by positivity : (0 : ℝ) ≤ 3 * n * (8 * u * n) ^ 2)
    nlinarith only [h]
  have hrad : (n : ℝ) * (1650 * u * n ^ 2) ^ 2 + 3 * χ * n * (8 * u * n) ^ 2 ≤
      2722692 * (u * (n : ℝ) ^ 3) ^ 2 := by
    have hA := mul_le_mul_of_nonneg_left h5 (by positivity : (0 : ℝ) ≤ 2722500 * u ^ 2)
    have hB := mul_le_mul_of_nonneg_left h4 (by positivity : (0 : ℝ) ≤ 192 * u ^ 2)
    nlinarith only [hχterm, hA, hB]
  rw [Real.sqrt_le_left (by norm_num)]
  calc _ ≤ 2722692 * (u * (n : ℝ) ^ 3) ^ 2 := hrad
    _ ≤ 2722692 * (1 / 10 ^ 45 : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hu 2) (by norm_num)
    _ ≤ _ := by norm_num

/-- The small table caps imply the same `10^-20` root allowance for the revised design. -/
theorem odd_root_of_small_tables (hn : 1 ≤ n) (t : ℝ) (c : Ret n) {u χ : ℝ}
    (hu0 : 0 ≤ u) (hu : u * (n : ℝ) ^ 3 ≤ 1 / 10 ^ 45)
    (hχ0 : 0 ≤ χ) (hχ : χ ≤ n) (he : 0 < eR c)
    (hc : normSq c.2.1.2 ≤ 2 / (n : ℝ) * eR c * n * χ)
    (hf : ∀ g, g ≤ Js n - 1 → |passFSt c g - passF c g| ≤ 8 * u * n)
    (hw : ∀ g, g ≤ Js n - 1 → |passWSt c g - passW c g| ≤ 130 * u * (n : ℝ) ^ 2)
    (hF : ∀ g, g ≤ Js n - 1 → |passF c g| ≤ 9 * n) :
    |√(qTilde (statedDesign2 n) t c) - √(qTilde (idealDesignFloor n (scaleFloor n)) t c)| ≤
      1 / 10 ^ 20 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs := scaleFloor_pos n
  have hc' : normSq c.2.1.2 ≤ 2 * eR c * χ := by
    have h : 2 / (n : ℝ) * eR c * n * χ = 2 * eR c * χ := by field_simp
    exact hc.trans_eq h
  have hfloor : (1 : ℝ) ≤ 6 * scaleFloor n := by
    have h := (scaleFloor_bounds n).1
    linarith
  have hu1 : u ≤ 1 / 64 := by
    have hpow : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hnR
    have h := mul_le_mul_of_nonneg_left hpow hu0
    linarith
  let δ := (130 * u * (n : ℝ) ^ 2 + (8 * u * n) * (2 * (9 * n) + 8 * u * n)) / scaleFloor n
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ := table_scale_cap n hu0 hu1
  have hδhalf : δ ≤ 1 / 2 := by
    have h23 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := pow_le_pow_right₀ hnR (by norm_num)
    have hp := mul_le_mul_of_nonneg_left h23 hu0
    change δ ≤ 1650 * u * (n : ℝ) ^ 2 at hδ
    nlinarith only [hδ, hu, hp]
  have hroot := odd_root_of_tables_floor hn t c hf hw hF hδhalf
  refine hroot.trans ((sqrt_le_sqrt (add_le_add ?_ ?_)).trans (small_table_numeric hn hu0 hu hχ))
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ0 hδ 2) hn0.le
  · change (8 * u * n / √(eR c)) ^ 2 * normSq c.2.1.2 /
        (2 * (2 / (n : ℝ) * scaleFloor n)) ≤ 3 * χ * n * (8 * u * n) ^ 2
    rw [div_pow, sq_sqrt he.le]
    have heq : (8 * u * n) ^ 2 / eR c * normSq c.2.1.2 /
        (2 * (2 / (n : ℝ) * scaleFloor n)) =
        (8 * u * n) ^ 2 * normSq c.2.1.2 * n / (4 * scaleFloor n * eR c) := by
      field_simp; ring
    rw [heq, div_le_iff₀ (by positivity : 0 < 4 * scaleFloor n * eR c)]
    calc _ ≤ (8 * u * n) ^ 2 * (2 * eR c * χ) * n :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc' (sq_nonneg _)) hn0.le
      _ ≤ (8 * u * n) ^ 2 * (6 * scaleFloor n * (2 * eR c * χ)) * n := by
          have hscaled : 2 * eR c * χ ≤ 6 * scaleFloor n * (2 * eR c * χ) := by
            simpa only [one_mul] using (mul_le_mul_of_nonneg_right hfloor
              (by positivity : 0 ≤ 2 * eR c * χ))
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hscaled (sq_nonneg _)) hn0.le
      _ = _ := by ring

end BstLean.Part289

/-- info: 'BstLean.Part289.odd_root_of_small_tables' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.odd_root_of_small_tables
