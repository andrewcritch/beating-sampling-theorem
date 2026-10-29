import BstLean.Part289Pass
import BstLean.Part278Mix

/-! Part 09 table perturbation with a floor parameter: `1/s₀` replaces 5,
and `2*s₀/n` replaces the scale lower bound `.4/n`. -/
namespace BstLean.Part289
open Real MeasureTheory BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part272
variable {n : ℕ}

theorem mix_scalar_floor {s₀ f f' w w' δf δw F : ℝ} (hs₀ : 0 < s₀)
    (hf : |f' - f| ≤ δf) (hw : |w' - w| ≤ δw) (hF : |f| ≤ F) :
    |max s₀ (w' - f' ^ 2) / max s₀ (w - f ^ 2) - 1| ≤
      (δw + δf * (2 * F + δf)) / s₀ := by
  have hM : s₀ ≤ max s₀ (w - f ^ 2) := le_max_left _ _
  have hM0 : 0 < max s₀ (w - f ^ 2) := hs₀.trans_le hM
  have hδf : 0 ≤ δf := (abs_nonneg _).trans hf
  have hsq : |f' ^ 2 - f ^ 2| ≤ δf * (2 * F + δf) := by
    rw [show f' ^ 2 - f ^ 2 = (f' - f) * (f' - f + 2 * f) by ring, abs_mul]
    refine mul_le_mul hf ?_ (abs_nonneg _) hδf
    calc |f' - f + 2 * f| ≤ |f' - f| + |2 * f| := abs_add_le _ _
      _ = |f' - f| + 2 * |f| := by rw [abs_mul, abs_two]
      _ ≤ 2 * F + δf := by linarith
  have hnum : |max s₀ (w' - f' ^ 2) - max s₀ (w - f ^ 2)| ≤
      δw + δf * (2 * F + δf) := by
    refine (floor_lipschitz s₀ _ _).trans ?_
    rw [show w' - f' ^ 2 - (w - f ^ 2) = (w' - w) - (f' ^ 2 - f ^ 2) by ring]
    exact (abs_sub _ _).trans (add_le_add hw hsq)
  rw [div_sub_one hM0.ne', abs_div, abs_of_pos hM0]
  exact (div_le_div_of_nonneg_right hnum hM0.le).trans
    (div_le_div_of_nonneg_left ((abs_nonneg _).trans hnum) hs₀ hM)

theorem gridMixFloor_pert (hn : 1 ≤ n) {s₀ : ℝ} (hs₀ : 0 < s₀)
    (D : Centres n) (τ : Ret n → ℝ) (fT fT' wT wT' : Ret n → ℕ → ℝ)
    (c : Ret n) {δf δw F : ℝ} (hf : ∀ g, g ≤ Js n - 1 → |fT' c g - fT c g| ≤ δf)
    (hw : ∀ g, g ≤ Js n - 1 → |wT' c g - wT c g| ≤ δw)
    (hF : ∀ g, g ≤ Js n - 1 → |fT c g| ≤ F) (s : ℝ) :
    |(gridMixFloor s₀ D τ fT' wT' c s).1 - (gridMixFloor s₀ D τ fT wT c s).1| ≤
        δf / √(normSq (D.bA c.1 c.2.1.1) / (n : ℝ)) ∧
      |(gridMixFloor s₀ D τ fT' wT' c s).2 / (gridMixFloor s₀ D τ fT wT c s).2 - 1| ≤
        (δw + δf * (2 * F + δf)) / s₀ ∧
      2 / (n : ℝ) * s₀ ≤ (gridMixFloor s₀ D τ fT wT c s).2 ∧
      0 < (gridMixFloor s₀ D τ fT' wT' c s).2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have hg : gridNode τ c s ≤ Js n - 1 := min_le_left _ _
  refine ⟨(Part278.gridMix_pert hn D τ fT fT' wT wT' c hf hw hF s).1, ?_, ?_, ?_⟩
  · change |(2 / (n : ℝ) * max s₀ _) / (2 / (n : ℝ) * max s₀ _) - 1| ≤ _
    rw [mul_div_mul_left _ _ hγ.ne']
    exact mix_scalar_floor hs₀ (hf _ hg) (hw _ hg) (hF _ hg)
  · exact mul_le_mul_of_nonneg_left (le_max_left _ _) hγ.le
  · exact mul_pos hγ (hs₀.trans_le (le_max_left _ _))

theorem statedDesign2_scale_lower (hn : 0 < n) (c : Ret n) (s : ℝ) :
    (34 / 100 : ℝ) / n ≤ ((statedDesign2 n).mix c s).2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [statedDesign2_scale]
  calc (34 / 100 : ℝ) / n = 2 / (n : ℝ) * (17 / 100) := by ring
    _ ≤ 2 / (n : ℝ) * scaleFloor n :=
      mul_le_mul_of_nonneg_left (scaleFloor_bounds n).1 (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)

/-- Both the executable tables and the exact tables use the adopted floor. -/
theorem odd_root_of_tables_floor (hn : 1 ≤ n) (t : ℝ) (c : Ret n) {δf δw F : ℝ}
    (hf : ∀ g, g ≤ Js n - 1 → |passFSt c g - passF c g| ≤ δf)
    (hw : ∀ g, g ≤ Js n - 1 → |passWSt c g - passW c g| ≤ δw)
    (hF : ∀ g, g ≤ Js n - 1 → |passF c g| ≤ F)
    (hδS : (δw + δf * (2 * F + δf)) / scaleFloor n ≤ 1 / 2) :
    |√(qTilde (statedDesign2 n) t c) - √(qTilde (idealDesignFloor n (scaleFloor n)) t c)| ≤
      √(n * ((δw + δf * (2 * F + δf)) / scaleFloor n) ^ 2 +
        (δf / √(normSq (bR c) / (n : ℝ))) ^ 2 * normSq c.2.1.2 /
          (2 * (2 / (n : ℝ) * scaleFloor n))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs₀ := scaleFloor_pos n
  have hP := fun s => gridMixFloor_pert hn hs₀ (paperCentres n) (fun c => tau0p c.1.1)
    passF passFSt passW passWSt c hf hw hF s
  exact Part278.qTilde_table_root_window (idealDesignFloor n (scaleFloor n)) (statedDesign2 n)
    rfl t c (S0 := 2 / (n : ℝ) * scaleFloor n) (by positivity)
    (fun s => (hP s).2.2.1) (fun s => (hP s).2.2.2)
    (fun s => (hP s).1) (fun s => (hP s).2.1) hδS

end BstLean.Part289

/-- info: 'BstLean.Part289.odd_root_of_tables_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.odd_root_of_tables_floor
/-- info: 'BstLean.Part289.statedDesign2_scale_lower' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.statedDesign2_scale_lower
