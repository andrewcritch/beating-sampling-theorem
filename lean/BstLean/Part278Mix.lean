import BstLean.Part278Root

/-!
# Part 278 (O4, second half): from table errors to the root of `q̃`

Paper: `theorem7-09-assembly.tex` (the root of the odd tables); `theorem7-01-statement-program.tex`,
step 6 (the mixture table `λ̃ = f̃_g/√e_b`, `S̃ = (2/n)·max(1/5, ω̃_g − f̃_g²)`).

* `gridMix_pert`: two pairs of stored tables at the same node. If `|f̃′_g − f̃_g| ≤ δ_f`,
  `|ω̃′_g − ω̃_g| ≤ δ_ω` and `|f̃_g| ≤ F` at every node, then the location factors differ by at most
  `δ_f/√e_b`, the scales have relative error at most `5(δ_ω + δ_f(2F + δ_f))`, and the scale has
  the floor `0.4/n`. No event is needed for the floor.
* `odd_root_of_tables`: for the stated design against `paperDesignP`, the same table bounds give
  `|√q̃(stated) − √q̃(paper)| ≤ √(n δ_S² + (δ_f/√e_b)²|c_A|²/(0.8/n))`, `δ_S = 5(δ_ω + δ_f(2F + δ_f))`,
  when `δ_S ≤ 1/2`.
-/

namespace BstLean.Part278

open Real MeasureTheory
open BstLean.Part130 (normSq normSq_nonneg)
open BstLean.Part157 (Ret Design Centres qTilde gridMix paperCentres Js)
open BstLean.Part169 (paperDesignP passF passW bR)
open BstLean.Part272 (statedDesign passFSt passWSt)

variable {n : ℕ}

theorem abs_max_fifth_sub (x y : ℝ) : |max (1 / 5) x - max (1 / 5) y| ≤ |x - y| := by
  rcases le_total (1 / 5) x with hx | hx <;> rcases le_total (1 / 5) y with hy | hy
  · simp only [max_eq_right hx, max_eq_right hy, le_refl]
  · rw [max_eq_right hx, max_eq_left hy, abs_le]
    constructor <;> linarith [le_abs_self (x - y), neg_abs_le (x - y)]
  · rw [max_eq_left hx, max_eq_right hy, abs_le]
    constructor <;> linarith [le_abs_self (x - y), neg_abs_le (x - y)]
  · rw [max_eq_left hx, max_eq_left hy, sub_self, abs_zero]; exact abs_nonneg _

/-- The scalar perturbation of one table entry. -/
theorem mix_scalar {f f' w w' δf δw F : ℝ} (hf : |f' - f| ≤ δf) (hw : |w' - w| ≤ δw)
    (hF : |f| ≤ F) :
    |max (1 / 5) (w' - f' ^ 2) / max (1 / 5) (w - f ^ 2) - 1| ≤ 5 * (δw + δf * (2 * F + δf)) := by
  have hM : (1 / 5 : ℝ) ≤ max (1 / 5) (w - f ^ 2) := le_max_left _ _
  have hM0 : (0 : ℝ) < max (1 / 5) (w - f ^ 2) := by linarith
  have hδf : 0 ≤ δf := (abs_nonneg _).trans hf
  have hF0 : 0 ≤ F := (abs_nonneg _).trans hF
  have hsq : |f' ^ 2 - f ^ 2| ≤ δf * (2 * F + δf) := by
    rw [show f' ^ 2 - f ^ 2 = (f' - f) * (f' - f + 2 * f) by ring, abs_mul]
    refine mul_le_mul hf ?_ (abs_nonneg _) hδf
    calc |f' - f + 2 * f| ≤ |f' - f| + |2 * f| := abs_add_le _ _
      _ = |f' - f| + 2 * |f| := by rw [abs_mul, abs_two]
      _ ≤ δf + 2 * F := by linarith
      _ = 2 * F + δf := by ring
  have hnum : |max (1 / 5) (w' - f' ^ 2) - max (1 / 5) (w - f ^ 2)| ≤
      δw + δf * (2 * F + δf) := by
    refine (abs_max_fifth_sub _ _).trans ?_
    rw [show w' - f' ^ 2 - (w - f ^ 2) = (w' - w) - (f' ^ 2 - f ^ 2) by ring]
    exact (abs_sub _ _).trans (add_le_add hw hsq)
  rw [div_sub_one hM0.ne', abs_div, abs_of_pos hM0, div_le_iff₀ hM0]
  have h0 : 0 ≤ δw + δf * (2 * F + δf) := (abs_nonneg _).trans hnum
  nlinarith [mul_nonneg h0 (by linarith : (0:ℝ) ≤ max (1 / 5) (w - f ^ 2) - 1 / 5)]

theorem nodeIdx_le (Jn : ℕ) (L H s : ℝ) : BstLean.Part157.nodeIdx Jn L H s ≤ Jn - 1 :=
  min_le_left _ _

/-- **The mixture table under a perturbation of the stored tables.** -/
theorem gridMix_pert (hn : 1 ≤ n) (D : Centres n) (τ : Ret n → ℝ) (fT fT' wT wT' : Ret n → ℕ → ℝ)
    (c : Ret n) {δf δw F : ℝ} (hf : ∀ g, g ≤ Js n - 1 → |fT' c g - fT c g| ≤ δf)
    (hw : ∀ g, g ≤ Js n - 1 → |wT' c g - wT c g| ≤ δw) (hF : ∀ g, g ≤ Js n - 1 → |fT c g| ≤ F)
    (s : ℝ) :
    |(gridMix D τ fT' wT' c s).1 - (gridMix D τ fT wT c s).1| ≤
        δf / √(normSq (D.bA c.1 c.2.1.1) / (n : ℝ)) ∧
      |(gridMix D τ fT' wT' c s).2 / (gridMix D τ fT wT c s).2 - 1| ≤
        5 * (δw + δf * (2 * F + δf)) ∧
      2 / (n : ℝ) * (1 / 5) ≤ (gridMix D τ fT wT c s).2 ∧
      0 < (gridMix D τ fT' wT' c s).2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2n : (0 : ℝ) < 2 / (n : ℝ) := by positivity
  unfold gridMix
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← sub_div, abs_div, abs_of_nonneg (sqrt_nonneg _)]
    exact div_le_div_of_nonneg_right (hf _ (nodeIdx_le _ _ _ _)) (sqrt_nonneg _)
  · rw [mul_div_mul_left _ _ h2n.ne']
    exact mix_scalar (hf _ (nodeIdx_le _ _ _ _)) (hw _ (nodeIdx_le _ _ _ _))
      (hF _ (nodeIdx_le _ _ _ _))
  · exact mul_le_mul_of_nonneg_left (le_max_left _ _) h2n.le
  · exact mul_pos h2n (lt_of_lt_of_le (by norm_num) (le_max_left _ _))

theorem statedDesign_mix (c : Ret n) (s : ℝ) :
    (statedDesign n).mix c s = gridMix (paperCentres n) (fun c => BstLean.Part157.tau0p c.1.1)
      passFSt passWSt c s := rfl

theorem paperDesignP_mix (c : Ret n) (s : ℝ) :
    (paperDesignP n).mix c s = gridMix (paperCentres n) (fun c => BstLean.Part157.tau0p c.1.1)
      passF passW c s := rfl

/-- **O4.** The root of `q̃` between the stated design and `paperDesignP` from uniform bounds on
the differences of the stored tables. -/
theorem odd_root_of_tables (hn : 1 ≤ n) (t : ℝ) (c : Ret n) {δf δw F : ℝ}
    (hf : ∀ g, g ≤ Js n - 1 → |passFSt c g - passF c g| ≤ δf)
    (hw : ∀ g, g ≤ Js n - 1 → |passWSt c g - passW c g| ≤ δw)
    (hF : ∀ g, g ≤ Js n - 1 → |passF c g| ≤ F) (hδS : 5 * (δw + δf * (2 * F + δf)) ≤ 1 / 2) :
    |√(qTilde (statedDesign n) t c) - √(qTilde (paperDesignP n) t c)| ≤
      √(n * (5 * (δw + δf * (2 * F + δf))) ^ 2 +
        (δf / √(normSq (bR c) / (n : ℝ))) ^ 2 * normSq c.2.1.2 / (2 * (2 / (n : ℝ) * (1 / 5)))) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hP := fun s => gridMix_pert hn (paperCentres n) (fun c => BstLean.Part157.tau0p c.1.1)
    passF passFSt passW passWSt c hf hw hF s
  refine qTilde_table_root_window (paperDesignP n) (statedDesign n) rfl t c
    (S0 := 2 / (n : ℝ) * (1 / 5)) (by positivity) (fun s => ?_) (fun s => ?_) (fun s => ?_)
    (fun s => ?_) hδS
  · rw [paperDesignP_mix]; exact (hP s).2.2.1
  · rw [statedDesign_mix]; exact (hP s).2.2.2
  · rw [statedDesign_mix, paperDesignP_mix]; exact (hP s).1
  · rw [statedDesign_mix, paperDesignP_mix]; exact (hP s).2.1

end BstLean.Part278
