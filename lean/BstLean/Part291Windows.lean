import BstLean.Part264bGeometryNormalize

namespace BstLean.BlueprintLow
open Real Set BstLean.Part199 BstLean.Part264b BstLean.Part255

noncomputable def lowCoreWindow : Window where
  t := 2.88
  z := 7.81
  pair := 3.27
  t_nonneg := by norm_num
  z_nonneg := by norm_num
  pair_nonneg := by norm_num

def lowWideWindow : Window where
  t := 6
  z := 20
  pair := 8
  t_nonneg := by norm_num
  z_nonneg := by norm_num
  pair_nonneg := by norm_num

theorem lowWindows_order : lowCoreWindow.LE lowWideWindow := by
  constructor <;> norm_num [lowCoreWindow, lowWideWindow]

theorem lowInvDimension {n : ℕ} (hn : 8000 ≤ n) : B 0 (1/8000) (invN n) := by
  have h : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  constructor
  · unfold invN; positivity
  · unfold invN; gcongr

end BstLean.BlueprintLow
