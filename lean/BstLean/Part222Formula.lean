import BstLean.Part222EnergyEvent

/-! The checked energy and mass definitions have the paper normalization. -/
namespace BstLean.Part222
open MeasureTheory Real
open BstLean.Part130

noncomputable def paperLayerAllowance (n : ℕ) : ℝ :=
  BstLean.Part195.rotationConstant 16 * √2 / n + 5/(2*(n : ℝ)^2)

theorem agentLayerAllowance_formula {n : ℕ} (hn : 1 ≤ n) :
    agentLayerAllowance n = paperLayerAllowance n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hm : (mA n : ℝ) = (n : ℝ)^2 := by unfold mA; push_cast; rfl
  unfold agentLayerAllowance layerAllowance paperLayerAllowance
  rw [hm, sqrt_div (by norm_num : (0 : ℝ) ≤ 2), sqrt_sq hnR.le]
  ring

theorem energyAllowance_formula {n : ℕ} (hn : 1 ≤ n) :
    energyAllowance n = (20000 : ℝ)^((32 : ℝ)⁻¹) *
      (2*paperLayerAllowance n+paperLayerAllowance n^2) := by
  unfold energyAllowance energyWeightAllowance
  rw [agentLayerAllowance_formula hn]

noncomputable def massGap (n : ℕ) (xi E u d : ℝ) : ℝ :=
  √(n : ℝ)*(√((1-u)^2-d)-√E)-√xi

lemma massGap_identity {n : ℕ} (hn : 1 ≤ n) {xi E u d : ℝ} (hxi : 0 ≤ xi) :
    massGap n xi E u d = √(n : ℝ)*(√((1-u)^2-d)-(√E+√(xi/n))) := by
  have hs : √(n : ℝ) ≠ 0 := (sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  unfold massGap
  rw [sqrt_div hxi]
  field_simp
  <;> ring

/-- The normalized mass equals the displayed paper formula at order twelve. -/
theorem massBound_formula {n : ℕ} (hn : 1 ≤ n) {M H xi E u d : ℝ}
    (hM : 0 ≤ M) (hxi : 0 ≤ xi)
    (hg : 0 < √((1-u)^2-d)-(√E+√(xi/n))) :
    massBound n M H xi E u d =
      (n : ℝ)*(H/u)^32 + (n : ℝ)*
        (BstLean.Part195.rotationConstant 12 * √M / massGap n xi E u d)^24 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : √(n : ℝ) ≠ 0 := (sqrt_pos.mpr hnR).ne'
  have hs24 : √(n : ℝ)^24 = (n : ℝ)^12 := by
    rw [show (24 : ℕ) = 2*12 from rfl, pow_mul, sq_sqrt hnR.le]
  have hm24 : √M^24 = M^12 := by
    rw [show (24 : ℕ) = 2*12 from rfl, pow_mul, sq_sqrt hM]
  rw [massGap_identity hn hxi]
  unfold massBound
  rw [mul_add]
  congr 1
  simp only [div_pow, mul_pow, hm24, hs24]
  field_simp
  <;> ring

#print axioms agentLayerAllowance_formula
#print axioms energyAllowance_formula
#print axioms massGap_identity
#print axioms massBound_formula
end BstLean.Part222
