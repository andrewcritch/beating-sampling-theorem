import BstLean.Part209Kernel

/-! The sharp square-root modulus of the kernel derivative on nonnegative overlaps. -/
namespace BstLean.Part209
open Real Set
open BstLean.Part130

lemma sin_lower_quarter {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ π / 4) :
    2 * sqrt 2 / π * z ≤ sin z := by
  have hc0 : 0 ≤ 4 * z / π := by positivity
  have hc1 : 4 * z / π ≤ 1 := (div_le_one pi_pos).mpr (by linarith)
  have h := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Icc (0 : ℝ) π by exact ⟨le_rfl, pi_pos.le⟩)
    (show π / 4 ∈ Icc (0 : ℝ) π by constructor <;> linarith [pi_pos])
    (sub_nonneg.mpr hc1) hc0 (by ring : (1 - 4 * z / π) + 4 * z / π = 1)
  simp only [smul_eq_mul, sin_zero, mul_zero, zero_add] at h
  have he : 4 * z / π * (π / 4) = z := by field_simp
  rw [he, sin_pi_div_four] at h
  convert h using 1 <;> ring

lemma arccos_sub_nonneg_le {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hy : y ≤ 1) :
    arccos x - arccos y ≤ π / 2 * sqrt (y - x) := by
  let a := arccos x
  let b := arccos y
  let δ := (a - b) / 2
  let σ := (a + b) / 2
  have hb0 : 0 ≤ b := arccos_nonneg y
  have hab : b ≤ a := arccos_le_arccos hxy
  have ha1 : a ≤ π / 2 := by
    have h := arccos_le_arccos hx
    simpa only [arccos_zero] using h
  have hxcos : cos a = x := cos_arccos (by linarith) (hxy.trans hy)
  have hycos : cos b = y := cos_arccos (by linarith) hy
  have hd0 : 0 ≤ δ := by dsimp [δ]; linarith
  have hd1 : δ ≤ π / 4 := by dsimp [δ]; linarith
  have hds : sin δ ≤ sin σ := by
    apply sin_le_sin_of_le_of_le_pi_div_two
    · linarith [pi_pos]
    · dsimp [σ]; linarith
    · dsimp [δ, σ]; linarith
  have hs := sin_lower_quarter hd0 hd1
  have hs0 : 0 ≤ 2 * sqrt 2 / π * δ := by positivity
  have he : y - x = 2 * sin σ * sin δ := by
    have h := cos_sub_cos b a
    have h₁ : (b + a) / 2 = σ := by dsimp [σ]; ring
    have h₂ : (b - a) / 2 = -δ := by dsimp [δ]; ring
    rw [h₁, h₂, sin_neg, hxcos, hycos] at h
    linarith
  have hsq := pow_le_pow_left₀ hs0 hs 2
  have hmul := mul_le_mul_of_nonneg_right hds (hs0.trans hs)
  have hs2 : sqrt (2 : ℝ) ^ 2 = 2 := sq_sqrt (by norm_num)
  have hsq' : (2 * sqrt 2 / π * δ) ^ 2 = 8 * δ ^ 2 / π ^ 2 := by
    rw [mul_pow, div_pow, mul_pow, hs2]
    ring
  rw [hsq'] at hsq
  have hδ : (4 / π * δ) ^ 2 ≤ y - x := by
    have hq : (4 / π * δ) ^ 2 = 2 * (8 * δ ^ 2 / π ^ 2) := by ring
    rw [hq, he]
    nlinarith
  have hroot := Real.le_sqrt_of_sq_le hδ
  have hfin := mul_le_mul_of_nonneg_left hroot (show 0 ≤ π / 2 by positivity)
  have he' : π / 2 * (4 / π * δ) = a - b := by dsimp [δ]; field_simp; ring
  rw [he'] at hfin
  exact hfin

/-- The constant is one half on `[0,1]`, including both endpoints. -/
theorem kernelSlope_holder {x y : ℝ} (hx : x ∈ Icc (0 : ℝ) 1)
    (hy : y ∈ Icc (0 : ℝ) 1) :
    |kernelSlope x - kernelSlope y| ≤ (1 / 2 : ℝ) * sqrt |x - y| := by
  suffices h : ∀ x y : ℝ, 0 ≤ x → x ≤ y → y ≤ 1 →
      |kernelSlope x - kernelSlope y| ≤ (1 / 2 : ℝ) * sqrt |x - y| by
    rcases le_total x y with hxy | hyx
    · exact h x y hx.1 hxy hy.2
    · simpa only [abs_sub_comm] using h y x hy.1 hyx hx.2
  intro x y hx hxy hy
  have ha := arccos_le_arccos hxy
  have h := div_le_div_of_nonneg_right (arccos_sub_nonneg_le hx hxy hy) pi_pos.le
  have he : kernelSlope x - kernelSlope y = -(arccos x - arccos y) / π := by
    unfold kernelSlope
    ring
  rw [he, abs_div, abs_neg, abs_of_nonneg (sub_nonneg.mpr ha), abs_of_pos pi_pos,
    abs_of_nonpos (sub_nonpos.mpr hxy), neg_sub]
  convert h using 1 <;> field_simp <;> ring

end BstLean.Part209
