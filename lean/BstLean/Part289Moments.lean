import BstLean.Part289Floor

/-! The Part 08 moment data do not depend on the program floor. -/
namespace BstLean.Part289
open Real MeasureTheory BstLean.Part169

structure BiasMoments {α : Type*} [MeasurableSpace α] (μ : Measure α) (K : Set α)
    (n : ℕ) (fb ft wb wt V : α → ℝ) (aw af Hf Cv : ℝ) : Prop where
  mfb : Measurable fb
  mft : Measurable ft
  mwb : Measurable wb
  mwt : Measurable wt
  mV : Measurable V
  haw : 0 < aw
  haf : 0 < af
  hHf : 0 < Hf
  hCv : 0 < Cv
  iW2 : IntegrableOn (fun a => ((n : ℝ) * (wb a - wt a)) ^ 2) K μ
  iW6 : IntegrableOn (fun a => ((n : ℝ) * (wb a - wt a)) ^ 6) K μ
  iW8 : IntegrableOn (fun a => ((n : ℝ) * (wb a - wt a)) ^ 8) K μ
  iF2 : IntegrableOn (fun a => ((n : ℝ) * (fb a - ft a)) ^ 2) K μ
  iF4 : IntegrableOn (fun a => ((n : ℝ) * (fb a - ft a)) ^ 4) K μ
  iF8 : IntegrableOn (fun a => ((n : ℝ) * (fb a - ft a)) ^ 8) K μ
  if4 : IntegrableOn (fun a => fb a ^ 4) K μ
  if24 : IntegrableOn (fun a => fb a ^ 24) K μ
  ifF2 : IntegrableOn (fun a => fb a ^ 2 * ((n : ℝ) * (fb a - ft a)) ^ 2) K μ
  ifF6 : IntegrableOn (fun a => fb a ^ 6 * ((n : ℝ) * (fb a - ft a)) ^ 6) K μ
  iV : IntegrableOn (fun a => ((n : ℝ) * V a) ^ 2) K μ
  hW8 : ∫ a in K, ((n : ℝ) * (wb a - wt a)) ^ 8 ∂μ ≤ aw ^ 8
  hF8 : ∫ a in K, ((n : ℝ) * (fb a - ft a)) ^ 8 ∂μ ≤ af ^ 8
  hf4 : ∫ a in K, fb a ^ 4 ∂μ ≤ Hf ^ 4
  hf24 : ∫ a in K, fb a ^ 24 ∂μ ≤ Hf ^ 24
  hV : ∫ a in K, ((n : ℝ) * V a) ^ 2 ∂μ ≤ Cv ^ 2

theorem scale_L2_floor {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {K : Set α} (hK : MeasurableSet K) (hK1 : μ.real K ≤ 1) {n : ℕ} (hn : 0 < n)
    {s₀ γ d aw af Hf Cv : ℝ} (hs₀ : 0 < s₀) (hγ : 0 < γ) (hd : s₀ ≤ d)
    {fb ft wb wt V : α → ℝ} (M : BiasMoments μ K n fb ft wb wt V aw af Hf Cv)
    (hSbd : ∀ a ∈ K, γ * d ≤ γ * (wb a - fb a ^ 2 - V a)) :
    IntegrableOn (fun a => ((n : ℝ) * (γ * max s₀ (wt a - ft a ^ 2) /
      (γ * (wb a - fb a ^ 2 - V a)) - 1)) ^ 2) K μ ∧
    ∫ a in K, ((n : ℝ) * (γ * max s₀ (wt a - ft a ^ 2) /
      (γ * (wb a - fb a ^ 2 - V a)) - 1)) ^ 2 ∂μ ≤
      ((aw + 2 * Hf * af + af ^ 2 / n + Cv) / d) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd0 : 0 < d := hs₀.trans_le hd
  have haw := M.haw
  have haf := M.haf
  have hHf := M.hHf
  have hCv := M.hCv
  let x1 : α → ℝ := fun a => |(n : ℝ) * (wb a - wt a)| / d
  let x2 : α → ℝ := fun a => 2 * |fb a| * |(n : ℝ) * (fb a - ft a)| / d
  let x3 : α → ℝ := fun a => ((n : ℝ) * (fb a - ft a)) ^ 2 / n / d
  let x4 : α → ℝ := fun a => |(n : ℝ) * V a| / d
  have m1 : Measurable x1 := ((M.mwb.sub M.mwt).const_mul _).abs.div_const _
  have m2 : Measurable x2 :=
    ((M.mfb.abs.const_mul 2).mul ((M.mfb.sub M.mft).const_mul _).abs).div_const _
  have m3 : Measurable x3 := ((((M.mfb.sub M.mft).const_mul _).pow_const 2).div_const _).div_const _
  have m4 : Measurable x4 := (M.mV.const_mul _).abs.div_const _
  have e1 : ∀ a, x1 a ^ 2 = ((n : ℝ) * (wb a - wt a)) ^ 2 / d ^ 2 := by
    intro a; simp only [x1, div_pow, sq_abs]
  have e2 : ∀ a, x2 a ^ 2 = 4 / d ^ 2 * (fb a ^ 2 * ((n : ℝ) * (fb a - ft a)) ^ 2) := by
    intro a; simp only [x2, div_pow, mul_pow, sq_abs]; ring
  have e3 : ∀ a, x3 a ^ 2 = ((n : ℝ) * (fb a - ft a)) ^ 4 / (n ^ 2 * d ^ 2) := by
    intro a; simp only [x3]; field_simp
  have e4 : ∀ a, x4 a ^ 2 = ((n : ℝ) * V a) ^ 2 / d ^ 2 := by
    intro a; simp only [x4, div_pow, sq_abs]
  have b1 : ∫ a in K, x1 a ^ 2 ∂μ ≤ (aw / d) ^ 2 := by
    simp only [e1]; rw [integral_div, div_pow]
    exact div_le_div_of_nonneg_right
      (sq_int_le_of_pow8 μ hK1 M.haw M.iW2 M.iW8 M.hW8) (by positivity)
  have b2 : ∫ a in K, x2 a ^ 2 ∂μ ≤ (2 * Hf * af / d) ^ 2 := by
    have hh := int_sq_mul_le M.if4 M.iF4 M.ifF2 M.hHf M.haf M.hf4
      (pow4_int_le_of_pow8 μ hK1 M.haf M.iF4 M.iF8 M.hF8)
    simp only [e2]; rw [integral_const_mul]
    calc _ ≤ 4 / d ^ 2 * (Hf ^ 2 * af ^ 2) :=
          mul_le_mul_of_nonneg_left hh (by positivity)
      _ = _ := by field_simp; ring
  have b3 : ∫ a in K, x3 a ^ 2 ∂μ ≤ (af ^ 2 / n / d) ^ 2 := by
    simp only [e3]; rw [integral_div]
    calc _ ≤ af ^ 4 / (n ^ 2 * d ^ 2) := div_le_div_of_nonneg_right
          (pow4_int_le_of_pow8 μ hK1 M.haf M.iF4 M.iF8 M.hF8) (by positivity)
      _ = _ := by field_simp
  have b4 : ∫ a in K, x4 a ^ 2 ∂μ ≤ (Cv / d) ^ 2 := by
    simp only [e4]; rw [integral_div, div_pow]
    exact div_le_div_of_nonneg_right M.hV (by positivity)
  have j1 : IntegrableOn (fun a => x1 a ^ 2) K μ := by
    simp only [e1]; exact M.iW2.div_const _
  have j2 : IntegrableOn (fun a => x2 a ^ 2) K μ := by
    simp only [e2]; exact M.ifF2.const_mul _
  have j3 : IntegrableOn (fun a => x3 a ^ 2) K μ := by
    simp only [e3]; exact M.iF4.div_const _
  have j4 : IntegrableOn (fun a => x4 a ^ 2) K μ := by
    simp only [e4]; exact M.iV.div_const _
  obtain ⟨k12, s12⟩ := int_sq_add m1.aestronglyMeasurable m2.aestronglyMeasurable j1 j2
    (by positivity) (by positivity) b1 b2
  obtain ⟨k123, s123⟩ := int_sq_add (m1.add m2).aestronglyMeasurable m3.aestronglyMeasurable
    k12 j3 (by positivity) (by positivity) s12 b3
  obtain ⟨k1234, s1234⟩ := int_sq_add ((m1.add m2).add m3).aestronglyMeasurable
    m4.aestronglyMeasurable k123 j4 (by positivity) (by positivity) s123 b4
  have hpt : ∀ a ∈ K, ((n : ℝ) * (γ * max s₀ (wt a - ft a ^ 2) /
      (γ * (wb a - fb a ^ 2 - V a)) - 1)) ^ 2 ≤ (x1 a + x2 a + x3 a + x4 a) ^ 2 := by
    intro a ha
    have hs := scale_pt_floor (wt := wt a) (ft := ft a) hs₀ hγ hd (hSbd a ha)
    have hle : |(n : ℝ) * (γ * max s₀ (wt a - ft a ^ 2) /
        (γ * (wb a - fb a ^ 2 - V a)) - 1)| ≤ x1 a + x2 a + x3 a + x4 a := by
      rw [abs_mul, abs_of_pos hnR]
      refine (mul_le_mul_of_nonneg_left hs hnR.le).trans (le_of_eq ?_)
      simp only [x1, x2, x3, x4, abs_mul, abs_of_pos hnR]
      field_simp
    calc _ = |(n : ℝ) * (γ * max s₀ (wt a - ft a ^ 2) /
          (γ * (wb a - fb a ^ 2 - V a)) - 1)| ^ 2 := (sq_abs _).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hle 2
  have mS : Measurable (fun a => ((n : ℝ) * (γ * max s₀ (wt a - ft a ^ 2) /
      (γ * (wb a - fb a ^ 2 - V a)) - 1)) ^ 2) :=
    (((((measurable_const.max (M.mwt.sub (M.mft.pow_const 2))).const_mul γ).div
      (((M.mwb.sub (M.mfb.pow_const 2)).sub M.mV).const_mul γ)).sub_const 1).const_mul _).pow_const 2
  have iS : IntegrableOn (fun a => ((n : ℝ) * (γ * max s₀ (wt a - ft a ^ 2) /
      (γ * (wb a - fb a ^ 2 - V a)) - 1)) ^ 2) K μ := by
    refine Integrable.mono' k1234 mS.aestronglyMeasurable ((ae_restrict_iff' hK).mpr
      (Filter.Eventually.of_forall fun a ha => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hpt a ha
  refine ⟨iS, (setIntegral_mono_on iS k1234 hK hpt).trans (s1234.trans (le_of_eq ?_))⟩
  field_simp

end BstLean.Part289

/-- info: 'BstLean.Part289.scale_L2_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.scale_L2_floor
