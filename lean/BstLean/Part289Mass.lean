import BstLean.Part289Moments

namespace BstLean.Part289
open Real MeasureTheory BstLean.Part169

/-- The same exceptional-mass price for any positive admissible program floor. -/
theorem scale_mass_floor {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {K : Set α} (hK : MeasurableSet K) (hK1 : μ.real K ≤ 1) {n : ℕ} (hn : 0 < n)
    {s₀ γ d ε vmax aw af Hf Cv : ℝ} (hs₀ : 0 < s₀) (hγ : 0 < γ) (hd : s₀ ≤ d)
    {fb ft wb wt V : α → ℝ} (M : BiasMoments μ K n fb ft wb wt V aw af Hf Cv)
    (hT : 0 < ε - vmax / d)
    (hSbd : ∀ a ∈ K, γ * d ≤ γ * (wb a - fb a ^ 2 - V a))
    (hVm : ∀ a ∈ K, |V a| ≤ vmax) :
    μ.real (K ∩ {a | ε < |γ * max s₀ (wt a - ft a ^ 2) /
      (γ * (wb a - fb a ^ 2 - V a)) - 1|}) ≤
      ((aw + 2 * Hf * af) / (99 / 100 * d * n * (ε - vmax / d))) ^ 6 +
        (af ^ 2 / (1 / 100 * d * n ^ 2 * (ε - vmax / d))) ^ 4 := by
  set T := ε - vmax / d with hTd
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hd0 : 0 < d := hs₀.trans_le hd
  let x : α → ℝ := fun a => |(n : ℝ) * (wb a - wt a)|
  let y : α → ℝ := fun a => 2 * |fb a| * |(n : ℝ) * (fb a - ft a)|
  let P1 : α → ℝ := fun a => (x a + y a) / (n * d)
  let P2 : α → ℝ := fun a => ((n : ℝ) * (fb a - ft a)) ^ 2 / (n ^ 2 * d)
  have mx : Measurable x := ((M.mwb.sub M.mwt).const_mul _).abs
  have my : Measurable y := (M.mfb.abs.const_mul 2).mul ((M.mfb.sub M.mft).const_mul _).abs
  have mP1 : Measurable P1 := (mx.add my).div_const _
  have mP2 : Measurable P2 := (((M.mfb.sub M.mft).const_mul _).pow_const 2).div_const _
  have hx0 : ∀ a, 0 ≤ x a := fun a => abs_nonneg _
  have hy0 : ∀ a, 0 ≤ y a := fun a => by dsimp [y]; positivity
  have hsub : K ∩ {a | ε < |γ * max s₀ (wt a - ft a ^ 2) /
        (γ * (wb a - fb a ^ 2 - V a)) - 1|} ⊆
      (K ∩ {a | (99 / 100 * T) ^ 6 ≤ P1 a ^ 6}) ∪
        (K ∩ {a | (1 / 100 * T) ^ 4 ≤ P2 a ^ 4}) := by
    rintro a ⟨ha, hε⟩
    simp only [Set.mem_ofPred_eq] at hε
    have hs := scale_pt_floor (wt := wt a) (ft := ft a) hs₀ hγ hd (hSbd a ha)
    have e : (|wb a - wt a| + 2 * |fb a| * |fb a - ft a| + (fb a - ft a) ^ 2 + |V a|) / d =
        P1 a + P2 a + |V a| / d := by
      simp only [P1, P2, x, y, abs_mul, abs_of_pos hnR]; field_simp
    rw [e] at hs
    have hV := div_le_div_of_nonneg_right (hVm a ha) hd0.le
    have hTP : T < P1 a + P2 a := by rw [hTd]; linarith
    by_cases h1 : 99 / 100 * T ≤ P1 a
    · left; exact ⟨ha, pow_le_pow_left₀ (by positivity) h1 6⟩
    · right
      refine ⟨ha, pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 / 100 * T) ?_ 4⟩
      push Not at h1; linarith
  have ex : ∀ a, x a ^ 6 = ((n : ℝ) * (wb a - wt a)) ^ 6 := by
    intro a; exact Even.pow_abs (by decide) _
  have ey : ∀ a, y a ^ 6 = 64 * (fb a ^ 6 * ((n : ℝ) * (fb a - ft a)) ^ 6) := by
    intro a; dsimp [y]
    rw [mul_pow, mul_pow, Even.pow_abs (by decide), Even.pow_abs (by decide)]; ring
  have i6x : IntegrableOn (fun a => x a ^ 6) K μ := by simp only [ex]; exact M.iW6
  have i6y : IntegrableOn (fun a => y a ^ 6) K μ := by simp only [ey]; exact M.ifF6.const_mul _
  have b6x : ∫ a in K, x a ^ 6 ∂μ ≤ aw ^ 6 := by
    simp only [ex]; exact int_pow6_of_pow8 hK1 M.haw M.iW6 M.iW8 M.hW8
  have b6y : ∫ a in K, y a ^ 6 ∂μ ≤ (2 * Hf * af) ^ 6 := by
    simp only [ey]; rw [integral_const_mul]
    have hh := int_pow6_mul_le M.if24 M.iF8 M.ifF6 M.hHf M.haf M.hf24 M.hF8
    calc _ ≤ 64 * (Hf ^ 6 * af ^ 6) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ = _ := by ring
  obtain ⟨ixy, bxy⟩ := int_pow6_add mx.aestronglyMeasurable my.aestronglyMeasurable hx0 hy0
    i6x i6y M.haw (by have := M.hHf; have := M.haf; positivity) b6x b6y
  have eP1 : ∀ a, P1 a ^ 6 = (x a + y a) ^ 6 / (n * d) ^ 6 := by
    intro a; dsimp [P1]; rw [div_pow]
  have eP2 : ∀ a, P2 a ^ 4 = ((n : ℝ) * (fb a - ft a)) ^ 8 / (n ^ 2 * d) ^ 4 := by
    intro a; dsimp [P2]; rw [div_pow]; ring
  have iP1 : IntegrableOn (fun a => P1 a ^ 6) K μ := by
    simp only [eP1]; exact ixy.div_const _
  have bP1 : ∫ a in K, P1 a ^ 6 ∂μ ≤ (aw + 2 * Hf * af) ^ 6 / (n * d) ^ 6 := by
    simp only [eP1]; rw [integral_div]
    exact div_le_div_of_nonneg_right bxy (by positivity)
  have iP2 : IntegrableOn (fun a => P2 a ^ 4) K μ := by
    simp only [eP2]; exact M.iF8.div_const _
  have bP2 : ∫ a in K, P2 a ^ 4 ∂μ ≤ af ^ 8 / (n ^ 2 * d) ^ 4 := by
    simp only [eP2]; rw [integral_div]
    exact div_le_div_of_nonneg_right M.hF8 (by positivity)
  have k1 := markov_on hK (mP1.pow_const 6) (fun a _ => by
    dsimp [P1]; have := hx0 a; have := hy0 a; positivity) iP1
    (by positivity : (0 : ℝ) < (99 / 100 * T) ^ 6)
  have k2 := markov_on hK (mP2.pow_const 4) (fun a _ => by dsimp [P2]; positivity) iP2
    (by positivity : (0 : ℝ) < (1 / 100 * T) ^ 4)
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (add_le_add ?_ ?_))
  · refine k1.trans ?_
    calc _ ≤ (aw + 2 * Hf * af) ^ 6 / (n * d) ^ 6 / (99 / 100 * T) ^ 6 :=
          div_le_div_of_nonneg_right bP1 (by positivity)
      _ = _ := by field_simp
  · refine k2.trans ?_
    calc _ ≤ af ^ 8 / (n ^ 2 * d) ^ 4 / (1 / 100 * T) ^ 4 :=
          div_le_div_of_nonneg_right bP2 (by positivity)
      _ = _ := by field_simp

end BstLean.Part289

/-- info: 'BstLean.Part289.scale_mass_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.scale_mass_floor
