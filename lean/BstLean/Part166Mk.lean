import Mathlib

namespace BstLean.Part166

open MeasureTheory ENNReal

/-- Weighted AM-GM (Young) step. -/
lemma young12 {x T : ℝ} (hx : 0 ≤ x) (hT : 0 < T) {p : ℕ} (hp : 12 ≤ p) :
    x ^ 12 ≤ (12 / (p : ℝ) / T ^ (p - 12)) * x ^ p + (1 - 12 / (p : ℝ)) * T ^ 12 := by
  have hpR : (12 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  set w : ℝ := 12 / (p : ℝ) with hw
  have hw0 : 0 ≤ w := by positivity
  have hw1 : 0 ≤ 1 - w := by
    rw [hw, sub_nonneg, div_le_one hp0]; exact hpR
  have key := Real.geom_mean_le_arith_mean2_weighted hw0 hw1 (pow_nonneg hx p)
    (pow_nonneg hT.le p) (by ring)
  have e1 : (x ^ p) ^ w = x ^ 12 := by
    rw [← Real.rpow_natCast x p, ← Real.rpow_mul hx]
    have : (p : ℝ) * w = ((12 : ℕ) : ℝ) := by rw [hw]; field_simp; norm_num
    rw [this, Real.rpow_natCast]
  have e2 : (T ^ p) ^ (1 - w) = T ^ (p - 12) := by
    rw [← Real.rpow_natCast T p, ← Real.rpow_mul hT.le]
    have : (p : ℝ) * (1 - w) = ((p - 12 : ℕ) : ℝ) := by
      rw [hw, Nat.cast_sub hp]; field_simp; push_cast; ring
    rw [this, Real.rpow_natCast]
  rw [e1, e2] at key
  have hTp : T ^ p = T ^ (p - 12) * T ^ 12 := by
    rw [← pow_add, Nat.sub_add_cancel hp]
  have hpos : 0 < T ^ (p - 12) := pow_pos hT _
  rw [hTp] at key
  have : x ^ 12 ≤ (w * x ^ p + (1 - w) * (T ^ (p - 12) * T ^ 12)) / T ^ (p - 12) := by
    rw [le_div_iff₀ hpos]; exact key
  calc x ^ 12 ≤ _ := this
    _ = _ := by field_simp

/-- Markov after a Young step: if the order-`p` moment is at most `T^p` then the order-12
moment is at most `T^12`. -/
theorem markov12 {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) [SFinite μ] (ν₁ : Measure β) [IsProbabilityMeasure ν₁]
    (ν₂ : Measure γ) [IsProbabilityMeasure ν₂]
    (Ψ : α → β → γ → ℝ) (hΨ : Measurable (fun z : α × β × γ => Ψ z.1 z.2.1 z.2.2))
    (h0 : ∀ A b c, 0 ≤ Ψ A b c) {p : ℕ} (hp : 12 ≤ p) {T : ℝ} (hT : 0 < T) :
    μ {A | ENNReal.ofReal (T ^ 12) < ∫⁻ b, ∫⁻ c, ENNReal.ofReal (Ψ A b c ^ 12) ∂ν₂ ∂ν₁} ≤
      (∫⁻ b, ∫⁻ c, ∫⁻ A, ENNReal.ofReal (Ψ A b c ^ p) ∂μ ∂ν₂ ∂ν₁) / ENNReal.ofReal (T ^ p) := by
  set k : ℝ := 12 / (p : ℝ) / T ^ (p - 12) with hk
  set C : ℝ := (1 - 12 / (p : ℝ)) * T ^ 12 with hC
  have hpR : (12 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hk0 : 0 ≤ k := by positivity
  have hC0 : 0 ≤ C := by
    apply mul_nonneg _ (by positivity)
    rw [sub_nonneg, div_le_one hp0]; exact hpR
  -- measurability
  have hm3 : ∀ q : ℕ, Measurable (fun z : (α × β) × γ => ENNReal.ofReal (Ψ z.1.1 z.1.2 z.2 ^ q)) :=
    fun q => ENNReal.measurable_ofReal.comp
      ((hΨ.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))).pow_const q)
  have hm2 : ∀ q : ℕ, Measurable (fun z : α × β => ∫⁻ c, ENNReal.ofReal (Ψ z.1 z.2 c ^ q) ∂ν₂) :=
    fun q => (hm3 q).lintegral_prod_right'
  have hm1 : ∀ q : ℕ, Measurable
      (fun A : α => ∫⁻ b, ∫⁻ c, ENNReal.ofReal (Ψ A b c ^ q) ∂ν₂ ∂ν₁) :=
    fun q => (hm2 q).lintegral_prod_right'
  have hmc : ∀ (q : ℕ) (A : α) (b : β), Measurable (fun c => ENNReal.ofReal (Ψ A b c ^ q)) :=
    fun q A b => ENNReal.measurable_ofReal.comp
      ((hΨ.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).pow_const q)
  -- step 2
  have hsub : {A | ENNReal.ofReal (T ^ 12) < ∫⁻ b, ∫⁻ c, ENNReal.ofReal (Ψ A b c ^ 12) ∂ν₂ ∂ν₁}
      ⊆ {A | ENNReal.ofReal (T ^ p) ≤ ∫⁻ b, ∫⁻ c, ENNReal.ofReal (Ψ A b c ^ p) ∂ν₂ ∂ν₁} := by
    intro A hA
    simp only [Set.mem_ofPred_eq] at hA ⊢
    by_contra hcon
    push Not at hcon
    apply (lt_irrefl _ (hA.trans_le _))
    have hpt : ∀ b c, ENNReal.ofReal (Ψ A b c ^ 12) ≤
        ENNReal.ofReal k * ENNReal.ofReal (Ψ A b c ^ p) + ENNReal.ofReal C := by
      intro b c
      rw [← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_add (mul_nonneg hk0 (pow_nonneg (h0 A b c) _)) hC0]
      exact ENNReal.ofReal_le_ofReal (young12 (h0 A b c) hT hp)
    calc ∫⁻ b, ∫⁻ c, ENNReal.ofReal (Ψ A b c ^ 12) ∂ν₂ ∂ν₁
        ≤ ∫⁻ b, (ENNReal.ofReal k * ∫⁻ c, ENNReal.ofReal (Ψ A b c ^ p) ∂ν₂ + ENNReal.ofReal C) ∂ν₁ := by
          apply lintegral_mono; intro b
          calc _ ≤ ∫⁻ c, (ENNReal.ofReal k * ENNReal.ofReal (Ψ A b c ^ p) + ENNReal.ofReal C) ∂ν₂ :=
                lintegral_mono (hpt b)
            _ = _ := by
                rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ofReal_ne_top]
                simp
      _ = ENNReal.ofReal k * ∫⁻ b, ∫⁻ c, ENNReal.ofReal (Ψ A b c ^ p) ∂ν₂ ∂ν₁ + ENNReal.ofReal C := by
          rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ ofReal_ne_top]
          simp
      _ ≤ ENNReal.ofReal k * ENNReal.ofReal (T ^ p) + ENNReal.ofReal C := by
          gcongr
      _ = ENNReal.ofReal (T ^ 12) := by
          rw [← ENNReal.ofReal_mul hk0, ← ENNReal.ofReal_add (mul_nonneg hk0 (by positivity)) hC0]
          congr 1
          have hTp : T ^ p = T ^ (p - 12) * T ^ 12 := by
            rw [← pow_add, Nat.sub_add_cancel hp]
          have hpos : 0 < T ^ (p - 12) := pow_pos hT _
          rw [hk, hC, hTp]; field_simp; ring
  -- step 3
  have hTp0 : ENNReal.ofReal (T ^ p) ≠ 0 := by
    simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  calc _ ≤ μ {A | ENNReal.ofReal (T ^ p) ≤ ∫⁻ b, ∫⁻ c, ENNReal.ofReal (Ψ A b c ^ p) ∂ν₂ ∂ν₁} :=
        measure_mono hsub
    _ ≤ (∫⁻ A, ∫⁻ b, ∫⁻ c, ENNReal.ofReal (Ψ A b c ^ p) ∂ν₂ ∂ν₁ ∂μ) / ENNReal.ofReal (T ^ p) :=
        meas_ge_le_lintegral_div (hm1 p).aemeasurable hTp0 ofReal_ne_top
    _ = _ := by
        congr 1
        rw [lintegral_lintegral_swap (hm2 p).aemeasurable]
        apply lintegral_congr; intro b
        apply lintegral_lintegral_swap
        apply Measurable.aemeasurable
        exact ENNReal.measurable_ofReal.comp
          ((hΨ.comp (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))).pow_const p)

theorem integral_le_of_lintegral {β γ : Type*} [MeasurableSpace β] [MeasurableSpace γ]
    (ν₁ : Measure β) [IsProbabilityMeasure ν₁] (ν₂ : Measure γ) [IsProbabilityMeasure ν₂]
    (g : β → γ → ℝ) (hg : Measurable (fun z : β × γ => g z.1 z.2)) (h0 : ∀ b c, 0 ≤ g b c)
    {T : ℝ} (hT : 0 ≤ T)
    (h : ∫⁻ b, ∫⁻ c, ENNReal.ofReal (g b c) ∂ν₂ ∂ν₁ ≤ ENNReal.ofReal T) :
    ∫ b, ∫ c, g b c ∂ν₂ ∂ν₁ ≤ T := by
  have hgc : ∀ b, Measurable (fun c => g b c) := fun b =>
    hg.comp (measurable_const.prodMk measurable_id)
  have hin : ∀ b, ∫ c, g b c ∂ν₂ = (∫⁻ c, ENNReal.ofReal (g b c) ∂ν₂).toReal := fun b =>
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (h0 b))
      (hgc b).aestronglyMeasurable
  simp_rw [hin]
  have hFm : Measurable (fun b => ∫⁻ c, ENNReal.ofReal (g b c) ∂ν₂) :=
    (ENNReal.measurable_ofReal.comp hg).lintegral_prod_right'
  rw [integral_toReal hFm.aemeasurable (ae_lt_top hFm (ne_top_of_le_ne_top ofReal_ne_top h))]
  exact ENNReal.toReal_le_of_le_ofReal hT h

end BstLean.Part166

open BstLean.Part166 in
#print axioms markov12
open BstLean.Part166 in
#print axioms integral_le_of_lintegral
