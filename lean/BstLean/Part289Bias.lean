import BstLean.Part289Mass
import BstLean.Part241Integral

/-! The Part 08 bias price and root for an arbitrary positive residual floor. -/
namespace BstLean.Part289
open Real MeasureTheory BstLean.Part169 BstLean.Part241
open BstLean.Part161 (hellG2)

theorem free_epsilon_price_floor {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {K : Set α} (hK : MeasurableSet K) (hK1 : μ.real K ≤ 1)
    {n : ℕ} (hn : 0 < n) {s₀ γ e χ d ε vmax aw af Hf Cv cA2 : ℝ}
    (hs₀ : 0 < s₀) (hγ : 0 < γ) (he : 0 < e) (hd : s₀ ≤ d)
    (hc0 : 0 ≤ cA2) (hc : cA2 ≤ γ * e * n * χ) (hε1 : ε < 1) (hT : 0 < ε - vmax / d)
    {fb ft wb wt V : α → ℝ} (M : BiasMoments μ K n fb ft wb wt V aw af Hf Cv)
    (hSbd : ∀ a ∈ K, γ * d ≤ γ * (wb a - fb a ^ 2 - V a))
    (hVm : ∀ a ∈ K, |V a| ≤ vmax) :
    ∫ a in K, hellG2 n ((fb a / √e - ft a / √e) ^ 2 * cA2)
      (γ * (wb a - fb a ^ 2 - V a)) (γ * max s₀ (wt a - ft a ^ 2)) ∂μ ≤
        squaredPrice n χ d ε vmax aw af Hf Cv := by
  rw [squaredPrice_eq_PB]
  have hse : 0 < √e := Real.sqrt_pos.mpr he
  have hsq : ∀ a, √e * (fb a / √e - ft a / √e) = fb a - ft a := by
    intro a; field_simp
  have eF2 : (fun a => ((n : ℝ) * (√e * (fb a / √e - ft a / √e))) ^ 2) =
      fun a => ((n : ℝ) * (fb a - ft a)) ^ 2 := by funext a; rw [hsq]
  have eF8 : (fun a => ((n : ℝ) * (√e * (fb a / √e - ft a / √e))) ^ 8) =
      fun a => ((n : ℝ) * (fb a - ft a)) ^ 8 := by funext a; rw [hsq]
  obtain ⟨iS, hS⟩ := scale_L2_floor hK hK1 hn hs₀ hγ hd M hSbd
  have hm := scale_mass_floor hK hK1 hn hs₀ hγ hd M hT hSbd hVm
  have mSb : Measurable (fun a => γ * (wb a - fb a ^ 2 - V a)) :=
    ((M.mwb.sub (M.mfb.pow_const 2)).sub M.mV).const_mul γ
  have mSt : Measurable (fun a => γ * max s₀ (wt a - ft a ^ 2)) :=
    (measurable_const.max (M.mwt.sub (M.mft.pow_const 2))).const_mul γ
  have hSt : ∀ a ∈ K, 0 < γ * max s₀ (wt a - ft a ^ 2) :=
    fun a _ => mul_pos hγ (hs₀.trans_le (le_max_left _ _))
  exact bias_price_L8 μ hK hK1 n hn (lb := fun a => fb a / √e) (lt := fun a => ft a / √e)
    mSb mSt hγ he (hs₀.trans_le hd) hc0 hc hε1 M.haf hSbd hSt
    (eF2 ▸ M.iF2) (eF8 ▸ M.iF8) iS (by rw [eF8]; exact M.hF8) hS hm

theorem free_epsilon_root_floor {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsFiniteMeasure μ] {K : Set α} (hK : MeasurableSet K) (hK1 : μ.real K ≤ 1)
    {n : ℕ} (hn : 0 < n) {s₀ γ e χ d ε vmax aw af Hf Cv cA2 : ℝ}
    (hs₀ : 0 < s₀) (hγ : 0 < γ) (he : 0 < e) (hd : s₀ ≤ d)
    (hc0 : 0 ≤ cA2) (hc : cA2 ≤ γ * e * n * χ) (hε1 : ε < 1) (hT : 0 < ε - vmax / d)
    {fb ft wb wt V : α → ℝ} (M : BiasMoments μ K n fb ft wb wt V aw af Hf Cv)
    (hSbd : ∀ a ∈ K, γ * d ≤ γ * (wb a - fb a ^ 2 - V a))
    (hVm : ∀ a ∈ K, |V a| ≤ vmax) :
    √(∫ a in K, hellG2 n ((fb a / √e - ft a / √e) ^ 2 * cA2)
      (γ * (wb a - fb a ^ 2 - V a)) (γ * max s₀ (wt a - ft a ^ 2)) ∂μ) ≤
        biasRoot n χ d ε vmax aw af Hf Cv :=
  Real.sqrt_le_sqrt (free_epsilon_price_floor μ hK hK1 hn hs₀ hγ he hd hc0 hc hε1 hT M hSbd hVm)

end BstLean.Part289

/-- info: 'BstLean.Part289.free_epsilon_root_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part289.free_epsilon_root_floor
