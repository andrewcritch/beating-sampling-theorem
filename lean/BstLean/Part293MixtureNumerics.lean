import BstLean.Part293BiasNumerics
import BstLean.Part242MixturePass

/-! Uniform rounded prices for the improved HQ mixture bound. -/
namespace BstLean.Part293
open Real BstLean.Part242

structure MixtureNumerics (n : ℕ) (ε A D C B Dd : ℝ) : Prop where
  epsilon : 0 ≤ ε ∧ ε ≤ 0.035
  energy : 0 ≤ A ∧ A ≤ 0.000000725
  scaled_energy : 0 ≤ (n : ℝ) * A ∧ (n : ℝ) * A ≤ 0.0058
  displacement : 0 ≤ D ∧ D ≤ 0.00154
  chi_price : C ≤ 0.0000146
  removed_mass : B ≤ 1.87 / 10 ^ 12
  displaced_price : Dd ≤ 1.295 / 10 ^ 7

theorem mixture_L3_le {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882)
    {ε A D C B Dd : ℝ} (S : MixtureNumerics n ε A D C B Dd) :
    mixL3 n ε A D ≤ 0.0025 := by
  have hl : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hu : (n : ℝ) ≤ 11882 := by exact_mod_cast hn'
  rcases S with ⟨he, ha, hna, hd, hc, hb, hdd⟩
  have hs : 0 ≤ √(A * D) ∧ √(A * D) ≤ 0.000034 :=
    ⟨sqrt_nonneg _, sqrt_le_iff.mpr ⟨by norm_num, by interval_num⟩⟩
  have hs' : 0 ≤ √((n : ℝ) / 2) ∧ √((n : ℝ) / 2) ≤ 78 :=
    ⟨sqrt_nonneg _, sqrt_le_iff.mpr ⟨by norm_num, by interval_num⟩⟩
  unfold mixL3
  generalize (n : ℝ) * A = NA at *
  generalize √(A * D) = sAD at *
  generalize √((n : ℝ) / 2) = sn at *
  interval_num

theorem fluctuation_price_le {n : ℕ} (hn : 8000 ≤ n) (hn' : n ≤ 11882)
    {ε A D C B Dd : ℝ} (S : MixtureNumerics n ε A D C B Dd) :
    √(2 * (1 + (0.0045 : ℝ)⁻¹) * B) + √(C / 4 + 6 * mixL3 n ε A D ^ 3) +
      √Dd ≤ 0.002329 := by
  have hL := mixture_L3_le hn hn' S
  have hL0 : 0 ≤ mixL3 n ε A D := by
    have he := S.epsilon
    have ha := S.energy
    have hd := S.displacement
    have he1 : 0 < 1 - ε := by linarith [he.2]
    have ha0 := ha.1
    have hd0 := hd.1
    unfold mixL3
    positivity
  have hr : √(2 * (1 + (0.0045 : ℝ)⁻¹) * B) ≤ 0.000029 := by
    apply sqrt_le_iff.mpr
    have hb := S.removed_mass
    constructor <;> norm_num at * <;> linarith
  have hm : √(C / 4 + 6 * mixL3 n ε A D ^ 3) ≤ 0.00194 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    have hc := S.chi_price
    have hp := pow_le_pow_left₀ hL0 hL 3
    norm_num at hp
    linarith
  have hd : √Dd ≤ 0.00036 := by
    apply sqrt_le_iff.mpr
    have hdd := S.displaced_price
    constructor <;> norm_num at * <;> linarith
  linarith

end BstLean.Part293

/-- info: 'BstLean.Part293.fluctuation_price_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms BstLean.Part293.fluctuation_price_le
