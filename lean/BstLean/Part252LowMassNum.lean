import BstLean.Part252MomentNum

/-! A rational sufficient condition for the remaining low-residual-mass bound. -/
namespace BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part188
open BstLean.Part195 BstLean.Part222

theorem rotation_sixteen_sharp : rotationConstant 16 ≤ 5448 / 1000 := by
  apply rotation_rational_bound <;> norm_num [Finset.prod_range_succ]

theorem energy_allowance_sharp_row : energyAllowance 12225 ≤ (2101 / 100 : ℝ) / 12225 := by
  have hs : √(2 / (mA 12225 : ℝ)) ≤ (1414214 / 10 ^ 6 : ℝ) / 12225 :=
    sqrt_le_iff.mpr (by norm_num [mA])
  have ha : agentLayerAllowance 12225 ≤ (5448 / 1000 : ℝ) * (1414214 / 10 ^ 6) / 12225 +
      5 / (2 * 12225 ^ 2) := by
    unfold agentLayerAllowance layerAllowance
    have hh := mul_le_mul rotation_sixteen_sharp hs (sqrt_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 5448 / 1000)
    norm_num [mA] at *
    linarith
  have ha0 : 0 ≤ agentLayerAllowance 12225 := layerAllowance_nonneg _
  have hr : (20000 : ℝ) ^ ((32 : ℝ)⁻¹) ≤ 13628 / 10000 := by
    apply le_of_pow_le_pow_left₀ (by norm_num : (32 : ℕ) ≠ 0)
      (by norm_num : (0 : ℝ) ≤ 13628 / 10000)
    have hh := rpow_inv_natCast_pow (by norm_num : (0 : ℝ) ≤ 20000)
      (by norm_num : (32 : ℕ) ≠ 0)
    norm_num only [Nat.cast_ofNat] at hh
    simp only [one_div] at hh
    rw [hh]
    norm_num
  have hr0 : 0 ≤ (20000 : ℝ) ^ ((32 : ℝ)⁻¹) := by positivity
  have he : energyWeightAllowance 12225 ≤
      2 * ((5448 / 1000 : ℝ) * (1414214 / 10 ^ 6) / 12225 + 5 / (2 * 12225 ^ 2)) +
      ((5448 / 1000 : ℝ) * (1414214 / 10 ^ 6) / 12225 + 5 / (2 * 12225 ^ 2)) ^ 2 := by
    unfold energyWeightAllowance
    nlinarith [pow_le_pow_left₀ ha0 ha 2]
  unfold energyAllowance
  calc
    _ ≤ (13628 / 10000 : ℝ) *
        (2 * ((5448 / 1000 : ℝ) * (1414214 / 10 ^ 6) / 12225 + 5 / (2 * 12225 ^ 2)) +
        ((5448 / 1000 : ℝ) * (1414214 / 10 ^ 6) / 12225 + 5 / (2 * 12225 ^ 2)) ^ 2) :=
      mul_le_mul hr he (energyWeightAllowance_nonneg _) (by norm_num)
    _ ≤ _ := by norm_num

theorem low_mass_gap :
    (3797 / 100000 : ℝ) ≤ √((1 - 42 / 10000) ^ 2 - mixtureFloor) -
      (√(706 / 1000) + √((4 / 100 : ℝ) / 12225)) := by
  have h1 : (880019 / 10 ^ 6 : ℝ) ≤ √((1 - 42 / 10000) ^ 2 - mixtureFloor) :=
    le_sqrt_of_sq_le (by norm_num [mixtureFloor])
  have h2 : √(706 / 1000 : ℝ) ≤ 840239 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  have h3 : √((4 / 100 : ℝ) / 12225) ≤ 181 / 10 ^ 5 := sqrt_le_iff.mpr (by norm_num)
  linarith

theorem low_mass_price_row :
    massBound 12225 (85 / 1000) ((2101 / 100) / 12225) (4 / 100) (706 / 1000)
      (42 / 10000) mixtureFloor ≤ 12225 * lowMassBudget := by
  have hg := low_mass_gap
  have hg0 : 0 < √((1 - 42 / 10000) ^ 2 - mixtureFloor) -
      (√(706 / 1000) + √((4 / 100 : ℝ) / 12225)) := by linarith
  have hr := rotation_twelve
  have hr0 := rotationConstant_nonneg 12
  unfold massBound
  simp only [Nat.cast_ofNat]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 12225)
  calc
    _ ≤ (((2101 / 100 : ℝ) / 12225) / (42 / 10000)) ^ 32 +
        ((48 / 10 : ℝ) ^ 24 * ((85 / 1000) / 12225) ^ 12) /
          (3797 / 100000) ^ 24 := by
      have hd := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3797 / 100000) hg 24
      have hn := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ hr0 hr 24)
        (by positivity : (0 : ℝ) ≤ ((85 / 1000) / 12225) ^ 12)
      exact add_le_add_right (div_le_div₀ (by positivity) hn (by positivity) hd)
        ((((2101 / 100 : ℝ) / 12225) / (42 / 10000)) ^ 32)
    _ ≤ lowMassBudget := by norm_num [lowMassBudget]

/-- Energy is supplied on the paid event. Direction, parallel centre and centre energy remain. -/
theorem low_mass_of_three_bounds {c : Ret 12225}
    (hw : WINDOW (paperDesignP 12225) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hb : ∀ j, 0 ≤ (paperDesignP 12225).bA c.1 c.2.1.1 j)
    (hdir : DirectionMoment (paperDesignP 12225) c (85 / 1000))
    (hpar : ParallelCentre (paperDesignP 12225) c (4 / 100))
    (henergy : centreEnergy (paperDesignP 12225) c ≤ 706 / 1000) :
    ∫ a, (BstLean.Part29.stdGauss (Fin (12225 - 1))).real
      {v | BstLean.Part162.sgA (paperDesignP 12225) c a v <
        √(2 / (12225 : ℝ) * mixtureFloor)} ∂muI 12225 ≤ lowMassBudget := by
  have hE := energyMoment_on_event (by norm_num) (paperDesignP 12225) c
    (hc.1.1.1.1 hw.2.1)
  have hE' : EnergyMoment (paperDesignP 12225) c ((2101 / 100) / 12225) :=
    ⟨by norm_num, hE.2.1, hE.2.2.trans
      (pow_le_pow_left₀ hE.1 energy_allowance_sharp_row 32)⟩
  exact low_mass_of_interfaces hw he hb ⟨hdir, hE', hpar⟩ henergy
    (by norm_num : (0 : ℝ) < 42 / 10000) (by norm_num)
    (by norm_num [mixtureFloor]) (by linarith [low_mass_gap]) low_mass_price_row

end BstLean.Part252
