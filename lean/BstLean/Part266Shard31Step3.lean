import BstLean.Part266Shard31Step2


/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13125
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13125 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13125) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13125 : ℝ) * (13125 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13125) /
    ((13125 : ℝ) * (13125 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13125} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13125}
    (hw : WINDOW (paperDesignP 13125) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13125) c a v - lbar (paperDesignP 13125) c a| ^ (2 * q)
      ∂stdGauss (Fin (13125 - 1)) ∂muI 13125 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13125)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13125}
    (hw : WINDOW (paperDesignP 13125) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13125) c a v - gbar (paperDesignP 13125) c a| ^ (2 * q)
      ∂stdGauss (Fin (13125 - 1)) ∂muI 13125 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13125)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13125) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13125}
    (hw : WINDOW (paperDesignP 13125) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13125 - 1))).real
      {v | sgA (paperDesignP 13125) c a v < √(2 / (13125 : ℝ) * mixtureFloor)}
      ∂muI 13125 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13125 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13125 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13125) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13125

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13125
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13125 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13125)
    (p : Ix 13125 × (Fin (13125 - 1) → ℝ)) :
    sgA (paperDesignP 13125) c p.1 p.2 ^ 2 ≤
      (2 / (13125 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13125).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13125) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13125 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13125 : ℝ) * _ ≤ 2 / 13125 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13125)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13125}
    (hw : WINDOW (paperDesignP 13125) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13125) c a v ^ 8
      ∂stdGauss (Fin (13125 - 1)) ∂muI 13125 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13125).prod (stdGauss (Fin (13125 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13125) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13125) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13125 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13125) c p.1 p.2)
      (√(2 / (13125 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13125)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13125 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13125) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13125}
    (hw : WINDOW (paperDesignP 13125) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13125) c a v -
      ∫ w, sA (paperDesignP 13125) c a w ∂stdGauss (Fin (13125 - 1))) ^ 2
      ∂stdGauss (Fin (13125 - 1))) ^ 2 ∂muI 13125 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13125) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13125

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13125
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13125}
    (hw : WINDOW (paperDesignP 13125) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13125).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13125) c M H xi)
    (hE : centreEnergy (paperDesignP 13125) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13125 : ℝ))))
    (hprice : massBound 13125 M H xi E u mixtureFloor ≤ 13125 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13125 - 1))).real
      {v | sgA (paperDesignP 13125) c a v < √(2 / (13125 : ℝ) * mixtureFloor)}
        ∂muI 13125 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13125).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13125) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13125) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13125)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13125

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13125
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13125) : ℝ :=
  (latitudeC / eR c) / ((13125 : ℝ) * (13125 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13125) / ((13125 : ℝ) * (13125 - 3))

theorem location_variance_on_event {c : Ret 13125}
    (hw : WINDOW (paperDesignP 13125) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13125) c a v - lbar (paperDesignP 13125) c a) ^ 2
      ∂stdGauss (Fin (13125 - 1))) ^ 2 ∂muI 13125 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13125)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13125}
    (hw : WINDOW (paperDesignP 13125) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13125) c a v - gbar (paperDesignP 13125) c a) ^ 2
      ∂stdGauss (Fin (13125 - 1))) ^ 2 ∂muI 13125 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13125)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13125}
    (hw : WINDOW (paperDesignP 13125) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13125 - 1))).real
      {v | sgA (paperDesignP 13125) c a v < √(2 / (13125 : ℝ) * mixtureFloor)}
      ∂muI 13125 ≤ lowMassBudget) :
    LatMom (paperDesignP 13125) c (√(2 / (13125 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13125

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13125
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13125} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13125 : ℝ) * (13125 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13125 : ℝ) * (13125 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13125 : ℝ) /
      ((13125 : ℝ) * (13125 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13125 : ℝ) * (13125 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13125 ≤ (2 * (16 / 5) / 13125 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13125} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (50164197 / 100000000000) ∧
    locationMomentBudget c 6 ≤ (308072751 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (845386479 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2398307333 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (5891477847 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (1616688169 / 200000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13125} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15483509 / 500000000000000) ∧ residualVarianceBudget ≤ (2831271 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13125 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2398307333 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13125

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13125
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13125 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13125) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13125) : ℝ :=
  exp (hqKappa * (13125 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((2890747 / 500000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (1156299 / 200000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13125} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (845386479 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (1616688169 / 50000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (1616688169 / 50000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((1616688169 / 50000000000000) : ℝ) / ((2890747 / 500000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (4499127 / 200000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13125} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1620149081 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((845386479 / 250000000000))) / ((2890747 / 500000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13125} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13125 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13125 * ((4499127 / 200000000) : ℝ) ^ 2 / 2 + ((1620149081 / 1000000000)) ^ 2 * (1 + (4499127 / 200000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13125 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13125 * ((4499127 / 200000000)) ^ 2 / 2 + ((1620149081 / 1000000000)) ^ 2 * (1 + (4499127 / 200000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((2890747 / 500000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (347866073 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121010762437 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13125

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13126
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13126 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13126) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13126 : ℝ) * (13126 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13126) /
    ((13126 : ℝ) * (13126 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13126} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13126}
    (hw : WINDOW (paperDesignP 13126) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13126) c a v - lbar (paperDesignP 13126) c a| ^ (2 * q)
      ∂stdGauss (Fin (13126 - 1)) ∂muI 13126 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13126)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13126}
    (hw : WINDOW (paperDesignP 13126) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13126) c a v - gbar (paperDesignP 13126) c a| ^ (2 * q)
      ∂stdGauss (Fin (13126 - 1)) ∂muI 13126 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13126)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13126) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13126}
    (hw : WINDOW (paperDesignP 13126) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13126 - 1))).real
      {v | sgA (paperDesignP 13126) c a v < √(2 / (13126 : ℝ) * mixtureFloor)}
      ∂muI 13126 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13126 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13126 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13126) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13126

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13126
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13126 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13126)
    (p : Ix 13126 × (Fin (13126 - 1) → ℝ)) :
    sgA (paperDesignP 13126) c p.1 p.2 ^ 2 ≤
      (2 / (13126 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13126).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13126) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13126 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13126 : ℝ) * _ ≤ 2 / 13126 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13126)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13126}
    (hw : WINDOW (paperDesignP 13126) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13126) c a v ^ 8
      ∂stdGauss (Fin (13126 - 1)) ∂muI 13126 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13126).prod (stdGauss (Fin (13126 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13126) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13126) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13126 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13126) c p.1 p.2)
      (√(2 / (13126 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13126)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13126 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13126) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13126}
    (hw : WINDOW (paperDesignP 13126) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13126) c a v -
      ∫ w, sA (paperDesignP 13126) c a w ∂stdGauss (Fin (13126 - 1))) ^ 2
      ∂stdGauss (Fin (13126 - 1))) ^ 2 ∂muI 13126 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13126) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13126

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13126
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13126}
    (hw : WINDOW (paperDesignP 13126) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13126).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13126) c M H xi)
    (hE : centreEnergy (paperDesignP 13126) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13126 : ℝ))))
    (hprice : massBound 13126 M H xi E u mixtureFloor ≤ 13126 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13126 - 1))).real
      {v | sgA (paperDesignP 13126) c a v < √(2 / (13126 : ℝ) * mixtureFloor)}
        ∂muI 13126 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13126).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13126) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13126) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13126)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13126

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13126
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13126) : ℝ :=
  (latitudeC / eR c) / ((13126 : ℝ) * (13126 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13126) / ((13126 : ℝ) * (13126 - 3))

theorem location_variance_on_event {c : Ret 13126}
    (hw : WINDOW (paperDesignP 13126) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13126) c a v - lbar (paperDesignP 13126) c a) ^ 2
      ∂stdGauss (Fin (13126 - 1))) ^ 2 ∂muI 13126 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13126)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13126}
    (hw : WINDOW (paperDesignP 13126) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13126) c a v - gbar (paperDesignP 13126) c a) ^ 2
      ∂stdGauss (Fin (13126 - 1))) ^ 2 ∂muI 13126 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13126)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13126}
    (hw : WINDOW (paperDesignP 13126) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13126 - 1))).real
      {v | sgA (paperDesignP 13126) c a v < √(2 / (13126 : ℝ) * mixtureFloor)}
      ∂muI 13126 ≤ lowMassBudget) :
    LatMom (paperDesignP 13126) c (√(2 / (13126 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13126

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13126
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13126} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13126 : ℝ) * (13126 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13126 : ℝ) * (13126 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13126 : ℝ) /
      ((13126 : ℝ) * (13126 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13126 : ℝ) * (13126 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13126 ≤ (2 * (16 / 5) / 13126 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13126} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (501603739 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (308049269 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (845322013 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (599508301 / 125000000000000) ∧
    residualMomentBudget 6 ≤ (5890804377 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (2020629131 / 250000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13126} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30962299 / 1000000000000000) ∧ residualVarianceBudget ≤ (88457 / 31250000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13126 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((599508301 / 125000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13126

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13126
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13126 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13126) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13126) : ℝ :=
  exp (hqKappa * (13126 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((2890637 / 500000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (231251 / 40000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13126} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (845322013 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (2020629131 / 62500000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (2020629131 / 62500000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((2020629131 / 62500000000000) : ℝ) / ((2890637 / 500000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22493909 / 1000000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13126} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1620087183 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((845322013 / 250000000000))) / ((2890637 / 500000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13126} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13126 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13126 * ((22493909 / 1000000000) : ℝ) ^ 2 / 2 + ((1620087183 / 1000000000)) ^ 2 * (1 + (22493909 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13126 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13126 * ((22493909 / 1000000000)) ^ 2 / 2 + ((1620087183 / 1000000000)) ^ 2 * (1 + (22493909 / 1000000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((2890637 / 500000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (347879163 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121019869769 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13126

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13127
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13127 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13127) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13127 : ℝ) * (13127 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13127) /
    ((13127 : ℝ) * (13127 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13127} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13127}
    (hw : WINDOW (paperDesignP 13127) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13127) c a v - lbar (paperDesignP 13127) c a| ^ (2 * q)
      ∂stdGauss (Fin (13127 - 1)) ∂muI 13127 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13127)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13127}
    (hw : WINDOW (paperDesignP 13127) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13127) c a v - gbar (paperDesignP 13127) c a| ^ (2 * q)
      ∂stdGauss (Fin (13127 - 1)) ∂muI 13127 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13127)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13127) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13127}
    (hw : WINDOW (paperDesignP 13127) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13127 - 1))).real
      {v | sgA (paperDesignP 13127) c a v < √(2 / (13127 : ℝ) * mixtureFloor)}
      ∂muI 13127 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13127 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13127 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13127) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13127

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13127
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13127 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13127)
    (p : Ix 13127 × (Fin (13127 - 1) → ℝ)) :
    sgA (paperDesignP 13127) c p.1 p.2 ^ 2 ≤
      (2 / (13127 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13127).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13127) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13127 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13127 : ℝ) * _ ≤ 2 / 13127 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13127)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13127}
    (hw : WINDOW (paperDesignP 13127) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13127) c a v ^ 8
      ∂stdGauss (Fin (13127 - 1)) ∂muI 13127 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13127).prod (stdGauss (Fin (13127 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13127) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13127) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13127 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13127) c p.1 p.2)
      (√(2 / (13127 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13127)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13127 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13127) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13127}
    (hw : WINDOW (paperDesignP 13127) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13127) c a v -
      ∫ w, sA (paperDesignP 13127) c a w ∂stdGauss (Fin (13127 - 1))) ^ 2
      ∂stdGauss (Fin (13127 - 1))) ^ 2 ∂muI 13127 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13127) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13127

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13127
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13127}
    (hw : WINDOW (paperDesignP 13127) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13127).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13127) c M H xi)
    (hE : centreEnergy (paperDesignP 13127) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13127 : ℝ))))
    (hprice : massBound 13127 M H xi E u mixtureFloor ≤ 13127 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13127 - 1))).real
      {v | sgA (paperDesignP 13127) c a v < √(2 / (13127 : ℝ) * mixtureFloor)}
        ∂muI 13127 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13127).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13127) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13127) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13127)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13127

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13127
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13127) : ℝ :=
  (latitudeC / eR c) / ((13127 : ℝ) * (13127 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13127) / ((13127 : ℝ) * (13127 - 3))

theorem location_variance_on_event {c : Ret 13127}
    (hw : WINDOW (paperDesignP 13127) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13127) c a v - lbar (paperDesignP 13127) c a) ^ 2
      ∂stdGauss (Fin (13127 - 1))) ^ 2 ∂muI 13127 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13127)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13127}
    (hw : WINDOW (paperDesignP 13127) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13127) c a v - gbar (paperDesignP 13127) c a) ^ 2
      ∂stdGauss (Fin (13127 - 1))) ^ 2 ∂muI 13127 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13127)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13127}
    (hw : WINDOW (paperDesignP 13127) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13127 - 1))).real
      {v | sgA (paperDesignP 13127) c a v < √(2 / (13127 : ℝ) * mixtureFloor)}
      ∂muI 13127 ≤ lowMassBudget) :
    LatMom (paperDesignP 13127) c (√(2 / (13127 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13127

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13127
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13127} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13127 : ℝ) * (13127 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13127 : ℝ) * (13127 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13127 : ℝ) /
      ((13127 : ℝ) * (13127 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13127 : ℝ) * (13127 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13127 ≤ (2 * (16 / 5) / 13127 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13127} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (250782757 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (616051581 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (169051511 / 200000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (959103651 / 200000000000000) ∧
    residualMomentBudget 6 ≤ (1178026207 / 200000000000000) ∧
    residualMomentBudget 12 ≤ (8081592379 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13127} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15478791 / 500000000000000) ∧ residualVarianceBudget ≤ (2829977 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13127 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((959103651 / 200000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13127

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13127
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13127 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13127) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13127) : ℝ :=
  exp (hqKappa * (13127 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5781053 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2890527 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13127} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (169051511 / 50000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8081592379 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8081592379 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8081592379 / 250000000000000) : ℝ) / ((5781053 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (5623047 / 250000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13127} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (64801023 / 40000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((169051511 / 50000000000))) / ((5781053 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13127} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13127 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13127 * ((5623047 / 250000000) : ℝ) ^ 2 / 2 + ((64801023 / 40000000)) ^ 2 * (1 + (5623047 / 250000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13127 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13127 * ((5623047 / 250000000)) ^ 2 / 2 + ((64801023 / 40000000)) ^ 2 * (1 + (5623047 / 250000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((5781053 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (173946157 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (60514510131 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13127

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13128
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13128 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13128) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13128 : ℝ) * (13128 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13128) /
    ((13128 : ℝ) * (13128 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13128} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13128}
    (hw : WINDOW (paperDesignP 13128) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13128) c a v - lbar (paperDesignP 13128) c a| ^ (2 * q)
      ∂stdGauss (Fin (13128 - 1)) ∂muI 13128 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13128)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13128}
    (hw : WINDOW (paperDesignP 13128) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13128) c a v - gbar (paperDesignP 13128) c a| ^ (2 * q)
      ∂stdGauss (Fin (13128 - 1)) ∂muI 13128 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13128)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13128) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13128}
    (hw : WINDOW (paperDesignP 13128) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13128 - 1))).real
      {v | sgA (paperDesignP 13128) c a v < √(2 / (13128 : ℝ) * mixtureFloor)}
      ∂muI 13128 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13128 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13128 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13128) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13128

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13128
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13128 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13128)
    (p : Ix 13128 × (Fin (13128 - 1) → ℝ)) :
    sgA (paperDesignP 13128) c p.1 p.2 ^ 2 ≤
      (2 / (13128 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13128).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13128) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13128 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13128 : ℝ) * _ ≤ 2 / 13128 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13128)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13128}
    (hw : WINDOW (paperDesignP 13128) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13128) c a v ^ 8
      ∂stdGauss (Fin (13128 - 1)) ∂muI 13128 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13128).prod (stdGauss (Fin (13128 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13128) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13128) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13128 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13128) c p.1 p.2)
      (√(2 / (13128 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13128)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13128 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13128) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13128}
    (hw : WINDOW (paperDesignP 13128) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13128) c a v -
      ∫ w, sA (paperDesignP 13128) c a w ∂stdGauss (Fin (13128 - 1))) ^ 2
      ∂stdGauss (Fin (13128 - 1))) ^ 2 ∂muI 13128 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13128) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13128

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13128
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13128}
    (hw : WINDOW (paperDesignP 13128) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13128).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13128) c M H xi)
    (hE : centreEnergy (paperDesignP 13128) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13128 : ℝ))))
    (hprice : massBound 13128 M H xi E u mixtureFloor ≤ 13128 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13128 - 1))).real
      {v | sgA (paperDesignP 13128) c a v < √(2 / (13128 : ℝ) * mixtureFloor)}
        ∂muI 13128 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13128).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13128) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13128) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13128)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13128

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13128
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13128) : ℝ :=
  (latitudeC / eR c) / ((13128 : ℝ) * (13128 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13128) / ((13128 : ℝ) * (13128 - 3))

theorem location_variance_on_event {c : Ret 13128}
    (hw : WINDOW (paperDesignP 13128) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13128) c a v - lbar (paperDesignP 13128) c a) ^ 2
      ∂stdGauss (Fin (13128 - 1))) ^ 2 ∂muI 13128 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13128)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13128}
    (hw : WINDOW (paperDesignP 13128) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13128) c a v - gbar (paperDesignP 13128) c a) ^ 2
      ∂stdGauss (Fin (13128 - 1))) ^ 2 ∂muI 13128 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13128)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13128}
    (hw : WINDOW (paperDesignP 13128) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13128 - 1))).real
      {v | sgA (paperDesignP 13128) c a v < √(2 / (13128 : ℝ) * mixtureFloor)}
      ∂muI 13128 ≤ lowMassBudget) :
    LatMom (paperDesignP 13128) c (√(2 / (13128 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13128

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13128
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13128} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13128 : ℝ) * (13128 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13128 : ℝ) * (13128 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13128 : ℝ) /
      ((13128 : ℝ) * (13128 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13128 : ℝ) * (13128 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13128 ≤ (2 * (16 / 5) / 13128 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13128} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (100305459 / 200000000000) ∧
    locationMomentBudget c 6 ≤ (616004631 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (211298277 / 250000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2397485103 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (2944728911 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (8080668409 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13128} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (6190573 / 200000000000000) ∧ residualVarianceBudget ≤ (282933 / 100000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13128 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2397485103 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13128

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13128
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13128 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13128) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13128) : ℝ :=
  exp (hqKappa * (13128 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5780833 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2890417 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13128} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (211298277 / 62500000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8080668409 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8080668409 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8080668409 / 250000000000000) : ℝ) / ((5780833 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11245231 / 500000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13128} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (202495463 / 125000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((211298277 / 62500000000))) / ((5780833 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13128} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13128 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13128 * ((11245231 / 500000000) : ℝ) ^ 2 / 2 + ((202495463 / 125000000)) ^ 2 * (1 + (11245231 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13128 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13128 * ((11245231 / 500000000)) ^ 2 / 2 + ((202495463 / 125000000)) ^ 2 * (1 + (11245231 / 500000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((5780833 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (173952703 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121038129713 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13128

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13129
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13129 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13129) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13129 : ℝ) * (13129 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13129) /
    ((13129 : ℝ) * (13129 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13129} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13129}
    (hw : WINDOW (paperDesignP 13129) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13129) c a v - lbar (paperDesignP 13129) c a| ^ (2 * q)
      ∂stdGauss (Fin (13129 - 1)) ∂muI 13129 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13129)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13129}
    (hw : WINDOW (paperDesignP 13129) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13129) c a v - gbar (paperDesignP 13129) c a| ^ (2 * q)
      ∂stdGauss (Fin (13129 - 1)) ∂muI 13129 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13129)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13129) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13129}
    (hw : WINDOW (paperDesignP 13129) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13129 - 1))).real
      {v | sgA (paperDesignP 13129) c a v < √(2 / (13129 : ℝ) * mixtureFloor)}
      ∂muI 13129 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13129 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13129 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13129) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13129

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13129
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13129 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13129)
    (p : Ix 13129 × (Fin (13129 - 1) → ℝ)) :
    sgA (paperDesignP 13129) c p.1 p.2 ^ 2 ≤
      (2 / (13129 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13129).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13129) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13129 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13129 : ℝ) * _ ≤ 2 / 13129 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13129)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13129}
    (hw : WINDOW (paperDesignP 13129) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13129) c a v ^ 8
      ∂stdGauss (Fin (13129 - 1)) ∂muI 13129 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13129).prod (stdGauss (Fin (13129 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13129) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13129) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13129 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13129) c p.1 p.2)
      (√(2 / (13129 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13129)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13129 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13129) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13129}
    (hw : WINDOW (paperDesignP 13129) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13129) c a v -
      ∫ w, sA (paperDesignP 13129) c a w ∂stdGauss (Fin (13129 - 1))) ^ 2
      ∂stdGauss (Fin (13129 - 1))) ^ 2 ∂muI 13129 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13129) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13129

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13129
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13129}
    (hw : WINDOW (paperDesignP 13129) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13129).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13129) c M H xi)
    (hE : centreEnergy (paperDesignP 13129) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13129 : ℝ))))
    (hprice : massBound 13129 M H xi E u mixtureFloor ≤ 13129 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13129 - 1))).real
      {v | sgA (paperDesignP 13129) c a v < √(2 / (13129 : ℝ) * mixtureFloor)}
        ∂muI 13129 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13129).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13129) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13129) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13129)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13129

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13129
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13129) : ℝ :=
  (latitudeC / eR c) / ((13129 : ℝ) * (13129 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13129) / ((13129 : ℝ) * (13129 - 3))

theorem location_variance_on_event {c : Ret 13129}
    (hw : WINDOW (paperDesignP 13129) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13129) c a v - lbar (paperDesignP 13129) c a) ^ 2
      ∂stdGauss (Fin (13129 - 1))) ^ 2 ∂muI 13129 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13129)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13129}
    (hw : WINDOW (paperDesignP 13129) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13129) c a v - gbar (paperDesignP 13129) c a) ^ 2
      ∂stdGauss (Fin (13129 - 1))) ^ 2 ∂muI 13129 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13129)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13129}
    (hw : WINDOW (paperDesignP 13129) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13129 - 1))).real
      {v | sgA (paperDesignP 13129) c a v < √(2 / (13129 : ℝ) * mixtureFloor)}
      ∂muI 13129 ≤ lowMassBudget) :
    LatMom (paperDesignP 13129) c (√(2 / (13129 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13129

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13129
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13129} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13129 : ℝ) * (13129 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13129 : ℝ) * (13129 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13129 : ℝ) /
      ((13129 : ℝ) * (13129 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13129 : ℝ) * (13129 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13129 ≤ (2 * (16 / 5) / 13129 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13129} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (250744541 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (76994711 / 125000000000) ∧
    locationMomentBudget c 12 ≤ (845128671 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4794422261 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (5888784737 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (1009968077 / 125000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13129} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (618963 / 20000000000000) ∧ residualVarianceBudget ≤ (2828683 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13129 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4794422261 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13129

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13129
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13129 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13129) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13129) : ℝ :=
  exp (hqKappa * (13129 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5780613 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2890307 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13129} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (845128671 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (1009968077 / 31250000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (1009968077 / 31250000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((1009968077 / 31250000000000) : ℝ) / ((5780613 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11244369 / 500000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13129} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1619901847 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((845128671 / 250000000000))) / ((5780613 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13129} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13129 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13129 * ((11244369 / 500000000) : ℝ) ^ 2 / 2 + ((1619901847 / 1000000000)) ^ 2 * (1 + (11244369 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13129 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13129 * ((11244369 / 500000000)) ^ 2 / 2 + ((1619901847 / 1000000000)) ^ 2 * (1 + (11244369 / 500000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((5780613 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (347918499 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (60523620111 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13129

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13130
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13130 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13130) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13130 : ℝ) * (13130 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13130) /
    ((13130 : ℝ) * (13130 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13130} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13130}
    (hw : WINDOW (paperDesignP 13130) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13130) c a v - lbar (paperDesignP 13130) c a| ^ (2 * q)
      ∂stdGauss (Fin (13130 - 1)) ∂muI 13130 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13130)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13130}
    (hw : WINDOW (paperDesignP 13130) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13130) c a v - gbar (paperDesignP 13130) c a| ^ (2 * q)
      ∂stdGauss (Fin (13130 - 1)) ∂muI 13130 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13130)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13130) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13130}
    (hw : WINDOW (paperDesignP 13130) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13130 - 1))).real
      {v | sgA (paperDesignP 13130) c a v < √(2 / (13130 : ℝ) * mixtureFloor)}
      ∂muI 13130 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13130 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13130 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13130) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13130

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13130
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13130 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13130)
    (p : Ix 13130 × (Fin (13130 - 1) → ℝ)) :
    sgA (paperDesignP 13130) c p.1 p.2 ^ 2 ≤
      (2 / (13130 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13130).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13130) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13130 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13130 : ℝ) * _ ≤ 2 / 13130 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13130)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13130}
    (hw : WINDOW (paperDesignP 13130) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13130) c a v ^ 8
      ∂stdGauss (Fin (13130 - 1)) ∂muI 13130 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13130).prod (stdGauss (Fin (13130 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13130) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13130) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13130 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13130) c p.1 p.2)
      (√(2 / (13130 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13130)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13130 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13130) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13130}
    (hw : WINDOW (paperDesignP 13130) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13130) c a v -
      ∫ w, sA (paperDesignP 13130) c a w ∂stdGauss (Fin (13130 - 1))) ^ 2
      ∂stdGauss (Fin (13130 - 1))) ^ 2 ∂muI 13130 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13130) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13130

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13130
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13130}
    (hw : WINDOW (paperDesignP 13130) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13130).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13130) c M H xi)
    (hE : centreEnergy (paperDesignP 13130) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13130 : ℝ))))
    (hprice : massBound 13130 M H xi E u mixtureFloor ≤ 13130 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13130 - 1))).real
      {v | sgA (paperDesignP 13130) c a v < √(2 / (13130 : ℝ) * mixtureFloor)}
        ∂muI 13130 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13130).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13130) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13130) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13130)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13130

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13130
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13130) : ℝ :=
  (latitudeC / eR c) / ((13130 : ℝ) * (13130 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13130) / ((13130 : ℝ) * (13130 - 3))

theorem location_variance_on_event {c : Ret 13130}
    (hw : WINDOW (paperDesignP 13130) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13130) c a v - lbar (paperDesignP 13130) c a) ^ 2
      ∂stdGauss (Fin (13130 - 1))) ^ 2 ∂muI 13130 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13130)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13130}
    (hw : WINDOW (paperDesignP 13130) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13130) c a v - gbar (paperDesignP 13130) c a) ^ 2
      ∂stdGauss (Fin (13130 - 1))) ^ 2 ∂muI 13130 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13130)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13130}
    (hw : WINDOW (paperDesignP 13130) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13130 - 1))).real
      {v | sgA (paperDesignP 13130) c a v < √(2 / (13130 : ℝ) * mixtureFloor)}
      ∂muI 13130 ≤ lowMassBudget) :
    LatMom (paperDesignP 13130) c (√(2 / (13130 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13130

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13130
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13130} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13130 : ℝ) * (13130 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13130 : ℝ) * (13130 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13130 : ℝ) /
      ((13130 : ℝ) * (13130 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13130 : ℝ) * (13130 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13130 ≤ (2 * (16 / 5) / 13130 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13130} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (4011607 / 8000000000) ∧
    locationMomentBudget c 6 ≤ (615910753 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (845064243 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4793874421 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (5888111779 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (8078820999 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13130} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (6188687 / 200000000000000) ∧ residualVarianceBudget ≤ (2828037 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13130 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4793874421 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13130

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13130
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13130 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13130) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13130) : ℝ :=
  exp (hqKappa * (13130 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5780393 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2890197 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13130} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (845064243 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8078820999 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8078820999 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8078820999 / 250000000000000) : ℝ) / ((5780393 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22487013 / 1000000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13130} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1619840003 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((845064243 / 250000000000))) / ((5780393 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13130} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13130 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13130 * ((22487013 / 1000000000) : ℝ) ^ 2 / 2 + ((1619840003 / 1000000000)) ^ 2 * (1 + (22487013 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13130 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13130 * ((22487013 / 1000000000)) ^ 2 / 2 + ((1619840003 / 1000000000)) ^ 2 * (1 + (22487013 / 1000000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((5780393 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (173965797 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121056351789 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13130

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13131
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13131 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13131) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13131 : ℝ) * (13131 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13131) /
    ((13131 : ℝ) * (13131 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13131} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13131}
    (hw : WINDOW (paperDesignP 13131) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13131) c a v - lbar (paperDesignP 13131) c a| ^ (2 * q)
      ∂stdGauss (Fin (13131 - 1)) ∂muI 13131 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13131)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13131}
    (hw : WINDOW (paperDesignP 13131) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13131) c a v - gbar (paperDesignP 13131) c a| ^ (2 * q)
      ∂stdGauss (Fin (13131 - 1)) ∂muI 13131 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13131)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13131) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13131}
    (hw : WINDOW (paperDesignP 13131) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13131 - 1))).real
      {v | sgA (paperDesignP 13131) c a v < √(2 / (13131 : ℝ) * mixtureFloor)}
      ∂muI 13131 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13131 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13131 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13131) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13131

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13131
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13131 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13131)
    (p : Ix 13131 × (Fin (13131 - 1) → ℝ)) :
    sgA (paperDesignP 13131) c p.1 p.2 ^ 2 ≤
      (2 / (13131 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13131).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13131) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13131 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13131 : ℝ) * _ ≤ 2 / 13131 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13131)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13131}
    (hw : WINDOW (paperDesignP 13131) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13131) c a v ^ 8
      ∂stdGauss (Fin (13131 - 1)) ∂muI 13131 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13131).prod (stdGauss (Fin (13131 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13131) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13131) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13131 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13131) c p.1 p.2)
      (√(2 / (13131 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13131)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13131 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13131) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13131}
    (hw : WINDOW (paperDesignP 13131) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13131) c a v -
      ∫ w, sA (paperDesignP 13131) c a w ∂stdGauss (Fin (13131 - 1))) ^ 2
      ∂stdGauss (Fin (13131 - 1))) ^ 2 ∂muI 13131 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13131) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13131

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13131
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13131}
    (hw : WINDOW (paperDesignP 13131) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13131).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13131) c M H xi)
    (hE : centreEnergy (paperDesignP 13131) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13131 : ℝ))))
    (hprice : massBound 13131 M H xi E u mixtureFloor ≤ 13131 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13131 - 1))).real
      {v | sgA (paperDesignP 13131) c a v < √(2 / (13131 : ℝ) * mixtureFloor)}
        ∂muI 13131 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13131).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13131) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13131) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13131)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13131

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13131
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13131) : ℝ :=
  (latitudeC / eR c) / ((13131 : ℝ) * (13131 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13131) / ((13131 : ℝ) * (13131 - 3))

theorem location_variance_on_event {c : Ret 13131}
    (hw : WINDOW (paperDesignP 13131) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13131) c a v - lbar (paperDesignP 13131) c a) ^ 2
      ∂stdGauss (Fin (13131 - 1))) ^ 2 ∂muI 13131 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13131)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13131}
    (hw : WINDOW (paperDesignP 13131) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13131) c a v - gbar (paperDesignP 13131) c a) ^ 2
      ∂stdGauss (Fin (13131 - 1))) ^ 2 ∂muI 13131 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13131)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13131}
    (hw : WINDOW (paperDesignP 13131) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13131 - 1))).real
      {v | sgA (paperDesignP 13131) c a v < √(2 / (13131 : ℝ) * mixtureFloor)}
      ∂muI 13131 ≤ lowMassBudget) :
    LatMom (paperDesignP 13131) c (√(2 / (13131 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13131

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13131
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13131} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13131 : ℝ) * (13131 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13131 : ℝ) * (13131 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13131 : ℝ) /
      ((13131 : ℝ) * (13131 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13131 : ℝ) * (13131 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13131 ≤ (2 * (16 / 5) / 13131 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13131} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (250706337 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (24634553 / 40000000000) ∧
    locationMomentBudget c 12 ≤ (33799993 / 40000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (958665337 / 200000000000000) ∧
    residualMomentBudget 6 ≤ (117748779 / 20000000000000) ∧
    residualMomentBudget 12 ≤ (4038948779 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13131} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15469361 / 500000000000000) ∧ residualVarianceBudget ≤ (2827391 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13131 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((958665337 / 200000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13131

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13131
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13131 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13131) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13131) : ℝ :=
  exp (hqKappa * (13131 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5780173 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2890087 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13131} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (33799993 / 10000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4038948779 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4038948779 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4038948779 / 125000000000000) : ℝ) / ((5780173 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22485289 / 1000000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13131} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1619778173 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((33799993 / 10000000000))) / ((5780173 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13131} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13131 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13131 * ((22485289 / 1000000000) : ℝ) ^ 2 / 2 + ((1619778173 / 1000000000)) ^ 2 * (1 + (22485289 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13131 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13131 * ((22485289 / 1000000000)) ^ 2 / 2 + ((1619778173 / 1000000000)) ^ 2 * (1 + (22485289 / 1000000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((5780173 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (347944689 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (60532732207 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13131

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13132
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13132 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13132) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13132 : ℝ) * (13132 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13132) /
    ((13132 : ℝ) * (13132 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13132} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13132}
    (hw : WINDOW (paperDesignP 13132) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13132) c a v - lbar (paperDesignP 13132) c a| ^ (2 * q)
      ∂stdGauss (Fin (13132 - 1)) ∂muI 13132 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13132)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13132}
    (hw : WINDOW (paperDesignP 13132) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13132) c a v - gbar (paperDesignP 13132) c a| ^ (2 * q)
      ∂stdGauss (Fin (13132 - 1)) ∂muI 13132 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13132)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13132) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13132}
    (hw : WINDOW (paperDesignP 13132) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13132 - 1))).real
      {v | sgA (paperDesignP 13132) c a v < √(2 / (13132 : ℝ) * mixtureFloor)}
      ∂muI 13132 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13132 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13132 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13132) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13132

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13132
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13132 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13132)
    (p : Ix 13132 × (Fin (13132 - 1) → ℝ)) :
    sgA (paperDesignP 13132) c p.1 p.2 ^ 2 ≤
      (2 / (13132 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13132).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13132) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13132 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13132 : ℝ) * _ ≤ 2 / 13132 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13132)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13132}
    (hw : WINDOW (paperDesignP 13132) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13132) c a v ^ 8
      ∂stdGauss (Fin (13132 - 1)) ∂muI 13132 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13132).prod (stdGauss (Fin (13132 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13132) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13132) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13132 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13132) c p.1 p.2)
      (√(2 / (13132 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13132)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13132 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13132) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13132}
    (hw : WINDOW (paperDesignP 13132) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13132) c a v -
      ∫ w, sA (paperDesignP 13132) c a w ∂stdGauss (Fin (13132 - 1))) ^ 2
      ∂stdGauss (Fin (13132 - 1))) ^ 2 ∂muI 13132 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13132) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13132

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13132
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13132}
    (hw : WINDOW (paperDesignP 13132) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13132).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13132) c M H xi)
    (hE : centreEnergy (paperDesignP 13132) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13132 : ℝ))))
    (hprice : massBound 13132 M H xi E u mixtureFloor ≤ 13132 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13132 - 1))).real
      {v | sgA (paperDesignP 13132) c a v < √(2 / (13132 : ℝ) * mixtureFloor)}
        ∂muI 13132 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13132).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13132) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13132) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13132)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13132

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13132
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13132) : ℝ :=
  (latitudeC / eR c) / ((13132 : ℝ) * (13132 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13132) / ((13132 : ℝ) * (13132 - 3))

theorem location_variance_on_event {c : Ret 13132}
    (hw : WINDOW (paperDesignP 13132) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13132) c a v - lbar (paperDesignP 13132) c a) ^ 2
      ∂stdGauss (Fin (13132 - 1))) ^ 2 ∂muI 13132 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13132)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13132}
    (hw : WINDOW (paperDesignP 13132) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13132) c a v - gbar (paperDesignP 13132) c a) ^ 2
      ∂stdGauss (Fin (13132 - 1))) ^ 2 ∂muI 13132 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13132)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13132}
    (hw : WINDOW (paperDesignP 13132) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13132 - 1))).real
      {v | sgA (paperDesignP 13132) c a v < √(2 / (13132 : ℝ) * mixtureFloor)}
      ∂muI 13132 ≤ lowMassBudget) :
    LatMom (paperDesignP 13132) c (√(2 / (13132 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13132

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13132
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13132} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13132 : ℝ) * (13132 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13132 : ℝ) * (13132 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13132 : ℝ) /
      ((13132 : ℝ) * (13132 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13132 : ℝ) * (13132 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13132 ≤ (2 * (16 / 5) / 13132 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13132} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (250687239 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (615816903 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (844935417 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2396389527 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (4709413 / 800000000000) ∧
    residualMomentBudget 12 ≤ (8076974293 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13132} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30934009 / 1000000000000000) ∧ residualVarianceBudget ≤ (565349 / 200000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13132 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2396389527 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13132

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13132
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13132 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13132) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13132) : ℝ :=
  exp (hqKappa * (13132 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5779953 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2889977 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13132} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (844935417 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8076974293 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8076974293 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8076974293 / 250000000000000) : ℝ) / ((5779953 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (4496713 / 200000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13132} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (809858179 / 500000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((844935417 / 250000000000))) / ((5779953 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13132} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13132 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13132 * ((4496713 / 200000000) : ℝ) ^ 2 / 2 + ((809858179 / 500000000)) ^ 2 * (1 + (4496713 / 200000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13132 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13132 * ((4496713 / 200000000)) ^ 2 / 2 + ((809858179 / 500000000)) ^ 2 * (1 + (4496713 / 200000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((5779953 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (69591557 / 200000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (60537289049 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13132

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13133
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13133 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13133) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13133 : ℝ) * (13133 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13133) /
    ((13133 : ℝ) * (13133 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13133} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13133}
    (hw : WINDOW (paperDesignP 13133) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13133) c a v - lbar (paperDesignP 13133) c a| ^ (2 * q)
      ∂stdGauss (Fin (13133 - 1)) ∂muI 13133 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13133)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13133}
    (hw : WINDOW (paperDesignP 13133) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13133) c a v - gbar (paperDesignP 13133) c a| ^ (2 * q)
      ∂stdGauss (Fin (13133 - 1)) ∂muI 13133 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13133)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13133) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13133}
    (hw : WINDOW (paperDesignP 13133) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13133 - 1))).real
      {v | sgA (paperDesignP 13133) c a v < √(2 / (13133 : ℝ) * mixtureFloor)}
      ∂muI 13133 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13133 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13133 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13133) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13133

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13133
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13133 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13133)
    (p : Ix 13133 × (Fin (13133 - 1) → ℝ)) :
    sgA (paperDesignP 13133) c p.1 p.2 ^ 2 ≤
      (2 / (13133 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13133).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13133) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13133 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13133 : ℝ) * _ ≤ 2 / 13133 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13133)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13133}
    (hw : WINDOW (paperDesignP 13133) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13133) c a v ^ 8
      ∂stdGauss (Fin (13133 - 1)) ∂muI 13133 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13133).prod (stdGauss (Fin (13133 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13133) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13133) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13133 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13133) c p.1 p.2)
      (√(2 / (13133 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13133)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13133 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13133) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13133}
    (hw : WINDOW (paperDesignP 13133) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13133) c a v -
      ∫ w, sA (paperDesignP 13133) c a w ∂stdGauss (Fin (13133 - 1))) ^ 2
      ∂stdGauss (Fin (13133 - 1))) ^ 2 ∂muI 13133 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13133) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13133

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13133
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13133}
    (hw : WINDOW (paperDesignP 13133) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13133).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13133) c M H xi)
    (hE : centreEnergy (paperDesignP 13133) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13133 : ℝ))))
    (hprice : massBound 13133 M H xi E u mixtureFloor ≤ 13133 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13133 - 1))).real
      {v | sgA (paperDesignP 13133) c a v < √(2 / (13133 : ℝ) * mixtureFloor)}
        ∂muI 13133 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13133).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13133) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13133) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13133)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13133

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13133
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13133) : ℝ :=
  (latitudeC / eR c) / ((13133 : ℝ) * (13133 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13133) / ((13133 : ℝ) * (13133 - 3))

theorem location_variance_on_event {c : Ret 13133}
    (hw : WINDOW (paperDesignP 13133) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13133) c a v - lbar (paperDesignP 13133) c a) ^ 2
      ∂stdGauss (Fin (13133 - 1))) ^ 2 ∂muI 13133 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13133)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13133}
    (hw : WINDOW (paperDesignP 13133) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13133) c a v - gbar (paperDesignP 13133) c a) ^ 2
      ∂stdGauss (Fin (13133 - 1))) ^ 2 ∂muI 13133 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13133)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13133}
    (hw : WINDOW (paperDesignP 13133) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13133 - 1))).real
      {v | sgA (paperDesignP 13133) c a v < √(2 / (13133 : ℝ) * mixtureFloor)}
      ∂muI 13133 ≤ lowMassBudget) :
    LatMom (paperDesignP 13133) c (√(2 / (13133 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13133

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13133
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13133} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13133 : ℝ) * (13133 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13133 : ℝ) * (13133 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13133 : ℝ) /
      ((13133 : ℝ) * (13133 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13133 : ℝ) * (13133 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13133 ≤ (2 * (16 / 5) / 13133 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13133} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (15666759 / 31250000000) ∧
    locationMomentBudget c 6 ≤ (615769989 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (844871019 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4792231527 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (5886093677 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (8076051203 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13133} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15464649 / 500000000000000) ∧ residualVarianceBudget ≤ (2826099 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13133 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4792231527 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13133

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13133
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13133 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13133) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13133) : ℝ :=
  exp (hqKappa * (13133 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5779733 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2889867 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13133} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (844871019 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8076051203 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8076051203 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8076051203 / 250000000000000) : ℝ) / ((5779733 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11240921 / 500000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13133} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1619654557 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((844871019 / 250000000000))) / ((5779733 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13133} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13133 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13133 * ((11240921 / 500000000) : ℝ) ^ 2 / 2 + ((1619654557 / 1000000000)) ^ 2 * (1 + (11240921 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13133 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13133 * ((11240921 / 500000000)) ^ 2 / 2 + ((1619654557 / 1000000000)) ^ 2 * (1 + (11240921 / 500000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((5779733 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (173985441 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121083692839 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13133

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13134
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13134 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13134) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13134 : ℝ) * (13134 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13134) /
    ((13134 : ℝ) * (13134 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13134} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13134}
    (hw : WINDOW (paperDesignP 13134) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13134) c a v - lbar (paperDesignP 13134) c a| ^ (2 * q)
      ∂stdGauss (Fin (13134 - 1)) ∂muI 13134 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13134)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13134}
    (hw : WINDOW (paperDesignP 13134) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13134) c a v - gbar (paperDesignP 13134) c a| ^ (2 * q)
      ∂stdGauss (Fin (13134 - 1)) ∂muI 13134 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13134)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13134) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13134}
    (hw : WINDOW (paperDesignP 13134) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13134 - 1))).real
      {v | sgA (paperDesignP 13134) c a v < √(2 / (13134 : ℝ) * mixtureFloor)}
      ∂muI 13134 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13134 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13134 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13134) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13134

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13134
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13134 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13134)
    (p : Ix 13134 × (Fin (13134 - 1) → ℝ)) :
    sgA (paperDesignP 13134) c p.1 p.2 ^ 2 ≤
      (2 / (13134 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13134).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13134) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13134 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13134 : ℝ) * _ ≤ 2 / 13134 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13134)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13134}
    (hw : WINDOW (paperDesignP 13134) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13134) c a v ^ 8
      ∂stdGauss (Fin (13134 - 1)) ∂muI 13134 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13134).prod (stdGauss (Fin (13134 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13134) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13134) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13134 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13134) c p.1 p.2)
      (√(2 / (13134 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13134)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13134 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13134) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13134}
    (hw : WINDOW (paperDesignP 13134) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13134) c a v -
      ∫ w, sA (paperDesignP 13134) c a w ∂stdGauss (Fin (13134 - 1))) ^ 2
      ∂stdGauss (Fin (13134 - 1))) ^ 2 ∂muI 13134 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13134) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13134

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13134
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13134}
    (hw : WINDOW (paperDesignP 13134) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13134).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13134) c M H xi)
    (hE : centreEnergy (paperDesignP 13134) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13134 : ℝ))))
    (hprice : massBound 13134 M H xi E u mixtureFloor ≤ 13134 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13134 - 1))).real
      {v | sgA (paperDesignP 13134) c a v < √(2 / (13134 : ℝ) * mixtureFloor)}
        ∂muI 13134 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13134).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13134) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13134) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13134)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13134

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13134
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13134) : ℝ :=
  (latitudeC / eR c) / ((13134 : ℝ) * (13134 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13134) / ((13134 : ℝ) * (13134 - 3))

theorem location_variance_on_event {c : Ret 13134}
    (hw : WINDOW (paperDesignP 13134) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13134) c a v - lbar (paperDesignP 13134) c a) ^ 2
      ∂stdGauss (Fin (13134 - 1))) ^ 2 ∂muI 13134 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13134)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13134}
    (hw : WINDOW (paperDesignP 13134) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13134) c a v - gbar (paperDesignP 13134) c a) ^ 2
      ∂stdGauss (Fin (13134 - 1))) ^ 2 ∂muI 13134 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13134)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13134}
    (hw : WINDOW (paperDesignP 13134) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13134 - 1))).real
      {v | sgA (paperDesignP 13134) c a v < √(2 / (13134 : ℝ) * mixtureFloor)}
      ∂muI 13134 ≤ lowMassBudget) :
    LatMom (paperDesignP 13134) c (√(2 / (13134 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13134

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13134
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13134} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13134 : ℝ) * (13134 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13134 : ℝ) * (13134 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13134 : ℝ) /
      ((13134 : ℝ) * (13134 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13134 : ℝ) * (13134 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13134 ≤ (2 * (16 / 5) / 13134 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13134} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (62662263 / 125000000000) ∧
    locationMomentBudget c 6 ≤ (615723083 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (844806631 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (598960513 / 125000000000000) ∧
    residualMomentBudget 6 ≤ (367838827 / 62500000000000) ∧
    residualMomentBudget 12 ≤ (807512829 / 100000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13134} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (7731147 / 250000000000000) ∧ residualVarianceBudget ≤ (1412727 / 500000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13134 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((598960513 / 125000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13134

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13134
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13134 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13134) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13134) : ℝ :=
  exp (hqKappa * (13134 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5779513 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2889757 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13134} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (844806631 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (807512829 / 25000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (807512829 / 25000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((807512829 / 25000000000000) : ℝ) / ((5779513 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22480119 / 1000000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13134} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1619592771 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((844806631 / 250000000000))) / ((5779513 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13134} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13134 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13134 * ((22480119 / 1000000000) : ℝ) ^ 2 / 2 + ((1619592771 / 1000000000)) ^ 2 * (1 + (22480119 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13134 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13134 * ((22480119 / 1000000000)) ^ 2 / 2 + ((1619592771 / 1000000000)) ^ 2 * (1 + (22480119 / 1000000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((5779513 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (17399199 / 50000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121092808639 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13134

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13135
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13135 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13135) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13135 : ℝ) * (13135 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13135) /
    ((13135 : ℝ) * (13135 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13135} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13135}
    (hw : WINDOW (paperDesignP 13135) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13135) c a v - lbar (paperDesignP 13135) c a| ^ (2 * q)
      ∂stdGauss (Fin (13135 - 1)) ∂muI 13135 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13135)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13135}
    (hw : WINDOW (paperDesignP 13135) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13135) c a v - gbar (paperDesignP 13135) c a| ^ (2 * q)
      ∂stdGauss (Fin (13135 - 1)) ∂muI 13135 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13135)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13135) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13135}
    (hw : WINDOW (paperDesignP 13135) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13135 - 1))).real
      {v | sgA (paperDesignP 13135) c a v < √(2 / (13135 : ℝ) * mixtureFloor)}
      ∂muI 13135 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13135 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13135 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13135) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13135

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13135
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13135 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13135)
    (p : Ix 13135 × (Fin (13135 - 1) → ℝ)) :
    sgA (paperDesignP 13135) c p.1 p.2 ^ 2 ≤
      (2 / (13135 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13135).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13135) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13135 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13135 : ℝ) * _ ≤ 2 / 13135 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13135)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13135}
    (hw : WINDOW (paperDesignP 13135) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13135) c a v ^ 8
      ∂stdGauss (Fin (13135 - 1)) ∂muI 13135 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13135).prod (stdGauss (Fin (13135 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13135) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13135) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13135 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13135) c p.1 p.2)
      (√(2 / (13135 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13135)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13135 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13135) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13135}
    (hw : WINDOW (paperDesignP 13135) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13135) c a v -
      ∫ w, sA (paperDesignP 13135) c a w ∂stdGauss (Fin (13135 - 1))) ^ 2
      ∂stdGauss (Fin (13135 - 1))) ^ 2 ∂muI 13135 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13135) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13135

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13135
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13135}
    (hw : WINDOW (paperDesignP 13135) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13135).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13135) c M H xi)
    (hE : centreEnergy (paperDesignP 13135) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13135 : ℝ))))
    (hprice : massBound 13135 M H xi E u mixtureFloor ≤ 13135 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13135 - 1))).real
      {v | sgA (paperDesignP 13135) c a v < √(2 / (13135 : ℝ) * mixtureFloor)}
        ∂muI 13135 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13135).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13135) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13135) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13135)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13135

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13135
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13135) : ℝ :=
  (latitudeC / eR c) / ((13135 : ℝ) * (13135 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13135) / ((13135 : ℝ) * (13135 - 3))

theorem location_variance_on_event {c : Ret 13135}
    (hw : WINDOW (paperDesignP 13135) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13135) c a v - lbar (paperDesignP 13135) c a) ^ 2
      ∂stdGauss (Fin (13135 - 1))) ^ 2 ∂muI 13135 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13135)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13135}
    (hw : WINDOW (paperDesignP 13135) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13135) c a v - gbar (paperDesignP 13135) c a) ^ 2
      ∂stdGauss (Fin (13135 - 1))) ^ 2 ∂muI 13135 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13135)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13135}
    (hw : WINDOW (paperDesignP 13135) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13135 - 1))).real
      {v | sgA (paperDesignP 13135) c a v < √(2 / (13135 : ℝ) * mixtureFloor)}
      ∂muI 13135 ≤ lowMassBudget) :
    LatMom (paperDesignP 13135) c (√(2 / (13135 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13135

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13135
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13135} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13135 : ℝ) * (13135 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13135 : ℝ) * (13135 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13135 : ℝ) /
      ((13135 : ℝ) * (13135 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13135 : ℝ) * (13135 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13135 ≤ (2 * (16 / 5) / 13135 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13135} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (250629963 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (615676183 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (211185563 / 250000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (958227357 / 200000000000000) ∧
    residualMomentBudget 6 ≤ (1471187229 / 250000000000000) ∧
    residualMomentBudget 12 ≤ (504637847 / 62500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13135} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30919879 / 1000000000000000) ∧ residualVarianceBudget ≤ (2824809 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13135 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((958227357 / 200000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13135

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13135
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13135 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13135) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13135) : ℝ :=
  exp (hqKappa * (13135 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5779293 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2889647 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13135} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (211185563 / 62500000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (504637847 / 15625000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (504637847 / 15625000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((504637847 / 15625000000000) : ℝ) / ((5779293 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (5619599 / 250000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13135} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1619530997 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((211185563 / 62500000000))) / ((5779293 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13135} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13135 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13135 * ((5619599 / 250000000) : ℝ) ^ 2 / 2 + ((1619530997 / 1000000000)) ^ 2 * (1 + (5619599 / 250000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13135 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13135 * ((5619599 / 250000000)) ^ 2 / 2 + ((1619530997 / 1000000000)) ^ 2 * (1 + (5619599 / 250000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((5779293 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (8699927 / 25000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (60550962749 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13135

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13136
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13136 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13136) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13136 : ℝ) * (13136 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13136) /
    ((13136 : ℝ) * (13136 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13136} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13136}
    (hw : WINDOW (paperDesignP 13136) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13136) c a v - lbar (paperDesignP 13136) c a| ^ (2 * q)
      ∂stdGauss (Fin (13136 - 1)) ∂muI 13136 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13136)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13136}
    (hw : WINDOW (paperDesignP 13136) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13136) c a v - gbar (paperDesignP 13136) c a| ^ (2 * q)
      ∂stdGauss (Fin (13136 - 1)) ∂muI 13136 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13136)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13136) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13136}
    (hw : WINDOW (paperDesignP 13136) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13136 - 1))).real
      {v | sgA (paperDesignP 13136) c a v < √(2 / (13136 : ℝ) * mixtureFloor)}
      ∂muI 13136 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13136 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13136 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13136) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13136

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13136
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13136 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13136)
    (p : Ix 13136 × (Fin (13136 - 1) → ℝ)) :
    sgA (paperDesignP 13136) c p.1 p.2 ^ 2 ≤
      (2 / (13136 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13136).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13136) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13136 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13136 : ℝ) * _ ≤ 2 / 13136 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13136)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13136}
    (hw : WINDOW (paperDesignP 13136) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13136) c a v ^ 8
      ∂stdGauss (Fin (13136 - 1)) ∂muI 13136 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13136).prod (stdGauss (Fin (13136 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13136) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13136) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13136 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13136) c p.1 p.2)
      (√(2 / (13136 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13136)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13136 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13136) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13136}
    (hw : WINDOW (paperDesignP 13136) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13136) c a v -
      ∫ w, sA (paperDesignP 13136) c a w ∂stdGauss (Fin (13136 - 1))) ^ 2
      ∂stdGauss (Fin (13136 - 1))) ^ 2 ∂muI 13136 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13136) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13136

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13136
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13136}
    (hw : WINDOW (paperDesignP 13136) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13136).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13136) c M H xi)
    (hE : centreEnergy (paperDesignP 13136) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13136 : ℝ))))
    (hprice : massBound 13136 M H xi E u mixtureFloor ≤ 13136 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13136 - 1))).real
      {v | sgA (paperDesignP 13136) c a v < √(2 / (13136 : ℝ) * mixtureFloor)}
        ∂muI 13136 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13136).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13136) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13136) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13136)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13136

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13136
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13136) : ℝ :=
  (latitudeC / eR c) / ((13136 : ℝ) * (13136 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13136) / ((13136 : ℝ) * (13136 - 3))

theorem location_variance_on_event {c : Ret 13136}
    (hw : WINDOW (paperDesignP 13136) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13136) c a v - lbar (paperDesignP 13136) c a) ^ 2
      ∂stdGauss (Fin (13136 - 1))) ^ 2 ∂muI 13136 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13136)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13136}
    (hw : WINDOW (paperDesignP 13136) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13136) c a v - gbar (paperDesignP 13136) c a) ^ 2
      ∂stdGauss (Fin (13136 - 1))) ^ 2 ∂muI 13136 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13136)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13136}
    (hw : WINDOW (paperDesignP 13136) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13136 - 1))).real
      {v | sgA (paperDesignP 13136) c a v < √(2 / (13136 : ℝ) * mixtureFloor)}
      ∂muI 13136 ≤ lowMassBudget) :
    LatMom (paperDesignP 13136) c (√(2 / (13136 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13136

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13136
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13136} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13136 : ℝ) * (13136 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13136 : ℝ) * (13136 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13136 : ℝ) /
      ((13136 : ℝ) * (13136 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13136 : ℝ) * (13136 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13136 ≤ (2 * (16 / 5) / 13136 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13136} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (250610877 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (61562929 / 100000000000) ∧
    locationMomentBudget c 12 ≤ (844677883 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (479058957 / 100000000000000) ∧
    residualMomentBudget 6 ≤ (5884076727 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (807328299 / 100000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13136} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30915171 / 1000000000000000) ∧ residualVarianceBudget ≤ (2824163 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13136 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((479058957 / 100000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13136

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13136
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13136 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13136) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13136) : ℝ :=
  exp (hqKappa * (13136 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5779073 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2889537 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13136} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (844677883 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (807328299 / 25000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (807328299 / 25000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((807328299 / 25000000000000) : ℝ) / ((5779073 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11238337 / 500000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13136} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (809734619 / 500000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((844677883 / 250000000000))) / ((5779073 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13136} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13136 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13136 * ((11238337 / 500000000) : ℝ) ^ 2 / 2 + ((809734619 / 500000000)) ^ 2 * (1 + (11238337 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13136 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13136 * ((11238337 / 500000000)) ^ 2 / 2 + ((809734619 / 500000000)) ^ 2 * (1 + (11238337 / 500000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((5779073 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (17400509 / 50000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (15138880427 / 125000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13136

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13137
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13137 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13137) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13137 : ℝ) * (13137 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13137) /
    ((13137 : ℝ) * (13137 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13137} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13137}
    (hw : WINDOW (paperDesignP 13137) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13137) c a v - lbar (paperDesignP 13137) c a| ^ (2 * q)
      ∂stdGauss (Fin (13137 - 1)) ∂muI 13137 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13137)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13137}
    (hw : WINDOW (paperDesignP 13137) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13137) c a v - gbar (paperDesignP 13137) c a| ^ (2 * q)
      ∂stdGauss (Fin (13137 - 1)) ∂muI 13137 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13137)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13137) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13137}
    (hw : WINDOW (paperDesignP 13137) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13137 - 1))).real
      {v | sgA (paperDesignP 13137) c a v < √(2 / (13137 : ℝ) * mixtureFloor)}
      ∂muI 13137 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13137 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13137 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13137) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13137

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13137
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13137 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13137)
    (p : Ix 13137 × (Fin (13137 - 1) → ℝ)) :
    sgA (paperDesignP 13137) c p.1 p.2 ^ 2 ≤
      (2 / (13137 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13137).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13137) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13137 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13137 : ℝ) * _ ≤ 2 / 13137 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13137)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13137}
    (hw : WINDOW (paperDesignP 13137) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13137) c a v ^ 8
      ∂stdGauss (Fin (13137 - 1)) ∂muI 13137 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13137).prod (stdGauss (Fin (13137 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13137) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13137) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13137 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13137) c p.1 p.2)
      (√(2 / (13137 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13137)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13137 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13137) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13137}
    (hw : WINDOW (paperDesignP 13137) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13137) c a v -
      ∫ w, sA (paperDesignP 13137) c a w ∂stdGauss (Fin (13137 - 1))) ^ 2
      ∂stdGauss (Fin (13137 - 1))) ^ 2 ∂muI 13137 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13137) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13137

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13137
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13137}
    (hw : WINDOW (paperDesignP 13137) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13137).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13137) c M H xi)
    (hE : centreEnergy (paperDesignP 13137) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13137 : ℝ))))
    (hprice : massBound 13137 M H xi E u mixtureFloor ≤ 13137 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13137 - 1))).real
      {v | sgA (paperDesignP 13137) c a v < √(2 / (13137 : ℝ) * mixtureFloor)}
        ∂muI 13137 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13137).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13137) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13137) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13137)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13137

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13137
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13137) : ℝ :=
  (latitudeC / eR c) / ((13137 : ℝ) * (13137 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13137) / ((13137 : ℝ) * (13137 - 3))

theorem location_variance_on_event {c : Ret 13137}
    (hw : WINDOW (paperDesignP 13137) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13137) c a v - lbar (paperDesignP 13137) c a) ^ 2
      ∂stdGauss (Fin (13137 - 1))) ^ 2 ∂muI 13137 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13137)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13137}
    (hw : WINDOW (paperDesignP 13137) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13137) c a v - gbar (paperDesignP 13137) c a) ^ 2
      ∂stdGauss (Fin (13137 - 1))) ^ 2 ∂muI 13137 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13137)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13137}
    (hw : WINDOW (paperDesignP 13137) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13137 - 1))).real
      {v | sgA (paperDesignP 13137) c a v < √(2 / (13137 : ℝ) * mixtureFloor)}
      ∂muI 13137 ≤ lowMassBudget) :
    LatMom (paperDesignP 13137) c (√(2 / (13137 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13137

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13137
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13137} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13137 : ℝ) * (13137 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13137 : ℝ) * (13137 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13137 : ℝ) /
      ((13137 : ℝ) * (13137 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13137 : ℝ) * (13137 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13137 ≤ (2 * (16 / 5) / 13137 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13137} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (501183587 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (123116481 / 200000000000) ∧
    locationMomentBudget c 12 ≤ (33784541 / 40000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (239502123 / 50000000000000) ∧
    residualMomentBudget 6 ≤ (2941702333 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (2018090151 / 250000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13137} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15093 / 488281250000) ∧ residualVarianceBudget ≤ (2823519 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13137 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((239502123 / 50000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13137

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13137
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13137 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13137) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13137) : ℝ :=
  exp (hqKappa * (13137 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5778853 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2889427 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13137} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (33784541 / 10000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (2018090151 / 62500000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (2018090151 / 62500000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((2018090151 / 62500000000000) : ℝ) / ((5778853 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (2809369 / 125000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13137} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (323881499 / 200000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((33784541 / 10000000000))) / ((5778853 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13137} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13137 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13137 * ((2809369 / 125000000) : ℝ) ^ 2 / 2 + ((323881499 / 200000000)) ^ 2 * (1 + (2809369 / 125000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13137 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13137 * ((2809369 / 125000000)) ^ 2 / 2 + ((323881499 / 200000000)) ^ 2 * (1 + (2809369 / 125000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((5778853 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (348023281 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121120162393 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13137

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13138
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13138 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13138) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13138 : ℝ) * (13138 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13138) /
    ((13138 : ℝ) * (13138 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13138} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13138}
    (hw : WINDOW (paperDesignP 13138) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13138) c a v - lbar (paperDesignP 13138) c a| ^ (2 * q)
      ∂stdGauss (Fin (13138 - 1)) ∂muI 13138 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13138)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13138}
    (hw : WINDOW (paperDesignP 13138) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13138) c a v - gbar (paperDesignP 13138) c a| ^ (2 * q)
      ∂stdGauss (Fin (13138 - 1)) ∂muI 13138 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13138)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13138) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13138}
    (hw : WINDOW (paperDesignP 13138) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13138 - 1))).real
      {v | sgA (paperDesignP 13138) c a v < √(2 / (13138 : ℝ) * mixtureFloor)}
      ∂muI 13138 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13138 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13138 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13138) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13138

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13138
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13138 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13138)
    (p : Ix 13138 × (Fin (13138 - 1) → ℝ)) :
    sgA (paperDesignP 13138) c p.1 p.2 ^ 2 ≤
      (2 / (13138 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13138).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13138) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13138 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13138 : ℝ) * _ ≤ 2 / 13138 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13138)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13138}
    (hw : WINDOW (paperDesignP 13138) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13138) c a v ^ 8
      ∂stdGauss (Fin (13138 - 1)) ∂muI 13138 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13138).prod (stdGauss (Fin (13138 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13138) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13138) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13138 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13138) c p.1 p.2)
      (√(2 / (13138 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13138)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13138 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13138) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13138}
    (hw : WINDOW (paperDesignP 13138) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13138) c a v -
      ∫ w, sA (paperDesignP 13138) c a w ∂stdGauss (Fin (13138 - 1))) ^ 2
      ∂stdGauss (Fin (13138 - 1))) ^ 2 ∂muI 13138 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13138) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13138

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13138
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13138}
    (hw : WINDOW (paperDesignP 13138) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13138).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13138) c M H xi)
    (hE : centreEnergy (paperDesignP 13138) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13138 : ℝ))))
    (hprice : massBound 13138 M H xi E u mixtureFloor ≤ 13138 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13138 - 1))).real
      {v | sgA (paperDesignP 13138) c a v < √(2 / (13138 : ℝ) * mixtureFloor)}
        ∂muI 13138 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13138).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13138) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13138) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13138)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13138

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13138
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13138) : ℝ :=
  (latitudeC / eR c) / ((13138 : ℝ) * (13138 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13138) / ((13138 : ℝ) * (13138 - 3))

theorem location_variance_on_event {c : Ret 13138}
    (hw : WINDOW (paperDesignP 13138) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13138) c a v - lbar (paperDesignP 13138) c a) ^ 2
      ∂stdGauss (Fin (13138 - 1))) ^ 2 ∂muI 13138 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13138)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13138}
    (hw : WINDOW (paperDesignP 13138) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13138) c a v - gbar (paperDesignP 13138) c a) ^ 2
      ∂stdGauss (Fin (13138 - 1))) ^ 2 ∂muI 13138 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13138)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13138}
    (hw : WINDOW (paperDesignP 13138) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13138 - 1))).real
      {v | sgA (paperDesignP 13138) c a v < √(2 / (13138 : ℝ) * mixtureFloor)}
      ∂muI 13138 ≤ lowMassBudget) :
    LatMom (paperDesignP 13138) c (√(2 / (13138 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13138

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13138
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13138} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13138 : ℝ) * (13138 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13138 : ℝ) * (13138 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13138 : ℝ) /
      ((13138 : ℝ) * (13138 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13138 : ℝ) * (13138 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13138 ≤ (2 * (16 / 5) / 13138 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13138} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (501145427 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (307767763 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (33781967 / 40000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2394747727 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (2941366367 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (8071438393 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13138} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15452879 / 500000000000000) ∧ residualVarianceBudget ≤ (1411437 / 500000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13138 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2394747727 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13138

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13138
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13138 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13138) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13138) : ℝ :=
  exp (hqKappa * (13138 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5778633 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2889317 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13138} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (33781967 / 10000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8071438393 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8071438393 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8071438393 / 250000000000000) : ℝ) / ((5778633 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (2247323 / 100000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13138} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1619345763 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((33781967 / 10000000000))) / ((5778633 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13138} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13138 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13138 * ((2247323 / 100000000) : ℝ) ^ 2 / 2 + ((1619345763 / 1000000000)) ^ 2 * (1 + (2247323 / 100000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13138 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13138 * ((2247323 / 100000000)) ^ 2 / 2 + ((1619345763 / 1000000000)) ^ 2 * (1 + (2247323 / 100000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((5778633 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (10876137 / 31250) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (30282320607 / 250000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13138

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13139
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13139 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13139) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13139 : ℝ) * (13139 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13139) /
    ((13139 : ℝ) * (13139 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13139} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13139}
    (hw : WINDOW (paperDesignP 13139) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13139) c a v - lbar (paperDesignP 13139) c a| ^ (2 * q)
      ∂stdGauss (Fin (13139 - 1)) ∂muI 13139 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13139)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13139}
    (hw : WINDOW (paperDesignP 13139) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13139) c a v - gbar (paperDesignP 13139) c a| ^ (2 * q)
      ∂stdGauss (Fin (13139 - 1)) ∂muI 13139 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13139)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13139) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13139}
    (hw : WINDOW (paperDesignP 13139) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13139 - 1))).real
      {v | sgA (paperDesignP 13139) c a v < √(2 / (13139 : ℝ) * mixtureFloor)}
      ∂muI 13139 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13139 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13139 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13139) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13139

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13139
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13139 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13139)
    (p : Ix 13139 × (Fin (13139 - 1) → ℝ)) :
    sgA (paperDesignP 13139) c p.1 p.2 ^ 2 ≤
      (2 / (13139 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13139).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13139) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13139 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13139 : ℝ) * _ ≤ 2 / 13139 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13139)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13139}
    (hw : WINDOW (paperDesignP 13139) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13139) c a v ^ 8
      ∂stdGauss (Fin (13139 - 1)) ∂muI 13139 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13139).prod (stdGauss (Fin (13139 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13139) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13139) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13139 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13139) c p.1 p.2)
      (√(2 / (13139 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13139)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13139 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13139) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13139}
    (hw : WINDOW (paperDesignP 13139) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13139) c a v -
      ∫ w, sA (paperDesignP 13139) c a w ∂stdGauss (Fin (13139 - 1))) ^ 2
      ∂stdGauss (Fin (13139 - 1))) ^ 2 ∂muI 13139 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13139) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13139

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13139
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13139}
    (hw : WINDOW (paperDesignP 13139) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13139).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13139) c M H xi)
    (hE : centreEnergy (paperDesignP 13139) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13139 : ℝ))))
    (hprice : massBound 13139 M H xi E u mixtureFloor ≤ 13139 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13139 - 1))).real
      {v | sgA (paperDesignP 13139) c a v < √(2 / (13139 : ℝ) * mixtureFloor)}
        ∂muI 13139 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13139).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13139) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13139) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13139)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13139

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13139
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13139) : ℝ :=
  (latitudeC / eR c) / ((13139 : ℝ) * (13139 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13139) / ((13139 : ℝ) * (13139 - 3))

theorem location_variance_on_event {c : Ret 13139}
    (hw : WINDOW (paperDesignP 13139) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13139) c a v - lbar (paperDesignP 13139) c a) ^ 2
      ∂stdGauss (Fin (13139 - 1))) ^ 2 ∂muI 13139 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13139)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13139}
    (hw : WINDOW (paperDesignP 13139) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13139) c a v - gbar (paperDesignP 13139) c a) ^ 2
      ∂stdGauss (Fin (13139 - 1))) ^ 2 ∂muI 13139 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13139)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13139}
    (hw : WINDOW (paperDesignP 13139) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13139 - 1))).real
      {v | sgA (paperDesignP 13139) c a v < √(2 / (13139 : ℝ) * mixtureFloor)}
      ∂muI 13139 ≤ lowMassBudget) :
    LatMom (paperDesignP 13139) c (√(2 / (13139 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13139

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13139
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13139} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13139 : ℝ) * (13139 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13139 : ℝ) * (13139 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13139 : ℝ) /
      ((13139 : ℝ) * (13139 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13139 : ℝ) * (13139 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13139 ≤ (2 * (16 / 5) / 13139 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13139} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (62638409 / 125000000000) ∧
    locationMomentBudget c 6 ≤ (123097731 / 200000000000) ∧
    locationMomentBudget c 12 ≤ (211121209 / 250000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4788948551 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (5882060929 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (4035258179 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13139} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30901053 / 1000000000000000) ∧ residualVarianceBudget ≤ (2822229 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13139 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4788948551 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13139

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13139
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13139 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13139) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13139) : ℝ :=
  exp (hqKappa * (13139 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5778413 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2889207 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13139} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (211121209 / 62500000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4035258179 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4035258179 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4035258179 / 125000000000000) : ℝ) / ((5778413 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22471509 / 1000000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13139} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1619284047 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((211121209 / 62500000000))) / ((5778413 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13139} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13139 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13139 * ((22471509 / 1000000000) : ℝ) ^ 2 / 2 + ((1619284047 / 1000000000)) ^ 2 * (1 + (22471509 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13139 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13139 * ((22471509 / 1000000000)) ^ 2 / 2 + ((1619284047 / 1000000000)) ^ 2 * (1 + (22471509 / 1000000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((5778413 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (348049487 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121138403523 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13139

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13140
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13140 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13140) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13140 : ℝ) * (13140 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13140) /
    ((13140 : ℝ) * (13140 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13140} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13140}
    (hw : WINDOW (paperDesignP 13140) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13140) c a v - lbar (paperDesignP 13140) c a| ^ (2 * q)
      ∂stdGauss (Fin (13140 - 1)) ∂muI 13140 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13140)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13140}
    (hw : WINDOW (paperDesignP 13140) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13140) c a v - gbar (paperDesignP 13140) c a| ^ (2 * q)
      ∂stdGauss (Fin (13140 - 1)) ∂muI 13140 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13140)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13140) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13140}
    (hw : WINDOW (paperDesignP 13140) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13140 - 1))).real
      {v | sgA (paperDesignP 13140) c a v < √(2 / (13140 : ℝ) * mixtureFloor)}
      ∂muI 13140 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13140 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13140 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13140) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13140

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13140
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13140 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13140)
    (p : Ix 13140 × (Fin (13140 - 1) → ℝ)) :
    sgA (paperDesignP 13140) c p.1 p.2 ^ 2 ≤
      (2 / (13140 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13140).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13140) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13140 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13140 : ℝ) * _ ≤ 2 / 13140 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13140)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13140}
    (hw : WINDOW (paperDesignP 13140) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13140) c a v ^ 8
      ∂stdGauss (Fin (13140 - 1)) ∂muI 13140 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13140).prod (stdGauss (Fin (13140 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13140) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13140) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13140 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13140) c p.1 p.2)
      (√(2 / (13140 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13140)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13140 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13140) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13140}
    (hw : WINDOW (paperDesignP 13140) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13140) c a v -
      ∫ w, sA (paperDesignP 13140) c a w ∂stdGauss (Fin (13140 - 1))) ^ 2
      ∂stdGauss (Fin (13140 - 1))) ^ 2 ∂muI 13140 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13140) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13140

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13140
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13140}
    (hw : WINDOW (paperDesignP 13140) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13140).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13140) c M H xi)
    (hE : centreEnergy (paperDesignP 13140) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13140 : ℝ))))
    (hprice : massBound 13140 M H xi E u mixtureFloor ≤ 13140 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13140 - 1))).real
      {v | sgA (paperDesignP 13140) c a v < √(2 / (13140 : ℝ) * mixtureFloor)}
        ∂muI 13140 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13140).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13140) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13140) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13140)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13140

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13140
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13140) : ℝ :=
  (latitudeC / eR c) / ((13140 : ℝ) * (13140 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13140) / ((13140 : ℝ) * (13140 - 3))

theorem location_variance_on_event {c : Ret 13140}
    (hw : WINDOW (paperDesignP 13140) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13140) c a v - lbar (paperDesignP 13140) c a) ^ 2
      ∂stdGauss (Fin (13140 - 1))) ^ 2 ∂muI 13140 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13140)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13140}
    (hw : WINDOW (paperDesignP 13140) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13140) c a v - gbar (paperDesignP 13140) c a) ^ 2
      ∂stdGauss (Fin (13140 - 1))) ^ 2 ∂muI 13140 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13140)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13140}
    (hw : WINDOW (paperDesignP 13140) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13140 - 1))).real
      {v | sgA (paperDesignP 13140) c a v < √(2 / (13140 : ℝ) * mixtureFloor)}
      ∂muI 13140 ≤ lowMassBudget) :
    LatMom (paperDesignP 13140) c (√(2 / (13140 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13140

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13140
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13140} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13140 : ℝ) * (13140 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13140 : ℝ) * (13140 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13140 : ℝ) /
      ((13140 : ℝ) * (13140 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13140 : ℝ) * (13140 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13140 ≤ (2 * (16 / 5) / 13140 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13140} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (501069123 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (615441791 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (844420507 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4788401753 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (1470347313 / 250000000000000) ∧
    residualMomentBudget 12 ≤ (4034797249 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13140} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (617927 / 20000000000000) ∧ residualVarianceBudget ≤ (564317 / 200000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13140 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4788401753 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13140

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13140
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13140 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13140) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13140) : ℝ :=
  exp (hqKappa * (13140 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5778193 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2889097 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13140} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (844420507 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4034797249 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4034797249 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4034797249 / 125000000000000) : ℝ) / ((5778193 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (5617447 / 250000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13140} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (323844469 / 200000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((844420507 / 250000000000))) / ((5778193 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13140} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13140 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13140 * ((5617447 / 250000000) : ℝ) ^ 2 / 2 + ((323844469 / 200000000)) ^ 2 * (1 + (5617447 / 250000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13140 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13140 * ((5617447 / 250000000)) ^ 2 / 2 + ((323844469 / 200000000)) ^ 2 * (1 + (5617447 / 250000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((5778193 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (5438478 / 15625) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (60573762839 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13140

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13141
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13141 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13141) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13141 : ℝ) * (13141 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13141) /
    ((13141 : ℝ) * (13141 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13141} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13141}
    (hw : WINDOW (paperDesignP 13141) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13141) c a v - lbar (paperDesignP 13141) c a| ^ (2 * q)
      ∂stdGauss (Fin (13141 - 1)) ∂muI 13141 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13141)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13141}
    (hw : WINDOW (paperDesignP 13141) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13141) c a v - gbar (paperDesignP 13141) c a| ^ (2 * q)
      ∂stdGauss (Fin (13141 - 1)) ∂muI 13141 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13141)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13141) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13141}
    (hw : WINDOW (paperDesignP 13141) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13141 - 1))).real
      {v | sgA (paperDesignP 13141) c a v < √(2 / (13141 : ℝ) * mixtureFloor)}
      ∂muI 13141 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13141 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13141 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13141) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13141

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13141
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13141 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13141)
    (p : Ix 13141 × (Fin (13141 - 1) → ℝ)) :
    sgA (paperDesignP 13141) c p.1 p.2 ^ 2 ≤
      (2 / (13141 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13141).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13141) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13141 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13141 : ℝ) * _ ≤ 2 / 13141 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13141)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13141}
    (hw : WINDOW (paperDesignP 13141) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13141) c a v ^ 8
      ∂stdGauss (Fin (13141 - 1)) ∂muI 13141 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13141).prod (stdGauss (Fin (13141 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13141) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13141) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13141 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13141) c p.1 p.2)
      (√(2 / (13141 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13141)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13141 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13141) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13141}
    (hw : WINDOW (paperDesignP 13141) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13141) c a v -
      ∫ w, sA (paperDesignP 13141) c a w ∂stdGauss (Fin (13141 - 1))) ^ 2
      ∂stdGauss (Fin (13141 - 1))) ^ 2 ∂muI 13141 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13141) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13141

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13141
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13141}
    (hw : WINDOW (paperDesignP 13141) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13141).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13141) c M H xi)
    (hE : centreEnergy (paperDesignP 13141) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13141 : ℝ))))
    (hprice : massBound 13141 M H xi E u mixtureFloor ≤ 13141 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13141 - 1))).real
      {v | sgA (paperDesignP 13141) c a v < √(2 / (13141 : ℝ) * mixtureFloor)}
        ∂muI 13141 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13141).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13141) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13141) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13141)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13141

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13141
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13141) : ℝ :=
  (latitudeC / eR c) / ((13141 : ℝ) * (13141 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13141) / ((13141 : ℝ) * (13141 - 3))

theorem location_variance_on_event {c : Ret 13141}
    (hw : WINDOW (paperDesignP 13141) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13141) c a v - lbar (paperDesignP 13141) c a) ^ 2
      ∂stdGauss (Fin (13141 - 1))) ^ 2 ∂muI 13141 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13141)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13141}
    (hw : WINDOW (paperDesignP 13141) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13141) c a v - gbar (paperDesignP 13141) c a) ^ 2
      ∂stdGauss (Fin (13141 - 1))) ^ 2 ∂muI 13141 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13141)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13141}
    (hw : WINDOW (paperDesignP 13141) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13141 - 1))).real
      {v | sgA (paperDesignP 13141) c a v < √(2 / (13141 : ℝ) * mixtureFloor)}
      ∂muI 13141 ≤ lowMassBudget) :
    LatMom (paperDesignP 13141) c (√(2 / (13141 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13141

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13141
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13141} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13141 : ℝ) * (13141 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13141 : ℝ) * (13141 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13141 : ℝ) /
      ((13141 : ℝ) * (13141 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13141 : ℝ) * (13141 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13141 ≤ (2 * (16 / 5) / 13141 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13141} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (501030979 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (307697467 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (844356187 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4787855059 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (2940358851 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (4034336407 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13141} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30891647 / 1000000000000000) ∧ residualVarianceBudget ≤ (2820941 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13141 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4787855059 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13141

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13141
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13141 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13141) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13141) : ℝ :=
  exp (hqKappa * (13141 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5777973 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2888987 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13141} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (844356187 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4034336407 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4034336407 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4034336407 / 125000000000000) : ℝ) / ((5777973 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (5617017 / 250000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13141} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (101197541 / 62500000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((844356187 / 250000000000))) / ((5777973 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13141} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13141 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13141 * ((5617017 / 250000000) : ℝ) ^ 2 / 2 + ((101197541 / 62500000)) ^ 2 * (1 + (5617017 / 250000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13141 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13141 * ((5617017 / 250000000)) ^ 2 / 2 + ((101197541 / 62500000)) ^ 2 * (1 + (5617017 / 250000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((5777973 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (348075697 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (30289162223 / 250000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13141

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13142
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13142 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13142) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13142 : ℝ) * (13142 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13142) /
    ((13142 : ℝ) * (13142 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13142} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13142}
    (hw : WINDOW (paperDesignP 13142) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13142) c a v - lbar (paperDesignP 13142) c a| ^ (2 * q)
      ∂stdGauss (Fin (13142 - 1)) ∂muI 13142 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13142)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13142}
    (hw : WINDOW (paperDesignP 13142) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13142) c a v - gbar (paperDesignP 13142) c a| ^ (2 * q)
      ∂stdGauss (Fin (13142 - 1)) ∂muI 13142 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13142)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13142) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13142}
    (hw : WINDOW (paperDesignP 13142) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13142 - 1))).real
      {v | sgA (paperDesignP 13142) c a v < √(2 / (13142 : ℝ) * mixtureFloor)}
      ∂muI 13142 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13142 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13142 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13142) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13142

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13142
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13142 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13142)
    (p : Ix 13142 × (Fin (13142 - 1) → ℝ)) :
    sgA (paperDesignP 13142) c p.1 p.2 ^ 2 ≤
      (2 / (13142 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13142).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13142) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13142 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13142 : ℝ) * _ ≤ 2 / 13142 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13142)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13142}
    (hw : WINDOW (paperDesignP 13142) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13142) c a v ^ 8
      ∂stdGauss (Fin (13142 - 1)) ∂muI 13142 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13142).prod (stdGauss (Fin (13142 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13142) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13142) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13142 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13142) c p.1 p.2)
      (√(2 / (13142 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13142)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13142 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13142) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13142}
    (hw : WINDOW (paperDesignP 13142) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13142) c a v -
      ∫ w, sA (paperDesignP 13142) c a w ∂stdGauss (Fin (13142 - 1))) ^ 2
      ∂stdGauss (Fin (13142 - 1))) ^ 2 ∂muI 13142 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13142) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13142

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13142
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13142}
    (hw : WINDOW (paperDesignP 13142) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13142).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13142) c M H xi)
    (hE : centreEnergy (paperDesignP 13142) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13142 : ℝ))))
    (hprice : massBound 13142 M H xi E u mixtureFloor ≤ 13142 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13142 - 1))).real
      {v | sgA (paperDesignP 13142) c a v < √(2 / (13142 : ℝ) * mixtureFloor)}
        ∂muI 13142 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13142).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13142) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13142) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13142)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13142

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13142
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13142) : ℝ :=
  (latitudeC / eR c) / ((13142 : ℝ) * (13142 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13142) / ((13142 : ℝ) * (13142 - 3))

theorem location_variance_on_event {c : Ret 13142}
    (hw : WINDOW (paperDesignP 13142) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13142) c a v - lbar (paperDesignP 13142) c a) ^ 2
      ∂stdGauss (Fin (13142 - 1))) ^ 2 ∂muI 13142 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13142)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13142}
    (hw : WINDOW (paperDesignP 13142) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13142) c a v - gbar (paperDesignP 13142) c a) ^ 2
      ∂stdGauss (Fin (13142 - 1))) ^ 2 ∂muI 13142 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13142)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13142}
    (hw : WINDOW (paperDesignP 13142) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13142 - 1))).real
      {v | sgA (paperDesignP 13142) c a v < √(2 / (13142 : ℝ) * mixtureFloor)}
      ∂muI 13142 ≤ lowMassBudget) :
    LatMom (paperDesignP 13142) c (√(2 / (13142 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13142

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13142
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13142} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13142 : ℝ) * (13142 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13142 : ℝ) * (13142 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13142 : ℝ) /
      ((13142 : ℝ) * (13142 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13142 : ℝ) * (13142 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13142 ≤ (2 * (16 / 5) / 13142 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13142} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (250496421 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (123069617 / 200000000000) ∧
    locationMomentBudget c 12 ≤ (844291877 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4787308469 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (5880046281 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (1613550261 / 200000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13142} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (6177389 / 200000000000000) ∧ residualVarianceBudget ≤ (2820297 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13142 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4787308469 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13142

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13142
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13142 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13142) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13142) : ℝ :=
  exp (hqKappa * (13142 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5777753 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2888877 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13142} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (844291877 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (1613550261 / 50000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (1613550261 / 50000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((1613550261 / 50000000000000) : ℝ) / ((5777753 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (5616587 / 250000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13142} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (809549491 / 500000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((844291877 / 250000000000))) / ((5777753 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13142} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13142 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13142 * ((5616587 / 250000000) : ℝ) ^ 2 / 2 + ((809549491 / 500000000)) ^ 2 * (1 + (5616587 / 250000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13142 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13142 * ((5616587 / 250000000)) ^ 2 / 2 + ((809549491 / 500000000)) ^ 2 * (1 + (5616587 / 250000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((5777753 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (87022201 / 250000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (60582886583 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13142

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13143
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13143 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13143) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13143 : ℝ) * (13143 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13143) /
    ((13143 : ℝ) * (13143 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13143} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13143}
    (hw : WINDOW (paperDesignP 13143) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13143) c a v - lbar (paperDesignP 13143) c a| ^ (2 * q)
      ∂stdGauss (Fin (13143 - 1)) ∂muI 13143 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13143)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13143}
    (hw : WINDOW (paperDesignP 13143) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13143) c a v - gbar (paperDesignP 13143) c a| ^ (2 * q)
      ∂stdGauss (Fin (13143 - 1)) ∂muI 13143 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13143)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13143) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13143}
    (hw : WINDOW (paperDesignP 13143) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13143 - 1))).real
      {v | sgA (paperDesignP 13143) c a v < √(2 / (13143 : ℝ) * mixtureFloor)}
      ∂muI 13143 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13143 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13143 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13143) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13143

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13143
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13143 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13143)
    (p : Ix 13143 × (Fin (13143 - 1) → ℝ)) :
    sgA (paperDesignP 13143) c p.1 p.2 ^ 2 ≤
      (2 / (13143 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13143).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13143) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13143 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13143 : ℝ) * _ ≤ 2 / 13143 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13143)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13143}
    (hw : WINDOW (paperDesignP 13143) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13143) c a v ^ 8
      ∂stdGauss (Fin (13143 - 1)) ∂muI 13143 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13143).prod (stdGauss (Fin (13143 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13143) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13143) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13143 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13143) c p.1 p.2)
      (√(2 / (13143 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13143)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13143 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13143) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13143}
    (hw : WINDOW (paperDesignP 13143) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13143) c a v -
      ∫ w, sA (paperDesignP 13143) c a w ∂stdGauss (Fin (13143 - 1))) ^ 2
      ∂stdGauss (Fin (13143 - 1))) ^ 2 ∂muI 13143 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13143) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13143

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13143
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13143}
    (hw : WINDOW (paperDesignP 13143) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13143).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13143) c M H xi)
    (hE : centreEnergy (paperDesignP 13143) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13143 : ℝ))))
    (hprice : massBound 13143 M H xi E u mixtureFloor ≤ 13143 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13143 - 1))).real
      {v | sgA (paperDesignP 13143) c a v < √(2 / (13143 : ℝ) * mixtureFloor)}
        ∂muI 13143 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13143).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13143) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13143) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13143)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13143

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13143
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13143) : ℝ :=
  (latitudeC / eR c) / ((13143 : ℝ) * (13143 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13143) / ((13143 : ℝ) * (13143 - 3))

theorem location_variance_on_event {c : Ret 13143}
    (hw : WINDOW (paperDesignP 13143) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13143) c a v - lbar (paperDesignP 13143) c a) ^ 2
      ∂stdGauss (Fin (13143 - 1))) ^ 2 ∂muI 13143 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13143)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13143}
    (hw : WINDOW (paperDesignP 13143) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13143) c a v - gbar (paperDesignP 13143) c a) ^ 2
      ∂stdGauss (Fin (13143 - 1))) ^ 2 ∂muI 13143 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13143)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13143}
    (hw : WINDOW (paperDesignP 13143) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13143 - 1))).real
      {v | sgA (paperDesignP 13143) c a v < √(2 / (13143 : ℝ) * mixtureFloor)}
      ∂muI 13143 ≤ lowMassBudget) :
    LatMom (paperDesignP 13143) c (√(2 / (13143 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13143

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13143
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13143} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13143 : ℝ) * (13143 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13143 : ℝ) * (13143 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13143 : ℝ) /
      ((13143 : ℝ) * (13143 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13143 : ℝ) * (13143 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13143 ≤ (2 * (16 / 5) / 13143 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13143} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (50095471 / 100000000000) ∧
    locationMomentBudget c 6 ≤ (307650621 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (844227577 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4786761983 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (5879374987 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (2016707493 / 250000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13143} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (6176449 / 200000000000000) ∧ residualVarianceBudget ≤ (2819653 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13143 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4786761983 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13143

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13143
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13143 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13143) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13143) : ℝ :=
  exp (hqKappa * (13143 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5777533 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2888767 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13143} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (844227577 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (2016707493 / 62500000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (2016707493 / 62500000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((2016707493 / 62500000000000) : ℝ) / ((5777533 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (5616157 / 250000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13143} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (809518661 / 500000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((844227577 / 250000000000))) / ((5777533 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13143} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13143 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13143 * ((5616157 / 250000000) : ℝ) ^ 2 / 2 + ((809518661 / 500000000)) ^ 2 * (1 + (5616157 / 250000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13143 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13143 * ((5616157 / 250000000)) ^ 2 / 2 + ((809518661 / 500000000)) ^ 2 * (1 + (5616157 / 250000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((5777533 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (348101911 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (242349797 / 2000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13143

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13144
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13144 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13144) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13144 : ℝ) * (13144 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13144) /
    ((13144 : ℝ) * (13144 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13144} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13144}
    (hw : WINDOW (paperDesignP 13144) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13144) c a v - lbar (paperDesignP 13144) c a| ^ (2 * q)
      ∂stdGauss (Fin (13144 - 1)) ∂muI 13144 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13144)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13144}
    (hw : WINDOW (paperDesignP 13144) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13144) c a v - gbar (paperDesignP 13144) c a| ^ (2 * q)
      ∂stdGauss (Fin (13144 - 1)) ∂muI 13144 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13144)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13144) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13144}
    (hw : WINDOW (paperDesignP 13144) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13144 - 1))).real
      {v | sgA (paperDesignP 13144) c a v < √(2 / (13144 : ℝ) * mixtureFloor)}
      ∂muI 13144 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13144 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13144 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13144) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13144

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13144
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13144 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13144)
    (p : Ix 13144 × (Fin (13144 - 1) → ℝ)) :
    sgA (paperDesignP 13144) c p.1 p.2 ^ 2 ≤
      (2 / (13144 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13144).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13144) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13144 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13144 : ℝ) * _ ≤ 2 / 13144 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13144)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13144}
    (hw : WINDOW (paperDesignP 13144) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13144) c a v ^ 8
      ∂stdGauss (Fin (13144 - 1)) ∂muI 13144 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13144).prod (stdGauss (Fin (13144 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13144) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13144) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13144 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13144) c p.1 p.2)
      (√(2 / (13144 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13144)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13144 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13144) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13144}
    (hw : WINDOW (paperDesignP 13144) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13144) c a v -
      ∫ w, sA (paperDesignP 13144) c a w ∂stdGauss (Fin (13144 - 1))) ^ 2
      ∂stdGauss (Fin (13144 - 1))) ^ 2 ∂muI 13144 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13144) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13144

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13144
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13144}
    (hw : WINDOW (paperDesignP 13144) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13144).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13144) c M H xi)
    (hE : centreEnergy (paperDesignP 13144) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13144 : ℝ))))
    (hprice : massBound 13144 M H xi E u mixtureFloor ≤ 13144 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13144 - 1))).real
      {v | sgA (paperDesignP 13144) c a v < √(2 / (13144 : ℝ) * mixtureFloor)}
        ∂muI 13144 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13144).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13144) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13144) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13144)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13144

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13144
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13144) : ℝ :=
  (latitudeC / eR c) / ((13144 : ℝ) * (13144 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13144) / ((13144 : ℝ) * (13144 - 3))

theorem location_variance_on_event {c : Ret 13144}
    (hw : WINDOW (paperDesignP 13144) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13144) c a v - lbar (paperDesignP 13144) c a) ^ 2
      ∂stdGauss (Fin (13144 - 1))) ^ 2 ∂muI 13144 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13144)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13144}
    (hw : WINDOW (paperDesignP 13144) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13144) c a v - gbar (paperDesignP 13144) c a) ^ 2
      ∂stdGauss (Fin (13144 - 1))) ^ 2 ∂muI 13144 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13144)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13144}
    (hw : WINDOW (paperDesignP 13144) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13144 - 1))).real
      {v | sgA (paperDesignP 13144) c a v < √(2 / (13144 : ℝ) * mixtureFloor)}
      ∂muI 13144 ≤ lowMassBudget) :
    LatMom (paperDesignP 13144) c (√(2 / (13144 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13144

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13144
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13144} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13144 : ℝ) * (13144 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13144 : ℝ) * (13144 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13144 : ℝ) /
      ((13144 : ℝ) * (13144 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13144 : ℝ) * (13144 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13144 ≤ (2 * (16 / 5) / 13144 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13144} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (62614573 / 125000000000) ∧
    locationMomentBudget c 6 ≤ (307627203 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (844163287 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4786215601 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (5878703821 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (4032954407 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13144} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (6175509 / 200000000000000) ∧ residualVarianceBudget ≤ (2819009 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13144 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4786215601 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13144

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13144
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13144 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13144) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13144) : ℝ :=
  exp (hqKappa * (13144 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((2888657 / 500000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (1155463 / 200000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13144} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (844163287 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4032954407 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4032954407 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4032954407 / 125000000000000) : ℝ) / ((2888657 / 500000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (4492581 / 200000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13144} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (404743849 / 250000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((844163287 / 250000000000))) / ((2888657 / 500000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13144} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13144 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13144 * ((4492581 / 200000000) : ℝ) ^ 2 / 2 + ((404743849 / 250000000)) ^ 2 * (1 + (4492581 / 200000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13144 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13144 * ((4492581 / 200000000)) ^ 2 / 2 + ((404743849 / 250000000)) ^ 2 * (1 + (4492581 / 200000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((2888657 / 500000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (348114959 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121183982709 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13144

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13145
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13145 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13145) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13145 : ℝ) * (13145 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13145) /
    ((13145 : ℝ) * (13145 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13145} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13145}
    (hw : WINDOW (paperDesignP 13145) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13145) c a v - lbar (paperDesignP 13145) c a| ^ (2 * q)
      ∂stdGauss (Fin (13145 - 1)) ∂muI 13145 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13145)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13145}
    (hw : WINDOW (paperDesignP 13145) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13145) c a v - gbar (paperDesignP 13145) c a| ^ (2 * q)
      ∂stdGauss (Fin (13145 - 1)) ∂muI 13145 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13145)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13145) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13145}
    (hw : WINDOW (paperDesignP 13145) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13145 - 1))).real
      {v | sgA (paperDesignP 13145) c a v < √(2 / (13145 : ℝ) * mixtureFloor)}
      ∂muI 13145 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13145 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13145 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13145) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13145

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13145
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13145 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13145)
    (p : Ix 13145 × (Fin (13145 - 1) → ℝ)) :
    sgA (paperDesignP 13145) c p.1 p.2 ^ 2 ≤
      (2 / (13145 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13145).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13145) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13145 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13145 : ℝ) * _ ≤ 2 / 13145 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13145)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13145}
    (hw : WINDOW (paperDesignP 13145) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13145) c a v ^ 8
      ∂stdGauss (Fin (13145 - 1)) ∂muI 13145 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13145).prod (stdGauss (Fin (13145 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13145) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13145) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13145 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13145) c p.1 p.2)
      (√(2 / (13145 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13145)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13145 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13145) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13145}
    (hw : WINDOW (paperDesignP 13145) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13145) c a v -
      ∫ w, sA (paperDesignP 13145) c a w ∂stdGauss (Fin (13145 - 1))) ^ 2
      ∂stdGauss (Fin (13145 - 1))) ^ 2 ∂muI 13145 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13145) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13145

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13145
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13145}
    (hw : WINDOW (paperDesignP 13145) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13145).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13145) c M H xi)
    (hE : centreEnergy (paperDesignP 13145) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13145 : ℝ))))
    (hprice : massBound 13145 M H xi E u mixtureFloor ≤ 13145 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13145 - 1))).real
      {v | sgA (paperDesignP 13145) c a v < √(2 / (13145 : ℝ) * mixtureFloor)}
        ∂muI 13145 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13145).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13145) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13145) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13145)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13145

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13145
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13145) : ℝ :=
  (latitudeC / eR c) / ((13145 : ℝ) * (13145 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13145) / ((13145 : ℝ) * (13145 - 3))

theorem location_variance_on_event {c : Ret 13145}
    (hw : WINDOW (paperDesignP 13145) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13145) c a v - lbar (paperDesignP 13145) c a) ^ 2
      ∂stdGauss (Fin (13145 - 1))) ^ 2 ∂muI 13145 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13145)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13145}
    (hw : WINDOW (paperDesignP 13145) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13145) c a v - gbar (paperDesignP 13145) c a) ^ 2
      ∂stdGauss (Fin (13145 - 1))) ^ 2 ∂muI 13145 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13145)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13145}
    (hw : WINDOW (paperDesignP 13145) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13145 - 1))).real
      {v | sgA (paperDesignP 13145) c a v < √(2 / (13145 : ℝ) * mixtureFloor)}
      ∂muI 13145 ≤ lowMassBudget) :
    LatMom (paperDesignP 13145) c (√(2 / (13145 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13145

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13145
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13145} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13145 : ℝ) * (13145 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13145 : ℝ) * (13145 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13145 : ℝ) /
      ((13145 : ℝ) * (13145 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13145 : ℝ) * (13145 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13145 ≤ (2 * (16 / 5) / 13145 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13145} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (3913113 / 7812500000) ∧
    locationMomentBudget c 6 ≤ (307603789 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (422049503 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4785669323 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (5878032783 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (8064987831 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13145} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30872847 / 1000000000000000) ∧ residualVarianceBudget ≤ (1409183 / 500000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13145 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4785669323 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13145

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13145
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13145 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13145) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13145) : ℝ :=
  exp (hqKappa * (13145 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((2888547 / 500000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (1155419 / 200000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13145} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (422049503 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8064987831 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8064987831 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8064987831 / 250000000000000) : ℝ) / ((2888547 / 500000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11230593 / 500000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13145} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1618913763 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((422049503 / 125000000000))) / ((2888547 / 500000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13145} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13145 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13145 * ((11230593 / 500000000) : ℝ) ^ 2 / 2 + ((1618913763 / 1000000000)) ^ 2 * (1 + (11230593 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13145 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13145 * ((11230593 / 500000000)) ^ 2 / 2 + ((1618913763 / 1000000000)) ^ 2 * (1 + (11230593 / 500000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((2888547 / 500000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (348128069 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121193110159 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13145

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13146
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13146 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13146) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13146 : ℝ) * (13146 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13146) /
    ((13146 : ℝ) * (13146 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13146} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13146}
    (hw : WINDOW (paperDesignP 13146) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13146) c a v - lbar (paperDesignP 13146) c a| ^ (2 * q)
      ∂stdGauss (Fin (13146 - 1)) ∂muI 13146 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13146)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13146}
    (hw : WINDOW (paperDesignP 13146) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13146) c a v - gbar (paperDesignP 13146) c a| ^ (2 * q)
      ∂stdGauss (Fin (13146 - 1)) ∂muI 13146 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13146)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13146) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13146}
    (hw : WINDOW (paperDesignP 13146) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13146 - 1))).real
      {v | sgA (paperDesignP 13146) c a v < √(2 / (13146 : ℝ) * mixtureFloor)}
      ∂muI 13146 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13146 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13146 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13146) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13146

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13146
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13146 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13146)
    (p : Ix 13146 × (Fin (13146 - 1) → ℝ)) :
    sgA (paperDesignP 13146) c p.1 p.2 ^ 2 ≤
      (2 / (13146 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13146).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13146) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13146 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13146 : ℝ) * _ ≤ 2 / 13146 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13146)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13146}
    (hw : WINDOW (paperDesignP 13146) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13146) c a v ^ 8
      ∂stdGauss (Fin (13146 - 1)) ∂muI 13146 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13146).prod (stdGauss (Fin (13146 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13146) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13146) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13146 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13146) c p.1 p.2)
      (√(2 / (13146 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13146)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13146 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13146) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13146}
    (hw : WINDOW (paperDesignP 13146) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13146) c a v -
      ∫ w, sA (paperDesignP 13146) c a w ∂stdGauss (Fin (13146 - 1))) ^ 2
      ∂stdGauss (Fin (13146 - 1))) ^ 2 ∂muI 13146 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13146) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13146

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13146
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13146}
    (hw : WINDOW (paperDesignP 13146) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13146).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13146) c M H xi)
    (hE : centreEnergy (paperDesignP 13146) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13146 : ℝ))))
    (hprice : massBound 13146 M H xi E u mixtureFloor ≤ 13146 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13146 - 1))).real
      {v | sgA (paperDesignP 13146) c a v < √(2 / (13146 : ℝ) * mixtureFloor)}
        ∂muI 13146 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13146).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13146) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13146) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13146)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13146

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13146
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13146) : ℝ :=
  (latitudeC / eR c) / ((13146 : ℝ) * (13146 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13146) / ((13146 : ℝ) * (13146 - 3))

theorem location_variance_on_event {c : Ret 13146}
    (hw : WINDOW (paperDesignP 13146) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13146) c a v - lbar (paperDesignP 13146) c a) ^ 2
      ∂stdGauss (Fin (13146 - 1))) ^ 2 ∂muI 13146 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13146)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13146}
    (hw : WINDOW (paperDesignP 13146) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13146) c a v - gbar (paperDesignP 13146) c a) ^ 2
      ∂stdGauss (Fin (13146 - 1))) ^ 2 ∂muI 13146 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13146)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13146}
    (hw : WINDOW (paperDesignP 13146) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13146 - 1))).real
      {v | sgA (paperDesignP 13146) c a v < √(2 / (13146 : ℝ) * mixtureFloor)}
      ∂muI 13146 ≤ lowMassBudget) :
    LatMom (paperDesignP 13146) c (√(2 / (13146 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13146

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13146
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13146} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13146 : ℝ) * (13146 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13146 : ℝ) * (13146 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13146 : ℝ) /
      ((13146 : ℝ) * (13146 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13146 : ℝ) * (13146 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13146 ≤ (2 * (16 / 5) / 13146 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13146} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (10016807 / 20000000000) ∧
    locationMomentBudget c 6 ≤ (615160757 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (168806947 / 200000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4785123149 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (5877361873 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (504004189 / 62500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13146} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (617363 / 20000000000000) ∧ residualVarianceBudget ≤ (2817723 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13146 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4785123149 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13146

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13146
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13146 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13146) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13146) : ℝ :=
  exp (hqKappa * (13146 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((2888437 / 500000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (9243 / 1600000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13146} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (168806947 / 50000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (504004189 / 15625000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (504004189 / 15625000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((504004189 / 15625000000000) : ℝ) / ((2888437 / 500000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22459467 / 1000000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13146} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (323770429 / 200000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((168806947 / 50000000000))) / ((2888437 / 500000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13146} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13146 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13146 * ((22459467 / 1000000000) : ℝ) ^ 2 / 2 + ((323770429 / 200000000)) ^ 2 * (1 + (22459467 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13146 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13146 * ((22459467 / 1000000000)) ^ 2 / 2 + ((323770429 / 200000000)) ^ 2 * (1 + (22459467 / 1000000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((2888437 / 500000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (348141179 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121202238669 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13146

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13147
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13147 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13147) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13147 : ℝ) * (13147 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13147) /
    ((13147 : ℝ) * (13147 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13147} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13147}
    (hw : WINDOW (paperDesignP 13147) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13147) c a v - lbar (paperDesignP 13147) c a| ^ (2 * q)
      ∂stdGauss (Fin (13147 - 1)) ∂muI 13147 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13147)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13147}
    (hw : WINDOW (paperDesignP 13147) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13147) c a v - gbar (paperDesignP 13147) c a| ^ (2 * q)
      ∂stdGauss (Fin (13147 - 1)) ∂muI 13147 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13147)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13147) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13147}
    (hw : WINDOW (paperDesignP 13147) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13147 - 1))).real
      {v | sgA (paperDesignP 13147) c a v < √(2 / (13147 : ℝ) * mixtureFloor)}
      ∂muI 13147 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13147 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13147 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13147) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13147

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13147
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13147 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13147)
    (p : Ix 13147 × (Fin (13147 - 1) → ℝ)) :
    sgA (paperDesignP 13147) c p.1 p.2 ^ 2 ≤
      (2 / (13147 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13147).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13147) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13147 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13147 : ℝ) * _ ≤ 2 / 13147 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13147)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13147}
    (hw : WINDOW (paperDesignP 13147) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13147) c a v ^ 8
      ∂stdGauss (Fin (13147 - 1)) ∂muI 13147 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13147).prod (stdGauss (Fin (13147 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13147) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13147) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13147 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13147) c p.1 p.2)
      (√(2 / (13147 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13147)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13147 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13147) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13147}
    (hw : WINDOW (paperDesignP 13147) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13147) c a v -
      ∫ w, sA (paperDesignP 13147) c a w ∂stdGauss (Fin (13147 - 1))) ^ 2
      ∂stdGauss (Fin (13147 - 1))) ^ 2 ∂muI 13147 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13147) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13147

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13147
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13147}
    (hw : WINDOW (paperDesignP 13147) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13147).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13147) c M H xi)
    (hE : centreEnergy (paperDesignP 13147) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13147 : ℝ))))
    (hprice : massBound 13147 M H xi E u mixtureFloor ≤ 13147 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13147 - 1))).real
      {v | sgA (paperDesignP 13147) c a v < √(2 / (13147 : ℝ) * mixtureFloor)}
        ∂muI 13147 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13147).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13147) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13147) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13147)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13147

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13147
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13147) : ℝ :=
  (latitudeC / eR c) / ((13147 : ℝ) * (13147 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13147) / ((13147 : ℝ) * (13147 - 3))

theorem location_variance_on_event {c : Ret 13147}
    (hw : WINDOW (paperDesignP 13147) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13147) c a v - lbar (paperDesignP 13147) c a) ^ 2
      ∂stdGauss (Fin (13147 - 1))) ^ 2 ∂muI 13147 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13147)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13147}
    (hw : WINDOW (paperDesignP 13147) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13147) c a v - gbar (paperDesignP 13147) c a) ^ 2
      ∂stdGauss (Fin (13147 - 1))) ^ 2 ∂muI 13147 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13147)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13147}
    (hw : WINDOW (paperDesignP 13147) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13147 - 1))).real
      {v | sgA (paperDesignP 13147) c a v < √(2 / (13147 : ℝ) * mixtureFloor)}
      ∂muI 13147 ≤ lowMassBudget) :
    LatMom (paperDesignP 13147) c (√(2 / (13147 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13147

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13147
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13147} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13147 : ℝ) * (13147 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13147 : ℝ) * (13147 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13147 : ℝ) /
      ((13147 : ℝ) * (13147 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13147 : ℝ) * (13147 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13147 ≤ (2 * (16 / 5) / 13147 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13147} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (250401121 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (615113943 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (421985237 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2392288539 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (587669109 / 100000000000000) ∧
    residualMomentBudget 12 ≤ (8063146391 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13147} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15431727 / 500000000000000) ∧ residualVarianceBudget ≤ (70427 / 25000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13147 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2392288539 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13147

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13147
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13147 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13147) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13147) : ℝ :=
  exp (hqKappa * (13147 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((2888327 / 500000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (1155331 / 200000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13147} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (421985237 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8063146391 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8063146391 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8063146391 / 250000000000000) : ℝ) / ((2888327 / 500000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22457749 / 1000000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13147} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1618790541 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((421985237 / 125000000000))) / ((2888327 / 500000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13147} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13147 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13147 * ((22457749 / 1000000000) : ℝ) ^ 2 / 2 + ((1618790541 / 1000000000)) ^ 2 * (1 + (22457749 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13147 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13147 * ((22457749 / 1000000000)) ^ 2 / 2 + ((1618790541 / 1000000000)) ^ 2 * (1 + (22457749 / 1000000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((2888327 / 500000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (348154291 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121211368239 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13147

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13148
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13148 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13148) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13148 : ℝ) * (13148 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13148) /
    ((13148 : ℝ) * (13148 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13148} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13148}
    (hw : WINDOW (paperDesignP 13148) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13148) c a v - lbar (paperDesignP 13148) c a| ^ (2 * q)
      ∂stdGauss (Fin (13148 - 1)) ∂muI 13148 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13148)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13148}
    (hw : WINDOW (paperDesignP 13148) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13148) c a v - gbar (paperDesignP 13148) c a| ^ (2 * q)
      ∂stdGauss (Fin (13148 - 1)) ∂muI 13148 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13148)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13148) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13148}
    (hw : WINDOW (paperDesignP 13148) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13148 - 1))).real
      {v | sgA (paperDesignP 13148) c a v < √(2 / (13148 : ℝ) * mixtureFloor)}
      ∂muI 13148 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13148 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13148 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13148) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13148

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13148
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13148 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13148)
    (p : Ix 13148 × (Fin (13148 - 1) → ℝ)) :
    sgA (paperDesignP 13148) c p.1 p.2 ^ 2 ≤
      (2 / (13148 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13148).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13148) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13148 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13148 : ℝ) * _ ≤ 2 / 13148 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13148)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13148}
    (hw : WINDOW (paperDesignP 13148) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13148) c a v ^ 8
      ∂stdGauss (Fin (13148 - 1)) ∂muI 13148 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13148).prod (stdGauss (Fin (13148 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13148) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13148) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13148 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13148) c p.1 p.2)
      (√(2 / (13148 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13148)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13148 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13148) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13148}
    (hw : WINDOW (paperDesignP 13148) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13148) c a v -
      ∫ w, sA (paperDesignP 13148) c a w ∂stdGauss (Fin (13148 - 1))) ^ 2
      ∂stdGauss (Fin (13148 - 1))) ^ 2 ∂muI 13148 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13148) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13148

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13148
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13148}
    (hw : WINDOW (paperDesignP 13148) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13148).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13148) c M H xi)
    (hE : centreEnergy (paperDesignP 13148) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13148 : ℝ))))
    (hprice : massBound 13148 M H xi E u mixtureFloor ≤ 13148 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13148 - 1))).real
      {v | sgA (paperDesignP 13148) c a v < √(2 / (13148 : ℝ) * mixtureFloor)}
        ∂muI 13148 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13148).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13148) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13148) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13148)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13148

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13148
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13148) : ℝ :=
  (latitudeC / eR c) / ((13148 : ℝ) * (13148 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13148) / ((13148 : ℝ) * (13148 - 3))

theorem location_variance_on_event {c : Ret 13148}
    (hw : WINDOW (paperDesignP 13148) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13148) c a v - lbar (paperDesignP 13148) c a) ^ 2
      ∂stdGauss (Fin (13148 - 1))) ^ 2 ∂muI 13148 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13148)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13148}
    (hw : WINDOW (paperDesignP 13148) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13148) c a v - gbar (paperDesignP 13148) c a) ^ 2
      ∂stdGauss (Fin (13148 - 1))) ^ 2 ∂muI 13148 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13148)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13148}
    (hw : WINDOW (paperDesignP 13148) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13148 - 1))).real
      {v | sgA (paperDesignP 13148) c a v < √(2 / (13148 : ℝ) * mixtureFloor)}
      ∂muI 13148 ≤ lowMassBudget) :
    LatMom (paperDesignP 13148) c (√(2 / (13148 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13148

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13148
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13148} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13148 : ℝ) * (13148 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13148 : ℝ) * (13148 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13148 : ℝ) /
      ((13148 : ℝ) * (13148 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13148 : ℝ) * (13148 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13148 ≤ (2 * (16 / 5) / 13148 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13148} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (500764139 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (1201303 / 1953125000) ∧
    locationMomentBudget c 12 ≤ (843906223 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (598003889 / 125000000000000) ∧
    residualMomentBudget 6 ≤ (2938010217 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (4031112967 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13148} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15429379 / 500000000000000) ∧ residualVarianceBudget ≤ (2816437 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13148 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((598003889 / 125000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13148

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13148
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13148 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13148) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13148) : ℝ :=
  exp (hqKappa * (13148 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((1155287 / 200000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (1444109 / 250000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13148} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (843906223 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4031112967 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4031112967 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4031112967 / 125000000000000) : ℝ) / ((1155287 / 200000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22456027 / 1000000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13148} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (50585271 / 31250000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((843906223 / 250000000000))) / ((1155287 / 200000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13148} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13148 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13148 * ((22456027 / 1000000000) : ℝ) ^ 2 / 2 + ((50585271 / 31250000)) ^ 2 * (1 + (22456027 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13148 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13148 * ((22456027 / 1000000000)) ^ 2 / 2 + ((50585271 / 31250000)) ^ 2 * (1 + (22456027 / 1000000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((1155287 / 200000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (348167343 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121220456667 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13148

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13149
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13149 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13149) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13149 : ℝ) * (13149 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13149) /
    ((13149 : ℝ) * (13149 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13149} (he : 0 < eR c)
    {q : ℕ} (hq : q ≤ 12) : 0 < locationMomentBudget c q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold locationMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (div_pos hC he)
    (mul_pos (by norm_num) (by linarith))))

theorem residualMomentBudget_pos {q : ℕ} (hq : q ≤ 12) :
    0 < residualMomentBudget q := by
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  unfold residualMomentBudget
  exact mul_pos (rotation_positive q) (sqrt_pos.mpr (div_pos (by positivity)
    (mul_pos (by norm_num) (by linarith))))

theorem location_moment_on_event {c : Ret 13149}
    (hw : WINDOW (paperDesignP 13149) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13149) c a v - lbar (paperDesignP 13149) c a| ^ (2 * q)
      ∂stdGauss (Fin (13149 - 1)) ∂muI 13149 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13149)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13149}
    (hw : WINDOW (paperDesignP 13149) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13149) c a v - gbar (paperDesignP 13149) c a| ^ (2 * q)
      ∂stdGauss (Fin (13149 - 1)) ∂muI 13149 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13149)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13149) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13149}
    (hw : WINDOW (paperDesignP 13149) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13149 - 1))).real
      {v | sgA (paperDesignP 13149) c a v < √(2 / (13149 : ℝ) * mixtureFloor)}
      ∂muI 13149 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13149 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13149 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13149) c
    (show 0 < splitLocationWidth c from mul_pos (by norm_num) hl)
    (show 0 < splitResidualWidth from mul_pos (by norm_num) hs) 24
    (location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num))
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)) hmass
  have hratl : locationMomentBudget c 12 / splitLocationWidth c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : residualMomentBudget 12 / splitResidualWidth = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  apply h.trans
  rw [Bpap, hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta]

end BstLean.Part266.Row13149

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13149
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13149 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13149)
    (p : Ix 13149 × (Fin (13149 - 1) → ℝ)) :
    sgA (paperDesignP 13149) c p.1 p.2 ^ 2 ≤
      (2 / (13149 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13149).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13149) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13149 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13149 : ℝ) * _ ≤ 2 / 13149 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13149)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13149}
    (hw : WINDOW (paperDesignP 13149) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13149) c a v ^ 8
      ∂stdGauss (Fin (13149 - 1)) ∂muI 13149 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13149).prod (stdGauss (Fin (13149 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13149) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13149) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13149 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13149) c p.1 p.2)
      (√(2 / (13149 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13149)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13149 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13149) c p.1 p.2) fullResidualBudget := by
    refine ⟨hs.measurable, by unfold fullResidualBudget locationNorm; positivity,
      hs.bound.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    apply mul_le_mul_of_nonneg_left _ (sqrt_nonneg _)
    have he := energy_allowance_row
    unfold locationNorm
    linarith
  have hp := (hs'.toMoment (by norm_num : (8 : ℕ) ≠ 0)).power (k := 2) (r := 4)
  have hh := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0) hp).squareIntegral
  simp only [← pow_mul] at hh
  rw [integral_prod _ hh.1] at hh
  exact hh.2

noncomputable def scaleVarianceBudget : ℝ :=
  4 * residualMomentBudget 4 ^ 2 * fullResidualBudget ^ 2

theorem scale_variance_on_event {c : Ret 13149}
    (hw : WINDOW (paperDesignP 13149) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13149) c a v -
      ∫ w, sA (paperDesignP 13149) c a w ∂stdGauss (Fin (13149 - 1))) ^ 2
      ∂stdGauss (Fin (13149 - 1))) ^ 2 ∂muI 13149 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13149) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13149

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13149
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13149}
    (hw : WINDOW (paperDesignP 13149) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13149).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13149) c M H xi)
    (hE : centreEnergy (paperDesignP 13149) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13149 : ℝ))))
    (hprice : massBound 13149 M H xi E u mixtureFloor ≤ 13149 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13149 - 1))).real
      {v | sgA (paperDesignP 13149) c a v < √(2 / (13149 : ℝ) * mixtureFloor)}
        ∂muI 13149 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13149).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13149) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13149) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13149)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13149

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13149
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13149) : ℝ :=
  (latitudeC / eR c) / ((13149 : ℝ) * (13149 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13149) / ((13149 : ℝ) * (13149 - 3))

theorem location_variance_on_event {c : Ret 13149}
    (hw : WINDOW (paperDesignP 13149) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13149) c a v - lbar (paperDesignP 13149) c a) ^ 2
      ∂stdGauss (Fin (13149 - 1))) ^ 2 ∂muI 13149 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13149)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13149}
    (hw : WINDOW (paperDesignP 13149) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13149) c a v - gbar (paperDesignP 13149) c a) ^ 2
      ∂stdGauss (Fin (13149 - 1))) ^ 2 ∂muI 13149 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13149)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13149}
    (hw : WINDOW (paperDesignP 13149) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13149 - 1))).real
      {v | sgA (paperDesignP 13149) c a v < √(2 / (13149 : ℝ) * mixtureFloor)}
      ∂muI 13149 ≤ lowMassBudget) :
    LatMom (paperDesignP 13149) c (√(2 / (13149 : ℝ) * mixtureFloor)) 24 where
  Vs := residualVarianceBudget
  Vl := locationVarianceBudget c
  VS := scaleVarianceBudget
  ts8 := residualMomentBudget 4
  ts12 := residualMomentBudget 6
  tl8 := locationMomentBudget c 4
  tl12 := locationMomentBudget c 6
  tlq := locationMomentBudget c 12
  tsq := residualMomentBudget 12
  βlow := lowMassBudget
  hVs0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg (mul_nonneg (by norm_num) hC.le) (by norm_num))
      (by norm_num)
  hVl0 := by
    have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
    exact div_nonneg (div_nonneg hC.le he.le) (by norm_num)
  hVS0 := mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (sq_nonneg _)
  hts8 := residualMomentBudget_pos (by norm_num)
  hts12 := residualMomentBudget_pos (by norm_num)
  htl8 := locationMomentBudget_pos he (by norm_num)
  htl12 := locationMomentBudget_pos he (by norm_num)
  htlq := (locationMomentBudget_pos he (by norm_num)).le
  htsq := (residualMomentBudget_pos (by norm_num)).le
  hβl := by norm_num [lowMassBudget]
  hVs := residual_variance_on_event hw hc
  hVl := location_variance_on_event hw he hc
  hVS := scale_variance_on_event hw hc
  hs8 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num)
  hs12 := residual_moment_on_event hw hc (by norm_num : 1 ≤ 6) (by norm_num)
  hl8 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 4) (by norm_num)
  hl12 := location_moment_on_event hw he hc (by norm_num : 1 ≤ 6) (by norm_num)
  hlq := location_moment_on_event hw he hc (by norm_num : 1 ≤ 12) (by norm_num)
  hsq := residual_moment_on_event hw hc (by norm_num : 1 ≤ 12) (by norm_num)
  hmass := hmass

end BstLean.Part266.Row13149

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13149
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195

theorem rotation_rational_bound {q : ℕ} (hq : 1 ≤ q) (hq1 : q ≠ 1)
    {b : ℝ} (hb : 0 ≤ b)
    (hnum : (3141593 / 2000000 : ℝ) ^ (2 * q) *
      (∏ j ∈ Finset.range q, (2 * j + 1 : ℝ)) ≤ b ^ (2 * q)) : rotationConstant q ≤ b := by
  apply le_of_pow_le_pow_left₀ (by omega : 2 * q ≠ 0) hb
  rw [rotationConstant_pow hq hq1, gmom_even]
  refine (mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ π / 2)
      (by linarith [pi_lt_d6] : π / 2 ≤ 3141593 / 2000000) (2 * q))
    (by positivity)).trans hnum

theorem location_budget_cap {c : Ret 13149} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13149 : ℝ) * (13149 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13149 : ℝ) * (13149 - 1 - 2 * q) := by nlinarith
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ he0]
    linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold locationMomentBudget
  rw [mul_pow, sq_sqrt (div_nonneg (div_nonneg hC.le he0.le) hd.le)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le)
    (div_nonneg (div_nonneg hC.le he0.le) hd.le) (sq_nonneg R)).trans hnum

theorem residual_budget_cap {q : ℕ} (hq : q ≤ 12) {R b : ℝ}
    (hR : 0 ≤ R) (hb : 0 ≤ b) (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13149 : ℝ) /
      ((13149 : ℝ) * (13149 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13149 : ℝ) * (13149 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13149 ≤ (2 * (16 / 5) / 13149 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13149} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (250363021 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (38438771 / 62500000000) ∧
    locationMomentBudget c 12 ≤ (421920991 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4783485249 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (2937674953 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (2015326413 / 250000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13149} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (1928379 / 62500000000000) ∧ residualVarianceBudget ≤ (563159 / 200000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13149 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4783485249 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13149

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13149
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13149 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13149) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13149) : ℝ :=
  exp (hqKappa * (13149 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((1155243 / 200000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (722027 / 125000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13149} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (421920991 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (2015326413 / 62500000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (2015326413 / 62500000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((2015326413 / 62500000000000) : ℝ) / ((1155243 / 200000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22454309 / 1000000000) := by
  have hr := width_ratio_bounds
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> nlinarith

theorem hq_kappa_bounds : 0 ≤ hqKappa ∧ hqKappa ≤ 1001 / 1000 := by
  have he := hq_epsilon_bounds
  have hden : 0 < 1 - hqEpsilon ^ 2 := by nlinarith
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  nlinarith

theorem hq_location_bounds {c : Ret 13149} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1618667097 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((421920991 / 125000000000))) / ((1155243 / 200000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13149} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqExp c ∧ hqExp c ≤ 2187 := by
  have hκ := hq_kappa_bounds
  have hε := hq_epsilon_bounds
  have hL := hq_location_bounds he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : 13149 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13149 * ((22454309 / 1000000000) : ℝ) ^ 2 / 2 + ((1618667097 / 1000000000)) ^ 2 * (1 + (22454309 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13149 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13149 * ((22454309 / 1000000000)) ^ 2 / 2 + ((1618667097 / 1000000000)) ^ 2 * (1 + (22454309 / 1000000000))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (by norm_num))
            (mul_nonneg (sq_nonneg _) (by linarith))) (by norm_num)
      _ ≤ _ := by norm_num
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta]

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num : (8 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]
  · apply le_of_pow_le_pow_left₀ (by norm_num : (12 : ℕ) ≠ 0) (by norm_num : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num)]
    norm_num [eta]

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta])⟩

theorem c3_eta_bounds : 0 ≤ c3η eta splitResidualWidth rowSigma ∧
    c3η eta splitResidualWidth rowSigma ≤ 31 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta])
  have hs0 : 0 < √(1 - eta) := by linarith
  have hσ0 := sigma_pos
  unfold c3η
  refine ⟨div_nonneg residual_width_bounds.1.le (by positivity), ?_⟩
  have hd : (2 * ((1155243 / 200000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (348180457 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (60614794177 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13149
