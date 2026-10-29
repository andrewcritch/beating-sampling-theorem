import BstLean.Part266Shard29Step2


/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13075
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13075 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13075) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13075 : ℝ) * (13075 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13075) /
    ((13075 : ℝ) * (13075 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13075} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13075}
    (hw : WINDOW (paperDesignP 13075) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13075) c a v - lbar (paperDesignP 13075) c a| ^ (2 * q)
      ∂stdGauss (Fin (13075 - 1)) ∂muI 13075 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13075)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13075}
    (hw : WINDOW (paperDesignP 13075) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13075) c a v - gbar (paperDesignP 13075) c a| ^ (2 * q)
      ∂stdGauss (Fin (13075 - 1)) ∂muI 13075 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13075)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13075) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13075}
    (hw : WINDOW (paperDesignP 13075) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13075 - 1))).real
      {v | sgA (paperDesignP 13075) c a v < √(2 / (13075 : ℝ) * mixtureFloor)}
      ∂muI 13075 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13075 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13075 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13075) c
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

end BstLean.Part266.Row13075

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13075
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13075 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13075)
    (p : Ix 13075 × (Fin (13075 - 1) → ℝ)) :
    sgA (paperDesignP 13075) c p.1 p.2 ^ 2 ≤
      (2 / (13075 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13075).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13075) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13075 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13075 : ℝ) * _ ≤ 2 / 13075 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13075)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13075}
    (hw : WINDOW (paperDesignP 13075) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13075) c a v ^ 8
      ∂stdGauss (Fin (13075 - 1)) ∂muI 13075 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13075).prod (stdGauss (Fin (13075 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13075) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13075) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13075 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13075) c p.1 p.2)
      (√(2 / (13075 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13075)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13075 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13075) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13075}
    (hw : WINDOW (paperDesignP 13075) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13075) c a v -
      ∫ w, sA (paperDesignP 13075) c a w ∂stdGauss (Fin (13075 - 1))) ^ 2
      ∂stdGauss (Fin (13075 - 1))) ^ 2 ∂muI 13075 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13075) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13075

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13075
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13075}
    (hw : WINDOW (paperDesignP 13075) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13075).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13075) c M H xi)
    (hE : centreEnergy (paperDesignP 13075) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13075 : ℝ))))
    (hprice : massBound 13075 M H xi E u mixtureFloor ≤ 13075 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13075 - 1))).real
      {v | sgA (paperDesignP 13075) c a v < √(2 / (13075 : ℝ) * mixtureFloor)}
        ∂muI 13075 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13075).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13075) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13075) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13075)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13075

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13075
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13075) : ℝ :=
  (latitudeC / eR c) / ((13075 : ℝ) * (13075 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13075) / ((13075 : ℝ) * (13075 - 3))

theorem location_variance_on_event {c : Ret 13075}
    (hw : WINDOW (paperDesignP 13075) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13075) c a v - lbar (paperDesignP 13075) c a) ^ 2
      ∂stdGauss (Fin (13075 - 1))) ^ 2 ∂muI 13075 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13075)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13075}
    (hw : WINDOW (paperDesignP 13075) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13075) c a v - gbar (paperDesignP 13075) c a) ^ 2
      ∂stdGauss (Fin (13075 - 1))) ^ 2 ∂muI 13075 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13075)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13075}
    (hw : WINDOW (paperDesignP 13075) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13075 - 1))).real
      {v | sgA (paperDesignP 13075) c a v < √(2 / (13075 : ℝ) * mixtureFloor)}
      ∂muI 13075 ≤ lowMassBudget) :
    LatMom (paperDesignP 13075) c (√(2 / (13075 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13075

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13075
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

theorem location_budget_cap {c : Ret 13075} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13075 : ℝ) * (13075 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13075 : ℝ) * (13075 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13075 : ℝ) /
      ((13075 : ℝ) * (13075 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13075 : ℝ) * (13075 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13075 ≤ (2 * (16 / 5) / 13075 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13075} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (100712191 / 200000000000) ∧
    locationMomentBudget c 6 ≤ (618502871 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (212155603 / 250000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (1206040331 / 250000000000000) ∧
    residualMomentBudget 6 ≤ (370332231 / 62500000000000) ∧
    residualMomentBudget 12 ≤ (8129882541 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13075} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (1560217 / 50000000000000) ∧ residualVarianceBudget ≤ (2863879 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13075 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((1206040331 / 250000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13075

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13075
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13075 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13075) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13075) : ℝ :=
  exp (hqKappa * (13075 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((2896269 / 500000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5792539 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13075} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (212155603 / 62500000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8129882541 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8129882541 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8129882541 / 250000000000000) : ℝ) / ((2896269 / 500000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22582223 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 13075} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1623249831 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((212155603 / 62500000000))) / ((2896269 / 500000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13075} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13075 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13075 * ((22582223 / 1000000000) : ℝ) ^ 2 / 2 + ((1623249831 / 1000000000)) ^ 2 * (1 + (22582223 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13075 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13075 * ((22582223 / 1000000000)) ^ 2 / 2 + ((1623249831 / 1000000000)) ^ 2 * (1 + (22582223 / 1000000000))) := by
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
  have hd : (2 * ((2896269 / 500000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (13888409 / 40000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (120554898901 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13075

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13076
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13076 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13076) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13076 : ℝ) * (13076 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13076) /
    ((13076 : ℝ) * (13076 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13076} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13076}
    (hw : WINDOW (paperDesignP 13076) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13076) c a v - lbar (paperDesignP 13076) c a| ^ (2 * q)
      ∂stdGauss (Fin (13076 - 1)) ∂muI 13076 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13076)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13076}
    (hw : WINDOW (paperDesignP 13076) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13076) c a v - gbar (paperDesignP 13076) c a| ^ (2 * q)
      ∂stdGauss (Fin (13076 - 1)) ∂muI 13076 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13076)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13076) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13076}
    (hw : WINDOW (paperDesignP 13076) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13076 - 1))).real
      {v | sgA (paperDesignP 13076) c a v < √(2 / (13076 : ℝ) * mixtureFloor)}
      ∂muI 13076 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13076 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13076 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13076) c
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

end BstLean.Part266.Row13076

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13076
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13076 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13076)
    (p : Ix 13076 × (Fin (13076 - 1) → ℝ)) :
    sgA (paperDesignP 13076) c p.1 p.2 ^ 2 ≤
      (2 / (13076 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13076).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13076) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13076 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13076 : ℝ) * _ ≤ 2 / 13076 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13076)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13076}
    (hw : WINDOW (paperDesignP 13076) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13076) c a v ^ 8
      ∂stdGauss (Fin (13076 - 1)) ∂muI 13076 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13076).prod (stdGauss (Fin (13076 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13076) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13076) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13076 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13076) c p.1 p.2)
      (√(2 / (13076 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13076)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13076 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13076) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13076}
    (hw : WINDOW (paperDesignP 13076) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13076) c a v -
      ∫ w, sA (paperDesignP 13076) c a w ∂stdGauss (Fin (13076 - 1))) ^ 2
      ∂stdGauss (Fin (13076 - 1))) ^ 2 ∂muI 13076 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13076) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13076

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13076
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13076}
    (hw : WINDOW (paperDesignP 13076) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13076).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13076) c M H xi)
    (hE : centreEnergy (paperDesignP 13076) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13076 : ℝ))))
    (hprice : massBound 13076 M H xi E u mixtureFloor ≤ 13076 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13076 - 1))).real
      {v | sgA (paperDesignP 13076) c a v < √(2 / (13076 : ℝ) * mixtureFloor)}
        ∂muI 13076 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13076).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13076) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13076) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13076)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13076

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13076
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13076) : ℝ :=
  (latitudeC / eR c) / ((13076 : ℝ) * (13076 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13076) / ((13076 : ℝ) * (13076 - 3))

theorem location_variance_on_event {c : Ret 13076}
    (hw : WINDOW (paperDesignP 13076) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13076) c a v - lbar (paperDesignP 13076) c a) ^ 2
      ∂stdGauss (Fin (13076 - 1))) ^ 2 ∂muI 13076 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13076)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13076}
    (hw : WINDOW (paperDesignP 13076) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13076) c a v - gbar (paperDesignP 13076) c a) ^ 2
      ∂stdGauss (Fin (13076 - 1))) ^ 2 ∂muI 13076 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13076)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13076}
    (hw : WINDOW (paperDesignP 13076) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13076 - 1))).real
      {v | sgA (paperDesignP 13076) c a v < √(2 / (13076 : ℝ) * mixtureFloor)}
      ∂muI 13076 ≤ lowMassBudget) :
    LatMom (paperDesignP 13076) c (√(2 / (13076 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13076

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13076
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

theorem location_budget_cap {c : Ret 13076} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13076 : ℝ) * (13076 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13076 : ℝ) * (13076 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13076 : ℝ) /
      ((13076 : ℝ) * (13076 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13076 : ℝ) * (13076 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13076 ≤ (2 * (16 / 5) / 13076 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13076} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (3933769 / 7812500000) ∧
    locationMomentBudget c 6 ≤ (618455547 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (16971149 / 20000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4823607809 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (5924635767 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (1016118669 / 125000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13076} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (31199567 / 1000000000000000) ∧ residualVarianceBudget ≤ (1431611 / 500000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13076 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4823607809 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13076

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13076
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13076 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13076) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13076) : ℝ :=
  exp (hqKappa * (13076 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((1448079 / 250000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5792317 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13076} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (16971149 / 5000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (1016118669 / 31250000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (1016118669 / 31250000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((1016118669 / 31250000000000) : ℝ) / ((1448079 / 250000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22580487 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 13076} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (81159389 / 50000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((16971149 / 5000000000))) / ((1448079 / 250000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13076} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13076 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13076 * ((22580487 / 1000000000) : ℝ) ^ 2 / 2 + ((81159389 / 50000000)) ^ 2 * (1 + (22580487 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13076 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13076 * ((22580487 / 1000000000)) ^ 2 / 2 + ((81159389 / 50000000)) ^ 2 * (1 + (22580487 / 1000000000))) := by
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
  have hd : (2 * ((1448079 / 250000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (69444677 / 200000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (30141009269 / 250000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13076

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13077
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13077 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13077) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13077 : ℝ) * (13077 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13077) /
    ((13077 : ℝ) * (13077 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13077} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13077}
    (hw : WINDOW (paperDesignP 13077) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13077) c a v - lbar (paperDesignP 13077) c a| ^ (2 * q)
      ∂stdGauss (Fin (13077 - 1)) ∂muI 13077 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13077)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13077}
    (hw : WINDOW (paperDesignP 13077) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13077) c a v - gbar (paperDesignP 13077) c a| ^ (2 * q)
      ∂stdGauss (Fin (13077 - 1)) ∂muI 13077 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13077)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13077) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13077}
    (hw : WINDOW (paperDesignP 13077) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13077 - 1))).real
      {v | sgA (paperDesignP 13077) c a v < √(2 / (13077 : ℝ) * mixtureFloor)}
      ∂muI 13077 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13077 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13077 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13077) c
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

end BstLean.Part266.Row13077

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13077
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13077 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13077)
    (p : Ix 13077 × (Fin (13077 - 1) → ℝ)) :
    sgA (paperDesignP 13077) c p.1 p.2 ^ 2 ≤
      (2 / (13077 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13077).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13077) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13077 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13077 : ℝ) * _ ≤ 2 / 13077 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13077)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13077}
    (hw : WINDOW (paperDesignP 13077) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13077) c a v ^ 8
      ∂stdGauss (Fin (13077 - 1)) ∂muI 13077 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13077).prod (stdGauss (Fin (13077 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13077) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13077) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13077 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13077) c p.1 p.2)
      (√(2 / (13077 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13077)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13077 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13077) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13077}
    (hw : WINDOW (paperDesignP 13077) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13077) c a v -
      ∫ w, sA (paperDesignP 13077) c a w ∂stdGauss (Fin (13077 - 1))) ^ 2
      ∂stdGauss (Fin (13077 - 1))) ^ 2 ∂muI 13077 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13077) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13077

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13077
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13077}
    (hw : WINDOW (paperDesignP 13077) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13077).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13077) c M H xi)
    (hE : centreEnergy (paperDesignP 13077) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13077 : ℝ))))
    (hprice : massBound 13077 M H xi E u mixtureFloor ≤ 13077 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13077 - 1))).real
      {v | sgA (paperDesignP 13077) c a v < √(2 / (13077 : ℝ) * mixtureFloor)}
        ∂muI 13077 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13077).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13077) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13077) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13077)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13077

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13077
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13077) : ℝ :=
  (latitudeC / eR c) / ((13077 : ℝ) * (13077 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13077) / ((13077 : ℝ) * (13077 - 3))

theorem location_variance_on_event {c : Ret 13077}
    (hw : WINDOW (paperDesignP 13077) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13077) c a v - lbar (paperDesignP 13077) c a) ^ 2
      ∂stdGauss (Fin (13077 - 1))) ^ 2 ∂muI 13077 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13077)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13077}
    (hw : WINDOW (paperDesignP 13077) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13077) c a v - gbar (paperDesignP 13077) c a) ^ 2
      ∂stdGauss (Fin (13077 - 1))) ^ 2 ∂muI 13077 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13077)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13077}
    (hw : WINDOW (paperDesignP 13077) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13077 - 1))).real
      {v | sgA (paperDesignP 13077) c a v < √(2 / (13077 : ℝ) * mixtureFloor)}
      ∂muI 13077 ≤ lowMassBudget) :
    LatMom (paperDesignP 13077) c (√(2 / (13077 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13077

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13077
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

theorem location_budget_cap {c : Ret 13077} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13077 : ℝ) * (13077 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13077 : ℝ) * (13077 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13077 : ℝ) /
      ((13077 : ℝ) * (13077 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13077 : ℝ) * (13077 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13077 ≤ (2 * (16 / 5) / 13077 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13077} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (251741957 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (61840823 / 100000000000) ∧
    locationMomentBudget c 12 ≤ (848492499 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (3014409 / 625000000000) ∧
    residualMomentBudget 6 ≤ (23140453 / 3906250000000) ∧
    residualMomentBudget 12 ≤ (4064008171 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13077} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (6238959 / 200000000000000) ∧ residualVarianceBudget ≤ (572513 / 200000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13077 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((3014409 / 625000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13077

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13077
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13077 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13077) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13077) : ℝ :=
  exp (hqKappa * (13077 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((1158419 / 200000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (181003 / 31250000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13077} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (848492499 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4064008171 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4064008171 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4064008171 / 125000000000000) : ℝ) / ((1158419 / 200000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22578747 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 13077} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (324625093 / 200000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((848492499 / 250000000000))) / ((1158419 / 200000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13077} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13077 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13077 * ((22578747 / 1000000000) : ℝ) ^ 2 / 2 + ((324625093 / 200000000)) ^ 2 * (1 + (22578747 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13077 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13077 * ((22578747 / 1000000000)) ^ 2 / 2 + ((324625093 / 200000000)) ^ 2 * (1 + (22578747 / 1000000000))) := by
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
  have hd : (2 * ((1158419 / 200000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (69447297 / 200000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (120573134453 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13077

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13078
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13078 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13078) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13078 : ℝ) * (13078 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13078) /
    ((13078 : ℝ) * (13078 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13078} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13078}
    (hw : WINDOW (paperDesignP 13078) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13078) c a v - lbar (paperDesignP 13078) c a| ^ (2 * q)
      ∂stdGauss (Fin (13078 - 1)) ∂muI 13078 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13078)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13078}
    (hw : WINDOW (paperDesignP 13078) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13078) c a v - gbar (paperDesignP 13078) c a| ^ (2 * q)
      ∂stdGauss (Fin (13078 - 1)) ∂muI 13078 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13078)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13078) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13078}
    (hw : WINDOW (paperDesignP 13078) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13078 - 1))).real
      {v | sgA (paperDesignP 13078) c a v < √(2 / (13078 : ℝ) * mixtureFloor)}
      ∂muI 13078 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13078 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13078 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13078) c
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

end BstLean.Part266.Row13078

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13078
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13078 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13078)
    (p : Ix 13078 × (Fin (13078 - 1) → ℝ)) :
    sgA (paperDesignP 13078) c p.1 p.2 ^ 2 ≤
      (2 / (13078 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13078).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13078) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13078 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13078 : ℝ) * _ ≤ 2 / 13078 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13078)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13078}
    (hw : WINDOW (paperDesignP 13078) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13078) c a v ^ 8
      ∂stdGauss (Fin (13078 - 1)) ∂muI 13078 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13078).prod (stdGauss (Fin (13078 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13078) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13078) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13078 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13078) c p.1 p.2)
      (√(2 / (13078 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13078)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13078 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13078) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13078}
    (hw : WINDOW (paperDesignP 13078) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13078) c a v -
      ∫ w, sA (paperDesignP 13078) c a w ∂stdGauss (Fin (13078 - 1))) ^ 2
      ∂stdGauss (Fin (13078 - 1))) ^ 2 ∂muI 13078 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13078) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13078

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13078
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13078}
    (hw : WINDOW (paperDesignP 13078) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13078).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13078) c M H xi)
    (hE : centreEnergy (paperDesignP 13078) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13078 : ℝ))))
    (hprice : massBound 13078 M H xi E u mixtureFloor ≤ 13078 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13078 - 1))).real
      {v | sgA (paperDesignP 13078) c a v < √(2 / (13078 : ℝ) * mixtureFloor)}
        ∂muI 13078 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13078).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13078) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13078) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13078)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13078

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13078
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13078) : ℝ :=
  (latitudeC / eR c) / ((13078 : ℝ) * (13078 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13078) / ((13078 : ℝ) * (13078 - 3))

theorem location_variance_on_event {c : Ret 13078}
    (hw : WINDOW (paperDesignP 13078) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13078) c a v - lbar (paperDesignP 13078) c a) ^ 2
      ∂stdGauss (Fin (13078 - 1))) ^ 2 ∂muI 13078 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13078)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13078}
    (hw : WINDOW (paperDesignP 13078) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13078) c a v - gbar (paperDesignP 13078) c a) ^ 2
      ∂stdGauss (Fin (13078 - 1))) ^ 2 ∂muI 13078 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13078)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13078}
    (hw : WINDOW (paperDesignP 13078) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13078 - 1))).real
      {v | sgA (paperDesignP 13078) c a v < √(2 / (13078 : ℝ) * mixtureFloor)}
      ∂muI 13078 ≤ lowMassBudget) :
    LatMom (paperDesignP 13078) c (√(2 / (13078 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13078

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13078
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

theorem location_budget_cap {c : Ret 13078} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13078 : ℝ) * (13078 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13078 : ℝ) * (13078 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13078 : ℝ) /
      ((13078 : ℝ) * (13078 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13078 : ℝ) * (13078 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13078 ≤ (2 * (16 / 5) / 13078 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13078} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (251722701 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (618360921 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (848427557 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (602812637 / 125000000000000) ∧
    residualMomentBudget 6 ≤ (5923276299 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (812708351 / 100000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13078} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (3898753 / 125000000000000) ∧ residualVarianceBudget ≤ (715477 / 250000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13078 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((602812637 / 125000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13078

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13078
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13078 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13078) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13078) : ℝ :=
  exp (hqKappa * (13078 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5791873 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2895937 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13078} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (848427557 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (812708351 / 25000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (812708351 / 25000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((812708351 / 25000000000000) : ℝ) / ((5791873 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (5644253 / 250000000) := by
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

theorem hq_location_bounds {c : Ret 13078} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1623063443 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((848427557 / 250000000000))) / ((5791873 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13078} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13078 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13078 * ((5644253 / 250000000) : ℝ) ^ 2 / 2 + ((1623063443 / 1000000000)) ^ 2 * (1 + (5644253 / 250000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13078 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13078 * ((5644253 / 250000000)) ^ 2 / 2 + ((1623063443 / 1000000000)) ^ 2 * (1 + (5644253 / 250000000))) := by
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
  have hd : (2 * ((5791873 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (173624823 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (120582274761 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13078

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13079
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13079 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13079) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13079 : ℝ) * (13079 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13079) /
    ((13079 : ℝ) * (13079 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13079} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13079}
    (hw : WINDOW (paperDesignP 13079) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13079) c a v - lbar (paperDesignP 13079) c a| ^ (2 * q)
      ∂stdGauss (Fin (13079 - 1)) ∂muI 13079 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13079)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13079}
    (hw : WINDOW (paperDesignP 13079) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13079) c a v - gbar (paperDesignP 13079) c a| ^ (2 * q)
      ∂stdGauss (Fin (13079 - 1)) ∂muI 13079 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13079)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13079) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13079}
    (hw : WINDOW (paperDesignP 13079) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13079 - 1))).real
      {v | sgA (paperDesignP 13079) c a v < √(2 / (13079 : ℝ) * mixtureFloor)}
      ∂muI 13079 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13079 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13079 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13079) c
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

end BstLean.Part266.Row13079

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13079
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13079 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13079)
    (p : Ix 13079 × (Fin (13079 - 1) → ℝ)) :
    sgA (paperDesignP 13079) c p.1 p.2 ^ 2 ≤
      (2 / (13079 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13079).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13079) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13079 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13079 : ℝ) * _ ≤ 2 / 13079 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13079)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13079}
    (hw : WINDOW (paperDesignP 13079) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13079) c a v ^ 8
      ∂stdGauss (Fin (13079 - 1)) ∂muI 13079 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13079).prod (stdGauss (Fin (13079 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13079) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13079) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13079 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13079) c p.1 p.2)
      (√(2 / (13079 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13079)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13079 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13079) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13079}
    (hw : WINDOW (paperDesignP 13079) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13079) c a v -
      ∫ w, sA (paperDesignP 13079) c a w ∂stdGauss (Fin (13079 - 1))) ^ 2
      ∂stdGauss (Fin (13079 - 1))) ^ 2 ∂muI 13079 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13079) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13079

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13079
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13079}
    (hw : WINDOW (paperDesignP 13079) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13079).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13079) c M H xi)
    (hE : centreEnergy (paperDesignP 13079) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13079 : ℝ))))
    (hprice : massBound 13079 M H xi E u mixtureFloor ≤ 13079 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13079 - 1))).real
      {v | sgA (paperDesignP 13079) c a v < √(2 / (13079 : ℝ) * mixtureFloor)}
        ∂muI 13079 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13079).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13079) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13079) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13079)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13079

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13079
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13079) : ℝ :=
  (latitudeC / eR c) / ((13079 : ℝ) * (13079 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13079) / ((13079 : ℝ) * (13079 - 3))

theorem location_variance_on_event {c : Ret 13079}
    (hw : WINDOW (paperDesignP 13079) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13079) c a v - lbar (paperDesignP 13079) c a) ^ 2
      ∂stdGauss (Fin (13079 - 1))) ^ 2 ∂muI 13079 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13079)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13079}
    (hw : WINDOW (paperDesignP 13079) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13079) c a v - gbar (paperDesignP 13079) c a) ^ 2
      ∂stdGauss (Fin (13079 - 1))) ^ 2 ∂muI 13079 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13079)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13079}
    (hw : WINDOW (paperDesignP 13079) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13079 - 1))).real
      {v | sgA (paperDesignP 13079) c a v < √(2 / (13079 : ℝ) * mixtureFloor)}
      ∂muI 13079 ≤ lowMassBudget) :
    LatMom (paperDesignP 13079) c (√(2 / (13079 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13079

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13079
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

theorem location_budget_cap {c : Ret 13079} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13079 : ℝ) * (13079 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13079 : ℝ) * (13079 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13079 : ℝ) /
      ((13079 : ℝ) * (13079 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13079 : ℝ) * (13079 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13079 ≤ (2 * (16 / 5) / 13079 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13079} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (31462931 / 62500000000) ∧
    locationMomentBudget c 6 ≤ (309156809 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (424181313 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2410973949 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (148064919 / 25000000000000) ∧
    residualMomentBudget 12 ≤ (1015768857 / 125000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13079} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15592627 / 500000000000000) ∧ residualVarianceBudget ≤ (715313 / 250000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13079 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2410973949 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13079

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13079
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13079 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13079) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13079) : ℝ :=
  exp (hqKappa * (13079 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((1447913 / 250000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5791653 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13079} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (424181313 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (1015768857 / 31250000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (1015768857 / 31250000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((1015768857 / 31250000000000) : ℝ) / ((1447913 / 250000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (2821909 / 125000000) := by
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

theorem hq_location_bounds {c : Ret 13079} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1623001157 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((424181313 / 125000000000))) / ((1447913 / 250000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13079} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13079 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13079 * ((2821909 / 125000000) : ℝ) ^ 2 / 2 + ((1623001157 / 1000000000)) ^ 2 * (1 + (2821909 / 125000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13079 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13079 * ((2821909 / 125000000)) ^ 2 / 2 + ((1623001157 / 1000000000)) ^ 2 * (1 + (2821909 / 125000000))) := by
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
  have hd : (2 * ((1447913 / 250000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (86815687 / 250000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (120591374261 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13079

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13080
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13080 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13080) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13080 : ℝ) * (13080 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13080) /
    ((13080 : ℝ) * (13080 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13080} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13080}
    (hw : WINDOW (paperDesignP 13080) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13080) c a v - lbar (paperDesignP 13080) c a| ^ (2 * q)
      ∂stdGauss (Fin (13080 - 1)) ∂muI 13080 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13080)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13080}
    (hw : WINDOW (paperDesignP 13080) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13080) c a v - gbar (paperDesignP 13080) c a| ^ (2 * q)
      ∂stdGauss (Fin (13080 - 1)) ∂muI 13080 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13080)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13080) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13080}
    (hw : WINDOW (paperDesignP 13080) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13080 - 1))).real
      {v | sgA (paperDesignP 13080) c a v < √(2 / (13080 : ℝ) * mixtureFloor)}
      ∂muI 13080 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13080 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13080 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13080) c
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

end BstLean.Part266.Row13080

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13080
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13080 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13080)
    (p : Ix 13080 × (Fin (13080 - 1) → ℝ)) :
    sgA (paperDesignP 13080) c p.1 p.2 ^ 2 ≤
      (2 / (13080 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13080).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13080) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13080 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13080 : ℝ) * _ ≤ 2 / 13080 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13080)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13080}
    (hw : WINDOW (paperDesignP 13080) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13080) c a v ^ 8
      ∂stdGauss (Fin (13080 - 1)) ∂muI 13080 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13080).prod (stdGauss (Fin (13080 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13080) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13080) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13080 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13080) c p.1 p.2)
      (√(2 / (13080 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13080)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13080 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13080) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13080}
    (hw : WINDOW (paperDesignP 13080) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13080) c a v -
      ∫ w, sA (paperDesignP 13080) c a w ∂stdGauss (Fin (13080 - 1))) ^ 2
      ∂stdGauss (Fin (13080 - 1))) ^ 2 ∂muI 13080 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13080) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13080

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13080
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13080}
    (hw : WINDOW (paperDesignP 13080) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13080).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13080) c M H xi)
    (hE : centreEnergy (paperDesignP 13080) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13080 : ℝ))))
    (hprice : massBound 13080 M H xi E u mixtureFloor ≤ 13080 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13080 - 1))).real
      {v | sgA (paperDesignP 13080) c a v < √(2 / (13080 : ℝ) * mixtureFloor)}
        ∂muI 13080 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13080).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13080) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13080) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13080)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13080

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13080
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13080) : ℝ :=
  (latitudeC / eR c) / ((13080 : ℝ) * (13080 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13080) / ((13080 : ℝ) * (13080 - 3))

theorem location_variance_on_event {c : Ret 13080}
    (hw : WINDOW (paperDesignP 13080) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13080) c a v - lbar (paperDesignP 13080) c a) ^ 2
      ∂stdGauss (Fin (13080 - 1))) ^ 2 ∂muI 13080 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13080)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13080}
    (hw : WINDOW (paperDesignP 13080) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13080) c a v - gbar (paperDesignP 13080) c a) ^ 2
      ∂stdGauss (Fin (13080 - 1))) ^ 2 ∂muI 13080 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13080)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13080}
    (hw : WINDOW (paperDesignP 13080) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13080 - 1))).real
      {v | sgA (paperDesignP 13080) c a v < √(2 / (13080 : ℝ) * mixtureFloor)}
      ∂muI 13080 ≤ lowMassBudget) :
    LatMom (paperDesignP 13080) c (√(2 / (13080 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13080

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13080
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

theorem location_budget_cap {c : Ret 13080} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13080 : ℝ) * (13080 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13080 : ℝ) * (13080 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13080 : ℝ) /
      ((13080 : ℝ) * (13080 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13080 : ℝ) * (13080 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13080 ≤ (2 * (16 / 5) / 13080 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13080} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (125842099 / 250000000000) ∧
    locationMomentBudget c 6 ≤ (618266323 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (106037213 / 125000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2410697403 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (118438347 / 20000000000000) ∧
    residualMomentBudget 12 ≤ (8125218381 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13080} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (6236097 / 200000000000000) ∧ residualVarianceBudget ≤ (572119 / 200000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13080 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2410697403 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13080

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13080
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13080 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13080) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13080) : ℝ :=
  exp (hqKappa * (13080 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((579143 / 100000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5791431 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13080} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (106037213 / 31250000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8125218381 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8125218381 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8125218381 / 250000000000000) : ℝ) / ((579143 / 100000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11286769 / 500000000) := by
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

theorem hq_location_bounds {c : Ret 13080} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (405734791 / 250000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((106037213 / 31250000000))) / ((579143 / 100000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13080} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13080 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13080 * ((11286769 / 500000000) : ℝ) ^ 2 / 2 + ((405734791 / 250000000)) ^ 2 * (1 + (11286769 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13080 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13080 * ((11286769 / 500000000)) ^ 2 / 2 + ((405734791 / 250000000)) ^ 2 * (1 + (11286769 / 500000000))) := by
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
  have hd : (2 * ((579143 / 100000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (347275911 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (60300258351 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13080

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13081
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13081 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13081) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13081 : ℝ) * (13081 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13081) /
    ((13081 : ℝ) * (13081 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13081} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13081}
    (hw : WINDOW (paperDesignP 13081) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13081) c a v - lbar (paperDesignP 13081) c a| ^ (2 * q)
      ∂stdGauss (Fin (13081 - 1)) ∂muI 13081 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13081)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13081}
    (hw : WINDOW (paperDesignP 13081) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13081) c a v - gbar (paperDesignP 13081) c a| ^ (2 * q)
      ∂stdGauss (Fin (13081 - 1)) ∂muI 13081 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13081)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13081) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13081}
    (hw : WINDOW (paperDesignP 13081) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13081 - 1))).real
      {v | sgA (paperDesignP 13081) c a v < √(2 / (13081 : ℝ) * mixtureFloor)}
      ∂muI 13081 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13081 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13081 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13081) c
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

end BstLean.Part266.Row13081

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13081
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13081 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13081)
    (p : Ix 13081 × (Fin (13081 - 1) → ℝ)) :
    sgA (paperDesignP 13081) c p.1 p.2 ^ 2 ≤
      (2 / (13081 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13081).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13081) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13081 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13081 : ℝ) * _ ≤ 2 / 13081 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13081)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13081}
    (hw : WINDOW (paperDesignP 13081) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13081) c a v ^ 8
      ∂stdGauss (Fin (13081 - 1)) ∂muI 13081 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13081).prod (stdGauss (Fin (13081 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13081) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13081) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13081 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13081) c p.1 p.2)
      (√(2 / (13081 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13081)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13081 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13081) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13081}
    (hw : WINDOW (paperDesignP 13081) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13081) c a v -
      ∫ w, sA (paperDesignP 13081) c a w ∂stdGauss (Fin (13081 - 1))) ^ 2
      ∂stdGauss (Fin (13081 - 1))) ^ 2 ∂muI 13081 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13081) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13081

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13081
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13081}
    (hw : WINDOW (paperDesignP 13081) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13081).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13081) c M H xi)
    (hE : centreEnergy (paperDesignP 13081) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13081 : ℝ))))
    (hprice : massBound 13081 M H xi E u mixtureFloor ≤ 13081 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13081 - 1))).real
      {v | sgA (paperDesignP 13081) c a v < √(2 / (13081 : ℝ) * mixtureFloor)}
        ∂muI 13081 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13081).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13081) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13081) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13081)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13081

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13081
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13081) : ℝ :=
  (latitudeC / eR c) / ((13081 : ℝ) * (13081 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13081) / ((13081 : ℝ) * (13081 - 3))

theorem location_variance_on_event {c : Ret 13081}
    (hw : WINDOW (paperDesignP 13081) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13081) c a v - lbar (paperDesignP 13081) c a) ^ 2
      ∂stdGauss (Fin (13081 - 1))) ^ 2 ∂muI 13081 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13081)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13081}
    (hw : WINDOW (paperDesignP 13081) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13081) c a v - gbar (paperDesignP 13081) c a) ^ 2
      ∂stdGauss (Fin (13081 - 1))) ^ 2 ∂muI 13081 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13081)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13081}
    (hw : WINDOW (paperDesignP 13081) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13081 - 1))).real
      {v | sgA (paperDesignP 13081) c a v < √(2 / (13081 : ℝ) * mixtureFloor)}
      ∂muI 13081 ≤ lowMassBudget) :
    LatMom (paperDesignP 13081) c (√(2 / (13081 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13081

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13081
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

theorem location_budget_cap {c : Ret 13081} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13081 : ℝ) * (13081 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13081 : ℝ) * (13081 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13081 : ℝ) /
      ((13081 : ℝ) * (13081 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13081 : ℝ) * (13081 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13081 ≤ (2 * (16 / 5) / 13081 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13081} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (251664951 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (123643807 / 200000000000) ∧
    locationMomentBudget c 12 ≤ (106029099 / 125000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (241042091 / 50000000000000) ∧
    residualMomentBudget 6 ≤ (5921238071 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (1624857217 / 200000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13081} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (31175717 / 1000000000000000) ∧ residualVarianceBudget ≤ (2859939 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13081 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((241042091 / 50000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13081

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13081
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13081 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13081) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13081) : ℝ :=
  exp (hqKappa * (13081 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5791209 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (579121 / 100000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13081} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (106029099 / 31250000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (1624857217 / 50000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (1624857217 / 50000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((1624857217 / 50000000000000) : ℝ) / ((5791209 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22571799 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 13081} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (324575381 / 200000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((106029099 / 31250000000))) / ((5791209 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13081} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13081 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13081 * ((22571799 / 1000000000) : ℝ) ^ 2 / 2 + ((324575381 / 200000000)) ^ 2 * (1 + (22571799 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13081 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13081 * ((22571799 / 1000000000)) ^ 2 / 2 + ((324575381 / 200000000)) ^ 2 * (1 + (22571799 / 1000000000))) := by
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
  have hd : (2 * ((5791209 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (69457803 / 200000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (120609618327 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13081

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13082
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13082 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13082) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13082 : ℝ) * (13082 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13082) /
    ((13082 : ℝ) * (13082 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13082} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13082}
    (hw : WINDOW (paperDesignP 13082) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13082) c a v - lbar (paperDesignP 13082) c a| ^ (2 * q)
      ∂stdGauss (Fin (13082 - 1)) ∂muI 13082 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13082)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13082}
    (hw : WINDOW (paperDesignP 13082) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13082) c a v - gbar (paperDesignP 13082) c a| ^ (2 * q)
      ∂stdGauss (Fin (13082 - 1)) ∂muI 13082 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13082)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13082) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13082}
    (hw : WINDOW (paperDesignP 13082) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13082 - 1))).real
      {v | sgA (paperDesignP 13082) c a v < √(2 / (13082 : ℝ) * mixtureFloor)}
      ∂muI 13082 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13082 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13082 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13082) c
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

end BstLean.Part266.Row13082

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13082
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13082 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13082)
    (p : Ix 13082 × (Fin (13082 - 1) → ℝ)) :
    sgA (paperDesignP 13082) c p.1 p.2 ^ 2 ≤
      (2 / (13082 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13082).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13082) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13082 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13082 : ℝ) * _ ≤ 2 / 13082 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13082)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13082}
    (hw : WINDOW (paperDesignP 13082) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13082) c a v ^ 8
      ∂stdGauss (Fin (13082 - 1)) ∂muI 13082 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13082).prod (stdGauss (Fin (13082 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13082) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13082) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13082 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13082) c p.1 p.2)
      (√(2 / (13082 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13082)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13082 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13082) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13082}
    (hw : WINDOW (paperDesignP 13082) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13082) c a v -
      ∫ w, sA (paperDesignP 13082) c a w ∂stdGauss (Fin (13082 - 1))) ^ 2
      ∂stdGauss (Fin (13082 - 1))) ^ 2 ∂muI 13082 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13082) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13082

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13082
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13082}
    (hw : WINDOW (paperDesignP 13082) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13082).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13082) c M H xi)
    (hE : centreEnergy (paperDesignP 13082) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13082 : ℝ))))
    (hprice : massBound 13082 M H xi E u mixtureFloor ≤ 13082 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13082 - 1))).real
      {v | sgA (paperDesignP 13082) c a v < √(2 / (13082 : ℝ) * mixtureFloor)}
        ∂muI 13082 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13082).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13082) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13082) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13082)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13082

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13082
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13082) : ℝ :=
  (latitudeC / eR c) / ((13082 : ℝ) * (13082 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13082) / ((13082 : ℝ) * (13082 - 3))

theorem location_variance_on_event {c : Ret 13082}
    (hw : WINDOW (paperDesignP 13082) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13082) c a v - lbar (paperDesignP 13082) c a) ^ 2
      ∂stdGauss (Fin (13082 - 1))) ^ 2 ∂muI 13082 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13082)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13082}
    (hw : WINDOW (paperDesignP 13082) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13082) c a v - gbar (paperDesignP 13082) c a) ^ 2
      ∂stdGauss (Fin (13082 - 1))) ^ 2 ∂muI 13082 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13082)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13082}
    (hw : WINDOW (paperDesignP 13082) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13082 - 1))).real
      {v | sgA (paperDesignP 13082) c a v < √(2 / (13082 : ℝ) * mixtureFloor)}
      ∂muI 13082 ≤ lowMassBudget) :
    LatMom (paperDesignP 13082) c (√(2 / (13082 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13082

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13082
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

theorem location_budget_cap {c : Ret 13082} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13082 : ℝ) * (13082 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13082 : ℝ) * (13082 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13082 : ℝ) /
      ((13082 : ℝ) * (13082 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13082 : ℝ) * (13082 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13082 ≤ (2 * (16 / 5) / 13082 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13082} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (251645707 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (309085877 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (848167891 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (241014447 / 50000000000000) ∧
    residualMomentBudget 6 ≤ (2960279461 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (4061676983 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13082} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (31170951 / 1000000000000000) ∧ residualVarianceBudget ≤ (714821 / 250000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13082 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((241014447 / 50000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13082

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13082
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13082 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13082) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13082) : ℝ :=
  exp (hqKappa * (13082 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((1447747 / 250000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5790989 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13082} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (848167891 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4061676983 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4061676983 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4061676983 / 125000000000000) : ℝ) / ((1447747 / 250000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22570061 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 13082} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (811407331 / 500000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((848167891 / 250000000000))) / ((1447747 / 250000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13082} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13082 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13082 * ((22570061 / 1000000000) : ℝ) ^ 2 / 2 + ((811407331 / 500000000)) ^ 2 * (1 + (22570061 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13082 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13082 * ((22570061 / 1000000000)) ^ 2 / 2 + ((811407331 / 500000000)) ^ 2 * (1 + (22570061 / 1000000000))) := by
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
  have hd : (2 * ((1447747 / 250000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (8682553 / 25000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (120618721011 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13082

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13083
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13083 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13083) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13083 : ℝ) * (13083 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13083) /
    ((13083 : ℝ) * (13083 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13083} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13083}
    (hw : WINDOW (paperDesignP 13083) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13083) c a v - lbar (paperDesignP 13083) c a| ^ (2 * q)
      ∂stdGauss (Fin (13083 - 1)) ∂muI 13083 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13083)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13083}
    (hw : WINDOW (paperDesignP 13083) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13083) c a v - gbar (paperDesignP 13083) c a| ^ (2 * q)
      ∂stdGauss (Fin (13083 - 1)) ∂muI 13083 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13083)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13083) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13083}
    (hw : WINDOW (paperDesignP 13083) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13083 - 1))).real
      {v | sgA (paperDesignP 13083) c a v < √(2 / (13083 : ℝ) * mixtureFloor)}
      ∂muI 13083 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13083 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13083 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13083) c
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

end BstLean.Part266.Row13083

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13083
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13083 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13083)
    (p : Ix 13083 × (Fin (13083 - 1) → ℝ)) :
    sgA (paperDesignP 13083) c p.1 p.2 ^ 2 ≤
      (2 / (13083 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13083).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13083) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13083 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13083 : ℝ) * _ ≤ 2 / 13083 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13083)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13083}
    (hw : WINDOW (paperDesignP 13083) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13083) c a v ^ 8
      ∂stdGauss (Fin (13083 - 1)) ∂muI 13083 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13083).prod (stdGauss (Fin (13083 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13083) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13083) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13083 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13083) c p.1 p.2)
      (√(2 / (13083 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13083)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13083 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13083) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13083}
    (hw : WINDOW (paperDesignP 13083) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13083) c a v -
      ∫ w, sA (paperDesignP 13083) c a w ∂stdGauss (Fin (13083 - 1))) ^ 2
      ∂stdGauss (Fin (13083 - 1))) ^ 2 ∂muI 13083 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13083) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13083

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13083
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13083}
    (hw : WINDOW (paperDesignP 13083) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13083).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13083) c M H xi)
    (hE : centreEnergy (paperDesignP 13083) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13083 : ℝ))))
    (hprice : massBound 13083 M H xi E u mixtureFloor ≤ 13083 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13083 - 1))).real
      {v | sgA (paperDesignP 13083) c a v < √(2 / (13083 : ℝ) * mixtureFloor)}
        ∂muI 13083 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13083).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13083) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13083) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13083)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13083

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13083
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13083) : ℝ :=
  (latitudeC / eR c) / ((13083 : ℝ) * (13083 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13083) / ((13083 : ℝ) * (13083 - 3))

theorem location_variance_on_event {c : Ret 13083}
    (hw : WINDOW (paperDesignP 13083) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13083) c a v - lbar (paperDesignP 13083) c a) ^ 2
      ∂stdGauss (Fin (13083 - 1))) ^ 2 ∂muI 13083 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13083)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13083}
    (hw : WINDOW (paperDesignP 13083) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13083) c a v - gbar (paperDesignP 13083) c a) ^ 2
      ∂stdGauss (Fin (13083 - 1))) ^ 2 ∂muI 13083 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13083)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13083}
    (hw : WINDOW (paperDesignP 13083) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13083 - 1))).real
      {v | sgA (paperDesignP 13083) c a v < √(2 / (13083 : ℝ) * mixtureFloor)}
      ∂muI 13083 ≤ lowMassBudget) :
    LatMom (paperDesignP 13083) c (√(2 / (13083 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13083

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13083
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

theorem location_budget_cap {c : Ret 13083} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13083 : ℝ) * (13083 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13083 : ℝ) * (13083 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13083 : ℝ) /
      ((13083 : ℝ) * (13083 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13083 : ℝ) * (13083 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13083 ≤ (2 * (16 / 5) / 13083 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13083} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (125813233 / 250000000000) ∧
    locationMomentBudget c 6 ≤ (618124481 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (848102999 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (963947233 / 200000000000000) ∧
    residualMomentBudget 6 ≤ (2959939951 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (4061211013 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13083} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (6233237 / 200000000000000) ∧ residualVarianceBudget ≤ (714657 / 250000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13083 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((963947233 / 200000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13083

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13083
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13083 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13083) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13083) : ℝ :=
  exp (hqKappa * (13083 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((2895383 / 500000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5790767 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13083} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (848102999 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4061211013 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4061211013 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4061211013 / 125000000000000) : ℝ) / ((2895383 / 500000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22568327 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 13083} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (202844089 / 125000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((848102999 / 250000000000))) / ((2895383 / 500000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13083} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13083 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13083 * ((22568327 / 1000000000) : ℝ) ^ 2 / 2 + ((202844089 / 125000000)) ^ 2 * (1 + (22568327 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13083 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13083 * ((22568327 / 1000000000)) ^ 2 / 2 + ((202844089 / 125000000)) ^ 2 * (1 + (22568327 / 1000000000))) := by
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
  have hd : (2 * ((2895383 / 500000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (347315287 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (2412557333 / 20000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13083

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13084
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13084 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13084) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13084 : ℝ) * (13084 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13084) /
    ((13084 : ℝ) * (13084 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13084} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13084}
    (hw : WINDOW (paperDesignP 13084) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13084) c a v - lbar (paperDesignP 13084) c a| ^ (2 * q)
      ∂stdGauss (Fin (13084 - 1)) ∂muI 13084 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13084)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13084}
    (hw : WINDOW (paperDesignP 13084) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13084) c a v - gbar (paperDesignP 13084) c a| ^ (2 * q)
      ∂stdGauss (Fin (13084 - 1)) ∂muI 13084 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13084)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13084) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13084}
    (hw : WINDOW (paperDesignP 13084) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13084 - 1))).real
      {v | sgA (paperDesignP 13084) c a v < √(2 / (13084 : ℝ) * mixtureFloor)}
      ∂muI 13084 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13084 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13084 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13084) c
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

end BstLean.Part266.Row13084

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13084
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13084 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13084)
    (p : Ix 13084 × (Fin (13084 - 1) → ℝ)) :
    sgA (paperDesignP 13084) c p.1 p.2 ^ 2 ≤
      (2 / (13084 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13084).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13084) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13084 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13084 : ℝ) * _ ≤ 2 / 13084 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13084)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13084}
    (hw : WINDOW (paperDesignP 13084) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13084) c a v ^ 8
      ∂stdGauss (Fin (13084 - 1)) ∂muI 13084 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13084).prod (stdGauss (Fin (13084 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13084) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13084) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13084 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13084) c p.1 p.2)
      (√(2 / (13084 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13084)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13084 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13084) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13084}
    (hw : WINDOW (paperDesignP 13084) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13084) c a v -
      ∫ w, sA (paperDesignP 13084) c a w ∂stdGauss (Fin (13084 - 1))) ^ 2
      ∂stdGauss (Fin (13084 - 1))) ^ 2 ∂muI 13084 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13084) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13084

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13084
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13084}
    (hw : WINDOW (paperDesignP 13084) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13084).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13084) c M H xi)
    (hE : centreEnergy (paperDesignP 13084) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13084 : ℝ))))
    (hprice : massBound 13084 M H xi E u mixtureFloor ≤ 13084 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13084 - 1))).real
      {v | sgA (paperDesignP 13084) c a v < √(2 / (13084 : ℝ) * mixtureFloor)}
        ∂muI 13084 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13084).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13084) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13084) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13084)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13084

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13084
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13084) : ℝ :=
  (latitudeC / eR c) / ((13084 : ℝ) * (13084 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13084) / ((13084 : ℝ) * (13084 - 3))

theorem location_variance_on_event {c : Ret 13084}
    (hw : WINDOW (paperDesignP 13084) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13084) c a v - lbar (paperDesignP 13084) c a) ^ 2
      ∂stdGauss (Fin (13084 - 1))) ^ 2 ∂muI 13084 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13084)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13084}
    (hw : WINDOW (paperDesignP 13084) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13084) c a v - gbar (paperDesignP 13084) c a) ^ 2
      ∂stdGauss (Fin (13084 - 1))) ^ 2 ∂muI 13084 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13084)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13084}
    (hw : WINDOW (paperDesignP 13084) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13084 - 1))).real
      {v | sgA (paperDesignP 13084) c a v < √(2 / (13084 : ℝ) * mixtureFloor)}
      ∂muI 13084 ≤ lowMassBudget) :
    LatMom (paperDesignP 13084) c (√(2 / (13084 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13084

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13084
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

theorem location_budget_cap {c : Ret 13084} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13084 : ℝ) * (13084 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13084 : ℝ) * (13084 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13084 : ℝ) /
      ((13084 : ℝ) * (13084 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13084 : ℝ) * (13084 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13084 ≤ (2 * (16 / 5) / 13084 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13084} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (100642891 / 200000000000) ∧
    locationMomentBudget c 6 ≤ (123615443 / 200000000000) ∧
    locationMomentBudget c 12 ≤ (848038117 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (963836699 / 200000000000000) ∧
    residualMomentBudget 6 ≤ (1479800253 / 250000000000000) ∧
    residualMomentBudget 12 ≤ (1015186283 / 125000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13084} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (31161421 / 1000000000000000) ∧ residualVarianceBudget ≤ (714493 / 250000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13084 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((963836699 / 200000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13084

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13084
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13084 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13084) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13084) : ℝ :=
  exp (hqKappa * (13084 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((1158109 / 200000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2895273 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13084} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (848038117 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (1015186283 / 31250000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (1015186283 / 31250000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((1015186283 / 31250000000000) : ℝ) / ((1158109 / 200000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (2256659 / 100000000) := by
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

theorem hq_location_bounds {c : Ret 13084} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (25354539 / 15625000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((848038117 / 250000000000))) / ((1158109 / 200000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13084} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13084 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13084 * ((2256659 / 100000000) : ℝ) ^ 2 / 2 + ((25354539 / 15625000)) ^ 2 * (1 + (2256659 / 100000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13084 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13084 * ((2256659 / 100000000)) ^ 2 / 2 + ((25354539 / 15625000)) ^ 2 * (1 + (2256659 / 100000000))) := by
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
  have hd : (2 * ((1158109 / 200000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (173664197 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (6031848573 / 50000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13084

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13085
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13085 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13085) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13085 : ℝ) * (13085 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13085) /
    ((13085 : ℝ) * (13085 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13085} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13085}
    (hw : WINDOW (paperDesignP 13085) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13085) c a v - lbar (paperDesignP 13085) c a| ^ (2 * q)
      ∂stdGauss (Fin (13085 - 1)) ∂muI 13085 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13085)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13085}
    (hw : WINDOW (paperDesignP 13085) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13085) c a v - gbar (paperDesignP 13085) c a| ^ (2 * q)
      ∂stdGauss (Fin (13085 - 1)) ∂muI 13085 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13085)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13085) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13085}
    (hw : WINDOW (paperDesignP 13085) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13085 - 1))).real
      {v | sgA (paperDesignP 13085) c a v < √(2 / (13085 : ℝ) * mixtureFloor)}
      ∂muI 13085 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13085 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13085 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13085) c
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

end BstLean.Part266.Row13085

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13085
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13085 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13085)
    (p : Ix 13085 × (Fin (13085 - 1) → ℝ)) :
    sgA (paperDesignP 13085) c p.1 p.2 ^ 2 ≤
      (2 / (13085 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13085).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13085) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13085 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13085 : ℝ) * _ ≤ 2 / 13085 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13085)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13085}
    (hw : WINDOW (paperDesignP 13085) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13085) c a v ^ 8
      ∂stdGauss (Fin (13085 - 1)) ∂muI 13085 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13085).prod (stdGauss (Fin (13085 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13085) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13085) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13085 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13085) c p.1 p.2)
      (√(2 / (13085 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13085)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13085 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13085) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13085}
    (hw : WINDOW (paperDesignP 13085) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13085) c a v -
      ∫ w, sA (paperDesignP 13085) c a w ∂stdGauss (Fin (13085 - 1))) ^ 2
      ∂stdGauss (Fin (13085 - 1))) ^ 2 ∂muI 13085 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13085) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13085

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13085
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13085}
    (hw : WINDOW (paperDesignP 13085) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13085).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13085) c M H xi)
    (hE : centreEnergy (paperDesignP 13085) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13085 : ℝ))))
    (hprice : massBound 13085 M H xi E u mixtureFloor ≤ 13085 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13085 - 1))).real
      {v | sgA (paperDesignP 13085) c a v < √(2 / (13085 : ℝ) * mixtureFloor)}
        ∂muI 13085 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13085).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13085) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13085) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13085)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13085

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13085
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13085) : ℝ :=
  (latitudeC / eR c) / ((13085 : ℝ) * (13085 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13085) / ((13085 : ℝ) * (13085 - 3))

theorem location_variance_on_event {c : Ret 13085}
    (hw : WINDOW (paperDesignP 13085) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13085) c a v - lbar (paperDesignP 13085) c a) ^ 2
      ∂stdGauss (Fin (13085 - 1))) ^ 2 ∂muI 13085 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13085)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13085}
    (hw : WINDOW (paperDesignP 13085) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13085) c a v - gbar (paperDesignP 13085) c a) ^ 2
      ∂stdGauss (Fin (13085 - 1))) ^ 2 ∂muI 13085 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13085)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13085}
    (hw : WINDOW (paperDesignP 13085) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13085 - 1))).real
      {v | sgA (paperDesignP 13085) c a v < √(2 / (13085 : ℝ) * mixtureFloor)}
      ∂muI 13085 ≤ lowMassBudget) :
    LatMom (paperDesignP 13085) c (√(2 / (13085 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13085

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13085
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

theorem location_budget_cap {c : Ret 13085} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13085 : ℝ) * (13085 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13085 : ℝ) * (13085 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13085 : ℝ) /
      ((13085 : ℝ) * (13085 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13085 : ℝ) * (13085 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13085 ≤ (2 * (16 / 5) / 13085 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13085} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (31448499 / 62500000000) ∧
    locationMomentBudget c 6 ≤ (154507489 / 250000000000) ∧
    locationMomentBudget c 12 ≤ (169594649 / 200000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (1204657733 / 250000000000000) ∧
    residualMomentBudget 6 ≤ (1479630563 / 250000000000000) ∧
    residualMomentBudget 12 ≤ (203013967 / 25000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13085} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15578329 / 500000000000000) ∧ residualVarianceBudget ≤ (2857317 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13085 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((1204657733 / 250000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13085

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13085
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13085 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13085) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13085) : ℝ :=
  exp (hqKappa * (13085 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((1447581 / 250000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (231613 / 40000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13085} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (169594649 / 50000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (203013967 / 6250000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (203013967 / 6250000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((203013967 / 6250000000000) : ℝ) / ((1447581 / 250000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22564853 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 13085} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (324525659 / 200000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((169594649 / 50000000000))) / ((1447581 / 250000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13085} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13085 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13085 * ((22564853 / 1000000000) : ℝ) ^ 2 / 2 + ((324525659 / 200000000)) ^ 2 * (1 + (22564853 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13085 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13085 * ((22564853 / 1000000000)) ^ 2 / 2 + ((324525659 / 200000000)) ^ 2 * (1 + (22564853 / 1000000000))) := by
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
  have hd : (2 * ((1447581 / 250000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (173670751 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (12064607733 / 100000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13085

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13086
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13086 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13086) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13086 : ℝ) * (13086 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13086) /
    ((13086 : ℝ) * (13086 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13086} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13086}
    (hw : WINDOW (paperDesignP 13086) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13086) c a v - lbar (paperDesignP 13086) c a| ^ (2 * q)
      ∂stdGauss (Fin (13086 - 1)) ∂muI 13086 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13086)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13086}
    (hw : WINDOW (paperDesignP 13086) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13086) c a v - gbar (paperDesignP 13086) c a| ^ (2 * q)
      ∂stdGauss (Fin (13086 - 1)) ∂muI 13086 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13086)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13086) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13086}
    (hw : WINDOW (paperDesignP 13086) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13086 - 1))).real
      {v | sgA (paperDesignP 13086) c a v < √(2 / (13086 : ℝ) * mixtureFloor)}
      ∂muI 13086 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13086 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13086 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13086) c
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

end BstLean.Part266.Row13086

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13086
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13086 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13086)
    (p : Ix 13086 × (Fin (13086 - 1) → ℝ)) :
    sgA (paperDesignP 13086) c p.1 p.2 ^ 2 ≤
      (2 / (13086 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13086).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13086) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13086 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13086 : ℝ) * _ ≤ 2 / 13086 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13086)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13086}
    (hw : WINDOW (paperDesignP 13086) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13086) c a v ^ 8
      ∂stdGauss (Fin (13086 - 1)) ∂muI 13086 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13086).prod (stdGauss (Fin (13086 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13086) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13086) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13086 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13086) c p.1 p.2)
      (√(2 / (13086 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13086)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13086 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13086) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13086}
    (hw : WINDOW (paperDesignP 13086) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13086) c a v -
      ∫ w, sA (paperDesignP 13086) c a w ∂stdGauss (Fin (13086 - 1))) ^ 2
      ∂stdGauss (Fin (13086 - 1))) ^ 2 ∂muI 13086 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13086) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13086

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13086
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13086}
    (hw : WINDOW (paperDesignP 13086) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13086).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13086) c M H xi)
    (hE : centreEnergy (paperDesignP 13086) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13086 : ℝ))))
    (hprice : massBound 13086 M H xi E u mixtureFloor ≤ 13086 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13086 - 1))).real
      {v | sgA (paperDesignP 13086) c a v < √(2 / (13086 : ℝ) * mixtureFloor)}
        ∂muI 13086 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13086).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13086) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13086) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13086)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13086

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13086
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13086) : ℝ :=
  (latitudeC / eR c) / ((13086 : ℝ) * (13086 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13086) / ((13086 : ℝ) * (13086 - 3))

theorem location_variance_on_event {c : Ret 13086}
    (hw : WINDOW (paperDesignP 13086) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13086) c a v - lbar (paperDesignP 13086) c a) ^ 2
      ∂stdGauss (Fin (13086 - 1))) ^ 2 ∂muI 13086 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13086)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13086}
    (hw : WINDOW (paperDesignP 13086) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13086) c a v - gbar (paperDesignP 13086) c a) ^ 2
      ∂stdGauss (Fin (13086 - 1))) ^ 2 ∂muI 13086 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13086)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13086}
    (hw : WINDOW (paperDesignP 13086) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13086 - 1))).real
      {v | sgA (paperDesignP 13086) c a v < √(2 / (13086 : ℝ) * mixtureFloor)}
      ∂muI 13086 ≤ lowMassBudget) :
    LatMom (paperDesignP 13086) c (√(2 / (13086 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13086

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13086
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

theorem location_budget_cap {c : Ret 13086} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13086 : ℝ) * (13086 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13086 : ℝ) * (13086 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13086 : ℝ) /
      ((13086 : ℝ) * (13086 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13086 : ℝ) * (13086 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13086 ≤ (2 * (16 / 5) / 13086 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13086} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (6289219 / 12500000000) ∧
    locationMomentBudget c 6 ≤ (38623919 / 62500000000) ∧
    locationMomentBudget c 12 ≤ (847908383 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2409039237 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (2958921811 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (4059813637 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13086} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (3893987 / 125000000000000) ∧ residualVarianceBudget ≤ (1428331 / 500000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13086 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2409039237 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13086

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13086
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13086 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13086) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13086) : ℝ :=
  exp (hqKappa * (13086 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5790103 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (723763 / 125000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13086} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (847908383 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4059813637 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4059813637 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4059813637 / 125000000000000) : ℝ) / ((5790103 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (5640779 / 250000000) := by
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

theorem hq_location_bounds {c : Ret 13086} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1622566107 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((847908383 / 250000000000))) / ((5790103 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13086} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13086 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13086 * ((5640779 / 250000000) : ℝ) ^ 2 / 2 + ((1622566107 / 1000000000)) ^ 2 * (1 + (5640779 / 250000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13086 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13086 * ((5640779 / 250000000)) ^ 2 / 2 + ((1622566107 / 1000000000)) ^ 2 * (1 + (5640779 / 250000000))) := by
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
  have hd : (2 * ((5790103 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (347354611 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (6032759213 / 50000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13086

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13087
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13087 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13087) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13087 : ℝ) * (13087 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13087) /
    ((13087 : ℝ) * (13087 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13087} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13087}
    (hw : WINDOW (paperDesignP 13087) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13087) c a v - lbar (paperDesignP 13087) c a| ^ (2 * q)
      ∂stdGauss (Fin (13087 - 1)) ∂muI 13087 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13087)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13087}
    (hw : WINDOW (paperDesignP 13087) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13087) c a v - gbar (paperDesignP 13087) c a| ^ (2 * q)
      ∂stdGauss (Fin (13087 - 1)) ∂muI 13087 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13087)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13087) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13087}
    (hw : WINDOW (paperDesignP 13087) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13087 - 1))).real
      {v | sgA (paperDesignP 13087) c a v < √(2 / (13087 : ℝ) * mixtureFloor)}
      ∂muI 13087 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13087 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13087 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13087) c
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

end BstLean.Part266.Row13087

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13087
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13087 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13087)
    (p : Ix 13087 × (Fin (13087 - 1) → ℝ)) :
    sgA (paperDesignP 13087) c p.1 p.2 ^ 2 ≤
      (2 / (13087 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13087).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13087) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13087 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13087 : ℝ) * _ ≤ 2 / 13087 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13087)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13087}
    (hw : WINDOW (paperDesignP 13087) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13087) c a v ^ 8
      ∂stdGauss (Fin (13087 - 1)) ∂muI 13087 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13087).prod (stdGauss (Fin (13087 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13087) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13087) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13087 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13087) c p.1 p.2)
      (√(2 / (13087 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13087)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13087 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13087) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13087}
    (hw : WINDOW (paperDesignP 13087) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13087) c a v -
      ∫ w, sA (paperDesignP 13087) c a w ∂stdGauss (Fin (13087 - 1))) ^ 2
      ∂stdGauss (Fin (13087 - 1))) ^ 2 ∂muI 13087 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13087) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13087

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13087
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13087}
    (hw : WINDOW (paperDesignP 13087) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13087).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13087) c M H xi)
    (hE : centreEnergy (paperDesignP 13087) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13087 : ℝ))))
    (hprice : massBound 13087 M H xi E u mixtureFloor ≤ 13087 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13087 - 1))).real
      {v | sgA (paperDesignP 13087) c a v < √(2 / (13087 : ℝ) * mixtureFloor)}
        ∂muI 13087 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13087).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13087) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13087) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13087)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13087

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13087
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13087) : ℝ :=
  (latitudeC / eR c) / ((13087 : ℝ) * (13087 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13087) / ((13087 : ℝ) * (13087 - 3))

theorem location_variance_on_event {c : Ret 13087}
    (hw : WINDOW (paperDesignP 13087) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13087) c a v - lbar (paperDesignP 13087) c a) ^ 2
      ∂stdGauss (Fin (13087 - 1))) ^ 2 ∂muI 13087 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13087)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13087}
    (hw : WINDOW (paperDesignP 13087) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13087) c a v - gbar (paperDesignP 13087) c a) ^ 2
      ∂stdGauss (Fin (13087 - 1))) ^ 2 ∂muI 13087 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13087)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13087}
    (hw : WINDOW (paperDesignP 13087) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13087 - 1))).real
      {v | sgA (paperDesignP 13087) c a v < √(2 / (13087 : ℝ) * mixtureFloor)}
      ∂muI 13087 ≤ lowMassBudget) :
    LatMom (paperDesignP 13087) c (√(2 / (13087 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13087

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13087
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

theorem location_budget_cap {c : Ret 13087} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13087 : ℝ) * (13087 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13087 : ℝ) * (13087 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13087 : ℝ) /
      ((13087 : ℝ) * (13087 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13087 : ℝ) * (13087 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13087 ≤ (2 * (16 / 5) / 13087 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13087} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (503099061 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (617935459 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (847843531 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4817526121 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (5917165121 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (4059348023 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13087} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15573567 / 500000000000000) ∧ residualVarianceBudget ≤ (2856007 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13087 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4817526121 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13087

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13087
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13087 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13087) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13087) : ℝ :=
  exp (hqKappa * (13087 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5789881 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2894941 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13087} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (847843531 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4059348023 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4059348023 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4059348023 / 125000000000000) : ℝ) / ((5789881 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (2820173 / 125000000) := by
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

theorem hq_location_bounds {c : Ret 13087} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (324500843 / 200000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((847843531 / 250000000000))) / ((5789881 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13087} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13087 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13087 * ((2820173 / 125000000) : ℝ) ^ 2 / 2 + ((324500843 / 200000000)) ^ 2 * (1 + (2820173 / 125000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13087 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13087 * ((2820173 / 125000000)) ^ 2 / 2 + ((324500843 / 200000000)) ^ 2 * (1 + (2820173 / 125000000))) := by
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
  have hd : (2 * ((5789881 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (173683891 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (30166083541 / 250000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13087

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13088
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13088 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13088) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13088 : ℝ) * (13088 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13088) /
    ((13088 : ℝ) * (13088 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13088} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13088}
    (hw : WINDOW (paperDesignP 13088) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13088) c a v - lbar (paperDesignP 13088) c a| ^ (2 * q)
      ∂stdGauss (Fin (13088 - 1)) ∂muI 13088 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13088)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13088}
    (hw : WINDOW (paperDesignP 13088) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13088) c a v - gbar (paperDesignP 13088) c a| ^ (2 * q)
      ∂stdGauss (Fin (13088 - 1)) ∂muI 13088 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13088)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13088) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13088}
    (hw : WINDOW (paperDesignP 13088) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13088 - 1))).real
      {v | sgA (paperDesignP 13088) c a v < √(2 / (13088 : ℝ) * mixtureFloor)}
      ∂muI 13088 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13088 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13088 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13088) c
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

end BstLean.Part266.Row13088

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13088
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13088 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13088)
    (p : Ix 13088 × (Fin (13088 - 1) → ℝ)) :
    sgA (paperDesignP 13088) c p.1 p.2 ^ 2 ≤
      (2 / (13088 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13088).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13088) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13088 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13088 : ℝ) * _ ≤ 2 / 13088 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13088)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13088}
    (hw : WINDOW (paperDesignP 13088) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13088) c a v ^ 8
      ∂stdGauss (Fin (13088 - 1)) ∂muI 13088 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13088).prod (stdGauss (Fin (13088 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13088) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13088) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13088 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13088) c p.1 p.2)
      (√(2 / (13088 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13088)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13088 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13088) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13088}
    (hw : WINDOW (paperDesignP 13088) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13088) c a v -
      ∫ w, sA (paperDesignP 13088) c a w ∂stdGauss (Fin (13088 - 1))) ^ 2
      ∂stdGauss (Fin (13088 - 1))) ^ 2 ∂muI 13088 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13088) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13088

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13088
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13088}
    (hw : WINDOW (paperDesignP 13088) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13088).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13088) c M H xi)
    (hE : centreEnergy (paperDesignP 13088) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13088 : ℝ))))
    (hprice : massBound 13088 M H xi E u mixtureFloor ≤ 13088 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13088 - 1))).real
      {v | sgA (paperDesignP 13088) c a v < √(2 / (13088 : ℝ) * mixtureFloor)}
        ∂muI 13088 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13088).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13088) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13088) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13088)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13088

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13088
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13088) : ℝ :=
  (latitudeC / eR c) / ((13088 : ℝ) * (13088 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13088) / ((13088 : ℝ) * (13088 - 3))

theorem location_variance_on_event {c : Ret 13088}
    (hw : WINDOW (paperDesignP 13088) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13088) c a v - lbar (paperDesignP 13088) c a) ^ 2
      ∂stdGauss (Fin (13088 - 1))) ^ 2 ∂muI 13088 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13088)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13088}
    (hw : WINDOW (paperDesignP 13088) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13088) c a v - gbar (paperDesignP 13088) c a) ^ 2
      ∂stdGauss (Fin (13088 - 1))) ^ 2 ∂muI 13088 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13088)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13088}
    (hw : WINDOW (paperDesignP 13088) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13088 - 1))).real
      {v | sgA (paperDesignP 13088) c a v < √(2 / (13088 : ℝ) * mixtureFloor)}
      ∂muI 13088 ≤ lowMassBudget) :
    LatMom (paperDesignP 13088) c (√(2 / (13088 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13088

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13088
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

theorem location_budget_cap {c : Ret 13088} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13088 : ℝ) * (13088 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13088 : ℝ) * (13088 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13088 : ℝ) /
      ((13088 : ℝ) * (13088 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13088 : ℝ) * (13088 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13088 ≤ (2 * (16 / 5) / 13088 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13088} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (3930161 / 7812500000) ∧
    locationMomentBudget c 6 ≤ (308944111 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (6623271 / 7812500000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2408486937 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (23665947 / 4000000000000) ∧
    residualMomentBudget 12 ≤ (2029441249 / 250000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13088} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15571187 / 500000000000000) ∧ residualVarianceBudget ≤ (2855353 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13088 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2408486937 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13088

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13088
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13088 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13088) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13088) : ℝ :=
  exp (hqKappa * (13088 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((289483 / 50000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5789661 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13088} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (6623271 / 1953125000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (2029441249 / 62500000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (2029441249 / 62500000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((2029441249 / 62500000000000) : ℝ) / ((289483 / 50000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (704989 / 31250000) := by
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

theorem hq_location_bounds {c : Ret 13088} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (324488411 / 200000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((6623271 / 1953125000))) / ((289483 / 50000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13088} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13088 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13088 * ((704989 / 31250000) : ℝ) ^ 2 / 2 + ((324488411 / 200000000)) ^ 2 * (1 + (704989 / 31250000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13088 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13088 * ((704989 / 31250000)) ^ 2 / 2 + ((324488411 / 200000000)) ^ 2 * (1 + (704989 / 31250000))) := by
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
  have hd : (2 * ((289483 / 50000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (347380893 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (6033672161 / 50000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13088

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13089
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13089 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13089) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13089 : ℝ) * (13089 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13089) /
    ((13089 : ℝ) * (13089 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13089} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13089}
    (hw : WINDOW (paperDesignP 13089) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13089) c a v - lbar (paperDesignP 13089) c a| ^ (2 * q)
      ∂stdGauss (Fin (13089 - 1)) ∂muI 13089 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13089)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13089}
    (hw : WINDOW (paperDesignP 13089) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13089) c a v - gbar (paperDesignP 13089) c a| ^ (2 * q)
      ∂stdGauss (Fin (13089 - 1)) ∂muI 13089 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13089)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13089) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13089}
    (hw : WINDOW (paperDesignP 13089) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13089 - 1))).real
      {v | sgA (paperDesignP 13089) c a v < √(2 / (13089 : ℝ) * mixtureFloor)}
      ∂muI 13089 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13089 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13089 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13089) c
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

end BstLean.Part266.Row13089

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13089
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13089 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13089)
    (p : Ix 13089 × (Fin (13089 - 1) → ℝ)) :
    sgA (paperDesignP 13089) c p.1 p.2 ^ 2 ≤
      (2 / (13089 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13089).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13089) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13089 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13089 : ℝ) * _ ≤ 2 / 13089 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13089)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13089}
    (hw : WINDOW (paperDesignP 13089) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13089) c a v ^ 8
      ∂stdGauss (Fin (13089 - 1)) ∂muI 13089 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13089).prod (stdGauss (Fin (13089 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13089) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13089) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13089 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13089) c p.1 p.2)
      (√(2 / (13089 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13089)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13089 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13089) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13089}
    (hw : WINDOW (paperDesignP 13089) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13089) c a v -
      ∫ w, sA (paperDesignP 13089) c a w ∂stdGauss (Fin (13089 - 1))) ^ 2
      ∂stdGauss (Fin (13089 - 1))) ^ 2 ∂muI 13089 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13089) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13089

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13089
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13089}
    (hw : WINDOW (paperDesignP 13089) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13089).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13089) c M H xi)
    (hE : centreEnergy (paperDesignP 13089) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13089 : ℝ))))
    (hprice : massBound 13089 M H xi E u mixtureFloor ≤ 13089 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13089 - 1))).real
      {v | sgA (paperDesignP 13089) c a v < √(2 / (13089 : ℝ) * mixtureFloor)}
        ∂muI 13089 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13089).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13089) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13089) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13089)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13089

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13089
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13089) : ℝ :=
  (latitudeC / eR c) / ((13089 : ℝ) * (13089 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13089) / ((13089 : ℝ) * (13089 - 3))

theorem location_variance_on_event {c : Ret 13089}
    (hw : WINDOW (paperDesignP 13089) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13089) c a v - lbar (paperDesignP 13089) c a) ^ 2
      ∂stdGauss (Fin (13089 - 1))) ^ 2 ∂muI 13089 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13089)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13089}
    (hw : WINDOW (paperDesignP 13089) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13089) c a v - gbar (paperDesignP 13089) c a) ^ 2
      ∂stdGauss (Fin (13089 - 1))) ^ 2 ∂muI 13089 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13089)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13089}
    (hw : WINDOW (paperDesignP 13089) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13089 - 1))).real
      {v | sgA (paperDesignP 13089) c a v < √(2 / (13089 : ℝ) * mixtureFloor)}
      ∂muI 13089 ≤ lowMassBudget) :
    LatMom (paperDesignP 13089) c (√(2 / (13089 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13089

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13089
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

theorem location_budget_cap {c : Ret 13089} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13089 : ℝ) * (13089 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13089 : ℝ) * (13089 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13089 : ℝ) /
      ((13089 : ℝ) * (13089 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13089 : ℝ) * (13089 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13089 ≤ (2 * (16 / 5) / 13089 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13089} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (503022161 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (19307531 / 31250000000) ∧
    locationMomentBudget c 12 ≤ (13245529 / 15625000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4816421733 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (5915808509 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (64934673 / 8000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13089} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (6227523 / 200000000000000) ∧ residualVarianceBudget ≤ (1427349 / 500000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13089 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4816421733 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13089

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13089
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13089 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13089) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13089) : ℝ :=
  exp (hqKappa * (13089 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5789439 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (4523 / 781250) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13089} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (13245529 / 3906250000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (64934673 / 2000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (64934673 / 2000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((64934673 / 2000000000000) : ℝ) / ((5789439 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22557913 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 13089} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1622379911 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((13245529 / 3906250000))) / ((5789439 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13089} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13089 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13089 * ((22557913 / 1000000000) : ℝ) ^ 2 / 2 + ((1622379911 / 1000000000)) ^ 2 * (1 + (22557913 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13089 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13089 * ((22557913 / 1000000000)) ^ 2 / 2 + ((1622379911 / 1000000000)) ^ 2 * (1 + (22557913 / 1000000000))) := by
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
  have hd : (2 * ((5789439 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (173697003 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (60341276669 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13089

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13090
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13090 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13090) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13090 : ℝ) * (13090 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13090) /
    ((13090 : ℝ) * (13090 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13090} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13090}
    (hw : WINDOW (paperDesignP 13090) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13090) c a v - lbar (paperDesignP 13090) c a| ^ (2 * q)
      ∂stdGauss (Fin (13090 - 1)) ∂muI 13090 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13090)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13090}
    (hw : WINDOW (paperDesignP 13090) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13090) c a v - gbar (paperDesignP 13090) c a| ^ (2 * q)
      ∂stdGauss (Fin (13090 - 1)) ∂muI 13090 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13090)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13090) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13090}
    (hw : WINDOW (paperDesignP 13090) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13090 - 1))).real
      {v | sgA (paperDesignP 13090) c a v < √(2 / (13090 : ℝ) * mixtureFloor)}
      ∂muI 13090 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13090 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13090 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13090) c
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

end BstLean.Part266.Row13090

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13090
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13090 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13090)
    (p : Ix 13090 × (Fin (13090 - 1) → ℝ)) :
    sgA (paperDesignP 13090) c p.1 p.2 ^ 2 ≤
      (2 / (13090 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13090).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13090) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13090 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13090 : ℝ) * _ ≤ 2 / 13090 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13090)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13090}
    (hw : WINDOW (paperDesignP 13090) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13090) c a v ^ 8
      ∂stdGauss (Fin (13090 - 1)) ∂muI 13090 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13090).prod (stdGauss (Fin (13090 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13090) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13090) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13090 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13090) c p.1 p.2)
      (√(2 / (13090 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13090)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13090 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13090) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13090}
    (hw : WINDOW (paperDesignP 13090) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13090) c a v -
      ∫ w, sA (paperDesignP 13090) c a w ∂stdGauss (Fin (13090 - 1))) ^ 2
      ∂stdGauss (Fin (13090 - 1))) ^ 2 ∂muI 13090 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13090) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13090

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13090
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13090}
    (hw : WINDOW (paperDesignP 13090) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13090).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13090) c M H xi)
    (hE : centreEnergy (paperDesignP 13090) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13090 : ℝ))))
    (hprice : massBound 13090 M H xi E u mixtureFloor ≤ 13090 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13090 - 1))).real
      {v | sgA (paperDesignP 13090) c a v < √(2 / (13090 : ℝ) * mixtureFloor)}
        ∂muI 13090 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13090).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13090) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13090) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13090)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13090

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13090
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13090) : ℝ :=
  (latitudeC / eR c) / ((13090 : ℝ) * (13090 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13090) / ((13090 : ℝ) * (13090 - 3))

theorem location_variance_on_event {c : Ret 13090}
    (hw : WINDOW (paperDesignP 13090) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13090) c a v - lbar (paperDesignP 13090) c a) ^ 2
      ∂stdGauss (Fin (13090 - 1))) ^ 2 ∂muI 13090 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13090)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13090}
    (hw : WINDOW (paperDesignP 13090) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13090) c a v - gbar (paperDesignP 13090) c a) ^ 2
      ∂stdGauss (Fin (13090 - 1))) ^ 2 ∂muI 13090 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13090)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13090}
    (hw : WINDOW (paperDesignP 13090) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13090 - 1))).real
      {v | sgA (paperDesignP 13090) c a v < √(2 / (13090 : ℝ) * mixtureFloor)}
      ∂muI 13090 ≤ lowMassBudget) :
    LatMom (paperDesignP 13090) c (√(2 / (13090 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13090

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13090
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

theorem location_budget_cap {c : Ret 13090} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13090 : ℝ) * (13090 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13090 : ℝ) * (13090 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13090 : ℝ) /
      ((13090 : ℝ) * (13090 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13090 : ℝ) * (13090 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13090 ≤ (2 * (16 / 5) / 13090 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13090} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (12574593 / 25000000000) ∧
    locationMomentBudget c 6 ≤ (617793769 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (423824517 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4815869697 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (5915130397 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (8115903431 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13090} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15566429 / 500000000000000) ∧ residualVarianceBudget ≤ (713511 / 250000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13090 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4815869697 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13090

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13090
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13090 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13090) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13090) : ℝ :=
  exp (hqKappa * (13090 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((2894609 / 500000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5789219 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13090} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (423824517 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8115903431 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8115903431 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8115903431 / 250000000000000) : ℝ) / ((2894609 / 500000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11278089 / 500000000) := by
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

theorem hq_location_bounds {c : Ret 13090} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1622317781 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((423824517 / 125000000000))) / ((2894609 / 500000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13090} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13090 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13090 * ((11278089 / 500000000) : ℝ) ^ 2 / 2 + ((1622317781 / 1000000000)) ^ 2 * (1 + (11278089 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13090 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13090 * ((11278089 / 500000000)) ^ 2 / 2 + ((1622317781 / 1000000000)) ^ 2 * (1 + (11278089 / 500000000))) := by
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
  have hd : (2 * ((2894609 / 500000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (347407119 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (30172916129 / 250000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13090

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13091
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13091 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13091) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13091 : ℝ) * (13091 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13091) /
    ((13091 : ℝ) * (13091 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13091} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13091}
    (hw : WINDOW (paperDesignP 13091) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13091) c a v - lbar (paperDesignP 13091) c a| ^ (2 * q)
      ∂stdGauss (Fin (13091 - 1)) ∂muI 13091 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13091)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13091}
    (hw : WINDOW (paperDesignP 13091) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13091) c a v - gbar (paperDesignP 13091) c a| ^ (2 * q)
      ∂stdGauss (Fin (13091 - 1)) ∂muI 13091 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13091)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13091) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13091}
    (hw : WINDOW (paperDesignP 13091) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13091 - 1))).real
      {v | sgA (paperDesignP 13091) c a v < √(2 / (13091 : ℝ) * mixtureFloor)}
      ∂muI 13091 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13091 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13091 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13091) c
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

end BstLean.Part266.Row13091

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13091
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13091 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13091)
    (p : Ix 13091 × (Fin (13091 - 1) → ℝ)) :
    sgA (paperDesignP 13091) c p.1 p.2 ^ 2 ≤
      (2 / (13091 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13091).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13091) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13091 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13091 : ℝ) * _ ≤ 2 / 13091 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13091)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13091}
    (hw : WINDOW (paperDesignP 13091) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13091) c a v ^ 8
      ∂stdGauss (Fin (13091 - 1)) ∂muI 13091 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13091).prod (stdGauss (Fin (13091 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13091) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13091) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13091 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13091) c p.1 p.2)
      (√(2 / (13091 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13091)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13091 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13091) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13091}
    (hw : WINDOW (paperDesignP 13091) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13091) c a v -
      ∫ w, sA (paperDesignP 13091) c a w ∂stdGauss (Fin (13091 - 1))) ^ 2
      ∂stdGauss (Fin (13091 - 1))) ^ 2 ∂muI 13091 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13091) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13091

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13091
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13091}
    (hw : WINDOW (paperDesignP 13091) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13091).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13091) c M H xi)
    (hE : centreEnergy (paperDesignP 13091) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13091 : ℝ))))
    (hprice : massBound 13091 M H xi E u mixtureFloor ≤ 13091 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13091 - 1))).real
      {v | sgA (paperDesignP 13091) c a v < √(2 / (13091 : ℝ) * mixtureFloor)}
        ∂muI 13091 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13091).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13091) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13091) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13091)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13091

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13091
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13091) : ℝ :=
  (latitudeC / eR c) / ((13091 : ℝ) * (13091 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13091) / ((13091 : ℝ) * (13091 - 3))

theorem location_variance_on_event {c : Ret 13091}
    (hw : WINDOW (paperDesignP 13091) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13091) c a v - lbar (paperDesignP 13091) c a) ^ 2
      ∂stdGauss (Fin (13091 - 1))) ^ 2 ∂muI 13091 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13091)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13091}
    (hw : WINDOW (paperDesignP 13091) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13091) c a v - gbar (paperDesignP 13091) c a) ^ 2
      ∂stdGauss (Fin (13091 - 1))) ^ 2 ∂muI 13091 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13091)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13091}
    (hw : WINDOW (paperDesignP 13091) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13091 - 1))).real
      {v | sgA (paperDesignP 13091) c a v < √(2 / (13091 : ℝ) * mixtureFloor)}
      ∂muI 13091 ≤ lowMassBudget) :
    LatMom (paperDesignP 13091) c (√(2 / (13091 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13091

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13091
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

theorem location_budget_cap {c : Ret 13091} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13091 : ℝ) * (13091 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13091 : ℝ) * (13091 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13091 : ℝ) /
      ((13091 : ℝ) * (13091 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13091 : ℝ) * (13091 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13091 ≤ (2 * (16 / 5) / 13091 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13091} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (125736321 / 250000000000) ∧
    locationMomentBudget c 6 ≤ (617746553 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (847584221 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2407658883 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (1182890483 / 200000000000000) ∧
    residualMomentBudget 12 ≤ (4057486457 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13091} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (31128101 / 1000000000000000) ∧ residualVarianceBudget ≤ (285339 / 100000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13091 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2407658883 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13091

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13091
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13091 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13091) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13091) : ℝ :=
  exp (hqKappa * (13091 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5788997 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2894499 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13091} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (847584221 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4057486457 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4057486457 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4057486457 / 125000000000000) : ℝ) / ((5788997 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22554443 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 13091} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (101390979 / 62500000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((847584221 / 250000000000))) / ((5788997 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13091} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13091 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13091 * ((22554443 / 1000000000) : ℝ) ^ 2 / 2 + ((101390979 / 62500000)) ^ 2 * (1 + (22554443 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13091 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13091 * ((22554443 / 1000000000)) ^ 2 / 2 + ((101390979 / 62500000)) ^ 2 * (1 + (22554443 / 1000000000))) := by
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
  have hd : (2 * ((5788997 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (347420233 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (24140155351 / 200000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13091

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13092
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13092 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13092) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13092 : ℝ) * (13092 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13092) /
    ((13092 : ℝ) * (13092 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13092} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13092}
    (hw : WINDOW (paperDesignP 13092) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13092) c a v - lbar (paperDesignP 13092) c a| ^ (2 * q)
      ∂stdGauss (Fin (13092 - 1)) ∂muI 13092 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13092)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13092}
    (hw : WINDOW (paperDesignP 13092) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13092) c a v - gbar (paperDesignP 13092) c a| ^ (2 * q)
      ∂stdGauss (Fin (13092 - 1)) ∂muI 13092 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13092)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13092) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13092}
    (hw : WINDOW (paperDesignP 13092) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13092 - 1))).real
      {v | sgA (paperDesignP 13092) c a v < √(2 / (13092 : ℝ) * mixtureFloor)}
      ∂muI 13092 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13092 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13092 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13092) c
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

end BstLean.Part266.Row13092

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13092
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13092 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13092)
    (p : Ix 13092 × (Fin (13092 - 1) → ℝ)) :
    sgA (paperDesignP 13092) c p.1 p.2 ^ 2 ≤
      (2 / (13092 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13092).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13092) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13092 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13092 : ℝ) * _ ≤ 2 / 13092 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13092)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13092}
    (hw : WINDOW (paperDesignP 13092) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13092) c a v ^ 8
      ∂stdGauss (Fin (13092 - 1)) ∂muI 13092 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13092).prod (stdGauss (Fin (13092 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13092) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13092) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13092 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13092) c p.1 p.2)
      (√(2 / (13092 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13092)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13092 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13092) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13092}
    (hw : WINDOW (paperDesignP 13092) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13092) c a v -
      ∫ w, sA (paperDesignP 13092) c a w ∂stdGauss (Fin (13092 - 1))) ^ 2
      ∂stdGauss (Fin (13092 - 1))) ^ 2 ∂muI 13092 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13092) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13092

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13092
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13092}
    (hw : WINDOW (paperDesignP 13092) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13092).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13092) c M H xi)
    (hE : centreEnergy (paperDesignP 13092) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13092 : ℝ))))
    (hprice : massBound 13092 M H xi E u mixtureFloor ≤ 13092 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13092 - 1))).real
      {v | sgA (paperDesignP 13092) c a v < √(2 / (13092 : ℝ) * mixtureFloor)}
        ∂muI 13092 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13092).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13092) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13092) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13092)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13092

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13092
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13092) : ℝ :=
  (latitudeC / eR c) / ((13092 : ℝ) * (13092 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13092) / ((13092 : ℝ) * (13092 - 3))

theorem location_variance_on_event {c : Ret 13092}
    (hw : WINDOW (paperDesignP 13092) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13092) c a v - lbar (paperDesignP 13092) c a) ^ 2
      ∂stdGauss (Fin (13092 - 1))) ^ 2 ∂muI 13092 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13092)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13092}
    (hw : WINDOW (paperDesignP 13092) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13092) c a v - gbar (paperDesignP 13092) c a) ^ 2
      ∂stdGauss (Fin (13092 - 1))) ^ 2 ∂muI 13092 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13092)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13092}
    (hw : WINDOW (paperDesignP 13092) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13092 - 1))).real
      {v | sgA (paperDesignP 13092) c a v < √(2 / (13092 : ℝ) * mixtureFloor)}
      ∂muI 13092 ≤ lowMassBudget) :
    LatMom (paperDesignP 13092) c (√(2 / (13092 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13092

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13092
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

theorem location_budget_cap {c : Ret 13092} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13092 : ℝ) * (13092 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13092 : ℝ) * (13092 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13092 : ℝ) /
      ((13092 : ℝ) * (13092 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13092 : ℝ) * (13092 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13092 ≤ (2 * (16 / 5) / 13092 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13092} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (100581371 / 200000000000) ∧
    locationMomentBudget c 6 ≤ (38606209 / 62500000000) ∧
    locationMomentBudget c 12 ≤ (847519419 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4814765941 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (2956887281 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (507127661 / 62500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13092} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (6224669 / 200000000000000) ∧ residualVarianceBudget ≤ (22287 / 7812500000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13092 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4814765941 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13092

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13092
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13092 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13092) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13092) : ℝ :=
  exp (hqKappa * (13092 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((723597 / 125000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5788777 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13092} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (847519419 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (507127661 / 15625000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (507127661 / 15625000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((507127661 / 15625000000000) : ℝ) / ((723597 / 125000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (5638177 / 250000000) := by
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

theorem hq_location_bounds {c : Ret 13092} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1622193563 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((847519419 / 250000000000))) / ((723597 / 125000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13092} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13092 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13092 * ((5638177 / 250000000) : ℝ) ^ 2 / 2 + ((1622193563 / 1000000000)) ^ 2 * (1 + (5638177 / 250000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13092 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13092 * ((5638177 / 250000000)) ^ 2 / 2 + ((1622193563 / 1000000000)) ^ 2 * (1 + (5638177 / 250000000))) := by
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
  have hd : (2 * ((723597 / 125000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (347433349 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (15088736257 / 125000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13092

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13093
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13093 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13093) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13093 : ℝ) * (13093 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13093) /
    ((13093 : ℝ) * (13093 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13093} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13093}
    (hw : WINDOW (paperDesignP 13093) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13093) c a v - lbar (paperDesignP 13093) c a| ^ (2 * q)
      ∂stdGauss (Fin (13093 - 1)) ∂muI 13093 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13093)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13093}
    (hw : WINDOW (paperDesignP 13093) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13093) c a v - gbar (paperDesignP 13093) c a| ^ (2 * q)
      ∂stdGauss (Fin (13093 - 1)) ∂muI 13093 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13093)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13093) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13093}
    (hw : WINDOW (paperDesignP 13093) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13093 - 1))).real
      {v | sgA (paperDesignP 13093) c a v < √(2 / (13093 : ℝ) * mixtureFloor)}
      ∂muI 13093 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13093 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13093 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13093) c
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

end BstLean.Part266.Row13093

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13093
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13093 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13093)
    (p : Ix 13093 × (Fin (13093 - 1) → ℝ)) :
    sgA (paperDesignP 13093) c p.1 p.2 ^ 2 ≤
      (2 / (13093 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13093).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13093) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13093 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13093 : ℝ) * _ ≤ 2 / 13093 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13093)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13093}
    (hw : WINDOW (paperDesignP 13093) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13093) c a v ^ 8
      ∂stdGauss (Fin (13093 - 1)) ∂muI 13093 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13093).prod (stdGauss (Fin (13093 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13093) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13093) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13093 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13093) c p.1 p.2)
      (√(2 / (13093 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13093)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13093 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13093) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13093}
    (hw : WINDOW (paperDesignP 13093) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13093) c a v -
      ∫ w, sA (paperDesignP 13093) c a w ∂stdGauss (Fin (13093 - 1))) ^ 2
      ∂stdGauss (Fin (13093 - 1))) ^ 2 ∂muI 13093 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13093) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13093

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13093
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13093}
    (hw : WINDOW (paperDesignP 13093) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13093).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13093) c M H xi)
    (hE : centreEnergy (paperDesignP 13093) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13093 : ℝ))))
    (hprice : massBound 13093 M H xi E u mixtureFloor ≤ 13093 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13093 - 1))).real
      {v | sgA (paperDesignP 13093) c a v < √(2 / (13093 : ℝ) * mixtureFloor)}
        ∂muI 13093 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13093).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13093) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13093) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13093)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13093

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13093
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13093) : ℝ :=
  (latitudeC / eR c) / ((13093 : ℝ) * (13093 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13093) / ((13093 : ℝ) * (13093 - 3))

theorem location_variance_on_event {c : Ret 13093}
    (hw : WINDOW (paperDesignP 13093) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13093) c a v - lbar (paperDesignP 13093) c a) ^ 2
      ∂stdGauss (Fin (13093 - 1))) ^ 2 ∂muI 13093 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13093)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13093}
    (hw : WINDOW (paperDesignP 13093) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13093) c a v - gbar (paperDesignP 13093) c a) ^ 2
      ∂stdGauss (Fin (13093 - 1))) ^ 2 ∂muI 13093 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13093)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13093}
    (hw : WINDOW (paperDesignP 13093) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13093 - 1))).real
      {v | sgA (paperDesignP 13093) c a v < √(2 / (13093 : ℝ) * mixtureFloor)}
      ∂muI 13093 ≤ lowMassBudget) :
    LatMom (paperDesignP 13093) c (√(2 / (13093 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13093

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13093
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

theorem location_budget_cap {c : Ret 13093} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13093 : ℝ) * (13093 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13093 : ℝ) * (13093 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13093 : ℝ) /
      ((13093 : ℝ) * (13093 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13093 : ℝ) * (13093 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13093 ≤ (2 * (16 / 5) / 13093 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13093} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (502868431 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (617652143 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (423727313 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4814214221 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (5913096839 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (1622622483 / 200000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13093} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (31118591 / 1000000000000000) ∧ residualVarianceBudget ≤ (1426041 / 500000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13093 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4814214221 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13093

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13093
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13093 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13093) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13093) : ℝ :=
  exp (hqKappa * (13093 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((1157711 / 200000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (1447139 / 250000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13093} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (423727313 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (1622622483 / 50000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (1622622483 / 50000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((1622622483 / 50000000000000) : ℝ) / ((1157711 / 200000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11275487 / 500000000) := by
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

theorem hq_location_bounds {c : Ret 13093} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (64885259 / 40000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((423727313 / 125000000000))) / ((1157711 / 200000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13093} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13093 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13093 * ((11275487 / 500000000) : ℝ) ^ 2 / 2 + ((64885259 / 40000000)) ^ 2 * (1 + (11275487 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13093 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13093 * ((11275487 / 500000000)) ^ 2 / 2 + ((64885259 / 40000000)) ^ 2 * (1 + (11275487 / 500000000))) := by
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
  have hd : (2 * ((1157711 / 200000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (69489293 / 200000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (120719004419 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13093

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13094
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13094 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13094) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13094 : ℝ) * (13094 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13094) /
    ((13094 : ℝ) * (13094 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13094} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13094}
    (hw : WINDOW (paperDesignP 13094) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13094) c a v - lbar (paperDesignP 13094) c a| ^ (2 * q)
      ∂stdGauss (Fin (13094 - 1)) ∂muI 13094 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13094)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13094}
    (hw : WINDOW (paperDesignP 13094) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13094) c a v - gbar (paperDesignP 13094) c a| ^ (2 * q)
      ∂stdGauss (Fin (13094 - 1)) ∂muI 13094 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13094)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13094) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13094}
    (hw : WINDOW (paperDesignP 13094) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13094 - 1))).real
      {v | sgA (paperDesignP 13094) c a v < √(2 / (13094 : ℝ) * mixtureFloor)}
      ∂muI 13094 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13094 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13094 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13094) c
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

end BstLean.Part266.Row13094

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13094
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13094 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13094)
    (p : Ix 13094 × (Fin (13094 - 1) → ℝ)) :
    sgA (paperDesignP 13094) c p.1 p.2 ^ 2 ≤
      (2 / (13094 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13094).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13094) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13094 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13094 : ℝ) * _ ≤ 2 / 13094 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13094)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13094}
    (hw : WINDOW (paperDesignP 13094) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13094) c a v ^ 8
      ∂stdGauss (Fin (13094 - 1)) ∂muI 13094 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13094).prod (stdGauss (Fin (13094 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13094) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13094) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13094 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13094) c p.1 p.2)
      (√(2 / (13094 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13094)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13094 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13094) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13094}
    (hw : WINDOW (paperDesignP 13094) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13094) c a v -
      ∫ w, sA (paperDesignP 13094) c a w ∂stdGauss (Fin (13094 - 1))) ^ 2
      ∂stdGauss (Fin (13094 - 1))) ^ 2 ∂muI 13094 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13094) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13094

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13094
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13094}
    (hw : WINDOW (paperDesignP 13094) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13094).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13094) c M H xi)
    (hE : centreEnergy (paperDesignP 13094) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13094 : ℝ))))
    (hprice : massBound 13094 M H xi E u mixtureFloor ≤ 13094 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13094 - 1))).real
      {v | sgA (paperDesignP 13094) c a v < √(2 / (13094 : ℝ) * mixtureFloor)}
        ∂muI 13094 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13094).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13094) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13094) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13094)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13094

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13094
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13094) : ℝ :=
  (latitudeC / eR c) / ((13094 : ℝ) * (13094 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13094) / ((13094 : ℝ) * (13094 - 3))

theorem location_variance_on_event {c : Ret 13094}
    (hw : WINDOW (paperDesignP 13094) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13094) c a v - lbar (paperDesignP 13094) c a) ^ 2
      ∂stdGauss (Fin (13094 - 1))) ^ 2 ∂muI 13094 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13094)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13094}
    (hw : WINDOW (paperDesignP 13094) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13094) c a v - gbar (paperDesignP 13094) c a) ^ 2
      ∂stdGauss (Fin (13094 - 1))) ^ 2 ∂muI 13094 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13094)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13094}
    (hw : WINDOW (paperDesignP 13094) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13094 - 1))).real
      {v | sgA (paperDesignP 13094) c a v < √(2 / (13094 : ℝ) * mixtureFloor)}
      ∂muI 13094 ≤ lowMassBudget) :
    LatMom (paperDesignP 13094) c (√(2 / (13094 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13094

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13094
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

theorem location_budget_cap {c : Ret 13094} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13094 : ℝ) * (13094 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13094 : ℝ) * (13094 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13094 : ℝ) /
      ((13094 : ℝ) * (13094 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13094 : ℝ) * (13094 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13094 ≤ (2 * (16 / 5) / 13094 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13094} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (251415007 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (617604949 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (847389843 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4813662607 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (1182483849 / 200000000000000) ∧
    residualMomentBudget 12 ≤ (8112182433 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13094} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (31113837 / 1000000000000000) ∧ residualVarianceBudget ≤ (2851429 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13094 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4813662607 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13094

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13094
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13094 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13094) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13094) : ℝ :=
  exp (hqKappa * (13094 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((2894167 / 500000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (1157667 / 200000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13094} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (847389843 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8112182433 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8112182433 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8112182433 / 250000000000000) : ℝ) / ((2894167 / 500000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22549241 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 13094} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1622069401 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((847389843 / 250000000000))) / ((2894167 / 500000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13094} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13094 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13094 * ((22549241 / 1000000000) : ℝ) ^ 2 / 2 + ((1622069401 / 1000000000)) ^ 2 * (1 + (22549241 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13094 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13094 * ((22549241 / 1000000000)) ^ 2 / 2 + ((1622069401 / 1000000000)) ^ 2 * (1 + (22549241 / 1000000000))) := by
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
  have hd : (2 * ((2894167 / 500000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (347459583 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (120728119843 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13094

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13095
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13095 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13095) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13095 : ℝ) * (13095 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13095) /
    ((13095 : ℝ) * (13095 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13095} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13095}
    (hw : WINDOW (paperDesignP 13095) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13095) c a v - lbar (paperDesignP 13095) c a| ^ (2 * q)
      ∂stdGauss (Fin (13095 - 1)) ∂muI 13095 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13095)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13095}
    (hw : WINDOW (paperDesignP 13095) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13095) c a v - gbar (paperDesignP 13095) c a| ^ (2 * q)
      ∂stdGauss (Fin (13095 - 1)) ∂muI 13095 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13095)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13095) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13095}
    (hw : WINDOW (paperDesignP 13095) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13095 - 1))).real
      {v | sgA (paperDesignP 13095) c a v < √(2 / (13095 : ℝ) * mixtureFloor)}
      ∂muI 13095 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13095 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13095 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13095) c
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

end BstLean.Part266.Row13095

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13095
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13095 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13095)
    (p : Ix 13095 × (Fin (13095 - 1) → ℝ)) :
    sgA (paperDesignP 13095) c p.1 p.2 ^ 2 ≤
      (2 / (13095 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13095).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13095) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13095 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13095 : ℝ) * _ ≤ 2 / 13095 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13095)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13095}
    (hw : WINDOW (paperDesignP 13095) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13095) c a v ^ 8
      ∂stdGauss (Fin (13095 - 1)) ∂muI 13095 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13095).prod (stdGauss (Fin (13095 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13095) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13095) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13095 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13095) c p.1 p.2)
      (√(2 / (13095 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13095)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13095 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13095) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13095}
    (hw : WINDOW (paperDesignP 13095) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13095) c a v -
      ∫ w, sA (paperDesignP 13095) c a w ∂stdGauss (Fin (13095 - 1))) ^ 2
      ∂stdGauss (Fin (13095 - 1))) ^ 2 ∂muI 13095 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13095) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13095

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13095
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13095}
    (hw : WINDOW (paperDesignP 13095) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13095).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13095) c M H xi)
    (hE : centreEnergy (paperDesignP 13095) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13095 : ℝ))))
    (hprice : massBound 13095 M H xi E u mixtureFloor ≤ 13095 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13095 - 1))).real
      {v | sgA (paperDesignP 13095) c a v < √(2 / (13095 : ℝ) * mixtureFloor)}
        ∂muI 13095 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13095).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13095) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13095) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13095)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13095

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13095
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13095) : ℝ :=
  (latitudeC / eR c) / ((13095 : ℝ) * (13095 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13095) / ((13095 : ℝ) * (13095 - 3))

theorem location_variance_on_event {c : Ret 13095}
    (hw : WINDOW (paperDesignP 13095) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13095) c a v - lbar (paperDesignP 13095) c a) ^ 2
      ∂stdGauss (Fin (13095 - 1))) ^ 2 ∂muI 13095 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13095)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13095}
    (hw : WINDOW (paperDesignP 13095) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13095) c a v - gbar (paperDesignP 13095) c a) ^ 2
      ∂stdGauss (Fin (13095 - 1))) ^ 2 ∂muI 13095 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13095)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13095}
    (hw : WINDOW (paperDesignP 13095) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13095 - 1))).real
      {v | sgA (paperDesignP 13095) c a v < √(2 / (13095 : ℝ) * mixtureFloor)}
      ∂muI 13095 ≤ lowMassBudget) :
    LatMom (paperDesignP 13095) c (√(2 / (13095 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13095

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13095
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

theorem location_budget_cap {c : Ret 13095} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13095 : ℝ) * (13095 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13095 : ℝ) * (13095 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13095 : ℝ) /
      ((13095 : ℝ) * (13095 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13095 : ℝ) * (13095 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13095 ≤ (2 * (16 / 5) / 13095 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13095} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (251395801 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (308778881 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (847325071 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2406555549 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (5911741781 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (8111252627 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13095} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (6221817 / 200000000000000) ∧ residualVarianceBudget ≤ (356347 / 125000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13095 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2406555549 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13095

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13095
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13095 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13095) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13095) : ℝ :=
  exp (hqKappa * (13095 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5788113 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2894057 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13095} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (847325071 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8111252627 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8111252627 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8111252627 / 250000000000000) : ℝ) / ((5788113 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22547507 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 13095} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1622007343 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((847325071 / 250000000000))) / ((5788113 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13095} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13095 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13095 * ((22547507 / 1000000000) : ℝ) ^ 2 / 2 + ((1622007343 / 1000000000)) ^ 2 * (1 + (22547507 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13095 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13095 * ((22547507 / 1000000000)) ^ 2 / 2 + ((1622007343 / 1000000000)) ^ 2 * (1 + (22547507 / 1000000000))) := by
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
  have hd : (2 * ((5788113 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (347472701 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (120737236329 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13095

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13096
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13096 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13096) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13096 : ℝ) * (13096 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13096) /
    ((13096 : ℝ) * (13096 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13096} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13096}
    (hw : WINDOW (paperDesignP 13096) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13096) c a v - lbar (paperDesignP 13096) c a| ^ (2 * q)
      ∂stdGauss (Fin (13096 - 1)) ∂muI 13096 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13096)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13096}
    (hw : WINDOW (paperDesignP 13096) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13096) c a v - gbar (paperDesignP 13096) c a| ^ (2 * q)
      ∂stdGauss (Fin (13096 - 1)) ∂muI 13096 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13096)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13096) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13096}
    (hw : WINDOW (paperDesignP 13096) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13096 - 1))).real
      {v | sgA (paperDesignP 13096) c a v < √(2 / (13096 : ℝ) * mixtureFloor)}
      ∂muI 13096 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13096 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13096 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13096) c
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

end BstLean.Part266.Row13096

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13096
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13096 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13096)
    (p : Ix 13096 × (Fin (13096 - 1) → ℝ)) :
    sgA (paperDesignP 13096) c p.1 p.2 ^ 2 ≤
      (2 / (13096 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13096).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13096) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13096 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13096 : ℝ) * _ ≤ 2 / 13096 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13096)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13096}
    (hw : WINDOW (paperDesignP 13096) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13096) c a v ^ 8
      ∂stdGauss (Fin (13096 - 1)) ∂muI 13096 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13096).prod (stdGauss (Fin (13096 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13096) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13096) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13096 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13096) c p.1 p.2)
      (√(2 / (13096 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13096)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13096 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13096) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13096}
    (hw : WINDOW (paperDesignP 13096) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13096) c a v -
      ∫ w, sA (paperDesignP 13096) c a w ∂stdGauss (Fin (13096 - 1))) ^ 2
      ∂stdGauss (Fin (13096 - 1))) ^ 2 ∂muI 13096 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13096) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13096

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13096
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13096}
    (hw : WINDOW (paperDesignP 13096) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13096).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13096) c M H xi)
    (hE : centreEnergy (paperDesignP 13096) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13096 : ℝ))))
    (hprice : massBound 13096 M H xi E u mixtureFloor ≤ 13096 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13096 - 1))).real
      {v | sgA (paperDesignP 13096) c a v < √(2 / (13096 : ℝ) * mixtureFloor)}
        ∂muI 13096 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13096).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13096) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13096) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13096)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13096

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13096
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13096) : ℝ :=
  (latitudeC / eR c) / ((13096 : ℝ) * (13096 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13096) / ((13096 : ℝ) * (13096 - 3))

theorem location_variance_on_event {c : Ret 13096}
    (hw : WINDOW (paperDesignP 13096) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13096) c a v - lbar (paperDesignP 13096) c a) ^ 2
      ∂stdGauss (Fin (13096 - 1))) ^ 2 ∂muI 13096 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13096)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13096}
    (hw : WINDOW (paperDesignP 13096) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13096) c a v - gbar (paperDesignP 13096) c a) ^ 2
      ∂stdGauss (Fin (13096 - 1))) ^ 2 ∂muI 13096 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13096)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13096}
    (hw : WINDOW (paperDesignP 13096) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13096 - 1))).real
      {v | sgA (paperDesignP 13096) c a v < √(2 / (13096 : ℝ) * mixtureFloor)}
      ∂muI 13096 ≤ lowMassBudget) :
    LatMom (paperDesignP 13096) c (√(2 / (13096 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13096

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13096
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

theorem location_budget_cap {c : Ret 13096} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13096 : ℝ) * (13096 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13096 : ℝ) * (13096 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13096 : ℝ) /
      ((13096 : ℝ) * (13096 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13096 : ℝ) * (13096 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13096 ≤ (2 * (16 / 5) / 13096 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13096} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (125688299 / 250000000000) ∧
    locationMomentBudget c 6 ≤ (617510583 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (211815077 / 250000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2406279847 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (1182212889 / 200000000000000) ∧
    residualMomentBudget 12 ≤ (8110323 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13096} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15552167 / 500000000000000) ∧ residualVarianceBudget ≤ (2850123 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13096 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2406279847 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13096

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13096
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13096 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13096) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13096) : ℝ :=
  exp (hqKappa * (13096 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((1446973 / 250000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5787893 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13096} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (211815077 / 62500000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8110323 / 250000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8110323 / 250000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8110323 / 250000000000) : ℝ) / ((1446973 / 250000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (901831 / 40000000) := by
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

theorem hq_location_bounds {c : Ret 13096} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (810972649 / 500000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((211815077 / 62500000000))) / ((1446973 / 250000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13096} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13096 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13096 * ((901831 / 40000000) : ℝ) ^ 2 / 2 + ((810972649 / 500000000)) ^ 2 * (1 + (901831 / 40000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13096 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13096 * ((901831 / 40000000)) ^ 2 / 2 + ((810972649 / 500000000)) ^ 2 * (1 + (901831 / 40000000))) := by
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
  have hd : (2 * ((1446973 / 250000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (347485821 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (60373176939 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13096

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13097
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13097 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13097) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13097 : ℝ) * (13097 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13097) /
    ((13097 : ℝ) * (13097 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13097} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13097}
    (hw : WINDOW (paperDesignP 13097) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13097) c a v - lbar (paperDesignP 13097) c a| ^ (2 * q)
      ∂stdGauss (Fin (13097 - 1)) ∂muI 13097 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13097)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13097}
    (hw : WINDOW (paperDesignP 13097) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13097) c a v - gbar (paperDesignP 13097) c a| ^ (2 * q)
      ∂stdGauss (Fin (13097 - 1)) ∂muI 13097 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13097)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13097) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13097}
    (hw : WINDOW (paperDesignP 13097) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13097 - 1))).real
      {v | sgA (paperDesignP 13097) c a v < √(2 / (13097 : ℝ) * mixtureFloor)}
      ∂muI 13097 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13097 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13097 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13097) c
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

end BstLean.Part266.Row13097

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13097
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13097 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13097)
    (p : Ix 13097 × (Fin (13097 - 1) → ℝ)) :
    sgA (paperDesignP 13097) c p.1 p.2 ^ 2 ≤
      (2 / (13097 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13097).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13097) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13097 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13097 : ℝ) * _ ≤ 2 / 13097 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13097)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13097}
    (hw : WINDOW (paperDesignP 13097) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13097) c a v ^ 8
      ∂stdGauss (Fin (13097 - 1)) ∂muI 13097 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13097).prod (stdGauss (Fin (13097 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13097) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13097) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13097 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13097) c p.1 p.2)
      (√(2 / (13097 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13097)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13097 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13097) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13097}
    (hw : WINDOW (paperDesignP 13097) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13097) c a v -
      ∫ w, sA (paperDesignP 13097) c a w ∂stdGauss (Fin (13097 - 1))) ^ 2
      ∂stdGauss (Fin (13097 - 1))) ^ 2 ∂muI 13097 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13097) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13097

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13097
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13097}
    (hw : WINDOW (paperDesignP 13097) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13097).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13097) c M H xi)
    (hE : centreEnergy (paperDesignP 13097) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13097 : ℝ))))
    (hprice : massBound 13097 M H xi E u mixtureFloor ≤ 13097 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13097 - 1))).real
      {v | sgA (paperDesignP 13097) c a v < √(2 / (13097 : ℝ) * mixtureFloor)}
        ∂muI 13097 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13097).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13097) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13097) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13097)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13097

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13097
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13097) : ℝ :=
  (latitudeC / eR c) / ((13097 : ℝ) * (13097 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13097) / ((13097 : ℝ) * (13097 - 3))

theorem location_variance_on_event {c : Ret 13097}
    (hw : WINDOW (paperDesignP 13097) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13097) c a v - lbar (paperDesignP 13097) c a) ^ 2
      ∂stdGauss (Fin (13097 - 1))) ^ 2 ∂muI 13097 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13097)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13097}
    (hw : WINDOW (paperDesignP 13097) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13097) c a v - gbar (paperDesignP 13097) c a) ^ 2
      ∂stdGauss (Fin (13097 - 1))) ^ 2 ∂muI 13097 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13097)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13097}
    (hw : WINDOW (paperDesignP 13097) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13097 - 1))).real
      {v | sgA (paperDesignP 13097) c a v < √(2 / (13097 : ℝ) * mixtureFloor)}
      ∂muI 13097 ≤ lowMassBudget) :
    LatMom (paperDesignP 13097) c (√(2 / (13097 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13097

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13097
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

theorem location_budget_cap {c : Ret 13097} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13097 : ℝ) * (13097 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13097 : ℝ) * (13097 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13097 : ℝ) /
      ((13097 : ℝ) * (13097 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13097 : ℝ) * (13097 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13097 ≤ (2 * (16 / 5) / 13097 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13097} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (125678699 / 250000000000) ∧
    locationMomentBudget c 6 ≤ (61746341 / 100000000000) ∧
    locationMomentBudget c 12 ≤ (169439111 / 200000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (962401679 / 200000000000000) ∧
    residualMomentBudget 6 ≤ (147759681 / 25000000000000) ∧
    residualMomentBudget 12 ≤ (162187871 / 20000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13097} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (31099583 / 1000000000000000) ∧ residualVarianceBudget ≤ (284947 / 100000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13097 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((962401679 / 200000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13097

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13097
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13097 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13097) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13097) : ℝ :=
  exp (hqKappa * (13097 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5787671 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (723459 / 125000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13097} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (169439111 / 50000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (162187871 / 5000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (162187871 / 5000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((162187871 / 5000000000000) : ℝ) / ((5787671 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11272021 / 500000000) := by
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

theorem hq_location_bounds {c : Ret 13097} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1621883267 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((169439111 / 50000000000))) / ((5787671 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13097} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13097 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13097 * ((11272021 / 500000000) : ℝ) ^ 2 / 2 + ((1621883267 / 1000000000)) ^ 2 * (1 + (11272021 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13097 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13097 * ((11272021 / 500000000)) ^ 2 / 2 + ((1621883267 / 1000000000)) ^ 2 * (1 + (11272021 / 500000000))) := by
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
  have hd : (2 * ((5787671 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (347498941 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (15094434061 / 125000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13097

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13098
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13098 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13098) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13098 : ℝ) * (13098 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13098) /
    ((13098 : ℝ) * (13098 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13098} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13098}
    (hw : WINDOW (paperDesignP 13098) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13098) c a v - lbar (paperDesignP 13098) c a| ^ (2 * q)
      ∂stdGauss (Fin (13098 - 1)) ∂muI 13098 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13098)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13098}
    (hw : WINDOW (paperDesignP 13098) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13098) c a v - gbar (paperDesignP 13098) c a| ^ (2 * q)
      ∂stdGauss (Fin (13098 - 1)) ∂muI 13098 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13098)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13098) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13098}
    (hw : WINDOW (paperDesignP 13098) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13098 - 1))).real
      {v | sgA (paperDesignP 13098) c a v < √(2 / (13098 : ℝ) * mixtureFloor)}
      ∂muI 13098 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13098 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13098 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13098) c
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

end BstLean.Part266.Row13098

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13098
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13098 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13098)
    (p : Ix 13098 × (Fin (13098 - 1) → ℝ)) :
    sgA (paperDesignP 13098) c p.1 p.2 ^ 2 ≤
      (2 / (13098 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13098).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13098) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13098 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13098 : ℝ) * _ ≤ 2 / 13098 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13098)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13098}
    (hw : WINDOW (paperDesignP 13098) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13098) c a v ^ 8
      ∂stdGauss (Fin (13098 - 1)) ∂muI 13098 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13098).prod (stdGauss (Fin (13098 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13098) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13098) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13098 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13098) c p.1 p.2)
      (√(2 / (13098 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13098)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13098 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13098) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13098}
    (hw : WINDOW (paperDesignP 13098) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13098) c a v -
      ∫ w, sA (paperDesignP 13098) c a w ∂stdGauss (Fin (13098 - 1))) ^ 2
      ∂stdGauss (Fin (13098 - 1))) ^ 2 ∂muI 13098 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13098) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13098

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13098
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13098}
    (hw : WINDOW (paperDesignP 13098) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13098).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13098) c M H xi)
    (hE : centreEnergy (paperDesignP 13098) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13098 : ℝ))))
    (hprice : massBound 13098 M H xi E u mixtureFloor ≤ 13098 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13098 - 1))).real
      {v | sgA (paperDesignP 13098) c a v < √(2 / (13098 : ℝ) * mixtureFloor)}
        ∂muI 13098 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13098).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13098) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13098) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13098)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13098

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13098
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13098) : ℝ :=
  (latitudeC / eR c) / ((13098 : ℝ) * (13098 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13098) / ((13098 : ℝ) * (13098 - 3))

theorem location_variance_on_event {c : Ret 13098}
    (hw : WINDOW (paperDesignP 13098) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13098) c a v - lbar (paperDesignP 13098) c a) ^ 2
      ∂stdGauss (Fin (13098 - 1))) ^ 2 ∂muI 13098 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13098)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13098}
    (hw : WINDOW (paperDesignP 13098) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13098) c a v - gbar (paperDesignP 13098) c a) ^ 2
      ∂stdGauss (Fin (13098 - 1))) ^ 2 ∂muI 13098 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13098)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13098}
    (hw : WINDOW (paperDesignP 13098) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13098 - 1))).real
      {v | sgA (paperDesignP 13098) c a v < √(2 / (13098 : ℝ) * mixtureFloor)}
      ∂muI 13098 ≤ lowMassBudget) :
    LatMom (paperDesignP 13098) c (√(2 / (13098 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13098

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13098
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

theorem location_budget_cap {c : Ret 13098} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13098 : ℝ) * (13098 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13098 : ℝ) * (13098 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13098 : ℝ) /
      ((13098 : ℝ) * (13098 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13098 : ℝ) * (13098 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13098 ≤ (2 * (16 / 5) / 13098 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13098} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (251338201 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (123483249 / 200000000000) ∧
    locationMomentBudget c 12 ≤ (847130811 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2405728601 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (5909710163 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (8108464277 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13098} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15547417 / 500000000000000) ∧ residualVarianceBudget ≤ (2848817 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13098 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2405728601 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13098

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13098
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13098 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13098) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13098) : ℝ :=
  exp (hqKappa * (13098 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((115749 / 20000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5787451 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13098} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (847130811 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8108464277 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8108464277 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8108464277 / 250000000000000) : ℝ) / ((115749 / 20000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (2254231 / 100000000) := by
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

theorem hq_location_bounds {c : Ret 13098} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1621821249 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((847130811 / 250000000000))) / ((115749 / 20000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13098} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13098 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13098 * ((2254231 / 100000000) : ℝ) ^ 2 / 2 + ((1621821249 / 1000000000)) ^ 2 * (1 + (2254231 / 100000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13098 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13098 * ((2254231 / 100000000)) ^ 2 / 2 + ((1621821249 / 1000000000)) ^ 2 * (1 + (2254231 / 100000000))) := by
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
  have hd : (2 * ((115749 / 20000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (347512063 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (120764592161 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13098

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13099
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13099 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13099) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13099 : ℝ) * (13099 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13099) /
    ((13099 : ℝ) * (13099 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13099} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13099}
    (hw : WINDOW (paperDesignP 13099) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13099) c a v - lbar (paperDesignP 13099) c a| ^ (2 * q)
      ∂stdGauss (Fin (13099 - 1)) ∂muI 13099 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13099)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13099}
    (hw : WINDOW (paperDesignP 13099) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13099) c a v - gbar (paperDesignP 13099) c a| ^ (2 * q)
      ∂stdGauss (Fin (13099 - 1)) ∂muI 13099 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13099)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13099) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13099}
    (hw : WINDOW (paperDesignP 13099) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13099 - 1))).real
      {v | sgA (paperDesignP 13099) c a v < √(2 / (13099 : ℝ) * mixtureFloor)}
      ∂muI 13099 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13099 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13099 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13099) c
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

end BstLean.Part266.Row13099

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13099
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13099 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13099)
    (p : Ix 13099 × (Fin (13099 - 1) → ℝ)) :
    sgA (paperDesignP 13099) c p.1 p.2 ^ 2 ≤
      (2 / (13099 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13099).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13099) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13099 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13099 : ℝ) * _ ≤ 2 / 13099 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13099)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13099}
    (hw : WINDOW (paperDesignP 13099) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13099) c a v ^ 8
      ∂stdGauss (Fin (13099 - 1)) ∂muI 13099 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13099).prod (stdGauss (Fin (13099 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13099) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13099) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13099 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13099) c p.1 p.2)
      (√(2 / (13099 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13099)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13099 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13099) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13099}
    (hw : WINDOW (paperDesignP 13099) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13099) c a v -
      ∫ w, sA (paperDesignP 13099) c a w ∂stdGauss (Fin (13099 - 1))) ^ 2
      ∂stdGauss (Fin (13099 - 1))) ^ 2 ∂muI 13099 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13099) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13099

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13099
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13099}
    (hw : WINDOW (paperDesignP 13099) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13099).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13099) c M H xi)
    (hE : centreEnergy (paperDesignP 13099) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13099 : ℝ))))
    (hprice : massBound 13099 M H xi E u mixtureFloor ≤ 13099 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13099 - 1))).real
      {v | sgA (paperDesignP 13099) c a v < √(2 / (13099 : ℝ) * mixtureFloor)}
        ∂muI 13099 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13099).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13099) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13099) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13099)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13099

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13099
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13099) : ℝ :=
  (latitudeC / eR c) / ((13099 : ℝ) * (13099 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13099) / ((13099 : ℝ) * (13099 - 3))

theorem location_variance_on_event {c : Ret 13099}
    (hw : WINDOW (paperDesignP 13099) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13099) c a v - lbar (paperDesignP 13099) c a) ^ 2
      ∂stdGauss (Fin (13099 - 1))) ^ 2 ∂muI 13099 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13099)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13099}
    (hw : WINDOW (paperDesignP 13099) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13099) c a v - gbar (paperDesignP 13099) c a) ^ 2
      ∂stdGauss (Fin (13099 - 1))) ^ 2 ∂muI 13099 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13099)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13099}
    (hw : WINDOW (paperDesignP 13099) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13099 - 1))).real
      {v | sgA (paperDesignP 13099) c a v < √(2 / (13099 : ℝ) * mixtureFloor)}
      ∂muI 13099 ≤ lowMassBudget) :
    LatMom (paperDesignP 13099) c (√(2 / (13099 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13099

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13099
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

theorem location_budget_cap {c : Ret 13099} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13099 : ℝ) * (13099 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13099 : ℝ) * (13099 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13099 : ℝ) /
      ((13099 : ℝ) * (13099 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13099 : ℝ) * (13099 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13099 ≤ (2 * (16 / 5) / 13099 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13099} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (502638013 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (617369087 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (423533039 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2405453057 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (23082161 / 3906250000000) ∧
    residualMomentBudget 12 ≤ (4053767591 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13099} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15545043 / 500000000000000) ∧ residualVarianceBudget ≤ (569633 / 200000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13099 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2405453057 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13099

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13099
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13099 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13099) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13099) : ℝ :=
  exp (hqKappa * (13099 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5787229 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (578723 / 100000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13099} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (423533039 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4053767591 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4053767591 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4053767591 / 125000000000000) : ℝ) / ((5787229 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11270289 / 500000000) := by
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

theorem hq_location_bounds {c : Ret 13099} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1621759247 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((423533039 / 125000000000))) / ((5787229 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13099} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13099 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13099 * ((11270289 / 500000000) : ℝ) ^ 2 / 2 + ((1621759247 / 1000000000)) ^ 2 * (1 + (11270289 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13099 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13099 * ((11270289 / 500000000)) ^ 2 / 2 + ((1621759247 / 1000000000)) ^ 2 * (1 + (11270289 / 500000000))) := by
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
  have hd : (2 * ((5787229 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (173762593 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (1887089264 / 15625) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13099
