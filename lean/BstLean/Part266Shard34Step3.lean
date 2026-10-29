import BstLean.Part266Shard34Step2


/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13200
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13200 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13200) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13200 : ℝ) * (13200 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13200) /
    ((13200 : ℝ) * (13200 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13200} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13200}
    (hw : WINDOW (paperDesignP 13200) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13200) c a v - lbar (paperDesignP 13200) c a| ^ (2 * q)
      ∂stdGauss (Fin (13200 - 1)) ∂muI 13200 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13200)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13200}
    (hw : WINDOW (paperDesignP 13200) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13200) c a v - gbar (paperDesignP 13200) c a| ^ (2 * q)
      ∂stdGauss (Fin (13200 - 1)) ∂muI 13200 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13200)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13200) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13200}
    (hw : WINDOW (paperDesignP 13200) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13200 - 1))).real
      {v | sgA (paperDesignP 13200) c a v < √(2 / (13200 : ℝ) * mixtureFloor)}
      ∂muI 13200 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13200 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13200 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13200) c
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

end BstLean.Part266.Row13200

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13200
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13200 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13200)
    (p : Ix 13200 × (Fin (13200 - 1) → ℝ)) :
    sgA (paperDesignP 13200) c p.1 p.2 ^ 2 ≤
      (2 / (13200 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13200).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13200) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13200 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13200 : ℝ) * _ ≤ 2 / 13200 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13200)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13200}
    (hw : WINDOW (paperDesignP 13200) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13200) c a v ^ 8
      ∂stdGauss (Fin (13200 - 1)) ∂muI 13200 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13200).prod (stdGauss (Fin (13200 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13200) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13200) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13200 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13200) c p.1 p.2)
      (√(2 / (13200 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13200)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13200 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13200) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13200}
    (hw : WINDOW (paperDesignP 13200) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13200) c a v -
      ∫ w, sA (paperDesignP 13200) c a w ∂stdGauss (Fin (13200 - 1))) ^ 2
      ∂stdGauss (Fin (13200 - 1))) ^ 2 ∂muI 13200 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13200) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13200

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13200
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13200}
    (hw : WINDOW (paperDesignP 13200) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13200).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13200) c M H xi)
    (hE : centreEnergy (paperDesignP 13200) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13200 : ℝ))))
    (hprice : massBound 13200 M H xi E u mixtureFloor ≤ 13200 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13200 - 1))).real
      {v | sgA (paperDesignP 13200) c a v < √(2 / (13200 : ℝ) * mixtureFloor)}
        ∂muI 13200 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13200).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13200) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13200) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13200)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13200

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13200
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13200) : ℝ :=
  (latitudeC / eR c) / ((13200 : ℝ) * (13200 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13200) / ((13200 : ℝ) * (13200 - 3))

theorem location_variance_on_event {c : Ret 13200}
    (hw : WINDOW (paperDesignP 13200) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13200) c a v - lbar (paperDesignP 13200) c a) ^ 2
      ∂stdGauss (Fin (13200 - 1))) ^ 2 ∂muI 13200 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13200)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13200}
    (hw : WINDOW (paperDesignP 13200) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13200) c a v - gbar (paperDesignP 13200) c a) ^ 2
      ∂stdGauss (Fin (13200 - 1))) ^ 2 ∂muI 13200 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13200)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13200}
    (hw : WINDOW (paperDesignP 13200) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13200 - 1))).real
      {v | sgA (paperDesignP 13200) c a v < √(2 / (13200 : ℝ) * mixtureFloor)}
      ∂muI 13200 ≤ lowMassBudget) :
    LatMom (paperDesignP 13200) c (√(2 / (13200 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13200

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13200
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

theorem location_budget_cap {c : Ret 13200} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13200 : ℝ) * (13200 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13200 : ℝ) * (13200 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13200 : ℝ) /
      ((13200 : ℝ) * (13200 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13200 : ℝ) * (13200 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13200 ≤ (2 * (16 / 5) / 13200 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13200} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (498790759 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (12252859 / 20000000000) ∧
    locationMomentBudget c 12 ≤ (84057859 / 100000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (59447291 / 12500000000000) ∧
    residualMomentBudget 6 ≤ (2920660663 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (500912649 / 62500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13200} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (382701 / 12500000000000) ∧ residualVarianceBudget ≤ (34791 / 12500000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13200 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((59447291 / 12500000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13200

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13200
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13200 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13200) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13200) : ℝ :=
  exp (hqKappa * (13200 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((2882523 / 500000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5765047 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13200} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (84057859 / 25000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (500912649 / 15625000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (500912649 / 15625000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((500912649 / 15625000000000) : ℝ) / ((2882523 / 500000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (2236699 / 100000000) := by
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

theorem hq_location_bounds {c : Ret 13200} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1615531043 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((84057859 / 25000000000))) / ((2882523 / 500000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13200} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13200 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13200 * ((2236699 / 100000000) : ℝ) ^ 2 / 2 + ((1615531043 / 1000000000)) ^ 2 * (1 + (2236699 / 100000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13200 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13200 * ((2236699 / 100000000)) ^ 2 / 2 + ((1615531043 / 1000000000)) ^ 2 * (1 + (2236699 / 100000000))) := by
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
  have hd : (2 * ((2882523 / 500000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (2180297 / 6250) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121694549779 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13200

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13201
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13201 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13201) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13201 : ℝ) * (13201 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13201) /
    ((13201 : ℝ) * (13201 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13201} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13201}
    (hw : WINDOW (paperDesignP 13201) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13201) c a v - lbar (paperDesignP 13201) c a| ^ (2 * q)
      ∂stdGauss (Fin (13201 - 1)) ∂muI 13201 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13201)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13201}
    (hw : WINDOW (paperDesignP 13201) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13201) c a v - gbar (paperDesignP 13201) c a| ^ (2 * q)
      ∂stdGauss (Fin (13201 - 1)) ∂muI 13201 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13201)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13201) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13201}
    (hw : WINDOW (paperDesignP 13201) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13201 - 1))).real
      {v | sgA (paperDesignP 13201) c a v < √(2 / (13201 : ℝ) * mixtureFloor)}
      ∂muI 13201 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13201 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13201 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13201) c
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

end BstLean.Part266.Row13201

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13201
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13201 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13201)
    (p : Ix 13201 × (Fin (13201 - 1) → ℝ)) :
    sgA (paperDesignP 13201) c p.1 p.2 ^ 2 ≤
      (2 / (13201 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13201).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13201) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13201 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13201 : ℝ) * _ ≤ 2 / 13201 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13201)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13201}
    (hw : WINDOW (paperDesignP 13201) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13201) c a v ^ 8
      ∂stdGauss (Fin (13201 - 1)) ∂muI 13201 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13201).prod (stdGauss (Fin (13201 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13201) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13201) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13201 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13201) c p.1 p.2)
      (√(2 / (13201 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13201)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13201 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13201) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13201}
    (hw : WINDOW (paperDesignP 13201) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13201) c a v -
      ∫ w, sA (paperDesignP 13201) c a w ∂stdGauss (Fin (13201 - 1))) ^ 2
      ∂stdGauss (Fin (13201 - 1))) ^ 2 ∂muI 13201 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13201) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13201

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13201
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13201}
    (hw : WINDOW (paperDesignP 13201) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13201).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13201) c M H xi)
    (hE : centreEnergy (paperDesignP 13201) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13201 : ℝ))))
    (hprice : massBound 13201 M H xi E u mixtureFloor ≤ 13201 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13201 - 1))).real
      {v | sgA (paperDesignP 13201) c a v < √(2 / (13201 : ℝ) * mixtureFloor)}
        ∂muI 13201 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13201).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13201) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13201) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13201)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13201

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13201
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13201) : ℝ :=
  (latitudeC / eR c) / ((13201 : ℝ) * (13201 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13201) / ((13201 : ℝ) * (13201 - 3))

theorem location_variance_on_event {c : Ret 13201}
    (hw : WINDOW (paperDesignP 13201) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13201) c a v - lbar (paperDesignP 13201) c a) ^ 2
      ∂stdGauss (Fin (13201 - 1))) ^ 2 ∂muI 13201 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13201)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13201}
    (hw : WINDOW (paperDesignP 13201) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13201) c a v - gbar (paperDesignP 13201) c a) ^ 2
      ∂stdGauss (Fin (13201 - 1))) ^ 2 ∂muI 13201 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13201)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13201}
    (hw : WINDOW (paperDesignP 13201) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13201 - 1))).real
      {v | sgA (paperDesignP 13201) c a v < √(2 / (13201 : ℝ) * mixtureFloor)}
      ∂muI 13201 ≤ lowMassBudget) :
    LatMom (paperDesignP 13201) c (√(2 / (13201 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13201

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13201
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

theorem location_budget_cap {c : Ret 13201} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13201 : ℝ) * (13201 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13201 : ℝ) * (13201 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13201 : ℝ) /
      ((13201 : ℝ) * (13201 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13201 : ℝ) * (13201 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13201 ≤ (2 * (16 / 5) / 13201 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13201} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (249376481 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (306298259 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (420257427 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2377621389 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (1168131477 / 200000000000000) ∧
    residualMomentBudget 12 ≤ (1001711393 / 125000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13201} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30611441 / 1000000000000000) ∧ residualVarianceBudget ≤ (347831 / 125000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13201 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2377621389 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13201

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13201
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13201 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13201) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13201) : ℝ :=
  exp (hqKappa * (13201 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5764827 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (1441207 / 250000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13201} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (420257427 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (1001711393 / 31250000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (1001711393 / 31250000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((1001711393 / 31250000000000) : ℝ) / ((5764827 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22365287 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 13201} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (323093983 / 200000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((420257427 / 125000000000))) / ((5764827 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13201} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13201 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13201 * ((22365287 / 1000000000) : ℝ) ^ 2 / 2 + ((323093983 / 200000000)) ^ 2 * (1 + (22365287 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13201 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13201 * ((22365287 / 1000000000)) ^ 2 / 2 + ((323093983 / 200000000)) ^ 2 * (1 + (22365287 / 1000000000))) := by
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
  have hd : (2 * ((5764827 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (174430313 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (30425923537 / 250000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13201

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13202
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13202 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13202) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13202 : ℝ) * (13202 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13202) /
    ((13202 : ℝ) * (13202 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13202} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13202}
    (hw : WINDOW (paperDesignP 13202) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13202) c a v - lbar (paperDesignP 13202) c a| ^ (2 * q)
      ∂stdGauss (Fin (13202 - 1)) ∂muI 13202 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13202)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13202}
    (hw : WINDOW (paperDesignP 13202) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13202) c a v - gbar (paperDesignP 13202) c a| ^ (2 * q)
      ∂stdGauss (Fin (13202 - 1)) ∂muI 13202 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13202)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13202) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13202}
    (hw : WINDOW (paperDesignP 13202) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13202 - 1))).real
      {v | sgA (paperDesignP 13202) c a v < √(2 / (13202 : ℝ) * mixtureFloor)}
      ∂muI 13202 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13202 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13202 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13202) c
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

end BstLean.Part266.Row13202

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13202
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13202 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13202)
    (p : Ix 13202 × (Fin (13202 - 1) → ℝ)) :
    sgA (paperDesignP 13202) c p.1 p.2 ^ 2 ≤
      (2 / (13202 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13202).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13202) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13202 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13202 : ℝ) * _ ≤ 2 / 13202 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13202)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13202}
    (hw : WINDOW (paperDesignP 13202) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13202) c a v ^ 8
      ∂stdGauss (Fin (13202 - 1)) ∂muI 13202 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13202).prod (stdGauss (Fin (13202 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13202) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13202) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13202 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13202) c p.1 p.2)
      (√(2 / (13202 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13202)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13202 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13202) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13202}
    (hw : WINDOW (paperDesignP 13202) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13202) c a v -
      ∫ w, sA (paperDesignP 13202) c a w ∂stdGauss (Fin (13202 - 1))) ^ 2
      ∂stdGauss (Fin (13202 - 1))) ^ 2 ∂muI 13202 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13202) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13202

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13202
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13202}
    (hw : WINDOW (paperDesignP 13202) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13202).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13202) c M H xi)
    (hE : centreEnergy (paperDesignP 13202) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13202 : ℝ))))
    (hprice : massBound 13202 M H xi E u mixtureFloor ≤ 13202 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13202 - 1))).real
      {v | sgA (paperDesignP 13202) c a v < √(2 / (13202 : ℝ) * mixtureFloor)}
        ∂muI 13202 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13202).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13202) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13202) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13202)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13202

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13202
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13202) : ℝ :=
  (latitudeC / eR c) / ((13202 : ℝ) * (13202 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13202) / ((13202 : ℝ) * (13202 - 3))

theorem location_variance_on_event {c : Ret 13202}
    (hw : WINDOW (paperDesignP 13202) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13202) c a v - lbar (paperDesignP 13202) c a) ^ 2
      ∂stdGauss (Fin (13202 - 1))) ^ 2 ∂muI 13202 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13202)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13202}
    (hw : WINDOW (paperDesignP 13202) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13202) c a v - gbar (paperDesignP 13202) c a) ^ 2
      ∂stdGauss (Fin (13202 - 1))) ^ 2 ∂muI 13202 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13202)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13202}
    (hw : WINDOW (paperDesignP 13202) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13202 - 1))).real
      {v | sgA (paperDesignP 13202) c a v < √(2 / (13202 : ℝ) * mixtureFloor)}
      ∂muI 13202 ≤ lowMassBudget) :
    LatMom (paperDesignP 13202) c (√(2 / (13202 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13202

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13202
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

theorem location_budget_cap {c : Ret 13202} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13202 : ℝ) * (13202 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13202 : ℝ) * (13202 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13202 : ℝ) /
      ((13202 : ℝ) * (13202 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13202 : ℝ) * (13202 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13202 ≤ (2 * (16 / 5) / 13202 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13202} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (49871517 / 100000000000) ∧
    locationMomentBudget c 6 ≤ (612550093 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (105056391 / 125000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4754702379 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (5839993569 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (8012780077 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13202} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (7651701 / 250000000000000) ∧ residualVarianceBudget ≤ (43469 / 15625000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13202 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4754702379 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13202

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13202
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13202 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13202) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13202) : ℝ :=
  exp (hqKappa * (13202 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5764609 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (576461 / 100000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13202} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (105056391 / 31250000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8012780077 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8012780077 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8012780077 / 250000000000000) : ℝ) / ((5764609 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22363581 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 13202} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1615408521 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((105056391 / 31250000000))) / ((5764609 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13202} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13202 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13202 * ((22363581 / 1000000000) : ℝ) ^ 2 / 2 + ((1615408521 / 1000000000)) ^ 2 * (1 + (22363581 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13202 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13202 * ((22363581 / 1000000000)) ^ 2 / 2 + ((1615408521 / 1000000000)) ^ 2 * (1 + (22363581 / 1000000000))) := by
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
  have hd : (2 * ((5764609 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (348873673 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (30428199279 / 250000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13202

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13203
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13203 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13203) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13203 : ℝ) * (13203 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13203) /
    ((13203 : ℝ) * (13203 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13203} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13203}
    (hw : WINDOW (paperDesignP 13203) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13203) c a v - lbar (paperDesignP 13203) c a| ^ (2 * q)
      ∂stdGauss (Fin (13203 - 1)) ∂muI 13203 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13203)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13203}
    (hw : WINDOW (paperDesignP 13203) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13203) c a v - gbar (paperDesignP 13203) c a| ^ (2 * q)
      ∂stdGauss (Fin (13203 - 1)) ∂muI 13203 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13203)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13203) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13203}
    (hw : WINDOW (paperDesignP 13203) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13203 - 1))).real
      {v | sgA (paperDesignP 13203) c a v < √(2 / (13203 : ℝ) * mixtureFloor)}
      ∂muI 13203 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13203 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13203 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13203) c
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

end BstLean.Part266.Row13203

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13203
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13203 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13203)
    (p : Ix 13203 × (Fin (13203 - 1) → ℝ)) :
    sgA (paperDesignP 13203) c p.1 p.2 ^ 2 ≤
      (2 / (13203 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13203).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13203) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13203 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13203 : ℝ) * _ ≤ 2 / 13203 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13203)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13203}
    (hw : WINDOW (paperDesignP 13203) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13203) c a v ^ 8
      ∂stdGauss (Fin (13203 - 1)) ∂muI 13203 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13203).prod (stdGauss (Fin (13203 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13203) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13203) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13203 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13203) c p.1 p.2)
      (√(2 / (13203 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13203)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13203 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13203) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13203}
    (hw : WINDOW (paperDesignP 13203) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13203) c a v -
      ∫ w, sA (paperDesignP 13203) c a w ∂stdGauss (Fin (13203 - 1))) ^ 2
      ∂stdGauss (Fin (13203 - 1))) ^ 2 ∂muI 13203 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13203) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13203

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13203
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13203}
    (hw : WINDOW (paperDesignP 13203) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13203).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13203) c M H xi)
    (hE : centreEnergy (paperDesignP 13203) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13203 : ℝ))))
    (hprice : massBound 13203 M H xi E u mixtureFloor ≤ 13203 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13203 - 1))).real
      {v | sgA (paperDesignP 13203) c a v < √(2 / (13203 : ℝ) * mixtureFloor)}
        ∂muI 13203 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13203).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13203) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13203) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13203)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13203

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13203
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13203) : ℝ :=
  (latitudeC / eR c) / ((13203 : ℝ) * (13203 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13203) / ((13203 : ℝ) * (13203 - 3))

theorem location_variance_on_event {c : Ret 13203}
    (hw : WINDOW (paperDesignP 13203) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13203) c a v - lbar (paperDesignP 13203) c a) ^ 2
      ∂stdGauss (Fin (13203 - 1))) ^ 2 ∂muI 13203 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13203)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13203}
    (hw : WINDOW (paperDesignP 13203) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13203) c a v - gbar (paperDesignP 13203) c a) ^ 2
      ∂stdGauss (Fin (13203 - 1))) ^ 2 ∂muI 13203 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13203)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13203}
    (hw : WINDOW (paperDesignP 13203) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13203 - 1))).real
      {v | sgA (paperDesignP 13203) c a v < √(2 / (13203 : ℝ) * mixtureFloor)}
      ∂muI 13203 ≤ lowMassBudget) :
    LatMom (paperDesignP 13203) c (√(2 / (13203 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13203

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13203
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

theorem location_budget_cap {c : Ret 13203} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13203 : ℝ) * (13203 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13203 : ℝ) * (13203 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13203 : ℝ) /
      ((13203 : ℝ) * (13203 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13203 : ℝ) * (13203 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13203 ≤ (2 * (16 / 5) / 13203 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13203} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (62334673 / 125000000000) ∧
    locationMomentBudget c 6 ≤ (153125919 / 250000000000) ∧
    locationMomentBudget c 12 ≤ (210096853 / 250000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2377081041 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (2919664939 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (4005934591 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13203} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30602167 / 1000000000000000) ∧ residualVarianceBudget ≤ (347673 / 125000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13203 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2377081041 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13203

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13203
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13203 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13203) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13203) : ℝ :=
  exp (hqKappa * (13203 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5764391 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (720549 / 125000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13203} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (210096853 / 62500000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4005934591 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4005934591 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4005934591 / 125000000000000) : ℝ) / ((5764391 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (35779 / 1600000) := by
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

theorem hq_location_bounds {c : Ret 13203} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (807673571 / 500000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((210096853 / 62500000000))) / ((5764391 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13203} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13203 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13203 * ((35779 / 1600000) : ℝ) ^ 2 / 2 + ((807673571 / 500000000)) ^ 2 * (1 + (35779 / 1600000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13203 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13203 * ((35779 / 1600000)) ^ 2 / 2 + ((807673571 / 500000000)) ^ 2 * (1 + (35779 / 1600000))) := by
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
  have hd : (2 * ((5764391 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (1090271 / 3125) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (24344380227 / 200000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13203

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13204
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13204 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13204) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13204 : ℝ) * (13204 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13204) /
    ((13204 : ℝ) * (13204 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13204} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13204}
    (hw : WINDOW (paperDesignP 13204) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13204) c a v - lbar (paperDesignP 13204) c a| ^ (2 * q)
      ∂stdGauss (Fin (13204 - 1)) ∂muI 13204 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13204)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13204}
    (hw : WINDOW (paperDesignP 13204) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13204) c a v - gbar (paperDesignP 13204) c a| ^ (2 * q)
      ∂stdGauss (Fin (13204 - 1)) ∂muI 13204 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13204)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13204) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13204}
    (hw : WINDOW (paperDesignP 13204) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13204 - 1))).real
      {v | sgA (paperDesignP 13204) c a v < √(2 / (13204 : ℝ) * mixtureFloor)}
      ∂muI 13204 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13204 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13204 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13204) c
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

end BstLean.Part266.Row13204

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13204
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13204 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13204)
    (p : Ix 13204 × (Fin (13204 - 1) → ℝ)) :
    sgA (paperDesignP 13204) c p.1 p.2 ^ 2 ≤
      (2 / (13204 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13204).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13204) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13204 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13204 : ℝ) * _ ≤ 2 / 13204 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13204)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13204}
    (hw : WINDOW (paperDesignP 13204) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13204) c a v ^ 8
      ∂stdGauss (Fin (13204 - 1)) ∂muI 13204 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13204).prod (stdGauss (Fin (13204 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13204) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13204) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13204 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13204) c p.1 p.2)
      (√(2 / (13204 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13204)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13204 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13204) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13204}
    (hw : WINDOW (paperDesignP 13204) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13204) c a v -
      ∫ w, sA (paperDesignP 13204) c a w ∂stdGauss (Fin (13204 - 1))) ^ 2
      ∂stdGauss (Fin (13204 - 1))) ^ 2 ∂muI 13204 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13204) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13204

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13204
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13204}
    (hw : WINDOW (paperDesignP 13204) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13204).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13204) c M H xi)
    (hE : centreEnergy (paperDesignP 13204) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13204 : ℝ))))
    (hprice : massBound 13204 M H xi E u mixtureFloor ≤ 13204 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13204 - 1))).real
      {v | sgA (paperDesignP 13204) c a v < √(2 / (13204 : ℝ) * mixtureFloor)}
        ∂muI 13204 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13204).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13204) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13204) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13204)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13204

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13204
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13204) : ℝ :=
  (latitudeC / eR c) / ((13204 : ℝ) * (13204 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13204) / ((13204 : ℝ) * (13204 - 3))

theorem location_variance_on_event {c : Ret 13204}
    (hw : WINDOW (paperDesignP 13204) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13204) c a v - lbar (paperDesignP 13204) c a) ^ 2
      ∂stdGauss (Fin (13204 - 1))) ^ 2 ∂muI 13204 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13204)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13204}
    (hw : WINDOW (paperDesignP 13204) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13204) c a v - gbar (paperDesignP 13204) c a) ^ 2
      ∂stdGauss (Fin (13204 - 1))) ^ 2 ∂muI 13204 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13204)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13204}
    (hw : WINDOW (paperDesignP 13204) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13204 - 1))).real
      {v | sgA (paperDesignP 13204) c a v < √(2 / (13204 : ℝ) * mixtureFloor)}
      ∂muI 13204 ≤ lowMassBudget) :
    LatMom (paperDesignP 13204) c (√(2 / (13204 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13204

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13204
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

theorem location_budget_cap {c : Ret 13204} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13204 : ℝ) * (13204 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13204 : ℝ) * (13204 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13204 : ℝ) /
      ((13204 : ℝ) * (13204 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13204 : ℝ) * (13204 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13204 ≤ (2 * (16 / 5) / 13204 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13204} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (124659901 / 250000000000) ∧
    locationMomentBudget c 6 ≤ (122491453 / 200000000000) ∧
    locationMomentBudget c 12 ≤ (168064741 / 200000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4753621887 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (2919333157 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (400547923 / 50000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13204} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30597531 / 1000000000000000) ∧ residualVarianceBudget ≤ (173797 / 62500000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13204 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4753621887 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13204

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13204
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13204 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13204) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13204) : ℝ :=
  exp (hqKappa * (13204 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((1441043 / 250000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5764173 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13204} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (168064741 / 50000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (400547923 / 12500000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (400547923 / 12500000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((400547923 / 12500000000000) : ℝ) / ((1441043 / 250000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22360173 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 13204} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (201910757 / 125000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((168064741 / 50000000000))) / ((1441043 / 250000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13204} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13204 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13204 * ((22360173 / 1000000000) : ℝ) ^ 2 / 2 + ((201910757 / 125000000)) ^ 2 * (1 + (22360173 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13204 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13204 * ((22360173 / 1000000000)) ^ 2 / 2 + ((201910757 / 125000000)) ^ 2 * (1 + (22360173 / 1000000000))) := by
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
  have hd : (2 * ((1441043 / 250000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (34889983 / 100000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (60865524337 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13204

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13205
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13205 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13205) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13205 : ℝ) * (13205 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13205) /
    ((13205 : ℝ) * (13205 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13205} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13205}
    (hw : WINDOW (paperDesignP 13205) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13205) c a v - lbar (paperDesignP 13205) c a| ^ (2 * q)
      ∂stdGauss (Fin (13205 - 1)) ∂muI 13205 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13205)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13205}
    (hw : WINDOW (paperDesignP 13205) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13205) c a v - gbar (paperDesignP 13205) c a| ^ (2 * q)
      ∂stdGauss (Fin (13205 - 1)) ∂muI 13205 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13205)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13205) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13205}
    (hw : WINDOW (paperDesignP 13205) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13205 - 1))).real
      {v | sgA (paperDesignP 13205) c a v < √(2 / (13205 : ℝ) * mixtureFloor)}
      ∂muI 13205 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13205 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13205 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13205) c
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

end BstLean.Part266.Row13205

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13205
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13205 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13205)
    (p : Ix 13205 × (Fin (13205 - 1) → ℝ)) :
    sgA (paperDesignP 13205) c p.1 p.2 ^ 2 ≤
      (2 / (13205 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13205).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13205) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13205 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13205 : ℝ) * _ ≤ 2 / 13205 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13205)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13205}
    (hw : WINDOW (paperDesignP 13205) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13205) c a v ^ 8
      ∂stdGauss (Fin (13205 - 1)) ∂muI 13205 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13205).prod (stdGauss (Fin (13205 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13205) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13205) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13205 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13205) c p.1 p.2)
      (√(2 / (13205 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13205)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13205 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13205) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13205}
    (hw : WINDOW (paperDesignP 13205) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13205) c a v -
      ∫ w, sA (paperDesignP 13205) c a w ∂stdGauss (Fin (13205 - 1))) ^ 2
      ∂stdGauss (Fin (13205 - 1))) ^ 2 ∂muI 13205 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13205) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13205

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13205
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13205}
    (hw : WINDOW (paperDesignP 13205) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13205).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13205) c M H xi)
    (hE : centreEnergy (paperDesignP 13205) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13205 : ℝ))))
    (hprice : massBound 13205 M H xi E u mixtureFloor ≤ 13205 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13205 - 1))).real
      {v | sgA (paperDesignP 13205) c a v < √(2 / (13205 : ℝ) * mixtureFloor)}
        ∂muI 13205 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13205).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13205) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13205) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13205)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13205

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13205
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13205) : ℝ :=
  (latitudeC / eR c) / ((13205 : ℝ) * (13205 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13205) / ((13205 : ℝ) * (13205 - 3))

theorem location_variance_on_event {c : Ret 13205}
    (hw : WINDOW (paperDesignP 13205) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13205) c a v - lbar (paperDesignP 13205) c a) ^ 2
      ∂stdGauss (Fin (13205 - 1))) ^ 2 ∂muI 13205 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13205)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13205}
    (hw : WINDOW (paperDesignP 13205) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13205) c a v - gbar (paperDesignP 13205) c a) ^ 2
      ∂stdGauss (Fin (13205 - 1))) ^ 2 ∂muI 13205 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13205)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13205}
    (hw : WINDOW (paperDesignP 13205) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13205 - 1))).real
      {v | sgA (paperDesignP 13205) c a v < √(2 / (13205 : ℝ) * mixtureFloor)}
      ∂muI 13205 ≤ lowMassBudget) :
    LatMom (paperDesignP 13205) c (√(2 / (13205 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13205

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13205
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

theorem location_budget_cap {c : Ret 13205} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13205 : ℝ) * (13205 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13205 : ℝ) * (13205 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13205 : ℝ) /
      ((13205 : ℝ) * (13205 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13205 : ℝ) * (13205 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13205 ≤ (2 * (16 / 5) / 13205 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13205} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (49860183 / 100000000000) ∧
    locationMomentBudget c 6 ≤ (612410861 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (105032501 / 125000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (950616359 / 200000000000000) ∧
    residualMomentBudget 6 ≤ (46704023 / 8000000000000) ∧
    residualMomentBudget 12 ≤ (801004791 / 100000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13205} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30592897 / 1000000000000000) ∧ residualVarianceBudget ≤ (69503 / 25000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13205 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((950616359 / 200000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13205

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13205
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13205 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13205) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13205) : ℝ :=
  exp (hqKappa * (13205 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((2881977 / 500000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (1152791 / 200000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13205} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (105032501 / 31250000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (801004791 / 25000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (801004791 / 25000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((801004791 / 25000000000000) : ℝ) / ((2881977 / 500000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (5589617 / 250000000) := by
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

theorem hq_location_bounds {c : Ret 13205} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (12618943 / 7812500) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((105032501 / 31250000000))) / ((2881977 / 500000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13205} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13205 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13205 * ((5589617 / 250000000) : ℝ) ^ 2 / 2 + ((12618943 / 7812500)) ^ 2 * (1 + (5589617 / 250000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13205 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13205 * ((5589617 / 250000000)) ^ 2 / 2 + ((12618943 / 7812500)) ^ 2 * (1 + (5589617 / 250000000))) := by
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
  have hd : (2 * ((2881977 / 500000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (348912879 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (60870077399 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13205

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13206
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13206 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13206) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13206 : ℝ) * (13206 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13206) /
    ((13206 : ℝ) * (13206 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13206} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13206}
    (hw : WINDOW (paperDesignP 13206) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13206) c a v - lbar (paperDesignP 13206) c a| ^ (2 * q)
      ∂stdGauss (Fin (13206 - 1)) ∂muI 13206 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13206)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13206}
    (hw : WINDOW (paperDesignP 13206) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13206) c a v - gbar (paperDesignP 13206) c a| ^ (2 * q)
      ∂stdGauss (Fin (13206 - 1)) ∂muI 13206 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13206)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13206) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13206}
    (hw : WINDOW (paperDesignP 13206) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13206 - 1))).real
      {v | sgA (paperDesignP 13206) c a v < √(2 / (13206 : ℝ) * mixtureFloor)}
      ∂muI 13206 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13206 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13206 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13206) c
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

end BstLean.Part266.Row13206

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13206
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13206 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13206)
    (p : Ix 13206 × (Fin (13206 - 1) → ℝ)) :
    sgA (paperDesignP 13206) c p.1 p.2 ^ 2 ≤
      (2 / (13206 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13206).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13206) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13206 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13206 : ℝ) * _ ≤ 2 / 13206 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13206)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13206}
    (hw : WINDOW (paperDesignP 13206) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13206) c a v ^ 8
      ∂stdGauss (Fin (13206 - 1)) ∂muI 13206 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13206).prod (stdGauss (Fin (13206 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13206) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13206) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13206 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13206) c p.1 p.2)
      (√(2 / (13206 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13206)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13206 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13206) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13206}
    (hw : WINDOW (paperDesignP 13206) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13206) c a v -
      ∫ w, sA (paperDesignP 13206) c a w ∂stdGauss (Fin (13206 - 1))) ^ 2
      ∂stdGauss (Fin (13206 - 1))) ^ 2 ∂muI 13206 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13206) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13206

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13206
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13206}
    (hw : WINDOW (paperDesignP 13206) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13206).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13206) c M H xi)
    (hE : centreEnergy (paperDesignP 13206) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13206 : ℝ))))
    (hprice : massBound 13206 M H xi E u mixtureFloor ≤ 13206 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13206 - 1))).real
      {v | sgA (paperDesignP 13206) c a v < √(2 / (13206 : ℝ) * mixtureFloor)}
        ∂muI 13206 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13206).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13206) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13206) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13206)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13206

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13206
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13206) : ℝ :=
  (latitudeC / eR c) / ((13206 : ℝ) * (13206 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13206) / ((13206 : ℝ) * (13206 - 3))

theorem location_variance_on_event {c : Ret 13206}
    (hw : WINDOW (paperDesignP 13206) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13206) c a v - lbar (paperDesignP 13206) c a) ^ 2
      ∂stdGauss (Fin (13206 - 1))) ^ 2 ∂muI 13206 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13206)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13206}
    (hw : WINDOW (paperDesignP 13206) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13206) c a v - gbar (paperDesignP 13206) c a) ^ 2
      ∂stdGauss (Fin (13206 - 1))) ^ 2 ∂muI 13206 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13206)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13206}
    (hw : WINDOW (paperDesignP 13206) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13206 - 1))).real
      {v | sgA (paperDesignP 13206) c a v < √(2 / (13206 : ℝ) * mixtureFloor)}
      ∂muI 13206 ≤ lowMassBudget) :
    LatMom (paperDesignP 13206) c (√(2 / (13206 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13206

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13206
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

theorem location_budget_cap {c : Ret 13206} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13206 : ℝ) * (13206 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13206 : ℝ) * (13206 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13206 : ℝ) /
      ((13206 : ℝ) * (13206 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13206 : ℝ) * (13206 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13206 ≤ (2 * (16 / 5) / 13206 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13206} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (498564061 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (122472893 / 200000000000) ∧
    locationMomentBudget c 12 ≤ (5251227 / 6250000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (950508361 / 200000000000000) ∧
    residualMomentBudget 6 ≤ (2918669781 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (8009137533 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13206} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30588263 / 1000000000000000) ∧ residualVarianceBudget ≤ (86859 / 31250000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13206 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((950508361 / 200000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13206

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13206
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13206 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13206) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13206) : ℝ :=
  exp (hqKappa * (13206 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((720467 / 125000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5763737 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13206} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (5251227 / 1562500000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8009137533 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8009137533 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8009137533 / 250000000000000) : ℝ) / ((720467 / 125000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22356763 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 13206} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (403790841 / 250000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((5251227 / 1562500000))) / ((720467 / 125000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13206} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13206 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13206 * ((22356763 / 1000000000) : ℝ) ^ 2 / 2 + ((403790841 / 250000000)) ^ 2 * (1 + (22356763 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13206 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13206 * ((22356763 / 1000000000)) ^ 2 / 2 + ((403790841 / 250000000)) ^ 2 * (1 + (22356763 / 1000000000))) := by
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
  have hd : (2 * ((720467 / 125000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (34892593 / 100000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121749261973 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13206

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13207
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13207 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13207) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13207 : ℝ) * (13207 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13207) /
    ((13207 : ℝ) * (13207 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13207} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13207}
    (hw : WINDOW (paperDesignP 13207) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13207) c a v - lbar (paperDesignP 13207) c a| ^ (2 * q)
      ∂stdGauss (Fin (13207 - 1)) ∂muI 13207 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13207)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13207}
    (hw : WINDOW (paperDesignP 13207) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13207) c a v - gbar (paperDesignP 13207) c a| ^ (2 * q)
      ∂stdGauss (Fin (13207 - 1)) ∂muI 13207 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13207)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13207) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13207}
    (hw : WINDOW (paperDesignP 13207) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13207 - 1))).real
      {v | sgA (paperDesignP 13207) c a v < √(2 / (13207 : ℝ) * mixtureFloor)}
      ∂muI 13207 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13207 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13207 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13207) c
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

end BstLean.Part266.Row13207

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13207
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13207 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13207)
    (p : Ix 13207 × (Fin (13207 - 1) → ℝ)) :
    sgA (paperDesignP 13207) c p.1 p.2 ^ 2 ≤
      (2 / (13207 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13207).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13207) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13207 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13207 : ℝ) * _ ≤ 2 / 13207 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13207)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13207}
    (hw : WINDOW (paperDesignP 13207) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13207) c a v ^ 8
      ∂stdGauss (Fin (13207 - 1)) ∂muI 13207 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13207).prod (stdGauss (Fin (13207 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13207) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13207) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13207 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13207) c p.1 p.2)
      (√(2 / (13207 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13207)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13207 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13207) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13207}
    (hw : WINDOW (paperDesignP 13207) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13207) c a v -
      ∫ w, sA (paperDesignP 13207) c a w ∂stdGauss (Fin (13207 - 1))) ^ 2
      ∂stdGauss (Fin (13207 - 1))) ^ 2 ∂muI 13207 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13207) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13207

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13207
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13207}
    (hw : WINDOW (paperDesignP 13207) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13207).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13207) c M H xi)
    (hE : centreEnergy (paperDesignP 13207) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13207 : ℝ))))
    (hprice : massBound 13207 M H xi E u mixtureFloor ≤ 13207 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13207 - 1))).real
      {v | sgA (paperDesignP 13207) c a v < √(2 / (13207 : ℝ) * mixtureFloor)}
        ∂muI 13207 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13207).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13207) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13207) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13207)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13207

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13207
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13207) : ℝ :=
  (latitudeC / eR c) / ((13207 : ℝ) * (13207 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13207) / ((13207 : ℝ) * (13207 - 3))

theorem location_variance_on_event {c : Ret 13207}
    (hw : WINDOW (paperDesignP 13207) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13207) c a v - lbar (paperDesignP 13207) c a) ^ 2
      ∂stdGauss (Fin (13207 - 1))) ^ 2 ∂muI 13207 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13207)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13207}
    (hw : WINDOW (paperDesignP 13207) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13207) c a v - gbar (paperDesignP 13207) c a) ^ 2
      ∂stdGauss (Fin (13207 - 1))) ^ 2 ∂muI 13207 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13207)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13207}
    (hw : WINDOW (paperDesignP 13207) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13207 - 1))).real
      {v | sgA (paperDesignP 13207) c a v < √(2 / (13207 : ℝ) * mixtureFloor)}
      ∂muI 13207 ≤ lowMassBudget) :
    LatMom (paperDesignP 13207) c (√(2 / (13207 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13207

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13207
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

theorem location_budget_cap {c : Ret 13207} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13207 : ℝ) * (13207 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13207 : ℝ) * (13207 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13207 : ℝ) /
      ((13207 : ℝ) * (13207 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13207 : ℝ) * (13207 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13207 ≤ (2 * (16 / 5) / 13207 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13207} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (498526299 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (24492723 / 40000000000) ∧
    locationMomentBudget c 12 ≤ (420066321 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4752001917 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (2918338187 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (15641069 / 1953125000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13207} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30583631 / 1000000000000000) ∧ residualVarianceBudget ≤ (2778857 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13207 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4752001917 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13207

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13207
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13207 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13207) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13207) : ℝ :=
  exp (hqKappa * (13207 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((2881759 / 500000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5763519 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13207} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (420066321 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (15641069 / 488281250000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (15641069 / 488281250000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((15641069 / 488281250000) : ℝ) / ((2881759 / 500000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11177529 / 500000000) := by
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

theorem hq_location_bounds {c : Ret 13207} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1615102039 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((420066321 / 125000000000))) / ((2881759 / 500000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13207} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13207 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13207 * ((11177529 / 500000000) : ℝ) ^ 2 / 2 + ((1615102039 / 1000000000)) ^ 2 * (1 + (11177529 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13207 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13207 * ((11177529 / 500000000)) ^ 2 / 2 + ((1615102039 / 1000000000)) ^ 2 * (1 + (11177529 / 500000000))) := by
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
  have hd : (2 * ((2881759 / 500000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (348938981 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (60879185099 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13207

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13208
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13208 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13208) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13208 : ℝ) * (13208 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13208) /
    ((13208 : ℝ) * (13208 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13208} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13208}
    (hw : WINDOW (paperDesignP 13208) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13208) c a v - lbar (paperDesignP 13208) c a| ^ (2 * q)
      ∂stdGauss (Fin (13208 - 1)) ∂muI 13208 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13208)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13208}
    (hw : WINDOW (paperDesignP 13208) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13208) c a v - gbar (paperDesignP 13208) c a| ^ (2 * q)
      ∂stdGauss (Fin (13208 - 1)) ∂muI 13208 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13208)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13208) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13208}
    (hw : WINDOW (paperDesignP 13208) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13208 - 1))).real
      {v | sgA (paperDesignP 13208) c a v < √(2 / (13208 : ℝ) * mixtureFloor)}
      ∂muI 13208 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13208 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13208 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13208) c
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

end BstLean.Part266.Row13208

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13208
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13208 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13208)
    (p : Ix 13208 × (Fin (13208 - 1) → ℝ)) :
    sgA (paperDesignP 13208) c p.1 p.2 ^ 2 ≤
      (2 / (13208 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13208).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13208) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13208 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13208 : ℝ) * _ ≤ 2 / 13208 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13208)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13208}
    (hw : WINDOW (paperDesignP 13208) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13208) c a v ^ 8
      ∂stdGauss (Fin (13208 - 1)) ∂muI 13208 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13208).prod (stdGauss (Fin (13208 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13208) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13208) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13208 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13208) c p.1 p.2)
      (√(2 / (13208 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13208)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13208 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13208) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13208}
    (hw : WINDOW (paperDesignP 13208) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13208) c a v -
      ∫ w, sA (paperDesignP 13208) c a w ∂stdGauss (Fin (13208 - 1))) ^ 2
      ∂stdGauss (Fin (13208 - 1))) ^ 2 ∂muI 13208 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13208) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13208

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13208
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13208}
    (hw : WINDOW (paperDesignP 13208) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13208).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13208) c M H xi)
    (hE : centreEnergy (paperDesignP 13208) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13208 : ℝ))))
    (hprice : massBound 13208 M H xi E u mixtureFloor ≤ 13208 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13208 - 1))).real
      {v | sgA (paperDesignP 13208) c a v < √(2 / (13208 : ℝ) * mixtureFloor)}
        ∂muI 13208 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13208).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13208) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13208) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13208)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13208

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13208
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13208) : ℝ :=
  (latitudeC / eR c) / ((13208 : ℝ) * (13208 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13208) / ((13208 : ℝ) * (13208 - 3))

theorem location_variance_on_event {c : Ret 13208}
    (hw : WINDOW (paperDesignP 13208) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13208) c a v - lbar (paperDesignP 13208) c a) ^ 2
      ∂stdGauss (Fin (13208 - 1))) ^ 2 ∂muI 13208 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13208)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13208}
    (hw : WINDOW (paperDesignP 13208) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13208) c a v - gbar (paperDesignP 13208) c a) ^ 2
      ∂stdGauss (Fin (13208 - 1))) ^ 2 ∂muI 13208 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13208)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13208}
    (hw : WINDOW (paperDesignP 13208) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13208 - 1))).real
      {v | sgA (paperDesignP 13208) c a v < √(2 / (13208 : ℝ) * mixtureFloor)}
      ∂muI 13208 ≤ lowMassBudget) :
    LatMom (paperDesignP 13208) c (√(2 / (13208 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13208

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13208
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

theorem location_budget_cap {c : Ret 13208} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13208 : ℝ) * (13208 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13208 : ℝ) * (13208 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13208 : ℝ) /
      ((13208 : ℝ) * (13208 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13208 : ℝ) * (13208 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13208 ≤ (2 * (16 / 5) / 13208 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13208} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (498488541 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (612271693 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (420034487 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (1187865533 / 250000000000000) ∧
    residualMomentBudget 6 ≤ (22796927 / 3906250000000) ∧
    residualMomentBudget 12 ≤ (500457331 / 62500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13208} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30578999 / 1000000000000000) ∧ residualVarianceBudget ≤ (1389113 / 500000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13208 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((1187865533 / 250000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13208

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13208
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13208 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13208) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13208) : ℝ :=
  exp (hqKappa * (13208 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((57633 / 10000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5763301 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13208} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (420034487 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (500457331 / 15625000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (500457331 / 15625000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((500457331 / 15625000000000) : ℝ) / ((57633 / 10000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11176677 / 500000000) := by
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

theorem hq_location_bounds {c : Ret 13208} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1615040729 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((420034487 / 125000000000))) / ((57633 / 10000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13208} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13208 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13208 * ((11176677 / 500000000) : ℝ) ^ 2 / 2 + ((1615040729 / 1000000000)) ^ 2 * (1 + (11176677 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13208 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13208 * ((11176677 / 500000000)) ^ 2 / 2 + ((1615040729 / 1000000000)) ^ 2 * (1 + (11176677 / 500000000))) := by
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
  have hd : (2 * ((57633 / 10000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (174476017 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (4870699179 / 40000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13208

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13209
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13209 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13209) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13209 : ℝ) * (13209 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13209) /
    ((13209 : ℝ) * (13209 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13209} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13209}
    (hw : WINDOW (paperDesignP 13209) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13209) c a v - lbar (paperDesignP 13209) c a| ^ (2 * q)
      ∂stdGauss (Fin (13209 - 1)) ∂muI 13209 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13209)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13209}
    (hw : WINDOW (paperDesignP 13209) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13209) c a v - gbar (paperDesignP 13209) c a| ^ (2 * q)
      ∂stdGauss (Fin (13209 - 1)) ∂muI 13209 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13209)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13209) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13209}
    (hw : WINDOW (paperDesignP 13209) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13209 - 1))).real
      {v | sgA (paperDesignP 13209) c a v < √(2 / (13209 : ℝ) * mixtureFloor)}
      ∂muI 13209 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13209 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13209 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13209) c
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

end BstLean.Part266.Row13209

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13209
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13209 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13209)
    (p : Ix 13209 × (Fin (13209 - 1) → ℝ)) :
    sgA (paperDesignP 13209) c p.1 p.2 ^ 2 ≤
      (2 / (13209 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13209).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13209) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13209 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13209 : ℝ) * _ ≤ 2 / 13209 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13209)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13209}
    (hw : WINDOW (paperDesignP 13209) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13209) c a v ^ 8
      ∂stdGauss (Fin (13209 - 1)) ∂muI 13209 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13209).prod (stdGauss (Fin (13209 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13209) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13209) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13209 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13209) c p.1 p.2)
      (√(2 / (13209 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13209)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13209 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13209) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13209}
    (hw : WINDOW (paperDesignP 13209) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13209) c a v -
      ∫ w, sA (paperDesignP 13209) c a w ∂stdGauss (Fin (13209 - 1))) ^ 2
      ∂stdGauss (Fin (13209 - 1))) ^ 2 ∂muI 13209 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13209) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13209

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13209
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13209}
    (hw : WINDOW (paperDesignP 13209) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13209).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13209) c M H xi)
    (hE : centreEnergy (paperDesignP 13209) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13209 : ℝ))))
    (hprice : massBound 13209 M H xi E u mixtureFloor ≤ 13209 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13209 - 1))).real
      {v | sgA (paperDesignP 13209) c a v < √(2 / (13209 : ℝ) * mixtureFloor)}
        ∂muI 13209 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13209).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13209) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13209) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13209)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13209

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13209
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13209) : ℝ :=
  (latitudeC / eR c) / ((13209 : ℝ) * (13209 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13209) / ((13209 : ℝ) * (13209 - 3))

theorem location_variance_on_event {c : Ret 13209}
    (hw : WINDOW (paperDesignP 13209) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13209) c a v - lbar (paperDesignP 13209) c a) ^ 2
      ∂stdGauss (Fin (13209 - 1))) ^ 2 ∂muI 13209 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13209)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13209}
    (hw : WINDOW (paperDesignP 13209) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13209) c a v - gbar (paperDesignP 13209) c a) ^ 2
      ∂stdGauss (Fin (13209 - 1))) ^ 2 ∂muI 13209 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13209)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13209}
    (hw : WINDOW (paperDesignP 13209) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13209 - 1))).real
      {v | sgA (paperDesignP 13209) c a v < √(2 / (13209 : ℝ) * mixtureFloor)}
      ∂muI 13209 ≤ lowMassBudget) :
    LatMom (paperDesignP 13209) c (√(2 / (13209 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13209

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13209
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

theorem location_budget_cap {c : Ret 13209} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13209 : ℝ) * (13209 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13209 : ℝ) * (13209 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13209 : ℝ) /
      ((13209 : ℝ) * (13209 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13209 : ℝ) * (13209 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13209 ≤ (2 * (16 / 5) / 13209 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13209} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (49845079 / 100000000000) ∧
    locationMomentBudget c 6 ≤ (306112659 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (210001329 / 250000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (296932653 / 62500000000000) ∧
    residualMomentBudget 6 ≤ (46682803 / 8000000000000) ∧
    residualMomentBudget 12 ≤ (2001601859 / 250000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13209} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30574369 / 1000000000000000) ∧ residualVarianceBudget ≤ (555519 / 200000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13209 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((296932653 / 62500000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13209

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13209
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13209 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13209) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13209) : ℝ :=
  exp (hqKappa * (13209 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5763081 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2881541 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13209} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (210001329 / 62500000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (2001601859 / 62500000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (2001601859 / 62500000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((2001601859 / 62500000000000) : ℝ) / ((5763081 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11175827 / 500000000) := by
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

theorem hq_location_bounds {c : Ret 13209} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (807489857 / 500000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((210001329 / 62500000000))) / ((5763081 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13209} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13209 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13209 * ((11175827 / 500000000) : ℝ) ^ 2 / 2 + ((807489857 / 500000000)) ^ 2 * (1 + (11175827 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13209 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13209 * ((11175827 / 500000000)) ^ 2 / 2 + ((807489857 / 500000000)) ^ 2 * (1 + (11175827 / 500000000))) := by
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
  have hd : (2 * ((5763081 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (87241287 / 250000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (60888316149 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13209

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13210
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13210 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13210) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13210 : ℝ) * (13210 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13210) /
    ((13210 : ℝ) * (13210 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13210} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13210}
    (hw : WINDOW (paperDesignP 13210) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13210) c a v - lbar (paperDesignP 13210) c a| ^ (2 * q)
      ∂stdGauss (Fin (13210 - 1)) ∂muI 13210 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13210)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13210}
    (hw : WINDOW (paperDesignP 13210) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13210) c a v - gbar (paperDesignP 13210) c a| ^ (2 * q)
      ∂stdGauss (Fin (13210 - 1)) ∂muI 13210 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13210)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13210) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13210}
    (hw : WINDOW (paperDesignP 13210) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13210 - 1))).real
      {v | sgA (paperDesignP 13210) c a v < √(2 / (13210 : ℝ) * mixtureFloor)}
      ∂muI 13210 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13210 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13210 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13210) c
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

end BstLean.Part266.Row13210

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13210
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13210 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13210)
    (p : Ix 13210 × (Fin (13210 - 1) → ℝ)) :
    sgA (paperDesignP 13210) c p.1 p.2 ^ 2 ≤
      (2 / (13210 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13210).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13210) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13210 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13210 : ℝ) * _ ≤ 2 / 13210 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13210)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13210}
    (hw : WINDOW (paperDesignP 13210) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13210) c a v ^ 8
      ∂stdGauss (Fin (13210 - 1)) ∂muI 13210 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13210).prod (stdGauss (Fin (13210 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13210) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13210) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13210 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13210) c p.1 p.2)
      (√(2 / (13210 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13210)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13210 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13210) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13210}
    (hw : WINDOW (paperDesignP 13210) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13210) c a v -
      ∫ w, sA (paperDesignP 13210) c a w ∂stdGauss (Fin (13210 - 1))) ^ 2
      ∂stdGauss (Fin (13210 - 1))) ^ 2 ∂muI 13210 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13210) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13210

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13210
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13210}
    (hw : WINDOW (paperDesignP 13210) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13210).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13210) c M H xi)
    (hE : centreEnergy (paperDesignP 13210) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13210 : ℝ))))
    (hprice : massBound 13210 M H xi E u mixtureFloor ≤ 13210 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13210 - 1))).real
      {v | sgA (paperDesignP 13210) c a v < √(2 / (13210 : ℝ) * mixtureFloor)}
        ∂muI 13210 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13210).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13210) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13210) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13210)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13210

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13210
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13210) : ℝ :=
  (latitudeC / eR c) / ((13210 : ℝ) * (13210 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13210) / ((13210 : ℝ) * (13210 - 3))

theorem location_variance_on_event {c : Ret 13210}
    (hw : WINDOW (paperDesignP 13210) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13210) c a v - lbar (paperDesignP 13210) c a) ^ 2
      ∂stdGauss (Fin (13210 - 1))) ^ 2 ∂muI 13210 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13210)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13210}
    (hw : WINDOW (paperDesignP 13210) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13210) c a v - gbar (paperDesignP 13210) c a) ^ 2
      ∂stdGauss (Fin (13210 - 1))) ^ 2 ∂muI 13210 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13210)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13210}
    (hw : WINDOW (paperDesignP 13210) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13210 - 1))).real
      {v | sgA (paperDesignP 13210) c a v < √(2 / (13210 : ℝ) * mixtureFloor)}
      ∂muI 13210 ≤ lowMassBudget) :
    LatMom (paperDesignP 13210) c (√(2 / (13210 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13210

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13210
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

theorem location_budget_cap {c : Ret 13210} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13210 : ℝ) * (13210 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13210 : ℝ) * (13210 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13210 : ℝ) /
      ((13210 : ℝ) * (13210 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13210 : ℝ) * (13210 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13210 ≤ (2 * (16 / 5) / 13210 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13210} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (124603261 / 250000000000) ∧
    locationMomentBudget c 6 ≤ (612178949 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (839941667 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4750382867 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (1458671891 / 250000000000000) ∧
    residualMomentBudget 12 ≤ (2001374437 / 250000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13210} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (1528487 / 50000000000000) ∧ residualVarianceBudget ≤ (694241 / 250000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13210 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4750382867 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13210

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13210
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13210 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13210) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13210) : ℝ :=
  exp (hqKappa * (13210 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5762863 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (360179 / 62500000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13210} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (839941667 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (2001374437 / 62500000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (2001374437 / 62500000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((2001374437 / 62500000000000) : ℝ) / ((5762863 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (446999 / 20000000) := by
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

theorem hq_location_bounds {c : Ret 13210} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1614918431 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((839941667 / 250000000000))) / ((5762863 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13210} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13210 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13210 * ((446999 / 20000000) : ℝ) ^ 2 / 2 + ((1614918431 / 1000000000)) ^ 2 * (1 + (446999 / 20000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13210 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13210 * ((446999 / 20000000)) ^ 2 / 2 + ((1614918431 / 1000000000)) ^ 2 * (1 + (446999 / 20000000))) := by
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
  have hd : (2 * ((5762863 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (348978203 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121785743681 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13210

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13211
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13211 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13211) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13211 : ℝ) * (13211 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13211) /
    ((13211 : ℝ) * (13211 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13211} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13211}
    (hw : WINDOW (paperDesignP 13211) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13211) c a v - lbar (paperDesignP 13211) c a| ^ (2 * q)
      ∂stdGauss (Fin (13211 - 1)) ∂muI 13211 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13211)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13211}
    (hw : WINDOW (paperDesignP 13211) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13211) c a v - gbar (paperDesignP 13211) c a| ^ (2 * q)
      ∂stdGauss (Fin (13211 - 1)) ∂muI 13211 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13211)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13211) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13211}
    (hw : WINDOW (paperDesignP 13211) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13211 - 1))).real
      {v | sgA (paperDesignP 13211) c a v < √(2 / (13211 : ℝ) * mixtureFloor)}
      ∂muI 13211 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13211 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13211 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13211) c
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

end BstLean.Part266.Row13211

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13211
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13211 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13211)
    (p : Ix 13211 × (Fin (13211 - 1) → ℝ)) :
    sgA (paperDesignP 13211) c p.1 p.2 ^ 2 ≤
      (2 / (13211 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13211).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13211) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13211 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13211 : ℝ) * _ ≤ 2 / 13211 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13211)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13211}
    (hw : WINDOW (paperDesignP 13211) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13211) c a v ^ 8
      ∂stdGauss (Fin (13211 - 1)) ∂muI 13211 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13211).prod (stdGauss (Fin (13211 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13211) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13211) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13211 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13211) c p.1 p.2)
      (√(2 / (13211 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13211)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13211 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13211) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13211}
    (hw : WINDOW (paperDesignP 13211) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13211) c a v -
      ∫ w, sA (paperDesignP 13211) c a w ∂stdGauss (Fin (13211 - 1))) ^ 2
      ∂stdGauss (Fin (13211 - 1))) ^ 2 ∂muI 13211 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13211) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13211

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13211
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13211}
    (hw : WINDOW (paperDesignP 13211) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13211).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13211) c M H xi)
    (hE : centreEnergy (paperDesignP 13211) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13211 : ℝ))))
    (hprice : massBound 13211 M H xi E u mixtureFloor ≤ 13211 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13211 - 1))).real
      {v | sgA (paperDesignP 13211) c a v < √(2 / (13211 : ℝ) * mixtureFloor)}
        ∂muI 13211 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13211).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13211) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13211) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13211)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13211

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13211
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13211) : ℝ :=
  (latitudeC / eR c) / ((13211 : ℝ) * (13211 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13211) / ((13211 : ℝ) * (13211 - 3))

theorem location_variance_on_event {c : Ret 13211}
    (hw : WINDOW (paperDesignP 13211) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13211) c a v - lbar (paperDesignP 13211) c a) ^ 2
      ∂stdGauss (Fin (13211 - 1))) ^ 2 ∂muI 13211 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13211)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13211}
    (hw : WINDOW (paperDesignP 13211) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13211) c a v - gbar (paperDesignP 13211) c a) ^ 2
      ∂stdGauss (Fin (13211 - 1))) ^ 2 ∂muI 13211 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13211)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13211}
    (hw : WINDOW (paperDesignP 13211) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13211 - 1))).real
      {v | sgA (paperDesignP 13211) c a v < √(2 / (13211 : ℝ) * mixtureFloor)}
      ∂muI 13211 ≤ lowMassBudget) :
    LatMom (paperDesignP 13211) c (√(2 / (13211 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13211

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13211
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

theorem location_budget_cap {c : Ret 13211} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13211 : ℝ) * (13211 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13211 : ℝ) * (13211 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13211 : ℝ) /
      ((13211 : ℝ) * (13211 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13211 : ℝ) * (13211 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13211 ≤ (2 * (16 / 5) / 13211 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13211} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (62296913 / 125000000000) ∧
    locationMomentBudget c 6 ≤ (153033147 / 250000000000) ∧
    locationMomentBudget c 12 ≤ (209969507 / 250000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (1187460847 / 250000000000000) ∧
    residualMomentBudget 6 ≤ (5834024879 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (8004588233 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13211} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30565111 / 1000000000000000) ∧ residualVarianceBudget ≤ (2776333 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13211 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((1187460847 / 250000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13211

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13211
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13211 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13211) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13211) : ℝ :=
  exp (hqKappa * (13211 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((1152529 / 200000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2881323 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13211} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (209969507 / 62500000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8004588233 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8004588233 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8004588233 / 250000000000000) : ℝ) / ((1152529 / 200000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22348247 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 13211} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (807428581 / 500000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((209969507 / 62500000000))) / ((1152529 / 200000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13211} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13211 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13211 * ((22348247 / 1000000000) : ℝ) ^ 2 / 2 + ((807428581 / 500000000)) ^ 2 * (1 + (22348247 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13211 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13211 * ((22348247 / 1000000000)) ^ 2 / 2 + ((807428581 / 500000000)) ^ 2 * (1 + (22348247 / 1000000000))) := by
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
  have hd : (2 * ((1152529 / 200000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (174495629 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121794856117 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13211

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13212
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13212 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13212) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13212 : ℝ) * (13212 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13212) /
    ((13212 : ℝ) * (13212 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13212} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13212}
    (hw : WINDOW (paperDesignP 13212) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13212) c a v - lbar (paperDesignP 13212) c a| ^ (2 * q)
      ∂stdGauss (Fin (13212 - 1)) ∂muI 13212 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13212)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13212}
    (hw : WINDOW (paperDesignP 13212) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13212) c a v - gbar (paperDesignP 13212) c a| ^ (2 * q)
      ∂stdGauss (Fin (13212 - 1)) ∂muI 13212 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13212)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13212) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13212}
    (hw : WINDOW (paperDesignP 13212) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13212 - 1))).real
      {v | sgA (paperDesignP 13212) c a v < √(2 / (13212 : ℝ) * mixtureFloor)}
      ∂muI 13212 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13212 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13212 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13212) c
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

end BstLean.Part266.Row13212

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13212
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13212 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13212)
    (p : Ix 13212 × (Fin (13212 - 1) → ℝ)) :
    sgA (paperDesignP 13212) c p.1 p.2 ^ 2 ≤
      (2 / (13212 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13212).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13212) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13212 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13212 : ℝ) * _ ≤ 2 / 13212 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13212)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13212}
    (hw : WINDOW (paperDesignP 13212) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13212) c a v ^ 8
      ∂stdGauss (Fin (13212 - 1)) ∂muI 13212 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13212).prod (stdGauss (Fin (13212 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13212) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13212) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13212 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13212) c p.1 p.2)
      (√(2 / (13212 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13212)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13212 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13212) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13212}
    (hw : WINDOW (paperDesignP 13212) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13212) c a v -
      ∫ w, sA (paperDesignP 13212) c a w ∂stdGauss (Fin (13212 - 1))) ^ 2
      ∂stdGauss (Fin (13212 - 1))) ^ 2 ∂muI 13212 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13212) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13212

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13212
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13212}
    (hw : WINDOW (paperDesignP 13212) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13212).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13212) c M H xi)
    (hE : centreEnergy (paperDesignP 13212) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13212 : ℝ))))
    (hprice : massBound 13212 M H xi E u mixtureFloor ≤ 13212 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13212 - 1))).real
      {v | sgA (paperDesignP 13212) c a v < √(2 / (13212 : ℝ) * mixtureFloor)}
        ∂muI 13212 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13212).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13212) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13212) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13212)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13212

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13212
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13212) : ℝ :=
  (latitudeC / eR c) / ((13212 : ℝ) * (13212 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13212) / ((13212 : ℝ) * (13212 - 3))

theorem location_variance_on_event {c : Ret 13212}
    (hw : WINDOW (paperDesignP 13212) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13212) c a v - lbar (paperDesignP 13212) c a) ^ 2
      ∂stdGauss (Fin (13212 - 1))) ^ 2 ∂muI 13212 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13212)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13212}
    (hw : WINDOW (paperDesignP 13212) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13212) c a v - gbar (paperDesignP 13212) c a) ^ 2
      ∂stdGauss (Fin (13212 - 1))) ^ 2 ∂muI 13212 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13212)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13212}
    (hw : WINDOW (paperDesignP 13212) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13212 - 1))).real
      {v | sgA (paperDesignP 13212) c a v < √(2 / (13212 : ℝ) * mixtureFloor)}
      ∂muI 13212 ≤ lowMassBudget) :
    LatMom (paperDesignP 13212) c (√(2 / (13212 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13212

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13212
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

theorem location_budget_cap {c : Ret 13212} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13212 : ℝ) * (13212 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13212 : ℝ) * (13212 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13212 : ℝ) /
      ((13212 : ℝ) * (13212 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13212 : ℝ) * (13212 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13212 ≤ (2 * (16 / 5) / 13212 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13212} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (49833757 / 100000000000) ∧
    locationMomentBudget c 6 ≤ (612086233 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (419907199 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4749304011 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (5833362319 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (800367889 / 100000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13212} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (7640121 / 250000000000000) ∧ residualVarianceBudget ≤ (2775703 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13212 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4749304011 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13212

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13212
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13212 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13212) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13212) : ℝ :=
  exp (hqKappa * (13212 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5762427 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (1440607 / 250000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13212} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (419907199 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (800367889 / 25000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (800367889 / 25000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((800367889 / 25000000000000) : ℝ) / ((5762427 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (1396659 / 62500000) := by
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

theorem hq_location_bounds {c : Ret 13212} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1614795907 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((419907199 / 125000000000))) / ((5762427 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13212} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13212 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13212 * ((1396659 / 62500000) : ℝ) ^ 2 / 2 + ((1614795907 / 1000000000)) ^ 2 * (1 + (1396659 / 62500000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13212 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13212 * ((1396659 / 62500000)) ^ 2 / 2 + ((1614795907 / 1000000000)) ^ 2 * (1 + (1396659 / 62500000))) := by
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
  have hd : (2 * ((5762427 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (69800863 / 200000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (30450992401 / 250000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13212

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13213
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13213 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13213) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13213 : ℝ) * (13213 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13213) /
    ((13213 : ℝ) * (13213 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13213} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13213}
    (hw : WINDOW (paperDesignP 13213) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13213) c a v - lbar (paperDesignP 13213) c a| ^ (2 * q)
      ∂stdGauss (Fin (13213 - 1)) ∂muI 13213 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13213)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13213}
    (hw : WINDOW (paperDesignP 13213) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13213) c a v - gbar (paperDesignP 13213) c a| ^ (2 * q)
      ∂stdGauss (Fin (13213 - 1)) ∂muI 13213 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13213)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13213) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13213}
    (hw : WINDOW (paperDesignP 13213) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13213 - 1))).real
      {v | sgA (paperDesignP 13213) c a v < √(2 / (13213 : ℝ) * mixtureFloor)}
      ∂muI 13213 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13213 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13213 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13213) c
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

end BstLean.Part266.Row13213

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13213
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13213 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13213)
    (p : Ix 13213 × (Fin (13213 - 1) → ℝ)) :
    sgA (paperDesignP 13213) c p.1 p.2 ^ 2 ≤
      (2 / (13213 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13213).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13213) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13213 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13213 : ℝ) * _ ≤ 2 / 13213 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13213)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13213}
    (hw : WINDOW (paperDesignP 13213) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13213) c a v ^ 8
      ∂stdGauss (Fin (13213 - 1)) ∂muI 13213 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13213).prod (stdGauss (Fin (13213 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13213) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13213) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13213 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13213) c p.1 p.2)
      (√(2 / (13213 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13213)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13213 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13213) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13213}
    (hw : WINDOW (paperDesignP 13213) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13213) c a v -
      ∫ w, sA (paperDesignP 13213) c a w ∂stdGauss (Fin (13213 - 1))) ^ 2
      ∂stdGauss (Fin (13213 - 1))) ^ 2 ∂muI 13213 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13213) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13213

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13213
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13213}
    (hw : WINDOW (paperDesignP 13213) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13213).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13213) c M H xi)
    (hE : centreEnergy (paperDesignP 13213) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13213 : ℝ))))
    (hprice : massBound 13213 M H xi E u mixtureFloor ≤ 13213 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13213 - 1))).real
      {v | sgA (paperDesignP 13213) c a v < √(2 / (13213 : ℝ) * mixtureFloor)}
        ∂muI 13213 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13213).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13213) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13213) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13213)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13213

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13213
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13213) : ℝ :=
  (latitudeC / eR c) / ((13213 : ℝ) * (13213 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13213) / ((13213 : ℝ) * (13213 - 3))

theorem location_variance_on_event {c : Ret 13213}
    (hw : WINDOW (paperDesignP 13213) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13213) c a v - lbar (paperDesignP 13213) c a) ^ 2
      ∂stdGauss (Fin (13213 - 1))) ^ 2 ∂muI 13213 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13213)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13213}
    (hw : WINDOW (paperDesignP 13213) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13213) c a v - gbar (paperDesignP 13213) c a) ^ 2
      ∂stdGauss (Fin (13213 - 1))) ^ 2 ∂muI 13213 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13213)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13213}
    (hw : WINDOW (paperDesignP 13213) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13213 - 1))).real
      {v | sgA (paperDesignP 13213) c a v < √(2 / (13213 : ℝ) * mixtureFloor)}
      ∂muI 13213 ≤ lowMassBudget) :
    LatMom (paperDesignP 13213) c (√(2 / (13213 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13213

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13213
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

theorem location_budget_cap {c : Ret 13213} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13213 : ℝ) * (13213 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13213 : ℝ) * (13213 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13213 : ℝ) /
      ((13213 : ℝ) * (13213 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13213 : ℝ) * (13213 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13213 ≤ (2 * (16 / 5) / 13213 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13213} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (249149921 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (306019943 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (419875389 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (74199449 / 15625000000000) ∧
    residualMomentBudget 6 ≤ (1458174971 / 250000000000000) ∧
    residualMomentBudget 12 ≤ (8002769719 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13213} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15277929 / 500000000000000) ∧ residualVarianceBudget ≤ (2775073 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13213 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((74199449 / 15625000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13213

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13213
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13213 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13213) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13213) : ℝ :=
  exp (hqKappa * (13213 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5762209 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (576221 / 100000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13213} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (419875389 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8002769719 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8002769719 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8002769719 / 250000000000000) : ℝ) / ((5762209 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11172421 / 500000000) := by
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

theorem hq_location_bounds {c : Ret 13213} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (807367333 / 500000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((419875389 / 125000000000))) / ((5762209 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13213} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13213 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13213 * ((11172421 / 500000000) : ℝ) ^ 2 / 2 + ((807367333 / 500000000)) ^ 2 * (1 + (11172421 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13213 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13213 * ((11172421 / 500000000)) ^ 2 / 2 + ((807367333 / 500000000)) ^ 2 * (1 + (11172421 / 500000000))) := by
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
  have hd : (2 * ((5762209 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (349017373 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121813084143 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13213

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13214
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13214 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13214) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13214 : ℝ) * (13214 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13214) /
    ((13214 : ℝ) * (13214 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13214} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13214}
    (hw : WINDOW (paperDesignP 13214) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13214) c a v - lbar (paperDesignP 13214) c a| ^ (2 * q)
      ∂stdGauss (Fin (13214 - 1)) ∂muI 13214 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13214)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13214}
    (hw : WINDOW (paperDesignP 13214) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13214) c a v - gbar (paperDesignP 13214) c a| ^ (2 * q)
      ∂stdGauss (Fin (13214 - 1)) ∂muI 13214 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13214)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13214) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13214}
    (hw : WINDOW (paperDesignP 13214) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13214 - 1))).real
      {v | sgA (paperDesignP 13214) c a v < √(2 / (13214 : ℝ) * mixtureFloor)}
      ∂muI 13214 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13214 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13214 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13214) c
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

end BstLean.Part266.Row13214

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13214
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13214 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13214)
    (p : Ix 13214 × (Fin (13214 - 1) → ℝ)) :
    sgA (paperDesignP 13214) c p.1 p.2 ^ 2 ≤
      (2 / (13214 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13214).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13214) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13214 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13214 : ℝ) * _ ≤ 2 / 13214 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13214)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13214}
    (hw : WINDOW (paperDesignP 13214) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13214) c a v ^ 8
      ∂stdGauss (Fin (13214 - 1)) ∂muI 13214 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13214).prod (stdGauss (Fin (13214 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13214) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13214) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13214 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13214) c p.1 p.2)
      (√(2 / (13214 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13214)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13214 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13214) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13214}
    (hw : WINDOW (paperDesignP 13214) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13214) c a v -
      ∫ w, sA (paperDesignP 13214) c a w ∂stdGauss (Fin (13214 - 1))) ^ 2
      ∂stdGauss (Fin (13214 - 1))) ^ 2 ∂muI 13214 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13214) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13214

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13214
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13214}
    (hw : WINDOW (paperDesignP 13214) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13214).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13214) c M H xi)
    (hE : centreEnergy (paperDesignP 13214) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13214 : ℝ))))
    (hprice : massBound 13214 M H xi E u mixtureFloor ≤ 13214 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13214 - 1))).real
      {v | sgA (paperDesignP 13214) c a v < √(2 / (13214 : ℝ) * mixtureFloor)}
        ∂muI 13214 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13214).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13214) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13214) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13214)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13214

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13214
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13214) : ℝ :=
  (latitudeC / eR c) / ((13214 : ℝ) * (13214 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13214) / ((13214 : ℝ) * (13214 - 3))

theorem location_variance_on_event {c : Ret 13214}
    (hw : WINDOW (paperDesignP 13214) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13214) c a v - lbar (paperDesignP 13214) c a) ^ 2
      ∂stdGauss (Fin (13214 - 1))) ^ 2 ∂muI 13214 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13214)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13214}
    (hw : WINDOW (paperDesignP 13214) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13214) c a v - gbar (paperDesignP 13214) c a) ^ 2
      ∂stdGauss (Fin (13214 - 1))) ^ 2 ∂muI 13214 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13214)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13214}
    (hw : WINDOW (paperDesignP 13214) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13214 - 1))).real
      {v | sgA (paperDesignP 13214) c a v < √(2 / (13214 : ℝ) * mixtureFloor)}
      ∂muI 13214 ≤ lowMassBudget) :
    LatMom (paperDesignP 13214) c (√(2 / (13214 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13214

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13214
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

theorem location_budget_cap {c : Ret 13214} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13214 : ℝ) * (13214 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13214 : ℝ) * (13214 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13214 : ℝ) /
      ((13214 : ℝ) * (13214 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13214 : ℝ) * (13214 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13214 ≤ (2 * (16 / 5) / 13214 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13214} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (498262119 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (305996773 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (820007 / 976562500) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4748225563 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (2916018787 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (100023259 / 12500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13214} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30551233 / 1000000000000000) ∧ residualVarianceBudget ≤ (2774443 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13214 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4748225563 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13214

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13214
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13214 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13214) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13214) : ℝ :=
  exp (hqKappa * (13214 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5761991 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (720249 / 125000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13214} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (820007 / 244140625) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (100023259 / 3125000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (100023259 / 3125000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((100023259 / 3125000000000) : ℝ) / ((5761991 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (1117157 / 50000000) := by
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

theorem hq_location_bounds {c : Ret 13214} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1614673439 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((820007 / 244140625))) / ((5761991 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13214} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13214 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13214 * ((1117157 / 50000000) : ℝ) ^ 2 / 2 + ((1614673439 / 1000000000)) ^ 2 * (1 + (1117157 / 50000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13214 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13214 * ((1117157 / 50000000)) ^ 2 / 2 + ((1614673439 / 1000000000)) ^ 2 * (1 + (1117157 / 50000000))) := by
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
  have hd : (2 * ((5761991 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (10907201 / 31250) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (60911099867 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13214

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13215
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13215 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13215) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13215 : ℝ) * (13215 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13215) /
    ((13215 : ℝ) * (13215 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13215} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13215}
    (hw : WINDOW (paperDesignP 13215) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13215) c a v - lbar (paperDesignP 13215) c a| ^ (2 * q)
      ∂stdGauss (Fin (13215 - 1)) ∂muI 13215 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13215)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13215}
    (hw : WINDOW (paperDesignP 13215) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13215) c a v - gbar (paperDesignP 13215) c a| ^ (2 * q)
      ∂stdGauss (Fin (13215 - 1)) ∂muI 13215 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13215)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13215) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13215}
    (hw : WINDOW (paperDesignP 13215) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13215 - 1))).real
      {v | sgA (paperDesignP 13215) c a v < √(2 / (13215 : ℝ) * mixtureFloor)}
      ∂muI 13215 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13215 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13215 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13215) c
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

end BstLean.Part266.Row13215

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13215
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13215 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13215)
    (p : Ix 13215 × (Fin (13215 - 1) → ℝ)) :
    sgA (paperDesignP 13215) c p.1 p.2 ^ 2 ≤
      (2 / (13215 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13215).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13215) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13215 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13215 : ℝ) * _ ≤ 2 / 13215 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13215)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13215}
    (hw : WINDOW (paperDesignP 13215) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13215) c a v ^ 8
      ∂stdGauss (Fin (13215 - 1)) ∂muI 13215 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13215).prod (stdGauss (Fin (13215 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13215) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13215) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13215 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13215) c p.1 p.2)
      (√(2 / (13215 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13215)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13215 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13215) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13215}
    (hw : WINDOW (paperDesignP 13215) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13215) c a v -
      ∫ w, sA (paperDesignP 13215) c a w ∂stdGauss (Fin (13215 - 1))) ^ 2
      ∂stdGauss (Fin (13215 - 1))) ^ 2 ∂muI 13215 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13215) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13215

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13215
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13215}
    (hw : WINDOW (paperDesignP 13215) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13215).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13215) c M H xi)
    (hE : centreEnergy (paperDesignP 13215) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13215 : ℝ))))
    (hprice : massBound 13215 M H xi E u mixtureFloor ≤ 13215 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13215 - 1))).real
      {v | sgA (paperDesignP 13215) c a v < √(2 / (13215 : ℝ) * mixtureFloor)}
        ∂muI 13215 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13215).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13215) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13215) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13215)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13215

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13215
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13215) : ℝ :=
  (latitudeC / eR c) / ((13215 : ℝ) * (13215 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13215) / ((13215 : ℝ) * (13215 - 3))

theorem location_variance_on_event {c : Ret 13215}
    (hw : WINDOW (paperDesignP 13215) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13215) c a v - lbar (paperDesignP 13215) c a) ^ 2
      ∂stdGauss (Fin (13215 - 1))) ^ 2 ∂muI 13215 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13215)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13215}
    (hw : WINDOW (paperDesignP 13215) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13215) c a v - gbar (paperDesignP 13215) c a) ^ 2
      ∂stdGauss (Fin (13215 - 1))) ^ 2 ∂muI 13215 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13215)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13215}
    (hw : WINDOW (paperDesignP 13215) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13215 - 1))).real
      {v | sgA (paperDesignP 13215) c a v < √(2 / (13215 : ℝ) * mixtureFloor)}
      ∂muI 13215 ≤ lowMassBudget) :
    LatMom (paperDesignP 13215) c (√(2 / (13215 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13215

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13215
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

theorem location_budget_cap {c : Ret 13215} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13215 : ℝ) * (13215 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13215 : ℝ) * (13215 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13215 : ℝ) /
      ((13215 : ℝ) * (13215 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13215 : ℝ) * (13215 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13215 ≤ (2 * (16 / 5) / 13215 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13215} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (249112201 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (152986803 / 250000000000) ∧
    locationMomentBudget c 12 ≤ (839623567 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (1186921623 / 250000000000000) ∧
    residualMomentBudget 6 ≤ (583137539 / 100000000000000) ∧
    residualMomentBudget 12 ≤ (8000951893 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13215} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30546609 / 1000000000000000) ∧ residualVarianceBudget ≤ (2773813 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13215 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((1186921623 / 250000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13215

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13215
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13215 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13215) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13215) : ℝ :=
  exp (hqKappa * (13215 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5761773 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2880887 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13215} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (839623567 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8000951893 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8000951893 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8000951893 / 250000000000000) : ℝ) / ((5761773 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11170719 / 500000000) := by
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

theorem hq_location_bounds {c : Ret 13215} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (64584489 / 40000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((839623567 / 250000000000))) / ((5761773 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13215} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13215 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13215 * ((11170719 / 500000000) : ℝ) ^ 2 / 2 + ((64584489 / 40000000)) ^ 2 * (1 + (11170719 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13215 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13215 * ((11170719 / 500000000)) ^ 2 / 2 + ((64584489 / 40000000)) ^ 2 * (1 + (11170719 / 500000000))) := by
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
  have hd : (2 * ((5761773 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (349043491 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121831316377 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13215

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13216
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13216 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13216) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13216 : ℝ) * (13216 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13216) /
    ((13216 : ℝ) * (13216 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13216} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13216}
    (hw : WINDOW (paperDesignP 13216) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13216) c a v - lbar (paperDesignP 13216) c a| ^ (2 * q)
      ∂stdGauss (Fin (13216 - 1)) ∂muI 13216 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13216)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13216}
    (hw : WINDOW (paperDesignP 13216) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13216) c a v - gbar (paperDesignP 13216) c a| ^ (2 * q)
      ∂stdGauss (Fin (13216 - 1)) ∂muI 13216 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13216)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13216) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13216}
    (hw : WINDOW (paperDesignP 13216) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13216 - 1))).real
      {v | sgA (paperDesignP 13216) c a v < √(2 / (13216 : ℝ) * mixtureFloor)}
      ∂muI 13216 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13216 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13216 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13216) c
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

end BstLean.Part266.Row13216

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13216
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13216 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13216)
    (p : Ix 13216 × (Fin (13216 - 1) → ℝ)) :
    sgA (paperDesignP 13216) c p.1 p.2 ^ 2 ≤
      (2 / (13216 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13216).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13216) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13216 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13216 : ℝ) * _ ≤ 2 / 13216 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13216)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13216}
    (hw : WINDOW (paperDesignP 13216) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13216) c a v ^ 8
      ∂stdGauss (Fin (13216 - 1)) ∂muI 13216 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13216).prod (stdGauss (Fin (13216 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13216) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13216) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13216 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13216) c p.1 p.2)
      (√(2 / (13216 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13216)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13216 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13216) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13216}
    (hw : WINDOW (paperDesignP 13216) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13216) c a v -
      ∫ w, sA (paperDesignP 13216) c a w ∂stdGauss (Fin (13216 - 1))) ^ 2
      ∂stdGauss (Fin (13216 - 1))) ^ 2 ∂muI 13216 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13216) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13216

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13216
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13216}
    (hw : WINDOW (paperDesignP 13216) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13216).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13216) c M H xi)
    (hE : centreEnergy (paperDesignP 13216) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13216 : ℝ))))
    (hprice : massBound 13216 M H xi E u mixtureFloor ≤ 13216 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13216 - 1))).real
      {v | sgA (paperDesignP 13216) c a v < √(2 / (13216 : ℝ) * mixtureFloor)}
        ∂muI 13216 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13216).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13216) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13216) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13216)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13216

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13216
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13216) : ℝ :=
  (latitudeC / eR c) / ((13216 : ℝ) * (13216 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13216) / ((13216 : ℝ) * (13216 - 3))

theorem location_variance_on_event {c : Ret 13216}
    (hw : WINDOW (paperDesignP 13216) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13216) c a v - lbar (paperDesignP 13216) c a) ^ 2
      ∂stdGauss (Fin (13216 - 1))) ^ 2 ∂muI 13216 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13216)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13216}
    (hw : WINDOW (paperDesignP 13216) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13216) c a v - gbar (paperDesignP 13216) c a) ^ 2
      ∂stdGauss (Fin (13216 - 1))) ^ 2 ∂muI 13216 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13216)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13216}
    (hw : WINDOW (paperDesignP 13216) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13216 - 1))).real
      {v | sgA (paperDesignP 13216) c a v < √(2 / (13216 : ℝ) * mixtureFloor)}
      ∂muI 13216 ≤ lowMassBudget) :
    LatMom (paperDesignP 13216) c (√(2 / (13216 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13216

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13216
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

theorem location_budget_cap {c : Ret 13216} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13216 : ℝ) * (13216 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13216 : ℝ) * (13216 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13216 : ℝ) /
      ((13216 : ℝ) * (13216 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13216 : ℝ) * (13216 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13216 ≤ (2 * (16 / 5) / 13216 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13216} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (49818669 / 100000000000) ∧
    locationMomentBudget c 6 ≤ (305950443 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (104944997 / 125000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4747147523 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (1457678333 / 250000000000000) ∧
    residualMomentBudget 12 ≤ (4000021619 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13216} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15270993 / 500000000000000) ∧ residualVarianceBudget ≤ (2773183 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13216 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4747147523 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13216

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13216
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13216 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13216) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13216) : ℝ :=
  exp (hqKappa * (13216 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((1152311 / 200000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (1440389 / 250000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13216} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (104944997 / 31250000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4000021619 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4000021619 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4000021619 / 125000000000000) : ℝ) / ((1152311 / 200000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22339737 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 13216} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (807275513 / 500000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((104944997 / 31250000000))) / ((1152311 / 200000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13216} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13216 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13216 * ((22339737 / 1000000000) : ℝ) ^ 2 / 2 + ((807275513 / 500000000)) ^ 2 * (1 + (22339737 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13216 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13216 * ((22339737 / 1000000000)) ^ 2 / 2 + ((807275513 / 500000000)) ^ 2 * (1 + (22339737 / 1000000000))) := by
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
  have hd : (2 * ((1152311 / 200000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (43632069 / 125000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (15230054259 / 125000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13216

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13217
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13217 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13217) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13217 : ℝ) * (13217 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13217) /
    ((13217 : ℝ) * (13217 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13217} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13217}
    (hw : WINDOW (paperDesignP 13217) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13217) c a v - lbar (paperDesignP 13217) c a| ^ (2 * q)
      ∂stdGauss (Fin (13217 - 1)) ∂muI 13217 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13217)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13217}
    (hw : WINDOW (paperDesignP 13217) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13217) c a v - gbar (paperDesignP 13217) c a| ^ (2 * q)
      ∂stdGauss (Fin (13217 - 1)) ∂muI 13217 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13217)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13217) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13217}
    (hw : WINDOW (paperDesignP 13217) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13217 - 1))).real
      {v | sgA (paperDesignP 13217) c a v < √(2 / (13217 : ℝ) * mixtureFloor)}
      ∂muI 13217 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13217 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13217 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13217) c
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

end BstLean.Part266.Row13217

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13217
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13217 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13217)
    (p : Ix 13217 × (Fin (13217 - 1) → ℝ)) :
    sgA (paperDesignP 13217) c p.1 p.2 ^ 2 ≤
      (2 / (13217 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13217).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13217) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13217 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13217 : ℝ) * _ ≤ 2 / 13217 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13217)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13217}
    (hw : WINDOW (paperDesignP 13217) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13217) c a v ^ 8
      ∂stdGauss (Fin (13217 - 1)) ∂muI 13217 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13217).prod (stdGauss (Fin (13217 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13217) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13217) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13217 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13217) c p.1 p.2)
      (√(2 / (13217 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13217)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13217 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13217) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13217}
    (hw : WINDOW (paperDesignP 13217) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13217) c a v -
      ∫ w, sA (paperDesignP 13217) c a w ∂stdGauss (Fin (13217 - 1))) ^ 2
      ∂stdGauss (Fin (13217 - 1))) ^ 2 ∂muI 13217 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13217) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13217

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13217
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13217}
    (hw : WINDOW (paperDesignP 13217) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13217).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13217) c M H xi)
    (hE : centreEnergy (paperDesignP 13217) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13217 : ℝ))))
    (hprice : massBound 13217 M H xi E u mixtureFloor ≤ 13217 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13217 - 1))).real
      {v | sgA (paperDesignP 13217) c a v < √(2 / (13217 : ℝ) * mixtureFloor)}
        ∂muI 13217 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13217).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13217) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13217) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13217)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13217

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13217
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13217) : ℝ :=
  (latitudeC / eR c) / ((13217 : ℝ) * (13217 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13217) / ((13217 : ℝ) * (13217 - 3))

theorem location_variance_on_event {c : Ret 13217}
    (hw : WINDOW (paperDesignP 13217) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13217) c a v - lbar (paperDesignP 13217) c a) ^ 2
      ∂stdGauss (Fin (13217 - 1))) ^ 2 ∂muI 13217 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13217)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13217}
    (hw : WINDOW (paperDesignP 13217) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13217) c a v - gbar (paperDesignP 13217) c a) ^ 2
      ∂stdGauss (Fin (13217 - 1))) ^ 2 ∂muI 13217 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13217)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13217}
    (hw : WINDOW (paperDesignP 13217) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13217 - 1))).real
      {v | sgA (paperDesignP 13217) c a v < √(2 / (13217 : ℝ) * mixtureFloor)}
      ∂muI 13217 ≤ lowMassBudget) :
    LatMom (paperDesignP 13217) c (√(2 / (13217 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13217

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13217
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

theorem location_budget_cap {c : Ret 13217} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13217 : ℝ) * (13217 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13217 : ℝ) * (13217 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13217 : ℝ) /
      ((13217 : ℝ) * (13217 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13217 : ℝ) * (13217 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13217 ≤ (2 * (16 / 5) / 13217 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13217} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (62268623 / 125000000000) ∧
    locationMomentBudget c 6 ≤ (611854567 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (167899279 / 200000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (296663041 / 62500000000000) ∧
    residualMomentBudget 6 ≤ (2915025699 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (1599826951 / 200000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13217} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (7634341 / 250000000000000) ∧ residualVarianceBudget ≤ (1386277 / 500000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13217 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((296663041 / 62500000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13217

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13217
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13217 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13217) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13217) : ℝ :=
  exp (hqKappa * (13217 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5761337 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2880669 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13217} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (167899279 / 50000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (1599826951 / 50000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (1599826951 / 50000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((1599826951 / 50000000000000) : ℝ) / ((5761337 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (5584509 / 250000000) := by
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

theorem hq_location_bounds {c : Ret 13217} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1614489841 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((167899279 / 50000000000))) / ((5761337 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13217} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13217 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13217 * ((5584509 / 250000000) : ℝ) ^ 2 / 2 + ((1614489841 / 1000000000)) ^ 2 * (1 + (5584509 / 250000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13217 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13217 * ((5584509 / 250000000)) ^ 2 / 2 + ((1614489841 / 1000000000)) ^ 2 * (1 + (5584509 / 250000000))) := by
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
  have hd : (2 * ((5761337 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (174534807 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (6092477641 / 50000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13217

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13218
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13218 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13218) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13218 : ℝ) * (13218 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13218) /
    ((13218 : ℝ) * (13218 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13218} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13218}
    (hw : WINDOW (paperDesignP 13218) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13218) c a v - lbar (paperDesignP 13218) c a| ^ (2 * q)
      ∂stdGauss (Fin (13218 - 1)) ∂muI 13218 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13218)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13218}
    (hw : WINDOW (paperDesignP 13218) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13218) c a v - gbar (paperDesignP 13218) c a| ^ (2 * q)
      ∂stdGauss (Fin (13218 - 1)) ∂muI 13218 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13218)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13218) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13218}
    (hw : WINDOW (paperDesignP 13218) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13218 - 1))).real
      {v | sgA (paperDesignP 13218) c a v < √(2 / (13218 : ℝ) * mixtureFloor)}
      ∂muI 13218 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13218 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13218 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13218) c
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

end BstLean.Part266.Row13218

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13218
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13218 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13218)
    (p : Ix 13218 × (Fin (13218 - 1) → ℝ)) :
    sgA (paperDesignP 13218) c p.1 p.2 ^ 2 ≤
      (2 / (13218 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13218).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13218) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13218 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13218 : ℝ) * _ ≤ 2 / 13218 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13218)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13218}
    (hw : WINDOW (paperDesignP 13218) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13218) c a v ^ 8
      ∂stdGauss (Fin (13218 - 1)) ∂muI 13218 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13218).prod (stdGauss (Fin (13218 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13218) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13218) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13218 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13218) c p.1 p.2)
      (√(2 / (13218 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13218)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13218 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13218) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13218}
    (hw : WINDOW (paperDesignP 13218) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13218) c a v -
      ∫ w, sA (paperDesignP 13218) c a w ∂stdGauss (Fin (13218 - 1))) ^ 2
      ∂stdGauss (Fin (13218 - 1))) ^ 2 ∂muI 13218 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13218) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13218

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13218
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13218}
    (hw : WINDOW (paperDesignP 13218) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13218).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13218) c M H xi)
    (hE : centreEnergy (paperDesignP 13218) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13218 : ℝ))))
    (hprice : massBound 13218 M H xi E u mixtureFloor ≤ 13218 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13218 - 1))).real
      {v | sgA (paperDesignP 13218) c a v < √(2 / (13218 : ℝ) * mixtureFloor)}
        ∂muI 13218 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13218).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13218) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13218) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13218)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13218

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13218
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13218) : ℝ :=
  (latitudeC / eR c) / ((13218 : ℝ) * (13218 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13218) / ((13218 : ℝ) * (13218 - 3))

theorem location_variance_on_event {c : Ret 13218}
    (hw : WINDOW (paperDesignP 13218) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13218) c a v - lbar (paperDesignP 13218) c a) ^ 2
      ∂stdGauss (Fin (13218 - 1))) ^ 2 ∂muI 13218 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13218)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13218}
    (hw : WINDOW (paperDesignP 13218) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13218) c a v - gbar (paperDesignP 13218) c a) ^ 2
      ∂stdGauss (Fin (13218 - 1))) ^ 2 ∂muI 13218 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13218)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13218}
    (hw : WINDOW (paperDesignP 13218) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13218 - 1))).real
      {v | sgA (paperDesignP 13218) c a v < √(2 / (13218 : ℝ) * mixtureFloor)}
      ∂muI 13218 ≤ lowMassBudget) :
    LatMom (paperDesignP 13218) c (√(2 / (13218 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13218

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13218
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

theorem location_budget_cap {c : Ret 13218} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13218 : ℝ) * (13218 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13218 : ℝ) * (13218 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13218 : ℝ) /
      ((13218 : ℝ) * (13218 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13218 : ℝ) * (13218 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13218 ≤ (2 * (16 / 5) / 13218 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13218} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (124527821 / 250000000000) ∧
    locationMomentBudget c 6 ≤ (305904127 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (839432823 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4746069891 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (582938959 / 100000000000000) ∧
    residualMomentBudget 12 ≤ (1999556611 / 250000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13218} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30532743 / 1000000000000000) ∧ residualVarianceBudget ≤ (692981 / 250000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13218 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4746069891 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13218

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13218
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13218 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13218) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13218) : ℝ :=
  exp (hqKappa * (13218 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5761119 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (36007 / 6250000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13218} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (839432823 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (1999556611 / 62500000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (1999556611 / 62500000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((1999556611 / 62500000000000) : ℝ) / ((5761119 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (4467267 / 200000000) := by
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

theorem hq_location_bounds {c : Ret 13218} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1614428669 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((839432823 / 250000000000))) / ((5761119 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13218} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13218 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13218 * ((4467267 / 200000000) : ℝ) ^ 2 / 2 + ((1614428669 / 1000000000)) ^ 2 * (1 + (4467267 / 200000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13218 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13218 * ((4467267 / 200000000)) ^ 2 / 2 + ((1614428669 / 1000000000)) ^ 2 * (1 + (4467267 / 200000000))) := by
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
  have hd : (2 * ((5761119 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (349082677 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (6092933631 / 50000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13218

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13219
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13219 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13219) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13219 : ℝ) * (13219 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13219) /
    ((13219 : ℝ) * (13219 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13219} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13219}
    (hw : WINDOW (paperDesignP 13219) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13219) c a v - lbar (paperDesignP 13219) c a| ^ (2 * q)
      ∂stdGauss (Fin (13219 - 1)) ∂muI 13219 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13219)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13219}
    (hw : WINDOW (paperDesignP 13219) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13219) c a v - gbar (paperDesignP 13219) c a| ^ (2 * q)
      ∂stdGauss (Fin (13219 - 1)) ∂muI 13219 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13219)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13219) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13219}
    (hw : WINDOW (paperDesignP 13219) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13219 - 1))).real
      {v | sgA (paperDesignP 13219) c a v < √(2 / (13219 : ℝ) * mixtureFloor)}
      ∂muI 13219 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13219 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13219 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13219) c
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

end BstLean.Part266.Row13219

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13219
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13219 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13219)
    (p : Ix 13219 × (Fin (13219 - 1) → ℝ)) :
    sgA (paperDesignP 13219) c p.1 p.2 ^ 2 ≤
      (2 / (13219 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13219).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13219) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13219 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13219 : ℝ) * _ ≤ 2 / 13219 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13219)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13219}
    (hw : WINDOW (paperDesignP 13219) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13219) c a v ^ 8
      ∂stdGauss (Fin (13219 - 1)) ∂muI 13219 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13219).prod (stdGauss (Fin (13219 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13219) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13219) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13219 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13219) c p.1 p.2)
      (√(2 / (13219 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13219)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13219 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13219) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13219}
    (hw : WINDOW (paperDesignP 13219) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13219) c a v -
      ∫ w, sA (paperDesignP 13219) c a w ∂stdGauss (Fin (13219 - 1))) ^ 2
      ∂stdGauss (Fin (13219 - 1))) ^ 2 ∂muI 13219 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13219) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13219

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13219
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13219}
    (hw : WINDOW (paperDesignP 13219) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13219).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13219) c M H xi)
    (hE : centreEnergy (paperDesignP 13219) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13219 : ℝ))))
    (hprice : massBound 13219 M H xi E u mixtureFloor ≤ 13219 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13219 - 1))).real
      {v | sgA (paperDesignP 13219) c a v < √(2 / (13219 : ℝ) * mixtureFloor)}
        ∂muI 13219 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13219).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13219) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13219) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13219)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13219

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13219
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13219) : ℝ :=
  (latitudeC / eR c) / ((13219 : ℝ) * (13219 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13219) / ((13219 : ℝ) * (13219 - 3))

theorem location_variance_on_event {c : Ret 13219}
    (hw : WINDOW (paperDesignP 13219) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13219) c a v - lbar (paperDesignP 13219) c a) ^ 2
      ∂stdGauss (Fin (13219 - 1))) ^ 2 ∂muI 13219 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13219)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13219}
    (hw : WINDOW (paperDesignP 13219) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13219) c a v - gbar (paperDesignP 13219) c a) ^ 2
      ∂stdGauss (Fin (13219 - 1))) ^ 2 ∂muI 13219 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13219)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13219}
    (hw : WINDOW (paperDesignP 13219) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13219 - 1))).real
      {v | sgA (paperDesignP 13219) c a v < √(2 / (13219 : ℝ) * mixtureFloor)}
      ∂muI 13219 ≤ lowMassBudget) :
    LatMom (paperDesignP 13219) c (√(2 / (13219 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13219

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13219
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

theorem location_budget_cap {c : Ret 13219} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13219 : ℝ) * (13219 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13219 : ℝ) * (13219 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13219 : ℝ) /
      ((13219 : ℝ) * (13219 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13219 : ℝ) * (13219 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13219 ≤ (2 * (16 / 5) / 13219 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13219} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (49807359 / 100000000000) ∧
    locationMomentBudget c 6 ≤ (611761949 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (839369261 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (1186382807 / 250000000000000) ∧
    residualMomentBudget 6 ≤ (5828727907 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (1599463661 / 200000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13219} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (30528123 / 1000000000000000) ∧ residualVarianceBudget ≤ (554259 / 200000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13219 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((1186382807 / 250000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13219

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13219
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13219 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13219) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13219) : ℝ :=
  exp (hqKappa * (13219 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5760901 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2880451 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13219} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (839369261 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (1599463661 / 50000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (1599463661 / 50000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((1599463661 / 50000000000000) : ℝ) / ((5760901 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (4466927 / 200000000) := by
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

theorem hq_location_bounds {c : Ret 13219} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (201795939 / 125000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((839369261 / 250000000000))) / ((5760901 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13219} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13219 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13219 * ((4466927 / 200000000) : ℝ) ^ 2 / 2 + ((201795939 / 125000000)) ^ 2 * (1 + (4466927 / 200000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13219 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13219 * ((4466927 / 200000000)) ^ 2 / 2 + ((201795939 / 125000000)) ^ 2 * (1 + (4466927 / 200000000))) := by
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
  have hd : (2 * ((5760901 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (17454787 / 50000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121867793473 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13219

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13220
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13220 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13220) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13220 : ℝ) * (13220 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13220) /
    ((13220 : ℝ) * (13220 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13220} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13220}
    (hw : WINDOW (paperDesignP 13220) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13220) c a v - lbar (paperDesignP 13220) c a| ^ (2 * q)
      ∂stdGauss (Fin (13220 - 1)) ∂muI 13220 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13220)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13220}
    (hw : WINDOW (paperDesignP 13220) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13220) c a v - gbar (paperDesignP 13220) c a| ^ (2 * q)
      ∂stdGauss (Fin (13220 - 1)) ∂muI 13220 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13220)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13220) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13220}
    (hw : WINDOW (paperDesignP 13220) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13220 - 1))).real
      {v | sgA (paperDesignP 13220) c a v < √(2 / (13220 : ℝ) * mixtureFloor)}
      ∂muI 13220 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13220 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13220 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13220) c
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

end BstLean.Part266.Row13220

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13220
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13220 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13220)
    (p : Ix 13220 × (Fin (13220 - 1) → ℝ)) :
    sgA (paperDesignP 13220) c p.1 p.2 ^ 2 ≤
      (2 / (13220 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13220).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13220) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13220 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13220 : ℝ) * _ ≤ 2 / 13220 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13220)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13220}
    (hw : WINDOW (paperDesignP 13220) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13220) c a v ^ 8
      ∂stdGauss (Fin (13220 - 1)) ∂muI 13220 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13220).prod (stdGauss (Fin (13220 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13220) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13220) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13220 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13220) c p.1 p.2)
      (√(2 / (13220 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13220)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13220 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13220) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13220}
    (hw : WINDOW (paperDesignP 13220) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13220) c a v -
      ∫ w, sA (paperDesignP 13220) c a w ∂stdGauss (Fin (13220 - 1))) ^ 2
      ∂stdGauss (Fin (13220 - 1))) ^ 2 ∂muI 13220 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13220) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13220

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13220
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13220}
    (hw : WINDOW (paperDesignP 13220) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13220).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13220) c M H xi)
    (hE : centreEnergy (paperDesignP 13220) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13220 : ℝ))))
    (hprice : massBound 13220 M H xi E u mixtureFloor ≤ 13220 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13220 - 1))).real
      {v | sgA (paperDesignP 13220) c a v < √(2 / (13220 : ℝ) * mixtureFloor)}
        ∂muI 13220 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13220).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13220) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13220) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13220)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13220

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13220
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13220) : ℝ :=
  (latitudeC / eR c) / ((13220 : ℝ) * (13220 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13220) / ((13220 : ℝ) * (13220 - 3))

theorem location_variance_on_event {c : Ret 13220}
    (hw : WINDOW (paperDesignP 13220) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13220) c a v - lbar (paperDesignP 13220) c a) ^ 2
      ∂stdGauss (Fin (13220 - 1))) ^ 2 ∂muI 13220 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13220)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13220}
    (hw : WINDOW (paperDesignP 13220) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13220) c a v - gbar (paperDesignP 13220) c a) ^ 2
      ∂stdGauss (Fin (13220 - 1))) ^ 2 ∂muI 13220 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13220)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13220}
    (hw : WINDOW (paperDesignP 13220) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13220 - 1))).real
      {v | sgA (paperDesignP 13220) c a v < √(2 / (13220 : ℝ) * mixtureFloor)}
      ∂muI 13220 ≤ lowMassBudget) :
    LatMom (paperDesignP 13220) c (√(2 / (13220 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13220

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13220
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

theorem location_budget_cap {c : Ret 13220} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13220 : ℝ) * (13220 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13220 : ℝ) * (13220 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13220 : ℝ) /
      ((13220 : ℝ) * (13220 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13220 : ℝ) * (13220 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13220 ≤ (2 * (16 / 5) / 13220 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13220} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (249017951 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (611715651 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (209826427 / 250000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (4744992667 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (5828066349 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (3998205169 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13220} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (1907719 / 62500000000000) ∧ residualVarianceBudget ≤ (1385333 / 500000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13220 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((4744992667 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13220

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13220
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13220 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13220) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13220) : ℝ :=
  exp (hqKappa * (13220 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5760683 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (1440171 / 250000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13220} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (209826427 / 62500000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (3998205169 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (3998205169 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((3998205169 / 125000000000000) : ℝ) / ((5760683 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (4466587 / 200000000) := by
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

theorem hq_location_bounds {c : Ret 13220} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1614306367 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((209826427 / 62500000000))) / ((5760683 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13220} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13220 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13220 * ((4466587 / 200000000) : ℝ) ^ 2 / 2 + ((1614306367 / 1000000000)) ^ 2 * (1 + (4466587 / 200000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13220 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13220 * ((4466587 / 200000000)) ^ 2 / 2 + ((1614306367 / 1000000000)) ^ 2 * (1 + (4466587 / 200000000))) := by
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
  have hd : (2 * ((5760683 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (69821761 / 200000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (121876915379 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13220

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13221
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13221 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13221) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13221 : ℝ) * (13221 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13221) /
    ((13221 : ℝ) * (13221 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13221} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13221}
    (hw : WINDOW (paperDesignP 13221) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13221) c a v - lbar (paperDesignP 13221) c a| ^ (2 * q)
      ∂stdGauss (Fin (13221 - 1)) ∂muI 13221 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13221)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13221}
    (hw : WINDOW (paperDesignP 13221) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13221) c a v - gbar (paperDesignP 13221) c a| ^ (2 * q)
      ∂stdGauss (Fin (13221 - 1)) ∂muI 13221 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13221)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13221) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13221}
    (hw : WINDOW (paperDesignP 13221) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13221 - 1))).real
      {v | sgA (paperDesignP 13221) c a v < √(2 / (13221 : ℝ) * mixtureFloor)}
      ∂muI 13221 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13221 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13221 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13221) c
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

end BstLean.Part266.Row13221

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13221
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13221 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13221)
    (p : Ix 13221 × (Fin (13221 - 1) → ℝ)) :
    sgA (paperDesignP 13221) c p.1 p.2 ^ 2 ≤
      (2 / (13221 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13221).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13221) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13221 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13221 : ℝ) * _ ≤ 2 / 13221 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13221)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13221}
    (hw : WINDOW (paperDesignP 13221) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13221) c a v ^ 8
      ∂stdGauss (Fin (13221 - 1)) ∂muI 13221 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13221).prod (stdGauss (Fin (13221 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13221) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13221) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13221 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13221) c p.1 p.2)
      (√(2 / (13221 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13221)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13221 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13221) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13221}
    (hw : WINDOW (paperDesignP 13221) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13221) c a v -
      ∫ w, sA (paperDesignP 13221) c a w ∂stdGauss (Fin (13221 - 1))) ^ 2
      ∂stdGauss (Fin (13221 - 1))) ^ 2 ∂muI 13221 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13221) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13221

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13221
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13221}
    (hw : WINDOW (paperDesignP 13221) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13221).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13221) c M H xi)
    (hE : centreEnergy (paperDesignP 13221) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13221 : ℝ))))
    (hprice : massBound 13221 M H xi E u mixtureFloor ≤ 13221 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13221 - 1))).real
      {v | sgA (paperDesignP 13221) c a v < √(2 / (13221 : ℝ) * mixtureFloor)}
        ∂muI 13221 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13221).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13221) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13221) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13221)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13221

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13221
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13221) : ℝ :=
  (latitudeC / eR c) / ((13221 : ℝ) * (13221 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13221) / ((13221 : ℝ) * (13221 - 3))

theorem location_variance_on_event {c : Ret 13221}
    (hw : WINDOW (paperDesignP 13221) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13221) c a v - lbar (paperDesignP 13221) c a) ^ 2
      ∂stdGauss (Fin (13221 - 1))) ^ 2 ∂muI 13221 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13221)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13221}
    (hw : WINDOW (paperDesignP 13221) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13221) c a v - gbar (paperDesignP 13221) c a) ^ 2
      ∂stdGauss (Fin (13221 - 1))) ^ 2 ∂muI 13221 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13221)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13221}
    (hw : WINDOW (paperDesignP 13221) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13221 - 1))).real
      {v | sgA (paperDesignP 13221) c a v < √(2 / (13221 : ℝ) * mixtureFloor)}
      ∂muI 13221 ≤ lowMassBudget) :
    LatMom (paperDesignP 13221) c (√(2 / (13221 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13221

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13221
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

theorem location_budget_cap {c : Ret 13221} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13221 : ℝ) * (13221 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13221 : ℝ) * (13221 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13221 : ℝ) /
      ((13221 : ℝ) * (13221 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13221 : ℝ) * (13221 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13221 ≤ (2 * (16 / 5) / 13221 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13221} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (497998219 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (7645867 / 12500000000) ∧
    locationMomentBudget c 12 ≤ (167848433 / 200000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (74132097 / 15625000000000) ∧
    residualMomentBudget 6 ≤ (1456851229 / 250000000000000) ∧
    residualMomentBudget 12 ≤ (7995502543 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13221} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15259443 / 500000000000000) ∧ residualVarianceBudget ≤ (1385019 / 500000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13221 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((74132097 / 15625000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13221

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13221
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13221 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13221) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13221) : ℝ :=
  exp (hqKappa * (13221 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((1152093 / 200000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2880233 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13221} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (167848433 / 50000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (7995502543 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (7995502543 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((7995502543 / 250000000000000) : ℝ) / ((1152093 / 200000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (4466247 / 200000000) := by
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

theorem hq_location_bounds {c : Ret 13221} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1614245237 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((167848433 / 50000000000))) / ((1152093 / 200000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13221} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13221 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13221 * ((4466247 / 200000000) : ℝ) ^ 2 / 2 + ((1614245237 / 1000000000)) ^ 2 * (1 + (4466247 / 200000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13221 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13221 * ((4466247 / 200000000)) ^ 2 / 2 + ((1614245237 / 1000000000)) ^ 2 * (1 + (4466247 / 200000000))) := by
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
  have hd : (2 * ((1152093 / 200000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (349121871 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (60943019169 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13221

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13222
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13222 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13222) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13222 : ℝ) * (13222 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13222) /
    ((13222 : ℝ) * (13222 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13222} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13222}
    (hw : WINDOW (paperDesignP 13222) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13222) c a v - lbar (paperDesignP 13222) c a| ^ (2 * q)
      ∂stdGauss (Fin (13222 - 1)) ∂muI 13222 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13222)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13222}
    (hw : WINDOW (paperDesignP 13222) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13222) c a v - gbar (paperDesignP 13222) c a| ^ (2 * q)
      ∂stdGauss (Fin (13222 - 1)) ∂muI 13222 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13222)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13222) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13222}
    (hw : WINDOW (paperDesignP 13222) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13222 - 1))).real
      {v | sgA (paperDesignP 13222) c a v < √(2 / (13222 : ℝ) * mixtureFloor)}
      ∂muI 13222 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13222 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13222 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13222) c
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

end BstLean.Part266.Row13222

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13222
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13222 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13222)
    (p : Ix 13222 × (Fin (13222 - 1) → ℝ)) :
    sgA (paperDesignP 13222) c p.1 p.2 ^ 2 ≤
      (2 / (13222 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13222).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13222) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13222 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13222 : ℝ) * _ ≤ 2 / 13222 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13222)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13222}
    (hw : WINDOW (paperDesignP 13222) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13222) c a v ^ 8
      ∂stdGauss (Fin (13222 - 1)) ∂muI 13222 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13222).prod (stdGauss (Fin (13222 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13222) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13222) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13222 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13222) c p.1 p.2)
      (√(2 / (13222 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13222)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13222 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13222) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13222}
    (hw : WINDOW (paperDesignP 13222) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13222) c a v -
      ∫ w, sA (paperDesignP 13222) c a w ∂stdGauss (Fin (13222 - 1))) ^ 2
      ∂stdGauss (Fin (13222 - 1))) ^ 2 ∂muI 13222 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13222) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13222

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13222
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13222}
    (hw : WINDOW (paperDesignP 13222) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13222).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13222) c M H xi)
    (hE : centreEnergy (paperDesignP 13222) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13222 : ℝ))))
    (hprice : massBound 13222 M H xi E u mixtureFloor ≤ 13222 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13222 - 1))).real
      {v | sgA (paperDesignP 13222) c a v < √(2 / (13222 : ℝ) * mixtureFloor)}
        ∂muI 13222 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13222).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13222) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13222) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13222)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13222

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13222
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13222) : ℝ :=
  (latitudeC / eR c) / ((13222 : ℝ) * (13222 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13222) / ((13222 : ℝ) * (13222 - 3))

theorem location_variance_on_event {c : Ret 13222}
    (hw : WINDOW (paperDesignP 13222) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13222) c a v - lbar (paperDesignP 13222) c a) ^ 2
      ∂stdGauss (Fin (13222 - 1))) ^ 2 ∂muI 13222 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13222)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13222}
    (hw : WINDOW (paperDesignP 13222) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13222) c a v - gbar (paperDesignP 13222) c a) ^ 2
      ∂stdGauss (Fin (13222 - 1))) ^ 2 ∂muI 13222 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13222)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13222}
    (hw : WINDOW (paperDesignP 13222) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13222 - 1))).real
      {v | sgA (paperDesignP 13222) c a v < √(2 / (13222 : ℝ) * mixtureFloor)}
      ∂muI 13222 ≤ lowMassBudget) :
    LatMom (paperDesignP 13222) c (√(2 / (13222 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13222

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13222
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

theorem location_budget_cap {c : Ret 13222} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13222 : ℝ) * (13222 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13222 : ℝ) * (13222 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13222 : ℝ) /
      ((13222 : ℝ) * (13222 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13222 : ℝ) * (13222 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13222 ≤ (2 * (16 / 5) / 13222 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13222} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (497960541 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (24464923 / 40000000000) ∧
    locationMomentBudget c 12 ≤ (104897329 / 125000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (94878317 / 20000000000000) ∧
    residualMomentBudget 6 ≤ (5826743609 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (7994594919 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13222} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (3051427 / 100000000000000) ∧ residualVarianceBudget ≤ (2769409 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13222 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((94878317 / 20000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13222

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13222
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13222 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13222) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13222) : ℝ :=
  exp (hqKappa * (13222 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5760247 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (720031 / 125000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13222} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (104897329 / 31250000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (7994594919 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (7994594919 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((7994594919 / 250000000000000) : ℝ) / ((5760247 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (348899 / 15625000) := by
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

theorem hq_location_bounds {c : Ret 13222} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (807092061 / 500000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((104897329 / 31250000000))) / ((5760247 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13222} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13222 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13222 * ((348899 / 15625000) : ℝ) ^ 2 / 2 + ((807092061 / 500000000)) ^ 2 * (1 + (348899 / 15625000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13222 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13222 * ((348899 / 15625000)) ^ 2 / 2 + ((807092061 / 500000000)) ^ 2 * (1 + (348899 / 15625000))) := by
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
  have hd : (2 * ((5760247 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (174567469 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (2437903247 / 20000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13222

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row13223
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 13223 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 13223) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((13223 : ℝ) * (13223 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 13223) /
    ((13223 : ℝ) * (13223 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 13223} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 13223}
    (hw : WINDOW (paperDesignP 13223) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 13223) c a v - lbar (paperDesignP 13223) c a| ^ (2 * q)
      ∂stdGauss (Fin (13223 - 1)) ∂muI 13223 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 13223)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 13223}
    (hw : WINDOW (paperDesignP 13223) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 13223) c a v - gbar (paperDesignP 13223) c a| ^ (2 * q)
      ∂stdGauss (Fin (13223 - 1)) ∂muI 13223 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 13223)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 13223) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 13223}
    (hw : WINDOW (paperDesignP 13223) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13223 - 1))).real
      {v | sgA (paperDesignP 13223) c a v < √(2 / (13223 : ℝ) * mixtureFloor)}
      ∂muI 13223 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (13223 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 13223 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 13223) c
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

end BstLean.Part266.Row13223

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row13223
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (13223 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 13223)
    (p : Ix 13223 × (Fin (13223 - 1) → ℝ)) :
    sgA (paperDesignP 13223) c p.1 p.2 ^ 2 ≤
      (2 / (13223 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 13223).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 13223) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 13223 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 13223 : ℝ) * _ ≤ 2 / 13223 *
    (normSq (hid2 (A1 c) (A2 c) _) / 13223)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 13223}
    (hw : WINDOW (paperDesignP 13223) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 13223) c a v ^ 8
      ∂stdGauss (Fin (13223 - 1)) ∂muI 13223 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 13223).prod (stdGauss (Fin (13223 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 13223) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 13223) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (13223 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 13223) c p.1 p.2)
      (√(2 / (13223 : ℝ)) * (1 + BstLean.Part222.energyAllowance 13223)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (13223 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 13223) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 13223}
    (hw : WINDOW (paperDesignP 13223) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 13223) c a v -
      ∫ w, sA (paperDesignP 13223) c a w ∂stdGauss (Fin (13223 - 1))) ^ 2
      ∂stdGauss (Fin (13223 - 1))) ^ 2 ∂muI 13223 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 13223) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row13223

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row13223
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 13223}
    (hw : WINDOW (paperDesignP 13223) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 13223).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 13223) c M H xi)
    (hE : centreEnergy (paperDesignP 13223) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (13223 : ℝ))))
    (hprice : massBound 13223 M H xi E u mixtureFloor ≤ 13223 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (13223 - 1))).real
      {v | sgA (paperDesignP 13223) c a v < √(2 / (13223 : ℝ) * mixtureFloor)}
        ∂muI 13223 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 13223).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 13223) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 13223) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 13223)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row13223

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row13223
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 13223) : ℝ :=
  (latitudeC / eR c) / ((13223 : ℝ) * (13223 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 13223) / ((13223 : ℝ) * (13223 - 3))

theorem location_variance_on_event {c : Ret 13223}
    (hw : WINDOW (paperDesignP 13223) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 13223) c a v - lbar (paperDesignP 13223) c a) ^ 2
      ∂stdGauss (Fin (13223 - 1))) ^ 2 ∂muI 13223 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 13223)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 13223}
    (hw : WINDOW (paperDesignP 13223) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 13223) c a v - gbar (paperDesignP 13223) c a) ^ 2
      ∂stdGauss (Fin (13223 - 1))) ^ 2 ∂muI 13223 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 13223)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 13223}
    (hw : WINDOW (paperDesignP 13223) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (13223 - 1))).real
      {v | sgA (paperDesignP 13223) c a v < √(2 / (13223 : ℝ) * mixtureFloor)}
      ∂muI 13223 ≤ lowMassBudget) :
    LatMom (paperDesignP 13223) c (√(2 / (13223 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row13223

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row13223
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

theorem location_budget_cap {c : Ret 13223} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((13223 : ℝ) * (13223 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13223 : ℝ) * (13223 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 13223 : ℝ) /
      ((13223 : ℝ) * (13223 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (13223 : ℝ) * (13223 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 13223 ≤ (2 * (16 / 5) / 13223 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 13223} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (49792287 / 100000000000) ∧
    locationMomentBudget c 6 ≤ (305788399 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (209778777 / 250000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (948675519 / 200000000000000) ∧
    residualMomentBudget 6 ≤ (2913041213 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (7993687467 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 13223} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (15254827 / 500000000000000) ∧ residualVarianceBudget ≤ (2768781 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (13223 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((948675519 / 200000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row13223

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row13223
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (13223 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 13223) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 13223) : ℝ :=
  exp (hqKappa * (13223 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((576003 / 100000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5760031 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 13223} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (209778777 / 62500000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (7993687467 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (7993687467 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((7993687467 / 250000000000000) : ℝ) / ((576003 / 100000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (22327833 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 13223} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1614122739 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((209778777 / 62500000000))) / ((576003 / 100000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 13223} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 13223 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      13223 * ((22327833 / 1000000000) : ℝ) ^ 2 / 2 + ((1614122739 / 1000000000)) ^ 2 * (1 + (22327833 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (13223 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13223 * ((22327833 / 1000000000)) ^ 2 / 2 + ((1614122739 / 1000000000)) ^ 2 * (1 + (22327833 / 1000000000))) := by
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
  have hd : (2 * ((576003 / 100000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (69829589 / 200000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (60952122427 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row13223
