import BstLean.Part266Shard15Step2


/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12725
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12725 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12725) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12725 : ℝ) * (12725 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12725) /
    ((12725 : ℝ) * (12725 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12725} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12725}
    (hw : WINDOW (paperDesignP 12725) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12725) c a v - lbar (paperDesignP 12725) c a| ^ (2 * q)
      ∂stdGauss (Fin (12725 - 1)) ∂muI 12725 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12725)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12725}
    (hw : WINDOW (paperDesignP 12725) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12725) c a v - gbar (paperDesignP 12725) c a| ^ (2 * q)
      ∂stdGauss (Fin (12725 - 1)) ∂muI 12725 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12725)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12725) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12725}
    (hw : WINDOW (paperDesignP 12725) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12725 - 1))).real
      {v | sgA (paperDesignP 12725) c a v < √(2 / (12725 : ℝ) * mixtureFloor)}
      ∂muI 12725 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12725 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12725 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12725) c
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

end BstLean.Part266.Row12725

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12725
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12725 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12725)
    (p : Ix 12725 × (Fin (12725 - 1) → ℝ)) :
    sgA (paperDesignP 12725) c p.1 p.2 ^ 2 ≤
      (2 / (12725 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12725).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12725) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12725 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12725 : ℝ) * _ ≤ 2 / 12725 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12725)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12725}
    (hw : WINDOW (paperDesignP 12725) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12725) c a v ^ 8
      ∂stdGauss (Fin (12725 - 1)) ∂muI 12725 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12725).prod (stdGauss (Fin (12725 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12725) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12725) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12725 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12725) c p.1 p.2)
      (√(2 / (12725 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12725)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12725 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12725) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12725}
    (hw : WINDOW (paperDesignP 12725) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12725) c a v -
      ∫ w, sA (paperDesignP 12725) c a w ∂stdGauss (Fin (12725 - 1))) ^ 2
      ∂stdGauss (Fin (12725 - 1))) ^ 2 ∂muI 12725 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12725) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12725

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12725
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12725}
    (hw : WINDOW (paperDesignP 12725) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12725).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12725) c M H xi)
    (hE : centreEnergy (paperDesignP 12725) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12725 : ℝ))))
    (hprice : massBound 12725 M H xi E u mixtureFloor ≤ 12725 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12725 - 1))).real
      {v | sgA (paperDesignP 12725) c a v < √(2 / (12725 : ℝ) * mixtureFloor)}
        ∂muI 12725 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12725).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12725) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12725) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12725)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12725

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12725
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12725) : ℝ :=
  (latitudeC / eR c) / ((12725 : ℝ) * (12725 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12725) / ((12725 : ℝ) * (12725 - 3))

theorem location_variance_on_event {c : Ret 12725}
    (hw : WINDOW (paperDesignP 12725) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12725) c a v - lbar (paperDesignP 12725) c a) ^ 2
      ∂stdGauss (Fin (12725 - 1))) ^ 2 ∂muI 12725 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12725)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12725}
    (hw : WINDOW (paperDesignP 12725) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12725) c a v - gbar (paperDesignP 12725) c a) ^ 2
      ∂stdGauss (Fin (12725 - 1))) ^ 2 ∂muI 12725 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12725)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12725}
    (hw : WINDOW (paperDesignP 12725) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12725 - 1))).real
      {v | sgA (paperDesignP 12725) c a v < √(2 / (12725 : ℝ) * mixtureFloor)}
      ∂muI 12725 ≤ lowMassBudget) :
    LatMom (paperDesignP 12725) c (√(2 / (12725 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12725

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12725
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

theorem location_budget_cap {c : Ret 12725} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12725 : ℝ) * (12725 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12725 : ℝ) * (12725 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12725 : ℝ) /
      ((12725 : ℝ) * (12725 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12725 : ℝ) * (12725 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12725 ≤ (2 * (16 / 5) / 12725 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12725} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (8084629 / 15625000000) ∧
    locationMomentBudget c 6 ≤ (635523437 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (871986669 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (5024603499 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (6171536449 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (8467819127 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12725} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (329447 / 10000000000000) ∧ residualVarianceBudget ≤ (310677 / 100000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12725 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((5024603499 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12725

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12725
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12725 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12725) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12725) : ℝ :=
  exp (hqKappa * (12725 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5871659 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (293583 / 50000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12725} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (871986669 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8467819127 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8467819127 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8467819127 / 250000000000000) : ℝ) / ((5871659 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (5801881 / 250000000) := by
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

theorem hq_location_bounds {c : Ret 12725} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1645465497 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((871986669 / 250000000000))) / ((5871659 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12725} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12725 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12725 * ((5801881 / 250000000) : ℝ) ^ 2 / 2 + ((1645465497 / 1000000000)) ^ 2 * (1 + (5801881 / 250000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12725 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12725 * ((5801881 / 250000000)) ^ 2 / 2 + ((1645465497 / 1000000000)) ^ 2 * (1 + (5801881 / 250000000))) := by
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
  have hd : (2 * ((5871659 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (5352878 / 15625) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (23472777649 / 200000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12725

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12726
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12726 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12726) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12726 : ℝ) * (12726 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12726) /
    ((12726 : ℝ) * (12726 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12726} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12726}
    (hw : WINDOW (paperDesignP 12726) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12726) c a v - lbar (paperDesignP 12726) c a| ^ (2 * q)
      ∂stdGauss (Fin (12726 - 1)) ∂muI 12726 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12726)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12726}
    (hw : WINDOW (paperDesignP 12726) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12726) c a v - gbar (paperDesignP 12726) c a| ^ (2 * q)
      ∂stdGauss (Fin (12726 - 1)) ∂muI 12726 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12726)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12726) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12726}
    (hw : WINDOW (paperDesignP 12726) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12726 - 1))).real
      {v | sgA (paperDesignP 12726) c a v < √(2 / (12726 : ℝ) * mixtureFloor)}
      ∂muI 12726 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12726 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12726 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12726) c
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

end BstLean.Part266.Row12726

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12726
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12726 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12726)
    (p : Ix 12726 × (Fin (12726 - 1) → ℝ)) :
    sgA (paperDesignP 12726) c p.1 p.2 ^ 2 ≤
      (2 / (12726 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12726).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12726) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12726 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12726 : ℝ) * _ ≤ 2 / 12726 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12726)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12726}
    (hw : WINDOW (paperDesignP 12726) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12726) c a v ^ 8
      ∂stdGauss (Fin (12726 - 1)) ∂muI 12726 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12726).prod (stdGauss (Fin (12726 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12726) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12726) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12726 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12726) c p.1 p.2)
      (√(2 / (12726 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12726)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12726 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12726) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12726}
    (hw : WINDOW (paperDesignP 12726) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12726) c a v -
      ∫ w, sA (paperDesignP 12726) c a w ∂stdGauss (Fin (12726 - 1))) ^ 2
      ∂stdGauss (Fin (12726 - 1))) ^ 2 ∂muI 12726 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12726) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12726

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12726
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12726}
    (hw : WINDOW (paperDesignP 12726) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12726).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12726) c M H xi)
    (hE : centreEnergy (paperDesignP 12726) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12726 : ℝ))))
    (hprice : massBound 12726 M H xi E u mixtureFloor ≤ 12726 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12726 - 1))).real
      {v | sgA (paperDesignP 12726) c a v < √(2 / (12726 : ℝ) * mixtureFloor)}
        ∂muI 12726 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12726).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12726) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12726) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12726)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12726

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12726
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12726) : ℝ :=
  (latitudeC / eR c) / ((12726 : ℝ) * (12726 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12726) / ((12726 : ℝ) * (12726 - 3))

theorem location_variance_on_event {c : Ret 12726}
    (hw : WINDOW (paperDesignP 12726) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12726) c a v - lbar (paperDesignP 12726) c a) ^ 2
      ∂stdGauss (Fin (12726 - 1))) ^ 2 ∂muI 12726 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12726)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12726}
    (hw : WINDOW (paperDesignP 12726) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12726) c a v - gbar (paperDesignP 12726) c a) ^ 2
      ∂stdGauss (Fin (12726 - 1))) ^ 2 ∂muI 12726 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12726)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12726}
    (hw : WINDOW (paperDesignP 12726) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12726 - 1))).real
      {v | sgA (paperDesignP 12726) c a v < √(2 / (12726 : ℝ) * mixtureFloor)}
      ∂muI 12726 ≤ lowMassBudget) :
    LatMom (paperDesignP 12726) c (√(2 / (12726 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12726

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12726
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

theorem location_budget_cap {c : Ret 12726} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12726 : ℝ) * (12726 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12726 : ℝ) * (12726 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12726 : ℝ) /
      ((12726 : ℝ) * (12726 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12726 : ℝ) * (12726 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12726 ≤ (2 * (16 / 5) / 12726 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12726} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (16167987 / 31250000000) ∧
    locationMomentBudget c 6 ≤ (9929273 / 15625000000) ∧
    locationMomentBudget c 12 ≤ (435959041 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2512005563 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (6170808783 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (8466820399 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12726} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (16469761 / 500000000000000) ∧ residualVarianceBudget ≤ (3106037 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12726 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2512005563 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12726

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12726
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12726 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12726) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12726) : ℝ :=
  exp (hqKappa * (12726 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((1467857 / 250000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5871429 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12726} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (435959041 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8466820399 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8466820399 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8466820399 / 250000000000000) : ℝ) / ((1467857 / 250000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (2320569 / 100000000) := by
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

theorem hq_location_bounds {c : Ret 12726} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (411350201 / 250000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((435959041 / 125000000000))) / ((1467857 / 250000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12726} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12726 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12726 * ((2320569 / 100000000) : ℝ) ^ 2 / 2 + ((411350201 / 250000000)) ^ 2 * (1 + (2320569 / 100000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12726 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12726 * ((2320569 / 100000000)) ^ 2 / 2 + ((411350201 / 250000000)) ^ 2 * (1 + (2320569 / 100000000))) := by
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
  have hd : (2 * ((1467857 / 250000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (68519503 / 200000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (3667906797 / 31250) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12726

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12727
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12727 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12727) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12727 : ℝ) * (12727 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12727) /
    ((12727 : ℝ) * (12727 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12727} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12727}
    (hw : WINDOW (paperDesignP 12727) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12727) c a v - lbar (paperDesignP 12727) c a| ^ (2 * q)
      ∂stdGauss (Fin (12727 - 1)) ∂muI 12727 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12727)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12727}
    (hw : WINDOW (paperDesignP 12727) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12727) c a v - gbar (paperDesignP 12727) c a| ^ (2 * q)
      ∂stdGauss (Fin (12727 - 1)) ∂muI 12727 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12727)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12727) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12727}
    (hw : WINDOW (paperDesignP 12727) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12727 - 1))).real
      {v | sgA (paperDesignP 12727) c a v < √(2 / (12727 : ℝ) * mixtureFloor)}
      ∂muI 12727 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12727 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12727 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12727) c
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

end BstLean.Part266.Row12727

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12727
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12727 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12727)
    (p : Ix 12727 × (Fin (12727 - 1) → ℝ)) :
    sgA (paperDesignP 12727) c p.1 p.2 ^ 2 ≤
      (2 / (12727 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12727).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12727) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12727 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12727 : ℝ) * _ ≤ 2 / 12727 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12727)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12727}
    (hw : WINDOW (paperDesignP 12727) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12727) c a v ^ 8
      ∂stdGauss (Fin (12727 - 1)) ∂muI 12727 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12727).prod (stdGauss (Fin (12727 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12727) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12727) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12727 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12727) c p.1 p.2)
      (√(2 / (12727 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12727)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12727 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12727) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12727}
    (hw : WINDOW (paperDesignP 12727) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12727) c a v -
      ∫ w, sA (paperDesignP 12727) c a w ∂stdGauss (Fin (12727 - 1))) ^ 2
      ∂stdGauss (Fin (12727 - 1))) ^ 2 ∂muI 12727 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12727) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12727

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12727
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12727}
    (hw : WINDOW (paperDesignP 12727) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12727).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12727) c M H xi)
    (hE : centreEnergy (paperDesignP 12727) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12727 : ℝ))))
    (hprice : massBound 12727 M H xi E u mixtureFloor ≤ 12727 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12727 - 1))).real
      {v | sgA (paperDesignP 12727) c a v < √(2 / (12727 : ℝ) * mixtureFloor)}
        ∂muI 12727 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12727).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12727) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12727) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12727)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12727

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12727
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12727) : ℝ :=
  (latitudeC / eR c) / ((12727 : ℝ) * (12727 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12727) / ((12727 : ℝ) * (12727 - 3))

theorem location_variance_on_event {c : Ret 12727}
    (hw : WINDOW (paperDesignP 12727) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12727) c a v - lbar (paperDesignP 12727) c a) ^ 2
      ∂stdGauss (Fin (12727 - 1))) ^ 2 ∂muI 12727 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12727)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12727}
    (hw : WINDOW (paperDesignP 12727) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12727) c a v - gbar (paperDesignP 12727) c a) ^ 2
      ∂stdGauss (Fin (12727 - 1))) ^ 2 ∂muI 12727 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12727)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12727}
    (hw : WINDOW (paperDesignP 12727) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12727 - 1))).real
      {v | sgA (paperDesignP 12727) c a v < √(2 / (12727 : ℝ) * mixtureFloor)}
      ∂muI 12727 ≤ lowMassBudget) :
    LatMom (paperDesignP 12727) c (√(2 / (12727 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12727

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12727
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

theorem location_budget_cap {c : Ret 12727} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12727 : ℝ) * (12727 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12727 : ℝ) * (12727 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12727 : ℝ) /
      ((12727 : ℝ) * (12727 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12727 : ℝ) * (12727 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12727 ≤ (2 * (16 / 5) / 12727 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12727} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (517334917 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (158855879 / 250000000000) ∧
    locationMomentBudget c 12 ≤ (174369901 / 200000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (502341887 / 100000000000000) ∧
    residualMomentBudget 6 ≤ (308504063 / 50000000000000) ∧
    residualMomentBudget 12 ≤ (8465821867 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12727} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (6586869 / 200000000000000) ∧ residualVarianceBudget ≤ (621061 / 200000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12727 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((502341887 / 100000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12727

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12727
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12727 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12727) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12727) : ℝ :=
  exp (hqKappa * (12727 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((2935599 / 500000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5871199 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12727} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (174369901 / 50000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8465821867 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8465821867 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8465821867 / 250000000000000) : ℝ) / ((2935599 / 500000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (23203851 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 12727} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (411333961 / 250000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((174369901 / 50000000000))) / ((2935599 / 500000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12727} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12727 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12727 * ((23203851 / 1000000000) : ℝ) ^ 2 / 2 + ((411333961 / 250000000)) ^ 2 * (1 + (23203851 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12727 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12727 * ((23203851 / 1000000000)) ^ 2 / 2 + ((411333961 / 250000000)) ^ 2 * (1 + (23203851 / 1000000000))) := by
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
  have hd : (2 * ((2935599 / 500000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (171305391 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (23476421529 / 200000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12727

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12728
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12728 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12728) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12728 : ℝ) * (12728 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12728) /
    ((12728 : ℝ) * (12728 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12728} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12728}
    (hw : WINDOW (paperDesignP 12728) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12728) c a v - lbar (paperDesignP 12728) c a| ^ (2 * q)
      ∂stdGauss (Fin (12728 - 1)) ∂muI 12728 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12728)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12728}
    (hw : WINDOW (paperDesignP 12728) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12728) c a v - gbar (paperDesignP 12728) c a| ^ (2 * q)
      ∂stdGauss (Fin (12728 - 1)) ∂muI 12728 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12728)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12728) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12728}
    (hw : WINDOW (paperDesignP 12728) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12728 - 1))).real
      {v | sgA (paperDesignP 12728) c a v < √(2 / (12728 : ℝ) * mixtureFloor)}
      ∂muI 12728 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12728 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12728 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12728) c
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

end BstLean.Part266.Row12728

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12728
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12728 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12728)
    (p : Ix 12728 × (Fin (12728 - 1) → ℝ)) :
    sgA (paperDesignP 12728) c p.1 p.2 ^ 2 ≤
      (2 / (12728 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12728).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12728) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12728 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12728 : ℝ) * _ ≤ 2 / 12728 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12728)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12728}
    (hw : WINDOW (paperDesignP 12728) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12728) c a v ^ 8
      ∂stdGauss (Fin (12728 - 1)) ∂muI 12728 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12728).prod (stdGauss (Fin (12728 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12728) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12728) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12728 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12728) c p.1 p.2)
      (√(2 / (12728 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12728)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12728 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12728) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12728}
    (hw : WINDOW (paperDesignP 12728) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12728) c a v -
      ∫ w, sA (paperDesignP 12728) c a w ∂stdGauss (Fin (12728 - 1))) ^ 2
      ∂stdGauss (Fin (12728 - 1))) ^ 2 ∂muI 12728 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12728) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12728

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12728
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12728}
    (hw : WINDOW (paperDesignP 12728) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12728).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12728) c M H xi)
    (hE : centreEnergy (paperDesignP 12728) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12728 : ℝ))))
    (hprice : massBound 12728 M H xi E u mixtureFloor ≤ 12728 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12728 - 1))).real
      {v | sgA (paperDesignP 12728) c a v < √(2 / (12728 : ℝ) * mixtureFloor)}
        ∂muI 12728 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12728).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12728) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12728) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12728)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12728

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12728
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12728) : ℝ :=
  (latitudeC / eR c) / ((12728 : ℝ) * (12728 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12728) / ((12728 : ℝ) * (12728 - 3))

theorem location_variance_on_event {c : Ret 12728}
    (hw : WINDOW (paperDesignP 12728) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12728) c a v - lbar (paperDesignP 12728) c a) ^ 2
      ∂stdGauss (Fin (12728 - 1))) ^ 2 ∂muI 12728 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12728)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12728}
    (hw : WINDOW (paperDesignP 12728) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12728) c a v - gbar (paperDesignP 12728) c a) ^ 2
      ∂stdGauss (Fin (12728 - 1))) ^ 2 ∂muI 12728 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12728)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12728}
    (hw : WINDOW (paperDesignP 12728) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12728 - 1))).real
      {v | sgA (paperDesignP 12728) c a v < √(2 / (12728 : ℝ) * mixtureFloor)}
      ∂muI 12728 ≤ lowMassBudget) :
    LatMom (paperDesignP 12728) c (√(2 / (12728 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12728

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12728
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

theorem location_budget_cap {c : Ret 12728} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12728 : ℝ) * (12728 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12728 : ℝ) * (12728 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12728 : ℝ) /
      ((12728 : ℝ) * (12728 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12728 : ℝ) * (12728 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12728 ≤ (2 * (16 / 5) / 12728 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12728} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (258647129 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (635373567 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (871780939 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (502282673 / 100000000000000) ∧
    residualMomentBudget 6 ≤ (154233847 / 25000000000000) ∧
    residualMomentBudget 12 ≤ (2116205883 / 250000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12728} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (32929169 / 1000000000000000) ∧ residualVarianceBudget ≤ (3104573 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12728 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((502282673 / 100000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12728

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12728
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12728 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12728) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12728) : ℝ :=
  exp (hqKappa * (12728 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5870967 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (733871 / 125000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12728} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (871780939 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (2116205883 / 62500000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (2116205883 / 62500000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((2116205883 / 62500000000000) : ℝ) / ((5870967 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (23202017 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 12728} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1645271181 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((871780939 / 250000000000))) / ((5870967 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12728} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12728 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12728 * ((23202017 / 1000000000) : ℝ) ^ 2 / 2 + ((1645271181 / 1000000000)) ^ 2 * (1 + (23202017 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12728 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12728 * ((23202017 / 1000000000)) ^ 2 / 2 + ((1645271181 / 1000000000)) ^ 2 * (1 + (23202017 / 1000000000))) := by
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
  have hd : (2 * ((5870967 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (85656027 / 250000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (29347809773 / 250000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12728

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12729
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12729 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12729) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12729 : ℝ) * (12729 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12729) /
    ((12729 : ℝ) * (12729 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12729} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12729}
    (hw : WINDOW (paperDesignP 12729) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12729) c a v - lbar (paperDesignP 12729) c a| ^ (2 * q)
      ∂stdGauss (Fin (12729 - 1)) ∂muI 12729 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12729)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12729}
    (hw : WINDOW (paperDesignP 12729) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12729) c a v - gbar (paperDesignP 12729) c a| ^ (2 * q)
      ∂stdGauss (Fin (12729 - 1)) ∂muI 12729 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12729)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12729) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12729}
    (hw : WINDOW (paperDesignP 12729) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12729 - 1))).real
      {v | sgA (paperDesignP 12729) c a v < √(2 / (12729 : ℝ) * mixtureFloor)}
      ∂muI 12729 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12729 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12729 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12729) c
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

end BstLean.Part266.Row12729

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12729
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12729 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12729)
    (p : Ix 12729 × (Fin (12729 - 1) → ℝ)) :
    sgA (paperDesignP 12729) c p.1 p.2 ^ 2 ≤
      (2 / (12729 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12729).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12729) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12729 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12729 : ℝ) * _ ≤ 2 / 12729 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12729)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12729}
    (hw : WINDOW (paperDesignP 12729) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12729) c a v ^ 8
      ∂stdGauss (Fin (12729 - 1)) ∂muI 12729 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12729).prod (stdGauss (Fin (12729 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12729) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12729) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12729 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12729) c p.1 p.2)
      (√(2 / (12729 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12729)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12729 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12729) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12729}
    (hw : WINDOW (paperDesignP 12729) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12729) c a v -
      ∫ w, sA (paperDesignP 12729) c a w ∂stdGauss (Fin (12729 - 1))) ^ 2
      ∂stdGauss (Fin (12729 - 1))) ^ 2 ∂muI 12729 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12729) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12729

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12729
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12729}
    (hw : WINDOW (paperDesignP 12729) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12729).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12729) c M H xi)
    (hE : centreEnergy (paperDesignP 12729) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12729 : ℝ))))
    (hprice : massBound 12729 M H xi E u mixtureFloor ≤ 12729 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12729 - 1))).real
      {v | sgA (paperDesignP 12729) c a v < √(2 / (12729 : ℝ) * mixtureFloor)}
        ∂muI 12729 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12729).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12729) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12729) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12729)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12729

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12729
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12729) : ℝ :=
  (latitudeC / eR c) / ((12729 : ℝ) * (12729 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12729) / ((12729 : ℝ) * (12729 - 3))

theorem location_variance_on_event {c : Ret 12729}
    (hw : WINDOW (paperDesignP 12729) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12729) c a v - lbar (paperDesignP 12729) c a) ^ 2
      ∂stdGauss (Fin (12729 - 1))) ^ 2 ∂muI 12729 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12729)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12729}
    (hw : WINDOW (paperDesignP 12729) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12729) c a v - gbar (paperDesignP 12729) c a) ^ 2
      ∂stdGauss (Fin (12729 - 1))) ^ 2 ∂muI 12729 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12729)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12729}
    (hw : WINDOW (paperDesignP 12729) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12729 - 1))).real
      {v | sgA (paperDesignP 12729) c a v < √(2 / (12729 : ℝ) * mixtureFloor)}
      ∂muI 12729 ≤ lowMassBudget) :
    LatMom (paperDesignP 12729) c (√(2 / (12729 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12729

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12729
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

theorem location_budget_cap {c : Ret 12729} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12729 : ℝ) * (12729 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12729 : ℝ) * (12729 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12729 : ℝ) /
      ((12729 : ℝ) * (12729 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12729 : ℝ) * (12729 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12729 ≤ (2 * (16 / 5) / 12729 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12729} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (129313401 / 250000000000) ∧
    locationMomentBudget c 6 ≤ (317661813 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (6810253 / 7812500000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2511117353 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (6168626643 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (8463825393 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12729} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (6584799 / 200000000000000) ∧ residualVarianceBudget ≤ (1551921 / 500000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12729 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2511117353 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12729

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12729
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12729 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12729) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12729) : ℝ :=
  exp (hqKappa * (12729 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((366921 / 62500000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5870737 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12729} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (6810253 / 1953125000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8463825393 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8463825393 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8463825393 / 250000000000000) : ℝ) / ((366921 / 62500000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (2900023 / 125000000) := by
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

theorem hq_location_bounds {c : Ret 12729} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (411301633 / 250000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((6810253 / 1953125000))) / ((366921 / 62500000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12729} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12729 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12729 * ((2900023 / 125000000) : ℝ) ^ 2 / 2 + ((411301633 / 250000000)) ^ 2 * (1 + (2900023 / 125000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12729 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12729 * ((2900023 / 125000000)) ^ 2 / 2 + ((411301633 / 250000000)) ^ 2 * (1 + (2900023 / 125000000))) := by
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
  have hd : (2 * ((366921 / 62500000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (68527487 / 200000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (29350092909 / 250000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12729

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12730
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12730 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12730) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12730 : ℝ) * (12730 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12730) /
    ((12730 : ℝ) * (12730 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12730} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12730}
    (hw : WINDOW (paperDesignP 12730) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12730) c a v - lbar (paperDesignP 12730) c a| ^ (2 * q)
      ∂stdGauss (Fin (12730 - 1)) ∂muI 12730 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12730)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12730}
    (hw : WINDOW (paperDesignP 12730) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12730) c a v - gbar (paperDesignP 12730) c a| ^ (2 * q)
      ∂stdGauss (Fin (12730 - 1)) ∂muI 12730 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12730)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12730) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12730}
    (hw : WINDOW (paperDesignP 12730) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12730 - 1))).real
      {v | sgA (paperDesignP 12730) c a v < √(2 / (12730 : ℝ) * mixtureFloor)}
      ∂muI 12730 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12730 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12730 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12730) c
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

end BstLean.Part266.Row12730

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12730
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12730 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12730)
    (p : Ix 12730 × (Fin (12730 - 1) → ℝ)) :
    sgA (paperDesignP 12730) c p.1 p.2 ^ 2 ≤
      (2 / (12730 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12730).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12730) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12730 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12730 : ℝ) * _ ≤ 2 / 12730 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12730)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12730}
    (hw : WINDOW (paperDesignP 12730) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12730) c a v ^ 8
      ∂stdGauss (Fin (12730 - 1)) ∂muI 12730 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12730).prod (stdGauss (Fin (12730 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12730) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12730) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12730 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12730) c p.1 p.2)
      (√(2 / (12730 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12730)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12730 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12730) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12730}
    (hw : WINDOW (paperDesignP 12730) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12730) c a v -
      ∫ w, sA (paperDesignP 12730) c a w ∂stdGauss (Fin (12730 - 1))) ^ 2
      ∂stdGauss (Fin (12730 - 1))) ^ 2 ∂muI 12730 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12730) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12730

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12730
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12730}
    (hw : WINDOW (paperDesignP 12730) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12730).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12730) c M H xi)
    (hE : centreEnergy (paperDesignP 12730) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12730 : ℝ))))
    (hprice : massBound 12730 M H xi E u mixtureFloor ≤ 12730 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12730 - 1))).real
      {v | sgA (paperDesignP 12730) c a v < √(2 / (12730 : ℝ) * mixtureFloor)}
        ∂muI 12730 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12730).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12730) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12730) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12730)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12730

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12730
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12730) : ℝ :=
  (latitudeC / eR c) / ((12730 : ℝ) * (12730 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12730) / ((12730 : ℝ) * (12730 - 3))

theorem location_variance_on_event {c : Ret 12730}
    (hw : WINDOW (paperDesignP 12730) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12730) c a v - lbar (paperDesignP 12730) c a) ^ 2
      ∂stdGauss (Fin (12730 - 1))) ^ 2 ∂muI 12730 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12730)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12730}
    (hw : WINDOW (paperDesignP 12730) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12730) c a v - gbar (paperDesignP 12730) c a) ^ 2
      ∂stdGauss (Fin (12730 - 1))) ^ 2 ∂muI 12730 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12730)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12730}
    (hw : WINDOW (paperDesignP 12730) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12730 - 1))).real
      {v | sgA (paperDesignP 12730) c a v < √(2 / (12730 : ℝ) * mixtureFloor)}
      ∂muI 12730 ≤ lowMassBudget) :
    LatMom (paperDesignP 12730) c (√(2 / (12730 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12730

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12730
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

theorem location_budget_cap {c : Ret 12730} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12730 : ℝ) * (12730 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12730 : ℝ) * (12730 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12730 : ℝ) /
      ((12730 : ℝ) * (12730 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12730 : ℝ) * (12730 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12730 ≤ (2 * (16 / 5) / 12730 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12730} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (517212957 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (635273693 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (2723887 / 3125000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (5021642799 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (1541974887 / 250000000000000) ∧
    residualMomentBudget 12 ≤ (169256549 / 20000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12730} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (16459411 / 500000000000000) ∧ residualVarianceBudget ≤ (310311 / 100000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12730 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((5021642799 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12730

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12730
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12730 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12730) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12730) : ℝ :=
  exp (hqKappa * (12730 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((2935253 / 500000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5870507 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12730} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (2723887 / 781250000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (169256549 / 5000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (169256549 / 5000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((169256549 / 5000000000000) : ℝ) / ((2935253 / 500000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (23198347 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 12730} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (82257081 / 50000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((2723887 / 781250000))) / ((2935253 / 500000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12730} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12730 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12730 * ((23198347 / 1000000000) : ℝ) ^ 2 / 2 + ((82257081 / 50000000)) ^ 2 * (1 + (23198347 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12730 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12730 * ((23198347 / 1000000000)) ^ 2 / 2 + ((82257081 / 50000000)) ^ 2 * (1 + (23198347 / 1000000000))) := by
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
  have hd : (2 * ((2935253 / 500000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (21415669 / 62500) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (14676183131 / 125000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12730

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12731
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12731 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12731) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12731 : ℝ) * (12731 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12731) /
    ((12731 : ℝ) * (12731 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12731} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12731}
    (hw : WINDOW (paperDesignP 12731) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12731) c a v - lbar (paperDesignP 12731) c a| ^ (2 * q)
      ∂stdGauss (Fin (12731 - 1)) ∂muI 12731 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12731)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12731}
    (hw : WINDOW (paperDesignP 12731) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12731) c a v - gbar (paperDesignP 12731) c a| ^ (2 * q)
      ∂stdGauss (Fin (12731 - 1)) ∂muI 12731 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12731)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12731) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12731}
    (hw : WINDOW (paperDesignP 12731) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12731 - 1))).real
      {v | sgA (paperDesignP 12731) c a v < √(2 / (12731 : ℝ) * mixtureFloor)}
      ∂muI 12731 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12731 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12731 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12731) c
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

end BstLean.Part266.Row12731

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12731
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12731 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12731)
    (p : Ix 12731 × (Fin (12731 - 1) → ℝ)) :
    sgA (paperDesignP 12731) c p.1 p.2 ^ 2 ≤
      (2 / (12731 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12731).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12731) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12731 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12731 : ℝ) * _ ≤ 2 / 12731 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12731)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12731}
    (hw : WINDOW (paperDesignP 12731) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12731) c a v ^ 8
      ∂stdGauss (Fin (12731 - 1)) ∂muI 12731 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12731).prod (stdGauss (Fin (12731 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12731) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12731) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12731 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12731) c p.1 p.2)
      (√(2 / (12731 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12731)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12731 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12731) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12731}
    (hw : WINDOW (paperDesignP 12731) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12731) c a v -
      ∫ w, sA (paperDesignP 12731) c a w ∂stdGauss (Fin (12731 - 1))) ^ 2
      ∂stdGauss (Fin (12731 - 1))) ^ 2 ∂muI 12731 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12731) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12731

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12731
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12731}
    (hw : WINDOW (paperDesignP 12731) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12731).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12731) c M H xi)
    (hE : centreEnergy (paperDesignP 12731) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12731 : ℝ))))
    (hprice : massBound 12731 M H xi E u mixtureFloor ≤ 12731 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12731 - 1))).real
      {v | sgA (paperDesignP 12731) c a v < √(2 / (12731 : ℝ) * mixtureFloor)}
        ∂muI 12731 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12731).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12731) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12731) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12731)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12731

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12731
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12731) : ℝ :=
  (latitudeC / eR c) / ((12731 : ℝ) * (12731 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12731) / ((12731 : ℝ) * (12731 - 3))

theorem location_variance_on_event {c : Ret 12731}
    (hw : WINDOW (paperDesignP 12731) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12731) c a v - lbar (paperDesignP 12731) c a) ^ 2
      ∂stdGauss (Fin (12731 - 1))) ^ 2 ∂muI 12731 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12731)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12731}
    (hw : WINDOW (paperDesignP 12731) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12731) c a v - gbar (paperDesignP 12731) c a) ^ 2
      ∂stdGauss (Fin (12731 - 1))) ^ 2 ∂muI 12731 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12731)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12731}
    (hw : WINDOW (paperDesignP 12731) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12731 - 1))).real
      {v | sgA (paperDesignP 12731) c a v < √(2 / (12731 : ℝ) * mixtureFloor)}
      ∂muI 12731 ≤ lowMassBudget) :
    LatMom (paperDesignP 12731) c (√(2 / (12731 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12731

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12731
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

theorem location_budget_cap {c : Ret 12731} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12731 : ℝ) * (12731 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12731 : ℝ) * (12731 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12731 : ℝ) /
      ((12731 : ℝ) * (12731 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12731 : ℝ) * (12731 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12731 ≤ (2 * (16 / 5) / 12731 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12731} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (517172317 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (79402971 / 125000000000) ∧
    locationMomentBudget c 12 ≤ (435787653 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (39226961 / 7812500000000) ∧
    residualMomentBudget 6 ≤ (6167172597 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (8461829703 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12731} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (658273 / 20000000000000) ∧ residualVarianceBudget ≤ (3102379 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12731 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((39226961 / 7812500000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12731

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12731
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12731 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12731) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12731) : ℝ :=
  exp (hqKappa * (12731 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((234811 / 40000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (1467569 / 250000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12731} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (435787653 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8461829703 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8461829703 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8461829703 / 250000000000000) : ℝ) / ((234811 / 40000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11598257 / 500000000) := by
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

theorem hq_location_bounds {c : Ret 12731} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1645077001 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((435787653 / 125000000000))) / ((234811 / 40000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12731} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12731 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12731 * ((11598257 / 500000000) : ℝ) ^ 2 / 2 + ((1645077001 / 1000000000)) ^ 2 * (1 + (11598257 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12731 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12731 * ((11598257 / 500000000)) ^ 2 / 2 + ((1645077001 / 1000000000)) ^ 2 * (1 + (11598257 / 500000000))) := by
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
  have hd : (2 * ((234811 / 40000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (171332017 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (117418599781 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12731

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12732
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12732 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12732) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12732 : ℝ) * (12732 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12732) /
    ((12732 : ℝ) * (12732 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12732} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12732}
    (hw : WINDOW (paperDesignP 12732) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12732) c a v - lbar (paperDesignP 12732) c a| ^ (2 * q)
      ∂stdGauss (Fin (12732 - 1)) ∂muI 12732 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12732)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12732}
    (hw : WINDOW (paperDesignP 12732) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12732) c a v - gbar (paperDesignP 12732) c a| ^ (2 * q)
      ∂stdGauss (Fin (12732 - 1)) ∂muI 12732 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12732)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12732) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12732}
    (hw : WINDOW (paperDesignP 12732) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12732 - 1))).real
      {v | sgA (paperDesignP 12732) c a v < √(2 / (12732 : ℝ) * mixtureFloor)}
      ∂muI 12732 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12732 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12732 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12732) c
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

end BstLean.Part266.Row12732

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12732
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12732 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12732)
    (p : Ix 12732 × (Fin (12732 - 1) → ℝ)) :
    sgA (paperDesignP 12732) c p.1 p.2 ^ 2 ≤
      (2 / (12732 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12732).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12732) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12732 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12732 : ℝ) * _ ≤ 2 / 12732 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12732)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12732}
    (hw : WINDOW (paperDesignP 12732) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12732) c a v ^ 8
      ∂stdGauss (Fin (12732 - 1)) ∂muI 12732 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12732).prod (stdGauss (Fin (12732 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12732) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12732) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12732 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12732) c p.1 p.2)
      (√(2 / (12732 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12732)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12732 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12732) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12732}
    (hw : WINDOW (paperDesignP 12732) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12732) c a v -
      ∫ w, sA (paperDesignP 12732) c a w ∂stdGauss (Fin (12732 - 1))) ^ 2
      ∂stdGauss (Fin (12732 - 1))) ^ 2 ∂muI 12732 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12732) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12732

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12732
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12732}
    (hw : WINDOW (paperDesignP 12732) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12732).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12732) c M H xi)
    (hE : centreEnergy (paperDesignP 12732) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12732 : ℝ))))
    (hprice : massBound 12732 M H xi E u mixtureFloor ≤ 12732 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12732 - 1))).real
      {v | sgA (paperDesignP 12732) c a v < √(2 / (12732 : ℝ) * mixtureFloor)}
        ∂muI 12732 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12732).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12732) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12732) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12732)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12732

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12732
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12732) : ℝ :=
  (latitudeC / eR c) / ((12732 : ℝ) * (12732 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12732) / ((12732 : ℝ) * (12732 - 3))

theorem location_variance_on_event {c : Ret 12732}
    (hw : WINDOW (paperDesignP 12732) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12732) c a v - lbar (paperDesignP 12732) c a) ^ 2
      ∂stdGauss (Fin (12732 - 1))) ^ 2 ∂muI 12732 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12732)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12732}
    (hw : WINDOW (paperDesignP 12732) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12732) c a v - gbar (paperDesignP 12732) c a) ^ 2
      ∂stdGauss (Fin (12732 - 1))) ^ 2 ∂muI 12732 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12732)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12732}
    (hw : WINDOW (paperDesignP 12732) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12732 - 1))).real
      {v | sgA (paperDesignP 12732) c a v < √(2 / (12732 : ℝ) * mixtureFloor)}
      ∂muI 12732 ≤ lowMassBudget) :
    LatMom (paperDesignP 12732) c (√(2 / (12732 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12732

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12732
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

theorem location_budget_cap {c : Ret 12732} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12732 : ℝ) * (12732 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12732 : ℝ) * (12732 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12732 : ℝ) /
      ((12732 : ℝ) * (12732 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12732 : ℝ) * (12732 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12732 ≤ (2 * (16 / 5) / 12732 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12732} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (258565841 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (12703477 / 20000000000) ∧
    locationMomentBudget c 12 ≤ (871506783 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (5020459333 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (1541611447 / 250000000000000) ∧
    residualMomentBudget 12 ≤ (1057604019 / 125000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12732} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (102839 / 3125000000000) ∧ residualVarianceBudget ≤ (193853 / 62500000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12732 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((5020459333 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12732

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12732
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12732 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12732) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12732) : ℝ :=
  exp (hqKappa * (12732 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((1174009 / 200000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2935023 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12732} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (871506783 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (1057604019 / 31250000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (1057604019 / 31250000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((1057604019 / 31250000000000) : ℝ) / ((1174009 / 200000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11597339 / 500000000) := by
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

theorem hq_location_bounds {c : Ret 12732} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (822506059 / 500000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((871506783 / 250000000000))) / ((1174009 / 200000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12732} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12732 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12732 * ((11597339 / 500000000) : ℝ) ^ 2 / 2 + ((822506059 / 500000000)) ^ 2 * (1 + (11597339 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12732 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12732 * ((11597339 / 500000000)) ^ 2 / 2 + ((822506059 / 500000000)) ^ 2 * (1 + (11597339 / 500000000))) := by
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
  have hd : (2 * ((1174009 / 200000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (68535461 / 200000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (117427695373 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12732

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12733
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12733 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12733) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12733 : ℝ) * (12733 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12733) /
    ((12733 : ℝ) * (12733 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12733} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12733}
    (hw : WINDOW (paperDesignP 12733) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12733) c a v - lbar (paperDesignP 12733) c a| ^ (2 * q)
      ∂stdGauss (Fin (12733 - 1)) ∂muI 12733 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12733)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12733}
    (hw : WINDOW (paperDesignP 12733) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12733) c a v - gbar (paperDesignP 12733) c a| ^ (2 * q)
      ∂stdGauss (Fin (12733 - 1)) ∂muI 12733 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12733)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12733) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12733}
    (hw : WINDOW (paperDesignP 12733) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12733 - 1))).real
      {v | sgA (paperDesignP 12733) c a v < √(2 / (12733 : ℝ) * mixtureFloor)}
      ∂muI 12733 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12733 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12733 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12733) c
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

end BstLean.Part266.Row12733

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12733
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12733 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12733)
    (p : Ix 12733 × (Fin (12733 - 1) → ℝ)) :
    sgA (paperDesignP 12733) c p.1 p.2 ^ 2 ≤
      (2 / (12733 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12733).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12733) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12733 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12733 : ℝ) * _ ≤ 2 / 12733 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12733)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12733}
    (hw : WINDOW (paperDesignP 12733) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12733) c a v ^ 8
      ∂stdGauss (Fin (12733 - 1)) ∂muI 12733 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12733).prod (stdGauss (Fin (12733 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12733) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12733) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12733 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12733) c p.1 p.2)
      (√(2 / (12733 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12733)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12733 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12733) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12733}
    (hw : WINDOW (paperDesignP 12733) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12733) c a v -
      ∫ w, sA (paperDesignP 12733) c a w ∂stdGauss (Fin (12733 - 1))) ^ 2
      ∂stdGauss (Fin (12733 - 1))) ^ 2 ∂muI 12733 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12733) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12733

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12733
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12733}
    (hw : WINDOW (paperDesignP 12733) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12733).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12733) c M H xi)
    (hE : centreEnergy (paperDesignP 12733) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12733 : ℝ))))
    (hprice : massBound 12733 M H xi E u mixtureFloor ≤ 12733 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12733 - 1))).real
      {v | sgA (paperDesignP 12733) c a v < √(2 / (12733 : ℝ) * mixtureFloor)}
        ∂muI 12733 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12733).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12733) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12733) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12733)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12733

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12733
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12733) : ℝ :=
  (latitudeC / eR c) / ((12733 : ℝ) * (12733 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12733) / ((12733 : ℝ) * (12733 - 3))

theorem location_variance_on_event {c : Ret 12733}
    (hw : WINDOW (paperDesignP 12733) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12733) c a v - lbar (paperDesignP 12733) c a) ^ 2
      ∂stdGauss (Fin (12733 - 1))) ^ 2 ∂muI 12733 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12733)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12733}
    (hw : WINDOW (paperDesignP 12733) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12733) c a v - gbar (paperDesignP 12733) c a) ^ 2
      ∂stdGauss (Fin (12733 - 1))) ^ 2 ∂muI 12733 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12733)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12733}
    (hw : WINDOW (paperDesignP 12733) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12733 - 1))).real
      {v | sgA (paperDesignP 12733) c a v < √(2 / (12733 : ℝ) * mixtureFloor)}
      ∂muI 12733 ≤ lowMassBudget) :
    LatMom (paperDesignP 12733) c (√(2 / (12733 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12733

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12733
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

theorem location_budget_cap {c : Ret 12733} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12733 : ℝ) * (12733 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12733 : ℝ) * (12733 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12733 : ℝ) /
      ((12733 : ℝ) * (12733 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12733 : ℝ) * (12733 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12733 ≤ (2 * (16 / 5) / 12733 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12733} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (258545527 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (635123941 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (871438271 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2509933887 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (3082859561 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (8459834797 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12733} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (3290331 / 100000000000000) ∧ residualVarianceBudget ≤ (3100917 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12733 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2509933887 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12733

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12733
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12733 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12733) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12733) : ℝ :=
  exp (hqKappa * (12733 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((2934907 / 500000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (1173963 / 200000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12733} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (871438271 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8459834797 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8459834797 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8459834797 / 250000000000000) : ℝ) / ((2934907 / 500000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11596423 / 500000000) := by
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

theorem hq_location_bounds {c : Ret 12733} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1644947531 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((871438271 / 250000000000))) / ((2934907 / 500000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12733} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12733 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12733 * ((11596423 / 500000000) : ℝ) ^ 2 / 2 + ((1644947531 / 1000000000)) ^ 2 * (1 + (11596423 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12733 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12733 * ((11596423 / 500000000)) ^ 2 / 2 + ((1644947531 / 1000000000)) ^ 2 * (1 + (11596423 / 500000000))) := by
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
  have hd : (2 * ((2934907 / 500000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (342690637 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (14679604037 / 125000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12733

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12734
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12734 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12734) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12734 : ℝ) * (12734 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12734) /
    ((12734 : ℝ) * (12734 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12734} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12734}
    (hw : WINDOW (paperDesignP 12734) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12734) c a v - lbar (paperDesignP 12734) c a| ^ (2 * q)
      ∂stdGauss (Fin (12734 - 1)) ∂muI 12734 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12734)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12734}
    (hw : WINDOW (paperDesignP 12734) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12734) c a v - gbar (paperDesignP 12734) c a| ^ (2 * q)
      ∂stdGauss (Fin (12734 - 1)) ∂muI 12734 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12734)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12734) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12734}
    (hw : WINDOW (paperDesignP 12734) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12734 - 1))).real
      {v | sgA (paperDesignP 12734) c a v < √(2 / (12734 : ℝ) * mixtureFloor)}
      ∂muI 12734 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12734 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12734 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12734) c
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

end BstLean.Part266.Row12734

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12734
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12734 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12734)
    (p : Ix 12734 × (Fin (12734 - 1) → ℝ)) :
    sgA (paperDesignP 12734) c p.1 p.2 ^ 2 ≤
      (2 / (12734 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12734).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12734) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12734 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12734 : ℝ) * _ ≤ 2 / 12734 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12734)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12734}
    (hw : WINDOW (paperDesignP 12734) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12734) c a v ^ 8
      ∂stdGauss (Fin (12734 - 1)) ∂muI 12734 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12734).prod (stdGauss (Fin (12734 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12734) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12734) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12734 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12734) c p.1 p.2)
      (√(2 / (12734 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12734)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12734 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12734) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12734}
    (hw : WINDOW (paperDesignP 12734) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12734) c a v -
      ∫ w, sA (paperDesignP 12734) c a w ∂stdGauss (Fin (12734 - 1))) ^ 2
      ∂stdGauss (Fin (12734 - 1))) ^ 2 ∂muI 12734 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12734) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12734

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12734
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12734}
    (hw : WINDOW (paperDesignP 12734) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12734).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12734) c M H xi)
    (hE : centreEnergy (paperDesignP 12734) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12734 : ℝ))))
    (hprice : massBound 12734 M H xi E u mixtureFloor ≤ 12734 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12734 - 1))).real
      {v | sgA (paperDesignP 12734) c a v < √(2 / (12734 : ℝ) * mixtureFloor)}
        ∂muI 12734 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12734).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12734) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12734) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12734)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12734

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12734
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12734) : ℝ :=
  (latitudeC / eR c) / ((12734 : ℝ) * (12734 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12734) / ((12734 : ℝ) * (12734 - 3))

theorem location_variance_on_event {c : Ret 12734}
    (hw : WINDOW (paperDesignP 12734) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12734) c a v - lbar (paperDesignP 12734) c a) ^ 2
      ∂stdGauss (Fin (12734 - 1))) ^ 2 ∂muI 12734 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12734)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12734}
    (hw : WINDOW (paperDesignP 12734) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12734) c a v - gbar (paperDesignP 12734) c a) ^ 2
      ∂stdGauss (Fin (12734 - 1))) ^ 2 ∂muI 12734 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12734)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12734}
    (hw : WINDOW (paperDesignP 12734) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12734 - 1))).real
      {v | sgA (paperDesignP 12734) c a v < √(2 / (12734 : ℝ) * mixtureFloor)}
      ∂muI 12734 ≤ lowMassBudget) :
    LatMom (paperDesignP 12734) c (√(2 / (12734 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12734

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12734
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

theorem location_budget_cap {c : Ret 12734} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12734 : ℝ) * (12734 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12734 : ℝ) * (12734 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12734 : ℝ) /
      ((12734 : ℝ) * (12734 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12734 : ℝ) * (12734 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12734 ≤ (2 * (16 / 5) / 12734 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12734} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (517050433 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (635074039 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (87136977 / 100000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (1254819083 / 250000000000000) ∧
    residualMomentBudget 6 ≤ (6164992599 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (4229418819 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12734} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (16449071 / 500000000000000) ∧ residualVarianceBudget ≤ (3100187 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12734 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((1254819083 / 250000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12734

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12734
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12734 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12734) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12734) : ℝ :=
  exp (hqKappa * (12734 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((366849 / 62500000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (1173917 / 200000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12734} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (87136977 / 25000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4229418819 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4229418819 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4229418819 / 125000000000000) : ℝ) / ((366849 / 62500000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (2319101 / 100000000) := by
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

theorem hq_location_bounds {c : Ret 12734} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1644882679 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((87136977 / 25000000000))) / ((366849 / 62500000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12734} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12734 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12734 * ((2319101 / 100000000) : ℝ) ^ 2 / 2 + ((1644882679 / 1000000000)) ^ 2 * (1 + (2319101 / 100000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12734 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12734 * ((2319101 / 100000000)) ^ 2 / 2 + ((1644882679 / 1000000000)) ^ 2 * (1 + (2319101 / 100000000))) := by
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
  have hd : (2 * ((366849 / 62500000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (34270391 / 100000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (117445930069 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12734

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12735
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12735 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12735) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12735 : ℝ) * (12735 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12735) /
    ((12735 : ℝ) * (12735 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12735} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12735}
    (hw : WINDOW (paperDesignP 12735) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12735) c a v - lbar (paperDesignP 12735) c a| ^ (2 * q)
      ∂stdGauss (Fin (12735 - 1)) ∂muI 12735 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12735)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12735}
    (hw : WINDOW (paperDesignP 12735) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12735) c a v - gbar (paperDesignP 12735) c a| ^ (2 * q)
      ∂stdGauss (Fin (12735 - 1)) ∂muI 12735 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12735)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12735) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12735}
    (hw : WINDOW (paperDesignP 12735) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12735 - 1))).real
      {v | sgA (paperDesignP 12735) c a v < √(2 / (12735 : ℝ) * mixtureFloor)}
      ∂muI 12735 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12735 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12735 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12735) c
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

end BstLean.Part266.Row12735

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12735
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12735 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12735)
    (p : Ix 12735 × (Fin (12735 - 1) → ℝ)) :
    sgA (paperDesignP 12735) c p.1 p.2 ^ 2 ≤
      (2 / (12735 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12735).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12735) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12735 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12735 : ℝ) * _ ≤ 2 / 12735 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12735)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12735}
    (hw : WINDOW (paperDesignP 12735) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12735) c a v ^ 8
      ∂stdGauss (Fin (12735 - 1)) ∂muI 12735 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12735).prod (stdGauss (Fin (12735 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12735) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12735) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12735 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12735) c p.1 p.2)
      (√(2 / (12735 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12735)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12735 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12735) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12735}
    (hw : WINDOW (paperDesignP 12735) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12735) c a v -
      ∫ w, sA (paperDesignP 12735) c a w ∂stdGauss (Fin (12735 - 1))) ^ 2
      ∂stdGauss (Fin (12735 - 1))) ^ 2 ∂muI 12735 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12735) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12735

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12735
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12735}
    (hw : WINDOW (paperDesignP 12735) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12735).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12735) c M H xi)
    (hE : centreEnergy (paperDesignP 12735) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12735 : ℝ))))
    (hprice : massBound 12735 M H xi E u mixtureFloor ≤ 12735 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12735 - 1))).real
      {v | sgA (paperDesignP 12735) c a v < √(2 / (12735 : ℝ) * mixtureFloor)}
        ∂muI 12735 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12735).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12735) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12735) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12735)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12735

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12735
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12735) : ℝ :=
  (latitudeC / eR c) / ((12735 : ℝ) * (12735 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12735) / ((12735 : ℝ) * (12735 - 3))

theorem location_variance_on_event {c : Ret 12735}
    (hw : WINDOW (paperDesignP 12735) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12735) c a v - lbar (paperDesignP 12735) c a) ^ 2
      ∂stdGauss (Fin (12735 - 1))) ^ 2 ∂muI 12735 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12735)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12735}
    (hw : WINDOW (paperDesignP 12735) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12735) c a v - gbar (paperDesignP 12735) c a) ^ 2
      ∂stdGauss (Fin (12735 - 1))) ^ 2 ∂muI 12735 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12735)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12735}
    (hw : WINDOW (paperDesignP 12735) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12735 - 1))).real
      {v | sgA (paperDesignP 12735) c a v < √(2 / (12735 : ℝ) * mixtureFloor)}
      ∂muI 12735 ≤ lowMassBudget) :
    LatMom (paperDesignP 12735) c (√(2 / (12735 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12735

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12735
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

theorem location_budget_cap {c : Ret 12735} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12735 : ℝ) * (12735 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12735 : ℝ) * (12735 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12735 : ℝ) /
      ((12735 : ℝ) * (12735 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12735 : ℝ) * (12735 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12735 ≤ (2 * (16 / 5) / 12735 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12735} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (258504909 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (127004829 / 200000000000) ∧
    locationMomentBudget c 12 ≤ (871301279 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (1003737001 / 200000000000000) ∧
    residualMomentBudget 6 ≤ (3082133109 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (4228920337 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12735} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (1315719 / 40000000000000) ∧ residualVarianceBudget ≤ (48429 / 15625000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12735 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((1003737001 / 200000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12735

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12735
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12735 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12735) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12735) : ℝ :=
  exp (hqKappa * (12735 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5869353 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2934677 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12735} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (871301279 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4228920337 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4228920337 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4228920337 / 125000000000000) : ℝ) / ((5869353 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (23189179 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 12735} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1644818121 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((871301279 / 250000000000))) / ((5869353 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12735} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12735 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12735 * ((23189179 / 1000000000) : ℝ) ^ 2 / 2 + ((1644818121 / 1000000000)) ^ 2 * (1 + (23189179 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12735 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12735 * ((23189179 / 1000000000)) ^ 2 / 2 + ((1644818121 / 1000000000)) ^ 2 * (1 + (23189179 / 1000000000))) := by
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
  have hd : (2 * ((5869353 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (85679311 / 250000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (58727534591 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12735

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12736
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12736 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12736) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12736 : ℝ) * (12736 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12736) /
    ((12736 : ℝ) * (12736 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12736} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12736}
    (hw : WINDOW (paperDesignP 12736) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12736) c a v - lbar (paperDesignP 12736) c a| ^ (2 * q)
      ∂stdGauss (Fin (12736 - 1)) ∂muI 12736 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12736)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12736}
    (hw : WINDOW (paperDesignP 12736) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12736) c a v - gbar (paperDesignP 12736) c a| ^ (2 * q)
      ∂stdGauss (Fin (12736 - 1)) ∂muI 12736 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12736)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12736) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12736}
    (hw : WINDOW (paperDesignP 12736) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12736 - 1))).real
      {v | sgA (paperDesignP 12736) c a v < √(2 / (12736 : ℝ) * mixtureFloor)}
      ∂muI 12736 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12736 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12736 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12736) c
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

end BstLean.Part266.Row12736

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12736
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12736 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12736)
    (p : Ix 12736 × (Fin (12736 - 1) → ℝ)) :
    sgA (paperDesignP 12736) c p.1 p.2 ^ 2 ≤
      (2 / (12736 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12736).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12736) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12736 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12736 : ℝ) * _ ≤ 2 / 12736 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12736)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12736}
    (hw : WINDOW (paperDesignP 12736) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12736) c a v ^ 8
      ∂stdGauss (Fin (12736 - 1)) ∂muI 12736 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12736).prod (stdGauss (Fin (12736 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12736) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12736) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12736 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12736) c p.1 p.2)
      (√(2 / (12736 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12736)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12736 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12736) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12736}
    (hw : WINDOW (paperDesignP 12736) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12736) c a v -
      ∫ w, sA (paperDesignP 12736) c a w ∂stdGauss (Fin (12736 - 1))) ^ 2
      ∂stdGauss (Fin (12736 - 1))) ^ 2 ∂muI 12736 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12736) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12736

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12736
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12736}
    (hw : WINDOW (paperDesignP 12736) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12736).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12736) c M H xi)
    (hE : centreEnergy (paperDesignP 12736) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12736 : ℝ))))
    (hprice : massBound 12736 M H xi E u mixtureFloor ≤ 12736 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12736 - 1))).real
      {v | sgA (paperDesignP 12736) c a v < √(2 / (12736 : ℝ) * mixtureFloor)}
        ∂muI 12736 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12736).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12736) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12736) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12736)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12736

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12736
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12736) : ℝ :=
  (latitudeC / eR c) / ((12736 : ℝ) * (12736 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12736) / ((12736 : ℝ) * (12736 - 3))

theorem location_variance_on_event {c : Ret 12736}
    (hw : WINDOW (paperDesignP 12736) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12736) c a v - lbar (paperDesignP 12736) c a) ^ 2
      ∂stdGauss (Fin (12736 - 1))) ^ 2 ∂muI 12736 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12736)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12736}
    (hw : WINDOW (paperDesignP 12736) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12736) c a v - gbar (paperDesignP 12736) c a) ^ 2
      ∂stdGauss (Fin (12736 - 1))) ^ 2 ∂muI 12736 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12736)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12736}
    (hw : WINDOW (paperDesignP 12736) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12736 - 1))).real
      {v | sgA (paperDesignP 12736) c a v < √(2 / (12736 : ℝ) * mixtureFloor)}
      ∂muI 12736 ≤ lowMassBudget) :
    LatMom (paperDesignP 12736) c (√(2 / (12736 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12736

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12736
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

theorem location_budget_cap {c : Ret 12736} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12736 : ℝ) * (12736 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12736 : ℝ) * (12736 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12736 : ℝ) /
      ((12736 : ℝ) * (12736 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12736 : ℝ) * (12736 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12736 ≤ (2 * (16 / 5) / 12736 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12736} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (516969209 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (634974259 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (871232799 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (1003618759 / 200000000000000) ∧
    residualMomentBudget 6 ≤ (308176999 / 50000000000000) ∧
    residualMomentBudget 12 ≤ (8456843907 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12736} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (32887809 / 1000000000000000) ∧ residualVarianceBudget ≤ (1549363 / 500000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12736 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((1003618759 / 200000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12736

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12736
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12736 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12736) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12736) : ℝ :=
  exp (hqKappa * (12736 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5869123 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (1467281 / 250000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12736} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (871232799 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8456843907 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8456843907 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8456843907 / 250000000000000) : ℝ) / ((5869123 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (4637469 / 200000000) := by
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

theorem hq_location_bounds {c : Ret 12736} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1644753299 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((871232799 / 250000000000))) / ((5869123 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12736} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12736 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12736 * ((4637469 / 200000000) : ℝ) ^ 2 / 2 + ((1644753299 / 1000000000)) ^ 2 * (1 + (4637469 / 200000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12736 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12736 * ((4637469 / 200000000)) ^ 2 / 2 + ((1644753299 / 1000000000)) ^ 2 * (1 + (4637469 / 200000000))) := by
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
  have hd : (2 * ((5869123 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (8568263 / 25000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (7341510571 / 62500) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12736

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12737
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12737 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12737) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12737 : ℝ) * (12737 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12737) /
    ((12737 : ℝ) * (12737 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12737} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12737}
    (hw : WINDOW (paperDesignP 12737) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12737) c a v - lbar (paperDesignP 12737) c a| ^ (2 * q)
      ∂stdGauss (Fin (12737 - 1)) ∂muI 12737 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12737)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12737}
    (hw : WINDOW (paperDesignP 12737) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12737) c a v - gbar (paperDesignP 12737) c a| ^ (2 * q)
      ∂stdGauss (Fin (12737 - 1)) ∂muI 12737 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12737)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12737) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12737}
    (hw : WINDOW (paperDesignP 12737) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12737 - 1))).real
      {v | sgA (paperDesignP 12737) c a v < √(2 / (12737 : ℝ) * mixtureFloor)}
      ∂muI 12737 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12737 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12737 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12737) c
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

end BstLean.Part266.Row12737

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12737
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12737 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12737)
    (p : Ix 12737 × (Fin (12737 - 1) → ℝ)) :
    sgA (paperDesignP 12737) c p.1 p.2 ^ 2 ≤
      (2 / (12737 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12737).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12737) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12737 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12737 : ℝ) * _ ≤ 2 / 12737 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12737)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12737}
    (hw : WINDOW (paperDesignP 12737) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12737) c a v ^ 8
      ∂stdGauss (Fin (12737 - 1)) ∂muI 12737 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12737).prod (stdGauss (Fin (12737 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12737) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12737) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12737 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12737) c p.1 p.2)
      (√(2 / (12737 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12737)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12737 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12737) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12737}
    (hw : WINDOW (paperDesignP 12737) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12737) c a v -
      ∫ w, sA (paperDesignP 12737) c a w ∂stdGauss (Fin (12737 - 1))) ^ 2
      ∂stdGauss (Fin (12737 - 1))) ^ 2 ∂muI 12737 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12737) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12737

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12737
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12737}
    (hw : WINDOW (paperDesignP 12737) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12737).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12737) c M H xi)
    (hE : centreEnergy (paperDesignP 12737) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12737 : ℝ))))
    (hprice : massBound 12737 M H xi E u mixtureFloor ≤ 12737 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12737 - 1))).real
      {v | sgA (paperDesignP 12737) c a v < √(2 / (12737 : ℝ) * mixtureFloor)}
        ∂muI 12737 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12737).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12737) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12737) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12737)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12737

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12737
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12737) : ℝ :=
  (latitudeC / eR c) / ((12737 : ℝ) * (12737 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12737) / ((12737 : ℝ) * (12737 - 3))

theorem location_variance_on_event {c : Ret 12737}
    (hw : WINDOW (paperDesignP 12737) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12737) c a v - lbar (paperDesignP 12737) c a) ^ 2
      ∂stdGauss (Fin (12737 - 1))) ^ 2 ∂muI 12737 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12737)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12737}
    (hw : WINDOW (paperDesignP 12737) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12737) c a v - gbar (paperDesignP 12737) c a) ^ 2
      ∂stdGauss (Fin (12737 - 1))) ^ 2 ∂muI 12737 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12737)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12737}
    (hw : WINDOW (paperDesignP 12737) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12737 - 1))).real
      {v | sgA (paperDesignP 12737) c a v < √(2 / (12737 : ℝ) * mixtureFloor)}
      ∂muI 12737 ≤ lowMassBudget) :
    LatMom (paperDesignP 12737) c (√(2 / (12737 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12737

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12737
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

theorem location_budget_cap {c : Ret 12737} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12737 : ℝ) * (12737 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12737 : ℝ) * (12737 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12737 : ℝ) /
      ((12737 : ℝ) * (12737 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12737 : ℝ) * (12737 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12737 ≤ (2 * (16 / 5) / 12737 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12737} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (516928607 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (634924381 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (871164331 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (5017502701 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (1232562777 / 200000000000000) ∧
    residualMomentBudget 12 ≤ (1056980917 / 125000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12737} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (6576529 / 200000000000000) ∧ residualVarianceBudget ≤ (774499 / 250000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12737 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((5017502701 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12737

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12737
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12737 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12737) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12737) : ℝ :=
  exp (hqKappa * (12737 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((1467223 / 250000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5868893 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12737} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (871164331 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (1056980917 / 31250000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (1056980917 / 31250000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((1056980917 / 31250000000000) : ℝ) / ((1467223 / 250000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11592757 / 500000000) := by
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

theorem hq_location_bounds {c : Ret 12737} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (822344387 / 500000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((871164331 / 250000000000))) / ((1467223 / 250000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12737} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12737 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12737 * ((11592757 / 500000000) : ℝ) ^ 2 / 2 + ((822344387 / 500000000)) ^ 2 * (1 + (11592757 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12737 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12737 * ((11592757 / 500000000)) ^ 2 / 2 + ((822344387 / 500000000)) ^ 2 * (1 + (11592757 / 500000000))) := by
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
  have hd : (2 * ((1467223 / 250000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (21421491 / 62500) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (117473310441 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12737

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12738
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12738 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12738) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12738 : ℝ) * (12738 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12738) /
    ((12738 : ℝ) * (12738 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12738} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12738}
    (hw : WINDOW (paperDesignP 12738) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12738) c a v - lbar (paperDesignP 12738) c a| ^ (2 * q)
      ∂stdGauss (Fin (12738 - 1)) ∂muI 12738 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12738)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12738}
    (hw : WINDOW (paperDesignP 12738) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12738) c a v - gbar (paperDesignP 12738) c a| ^ (2 * q)
      ∂stdGauss (Fin (12738 - 1)) ∂muI 12738 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12738)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12738) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12738}
    (hw : WINDOW (paperDesignP 12738) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12738 - 1))).real
      {v | sgA (paperDesignP 12738) c a v < √(2 / (12738 : ℝ) * mixtureFloor)}
      ∂muI 12738 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12738 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12738 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12738) c
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

end BstLean.Part266.Row12738

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12738
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12738 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12738)
    (p : Ix 12738 × (Fin (12738 - 1) → ℝ)) :
    sgA (paperDesignP 12738) c p.1 p.2 ^ 2 ≤
      (2 / (12738 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12738).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12738) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12738 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12738 : ℝ) * _ ≤ 2 / 12738 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12738)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12738}
    (hw : WINDOW (paperDesignP 12738) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12738) c a v ^ 8
      ∂stdGauss (Fin (12738 - 1)) ∂muI 12738 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12738).prod (stdGauss (Fin (12738 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12738) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12738) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12738 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12738) c p.1 p.2)
      (√(2 / (12738 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12738)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12738 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12738) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12738}
    (hw : WINDOW (paperDesignP 12738) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12738) c a v -
      ∫ w, sA (paperDesignP 12738) c a w ∂stdGauss (Fin (12738 - 1))) ^ 2
      ∂stdGauss (Fin (12738 - 1))) ^ 2 ∂muI 12738 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12738) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12738

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12738
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12738}
    (hw : WINDOW (paperDesignP 12738) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12738).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12738) c M H xi)
    (hE : centreEnergy (paperDesignP 12738) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12738 : ℝ))))
    (hprice : massBound 12738 M H xi E u mixtureFloor ≤ 12738 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12738 - 1))).real
      {v | sgA (paperDesignP 12738) c a v < √(2 / (12738 : ℝ) * mixtureFloor)}
        ∂muI 12738 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12738).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12738) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12738) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12738)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12738

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12738
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12738) : ℝ :=
  (latitudeC / eR c) / ((12738 : ℝ) * (12738 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12738) / ((12738 : ℝ) * (12738 - 3))

theorem location_variance_on_event {c : Ret 12738}
    (hw : WINDOW (paperDesignP 12738) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12738) c a v - lbar (paperDesignP 12738) c a) ^ 2
      ∂stdGauss (Fin (12738 - 1))) ^ 2 ∂muI 12738 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12738)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12738}
    (hw : WINDOW (paperDesignP 12738) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12738) c a v - gbar (paperDesignP 12738) c a) ^ 2
      ∂stdGauss (Fin (12738 - 1))) ^ 2 ∂muI 12738 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12738)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12738}
    (hw : WINDOW (paperDesignP 12738) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12738 - 1))).real
      {v | sgA (paperDesignP 12738) c a v < √(2 / (12738 : ℝ) * mixtureFloor)}
      ∂muI 12738 ≤ lowMassBudget) :
    LatMom (paperDesignP 12738) c (√(2 / (12738 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12738

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12738
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

theorem location_budget_cap {c : Ret 12738} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12738 : ℝ) * (12738 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12738 : ℝ) * (12738 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12738 : ℝ) /
      ((12738 : ℝ) * (12738 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12738 : ℝ) * (12738 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12738 ≤ (2 * (16 / 5) / 12738 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12738} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (516888011 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (63487451 / 100000000000) ∧
    locationMomentBudget c 12 ≤ (13610873 / 15625000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2508455861 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (1540521983 / 250000000000000) ∧
    residualMomentBudget 12 ≤ (105685637 / 12500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12738} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (32877481 / 1000000000000000) ∧ residualVarianceBudget ≤ (3097267 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12738 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2508455861 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12738

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12738
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12738 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12738) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12738) : ℝ :=
  exp (hqKappa * (12738 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((2934331 / 500000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5868663 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12738} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (13610873 / 3906250000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (105685637 / 3125000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (105685637 / 3125000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((105685637 / 3125000000000) : ℝ) / ((2934331 / 500000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (72449 / 3125000) := by
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

theorem hq_location_bounds {c : Ret 12738} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (822311991 / 500000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((13610873 / 3906250000))) / ((2934331 / 500000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12738} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12738 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12738 * ((72449 / 3125000) : ℝ) ^ 2 / 2 + ((822311991 / 500000000)) ^ 2 * (1 + (72449 / 3125000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12738 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12738 * ((72449 / 3125000)) ^ 2 / 2 + ((822311991 / 500000000)) ^ 2 * (1 + (72449 / 3125000))) := by
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
  have hd : (2 * ((2934331 / 500000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (171378567 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (58741206289 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12738

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12739
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12739 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12739) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12739 : ℝ) * (12739 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12739) /
    ((12739 : ℝ) * (12739 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12739} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12739}
    (hw : WINDOW (paperDesignP 12739) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12739) c a v - lbar (paperDesignP 12739) c a| ^ (2 * q)
      ∂stdGauss (Fin (12739 - 1)) ∂muI 12739 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12739)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12739}
    (hw : WINDOW (paperDesignP 12739) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12739) c a v - gbar (paperDesignP 12739) c a| ^ (2 * q)
      ∂stdGauss (Fin (12739 - 1)) ∂muI 12739 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12739)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12739) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12739}
    (hw : WINDOW (paperDesignP 12739) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12739 - 1))).real
      {v | sgA (paperDesignP 12739) c a v < √(2 / (12739 : ℝ) * mixtureFloor)}
      ∂muI 12739 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12739 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12739 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12739) c
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

end BstLean.Part266.Row12739

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12739
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12739 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12739)
    (p : Ix 12739 × (Fin (12739 - 1) → ℝ)) :
    sgA (paperDesignP 12739) c p.1 p.2 ^ 2 ≤
      (2 / (12739 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12739).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12739) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12739 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12739 : ℝ) * _ ≤ 2 / 12739 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12739)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12739}
    (hw : WINDOW (paperDesignP 12739) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12739) c a v ^ 8
      ∂stdGauss (Fin (12739 - 1)) ∂muI 12739 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12739).prod (stdGauss (Fin (12739 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12739) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12739) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12739 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12739) c p.1 p.2)
      (√(2 / (12739 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12739)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12739 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12739) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12739}
    (hw : WINDOW (paperDesignP 12739) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12739) c a v -
      ∫ w, sA (paperDesignP 12739) c a w ∂stdGauss (Fin (12739 - 1))) ^ 2
      ∂stdGauss (Fin (12739 - 1))) ^ 2 ∂muI 12739 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12739) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12739

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12739
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12739}
    (hw : WINDOW (paperDesignP 12739) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12739).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12739) c M H xi)
    (hE : centreEnergy (paperDesignP 12739) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12739 : ℝ))))
    (hprice : massBound 12739 M H xi E u mixtureFloor ≤ 12739 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12739 - 1))).real
      {v | sgA (paperDesignP 12739) c a v < √(2 / (12739 : ℝ) * mixtureFloor)}
        ∂muI 12739 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12739).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12739) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12739) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12739)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12739

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12739
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12739) : ℝ :=
  (latitudeC / eR c) / ((12739 : ℝ) * (12739 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12739) / ((12739 : ℝ) * (12739 - 3))

theorem location_variance_on_event {c : Ret 12739}
    (hw : WINDOW (paperDesignP 12739) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12739) c a v - lbar (paperDesignP 12739) c a) ^ 2
      ∂stdGauss (Fin (12739 - 1))) ^ 2 ∂muI 12739 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12739)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12739}
    (hw : WINDOW (paperDesignP 12739) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12739) c a v - gbar (paperDesignP 12739) c a) ^ 2
      ∂stdGauss (Fin (12739 - 1))) ^ 2 ∂muI 12739 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12739)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12739}
    (hw : WINDOW (paperDesignP 12739) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12739 - 1))).real
      {v | sgA (paperDesignP 12739) c a v < √(2 / (12739 : ℝ) * mixtureFloor)}
      ∂muI 12739 ≤ lowMassBudget) :
    LatMom (paperDesignP 12739) c (√(2 / (12739 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12739

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12739
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

theorem location_budget_cap {c : Ret 12739} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12739 : ℝ) * (12739 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12739 : ℝ) * (12739 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12739 : ℝ) /
      ((12739 : ℝ) * (12739 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12739 : ℝ) * (12739 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12739 ≤ (2 * (16 / 5) / 12739 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12739} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (516847421 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (79353081 / 125000000000) ∧
    locationMomentBudget c 12 ≤ (34841097 / 40000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (250816043 / 50000000000000) ∧
    residualMomentBudget 6 ≤ (6161362121 / 1000000000000000) ∧
    residualMomentBudget 12 ≤ (8453854779 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12739} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (32872319 / 1000000000000000) ∧ residualVarianceBudget ≤ (3096537 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12739 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((250816043 / 50000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12739

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12739
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12739 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12739) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12739) : ℝ :=
  exp (hqKappa * (12739 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((366777 / 62500000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5868433 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12739} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (34841097 / 10000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8453854779 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8453854779 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8453854779 / 250000000000000) : ℝ) / ((366777 / 62500000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (23181847 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 12739} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (822279603 / 500000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((34841097 / 10000000000))) / ((366777 / 62500000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12739} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12739 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12739 * ((23181847 / 1000000000) : ℝ) ^ 2 / 2 + ((822279603 / 500000000)) ^ 2 * (1 + (23181847 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12739 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12739 * ((23181847 / 1000000000)) ^ 2 / 2 + ((822279603 / 500000000)) ^ 2 * (1 + (23181847 / 1000000000))) := by
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
  have hd : (2 * ((366777 / 62500000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (342770413 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (117491515803 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12739

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12740
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12740 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12740) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12740 : ℝ) * (12740 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12740) /
    ((12740 : ℝ) * (12740 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12740} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12740}
    (hw : WINDOW (paperDesignP 12740) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12740) c a v - lbar (paperDesignP 12740) c a| ^ (2 * q)
      ∂stdGauss (Fin (12740 - 1)) ∂muI 12740 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12740)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12740}
    (hw : WINDOW (paperDesignP 12740) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12740) c a v - gbar (paperDesignP 12740) c a| ^ (2 * q)
      ∂stdGauss (Fin (12740 - 1)) ∂muI 12740 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12740)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12740) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12740}
    (hw : WINDOW (paperDesignP 12740) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12740 - 1))).real
      {v | sgA (paperDesignP 12740) c a v < √(2 / (12740 : ℝ) * mixtureFloor)}
      ∂muI 12740 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12740 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12740 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12740) c
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

end BstLean.Part266.Row12740

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12740
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12740 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12740)
    (p : Ix 12740 × (Fin (12740 - 1) → ℝ)) :
    sgA (paperDesignP 12740) c p.1 p.2 ^ 2 ≤
      (2 / (12740 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12740).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12740) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12740 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12740 : ℝ) * _ ≤ 2 / 12740 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12740)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12740}
    (hw : WINDOW (paperDesignP 12740) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12740) c a v ^ 8
      ∂stdGauss (Fin (12740 - 1)) ∂muI 12740 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12740).prod (stdGauss (Fin (12740 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12740) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12740) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12740 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12740) c p.1 p.2)
      (√(2 / (12740 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12740)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12740 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12740) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12740}
    (hw : WINDOW (paperDesignP 12740) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12740) c a v -
      ∫ w, sA (paperDesignP 12740) c a w ∂stdGauss (Fin (12740 - 1))) ^ 2
      ∂stdGauss (Fin (12740 - 1))) ^ 2 ∂muI 12740 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12740) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12740

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12740
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12740}
    (hw : WINDOW (paperDesignP 12740) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12740).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12740) c M H xi)
    (hE : centreEnergy (paperDesignP 12740) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12740 : ℝ))))
    (hprice : massBound 12740 M H xi E u mixtureFloor ≤ 12740 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12740 - 1))).real
      {v | sgA (paperDesignP 12740) c a v < √(2 / (12740 : ℝ) * mixtureFloor)}
        ∂muI 12740 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12740).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12740) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12740) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12740)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12740

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12740
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12740) : ℝ :=
  (latitudeC / eR c) / ((12740 : ℝ) * (12740 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12740) / ((12740 : ℝ) * (12740 - 3))

theorem location_variance_on_event {c : Ret 12740}
    (hw : WINDOW (paperDesignP 12740) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12740) c a v - lbar (paperDesignP 12740) c a) ^ 2
      ∂stdGauss (Fin (12740 - 1))) ^ 2 ∂muI 12740 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12740)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12740}
    (hw : WINDOW (paperDesignP 12740) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12740) c a v - gbar (paperDesignP 12740) c a) ^ 2
      ∂stdGauss (Fin (12740 - 1))) ^ 2 ∂muI 12740 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12740)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12740}
    (hw : WINDOW (paperDesignP 12740) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12740 - 1))).real
      {v | sgA (paperDesignP 12740) c a v < √(2 / (12740 : ℝ) * mixtureFloor)}
      ∂muI 12740 ≤ lowMassBudget) :
    LatMom (paperDesignP 12740) c (√(2 / (12740 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12740

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12740
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

theorem location_budget_cap {c : Ret 12740} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12740 : ℝ) * (12740 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12740 : ℝ) * (12740 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12740 : ℝ) /
      ((12740 : ℝ) * (12740 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12740 : ℝ) * (12740 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12740 ≤ (2 * (16 / 5) / 12740 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12740} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (258403419 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (634774793 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (217739747 / 250000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (2507865057 / 500000000000000) ∧
    residualMomentBudget 6 ≤ (3080318227 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (1690571759 / 200000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12740} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (16433579 / 500000000000000) ∧ residualVarianceBudget ≤ (12093 / 3906250000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12740 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((2507865057 / 500000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12740

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12740
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12740 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12740) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12740) : ℝ :=
  exp (hqKappa * (12740 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5868201 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2934101 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12740} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (217739747 / 62500000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (1690571759 / 50000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (1690571759 / 50000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((1690571759 / 50000000000000) : ℝ) / ((5868201 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11590009 / 500000000) := by
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

theorem hq_location_bounds {c : Ret 12740} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (65779789 / 40000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((217739747 / 62500000000))) / ((5868201 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12740} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12740 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12740 * ((11590009 / 500000000) : ℝ) ^ 2 / 2 + ((65779789 / 40000000)) ^ 2 * (1 + (11590009 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12740 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12740 * ((11590009 / 500000000)) ^ 2 / 2 + ((65779789 / 40000000)) ^ 2 * (1 + (11590009 / 500000000))) := by
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
  have hd : (2 * ((5868201 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (42847969 / 125000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (58750330197 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12740

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12741
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12741 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12741) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12741 : ℝ) * (12741 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12741) /
    ((12741 : ℝ) * (12741 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12741} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12741}
    (hw : WINDOW (paperDesignP 12741) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12741) c a v - lbar (paperDesignP 12741) c a| ^ (2 * q)
      ∂stdGauss (Fin (12741 - 1)) ∂muI 12741 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12741)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12741}
    (hw : WINDOW (paperDesignP 12741) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12741) c a v - gbar (paperDesignP 12741) c a| ^ (2 * q)
      ∂stdGauss (Fin (12741 - 1)) ∂muI 12741 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12741)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12741) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12741}
    (hw : WINDOW (paperDesignP 12741) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12741 - 1))).real
      {v | sgA (paperDesignP 12741) c a v < √(2 / (12741 : ℝ) * mixtureFloor)}
      ∂muI 12741 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12741 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12741 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12741) c
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

end BstLean.Part266.Row12741

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12741
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12741 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12741)
    (p : Ix 12741 × (Fin (12741 - 1) → ℝ)) :
    sgA (paperDesignP 12741) c p.1 p.2 ^ 2 ≤
      (2 / (12741 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12741).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12741) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12741 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12741 : ℝ) * _ ≤ 2 / 12741 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12741)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12741}
    (hw : WINDOW (paperDesignP 12741) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12741) c a v ^ 8
      ∂stdGauss (Fin (12741 - 1)) ∂muI 12741 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12741).prod (stdGauss (Fin (12741 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12741) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12741) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12741 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12741) c p.1 p.2)
      (√(2 / (12741 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12741)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12741 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12741) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12741}
    (hw : WINDOW (paperDesignP 12741) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12741) c a v -
      ∫ w, sA (paperDesignP 12741) c a w ∂stdGauss (Fin (12741 - 1))) ^ 2
      ∂stdGauss (Fin (12741 - 1))) ^ 2 ∂muI 12741 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12741) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12741

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12741
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12741}
    (hw : WINDOW (paperDesignP 12741) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12741).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12741) c M H xi)
    (hE : centreEnergy (paperDesignP 12741) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12741 : ℝ))))
    (hprice : massBound 12741 M H xi E u mixtureFloor ≤ 12741 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12741 - 1))).real
      {v | sgA (paperDesignP 12741) c a v < √(2 / (12741 : ℝ) * mixtureFloor)}
        ∂muI 12741 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12741).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12741) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12741) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12741)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12741

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12741
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12741) : ℝ :=
  (latitudeC / eR c) / ((12741 : ℝ) * (12741 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12741) / ((12741 : ℝ) * (12741 - 3))

theorem location_variance_on_event {c : Ret 12741}
    (hw : WINDOW (paperDesignP 12741) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12741) c a v - lbar (paperDesignP 12741) c a) ^ 2
      ∂stdGauss (Fin (12741 - 1))) ^ 2 ∂muI 12741 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12741)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12741}
    (hw : WINDOW (paperDesignP 12741) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12741) c a v - gbar (paperDesignP 12741) c a) ^ 2
      ∂stdGauss (Fin (12741 - 1))) ^ 2 ∂muI 12741 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12741)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12741}
    (hw : WINDOW (paperDesignP 12741) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12741 - 1))).real
      {v | sgA (paperDesignP 12741) c a v < √(2 / (12741 : ℝ) * mixtureFloor)}
      ∂muI 12741 ≤ lowMassBudget) :
    LatMom (paperDesignP 12741) c (√(2 / (12741 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12741

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12741
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

theorem location_budget_cap {c : Ret 12741} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12741 : ℝ) * (12741 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12741 : ℝ) * (12741 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12741 : ℝ) /
      ((12741 : ℝ) * (12741 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12741 : ℝ) * (12741 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12741 ≤ (2 * (16 / 5) / 12741 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12741} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (516766261 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (317362473 / 500000000000) ∧
    locationMomentBudget c 12 ≤ (435445281 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (1253784871 / 250000000000000) ∧
    residualMomentBudget 6 ≤ (384994433 / 62500000000000) ∧
    residualMomentBudget 12 ≤ (4225931503 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12741} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (32861999 / 1000000000000000) ∧ residualVarianceBudget ≤ (3095079 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12741 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((1253784871 / 250000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12741

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12741
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12741 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12741) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12741) : ℝ :=
  exp (hqKappa * (12741 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5867971 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (1466993 / 250000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12741} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (435445281 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4225931503 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4225931503 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4225931503 / 125000000000000) : ℝ) / ((5867971 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (4635637 / 200000000) := by
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

theorem hq_location_bounds {c : Ret 12741} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1644429979 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((435445281 / 125000000000))) / ((5867971 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12741} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12741 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12741 * ((4635637 / 200000000) : ℝ) ^ 2 / 2 + ((1644429979 / 1000000000)) ^ 2 * (1 + (4635637 / 200000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12741 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12741 * ((4635637 / 200000000)) ^ 2 / 2 + ((1644429979 / 1000000000)) ^ 2 * (1 + (4635637 / 200000000))) := by
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
  have hd : (2 * ((5867971 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (342797033 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (58754882901 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12741

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12742
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12742 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12742) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12742 : ℝ) * (12742 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12742) /
    ((12742 : ℝ) * (12742 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12742} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12742}
    (hw : WINDOW (paperDesignP 12742) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12742) c a v - lbar (paperDesignP 12742) c a| ^ (2 * q)
      ∂stdGauss (Fin (12742 - 1)) ∂muI 12742 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12742)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12742}
    (hw : WINDOW (paperDesignP 12742) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12742) c a v - gbar (paperDesignP 12742) c a| ^ (2 * q)
      ∂stdGauss (Fin (12742 - 1)) ∂muI 12742 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12742)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12742) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12742}
    (hw : WINDOW (paperDesignP 12742) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12742 - 1))).real
      {v | sgA (paperDesignP 12742) c a v < √(2 / (12742 : ℝ) * mixtureFloor)}
      ∂muI 12742 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12742 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12742 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12742) c
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

end BstLean.Part266.Row12742

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12742
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12742 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12742)
    (p : Ix 12742 × (Fin (12742 - 1) → ℝ)) :
    sgA (paperDesignP 12742) c p.1 p.2 ^ 2 ≤
      (2 / (12742 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12742).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12742) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12742 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12742 : ℝ) * _ ≤ 2 / 12742 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12742)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12742}
    (hw : WINDOW (paperDesignP 12742) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12742) c a v ^ 8
      ∂stdGauss (Fin (12742 - 1)) ∂muI 12742 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12742).prod (stdGauss (Fin (12742 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12742) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12742) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12742 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12742) c p.1 p.2)
      (√(2 / (12742 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12742)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12742 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12742) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12742}
    (hw : WINDOW (paperDesignP 12742) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12742) c a v -
      ∫ w, sA (paperDesignP 12742) c a w ∂stdGauss (Fin (12742 - 1))) ^ 2
      ∂stdGauss (Fin (12742 - 1))) ^ 2 ∂muI 12742 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12742) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12742

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12742
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12742}
    (hw : WINDOW (paperDesignP 12742) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12742).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12742) c M H xi)
    (hE : centreEnergy (paperDesignP 12742) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12742 : ℝ))))
    (hprice : massBound 12742 M H xi E u mixtureFloor ≤ 12742 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12742 - 1))).real
      {v | sgA (paperDesignP 12742) c a v < √(2 / (12742 : ℝ) * mixtureFloor)}
        ∂muI 12742 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12742).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12742) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12742) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12742)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12742

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12742
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12742) : ℝ :=
  (latitudeC / eR c) / ((12742 : ℝ) * (12742 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12742) / ((12742 : ℝ) * (12742 - 3))

theorem location_variance_on_event {c : Ret 12742}
    (hw : WINDOW (paperDesignP 12742) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12742) c a v - lbar (paperDesignP 12742) c a) ^ 2
      ∂stdGauss (Fin (12742 - 1))) ^ 2 ∂muI 12742 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12742)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12742}
    (hw : WINDOW (paperDesignP 12742) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12742) c a v - gbar (paperDesignP 12742) c a) ^ 2
      ∂stdGauss (Fin (12742 - 1))) ^ 2 ∂muI 12742 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12742)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12742}
    (hw : WINDOW (paperDesignP 12742) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12742 - 1))).real
      {v | sgA (paperDesignP 12742) c a v < √(2 / (12742 : ℝ) * mixtureFloor)}
      ∂muI 12742 ≤ lowMassBudget) :
    LatMom (paperDesignP 12742) c (√(2 / (12742 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12742

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12742
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

theorem location_budget_cap {c : Ret 12742} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12742 : ℝ) * (12742 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12742 : ℝ) * (12742 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12742 : ℝ) /
      ((12742 : ℝ) * (12742 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12742 : ℝ) * (12742 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12742 ≤ (2 * (16 / 5) / 12742 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12742} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (516725691 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (634675107 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (870822147 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (5014548969 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (1231837109 / 200000000000000) ∧
    residualMomentBudget 12 ≤ (2112716853 / 250000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12742} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (821421 / 25000000000000) ∧ residualVarianceBudget ≤ (61887 / 20000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12742 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((5014548969 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12742

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12742
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12742 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12742) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12742) : ℝ :=
  exp (hqKappa * (12742 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5867741 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (2933871 / 500000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12742} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (870822147 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (2112716853 / 62500000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (2112716853 / 62500000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((2112716853 / 62500000000000) : ℝ) / ((5867741 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (23176353 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 12742} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1644365249 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((870822147 / 250000000000))) / ((5867741 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12742} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12742 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12742 * ((23176353 / 1000000000) : ℝ) ^ 2 / 2 + ((1644365249 / 1000000000)) ^ 2 * (1 + (23176353 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12742 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12742 * ((23176353 / 1000000000)) ^ 2 / 2 + ((1644365249 / 1000000000)) ^ 2 * (1 + (23176353 / 1000000000))) := by
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
  have hd : (2 * ((5867741 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (85702579 / 250000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (1175188723 / 10000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12742

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12743
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12743 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12743) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12743 : ℝ) * (12743 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12743) /
    ((12743 : ℝ) * (12743 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12743} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12743}
    (hw : WINDOW (paperDesignP 12743) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12743) c a v - lbar (paperDesignP 12743) c a| ^ (2 * q)
      ∂stdGauss (Fin (12743 - 1)) ∂muI 12743 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12743)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12743}
    (hw : WINDOW (paperDesignP 12743) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12743) c a v - gbar (paperDesignP 12743) c a| ^ (2 * q)
      ∂stdGauss (Fin (12743 - 1)) ∂muI 12743 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12743)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12743) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12743}
    (hw : WINDOW (paperDesignP 12743) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12743 - 1))).real
      {v | sgA (paperDesignP 12743) c a v < √(2 / (12743 : ℝ) * mixtureFloor)}
      ∂muI 12743 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12743 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12743 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12743) c
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

end BstLean.Part266.Row12743

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12743
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12743 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12743)
    (p : Ix 12743 × (Fin (12743 - 1) → ℝ)) :
    sgA (paperDesignP 12743) c p.1 p.2 ^ 2 ≤
      (2 / (12743 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12743).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12743) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12743 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12743 : ℝ) * _ ≤ 2 / 12743 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12743)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12743}
    (hw : WINDOW (paperDesignP 12743) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12743) c a v ^ 8
      ∂stdGauss (Fin (12743 - 1)) ∂muI 12743 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12743).prod (stdGauss (Fin (12743 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12743) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12743) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12743 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12743) c p.1 p.2)
      (√(2 / (12743 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12743)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12743 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12743) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12743}
    (hw : WINDOW (paperDesignP 12743) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12743) c a v -
      ∫ w, sA (paperDesignP 12743) c a w ∂stdGauss (Fin (12743 - 1))) ^ 2
      ∂stdGauss (Fin (12743 - 1))) ^ 2 ∂muI 12743 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12743) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12743

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12743
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12743}
    (hw : WINDOW (paperDesignP 12743) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12743).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12743) c M H xi)
    (hE : centreEnergy (paperDesignP 12743) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12743 : ℝ))))
    (hprice : massBound 12743 M H xi E u mixtureFloor ≤ 12743 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12743 - 1))).real
      {v | sgA (paperDesignP 12743) c a v < √(2 / (12743 : ℝ) * mixtureFloor)}
        ∂muI 12743 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12743).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12743) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12743) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12743)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12743

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12743
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12743) : ℝ :=
  (latitudeC / eR c) / ((12743 : ℝ) * (12743 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12743) / ((12743 : ℝ) * (12743 - 3))

theorem location_variance_on_event {c : Ret 12743}
    (hw : WINDOW (paperDesignP 12743) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12743) c a v - lbar (paperDesignP 12743) c a) ^ 2
      ∂stdGauss (Fin (12743 - 1))) ^ 2 ∂muI 12743 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12743)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12743}
    (hw : WINDOW (paperDesignP 12743) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12743) c a v - gbar (paperDesignP 12743) c a) ^ 2
      ∂stdGauss (Fin (12743 - 1))) ^ 2 ∂muI 12743 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12743)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12743}
    (hw : WINDOW (paperDesignP 12743) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12743 - 1))).real
      {v | sgA (paperDesignP 12743) c a v < √(2 / (12743 : ℝ) * mixtureFloor)}
      ∂muI 12743 ≤ lowMassBudget) :
    LatMom (paperDesignP 12743) c (√(2 / (12743 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12743

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12743
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

theorem location_budget_cap {c : Ret 12743} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12743 : ℝ) * (12743 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12743 : ℝ) * (12743 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12743 : ℝ) /
      ((12743 : ℝ) * (12743 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12743 : ℝ) * (12743 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12743 ≤ (2 * (16 / 5) / 12743 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12743} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (516685127 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (158656319 / 250000000000) ∧
    locationMomentBudget c 12 ≤ (435376871 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (5013958571 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (1231692061 / 200000000000000) ∧
    residualMomentBudget 12 ≤ (4224936007 / 500000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12743} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (32851683 / 1000000000000000) ∧ residualVarianceBudget ≤ (1546811 / 500000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12743 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((5013958571 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12743

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12743
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12743 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12743) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12743) : ℝ :=
  exp (hqKappa * (12743 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((5867511 / 1000000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (733439 / 125000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12743} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (435376871 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (4224936007 / 125000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (4224936007 / 125000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((4224936007 / 125000000000000) : ℝ) / ((5867511 / 1000000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (23174521 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 12743} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (1644300533 / 1000000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((435376871 / 125000000000))) / ((5867511 / 1000000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12743} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12743 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12743 * ((23174521 / 1000000000) : ℝ) ^ 2 / 2 + ((1644300533 / 1000000000)) ^ 2 * (1 + (23174521 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12743 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12743 * ((23174521 / 1000000000)) ^ 2 / 2 + ((1644300533 / 1000000000)) ^ 2 * (1 + (23174521 / 1000000000))) := by
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
  have hd : (2 * ((5867511 / 1000000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (342823599 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (7345498743 / 62500) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12743

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12744
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12744 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12744) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12744 : ℝ) * (12744 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12744) /
    ((12744 : ℝ) * (12744 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12744} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12744}
    (hw : WINDOW (paperDesignP 12744) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12744) c a v - lbar (paperDesignP 12744) c a| ^ (2 * q)
      ∂stdGauss (Fin (12744 - 1)) ∂muI 12744 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12744)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12744}
    (hw : WINDOW (paperDesignP 12744) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12744) c a v - gbar (paperDesignP 12744) c a| ^ (2 * q)
      ∂stdGauss (Fin (12744 - 1)) ∂muI 12744 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12744)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12744) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12744}
    (hw : WINDOW (paperDesignP 12744) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12744 - 1))).real
      {v | sgA (paperDesignP 12744) c a v < √(2 / (12744 : ℝ) * mixtureFloor)}
      ∂muI 12744 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12744 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12744 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12744) c
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

end BstLean.Part266.Row12744

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12744
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12744 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12744)
    (p : Ix 12744 × (Fin (12744 - 1) → ℝ)) :
    sgA (paperDesignP 12744) c p.1 p.2 ^ 2 ≤
      (2 / (12744 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12744).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12744) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12744 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12744 : ℝ) * _ ≤ 2 / 12744 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12744)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12744}
    (hw : WINDOW (paperDesignP 12744) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12744) c a v ^ 8
      ∂stdGauss (Fin (12744 - 1)) ∂muI 12744 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12744).prod (stdGauss (Fin (12744 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12744) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12744) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12744 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12744) c p.1 p.2)
      (√(2 / (12744 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12744)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12744 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12744) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12744}
    (hw : WINDOW (paperDesignP 12744) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12744) c a v -
      ∫ w, sA (paperDesignP 12744) c a w ∂stdGauss (Fin (12744 - 1))) ^ 2
      ∂stdGauss (Fin (12744 - 1))) ^ 2 ∂muI 12744 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12744) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12744

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12744
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12744}
    (hw : WINDOW (paperDesignP 12744) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12744).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12744) c M H xi)
    (hE : centreEnergy (paperDesignP 12744) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12744 : ℝ))))
    (hprice : massBound 12744 M H xi E u mixtureFloor ≤ 12744 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12744 - 1))).real
      {v | sgA (paperDesignP 12744) c a v < √(2 / (12744 : ℝ) * mixtureFloor)}
        ∂muI 12744 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12744).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12744) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12744) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12744)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12744

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12744
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12744) : ℝ :=
  (latitudeC / eR c) / ((12744 : ℝ) * (12744 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12744) / ((12744 : ℝ) * (12744 - 3))

theorem location_variance_on_event {c : Ret 12744}
    (hw : WINDOW (paperDesignP 12744) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12744) c a v - lbar (paperDesignP 12744) c a) ^ 2
      ∂stdGauss (Fin (12744 - 1))) ^ 2 ∂muI 12744 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12744)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12744}
    (hw : WINDOW (paperDesignP 12744) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12744) c a v - gbar (paperDesignP 12744) c a) ^ 2
      ∂stdGauss (Fin (12744 - 1))) ^ 2 ∂muI 12744 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12744)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12744}
    (hw : WINDOW (paperDesignP 12744) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12744 - 1))).real
      {v | sgA (paperDesignP 12744) c a v < √(2 / (12744 : ℝ) * mixtureFloor)}
      ∂muI 12744 ≤ lowMassBudget) :
    LatMom (paperDesignP 12744) c (√(2 / (12744 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12744

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12744
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

theorem location_budget_cap {c : Ret 12744} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12744 : ℝ) * (12744 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12744 : ℝ) * (12744 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12744 : ℝ) /
      ((12744 : ℝ) * (12744 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12744 : ℝ) * (12744 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12744 ≤ (2 * (16 / 5) / 12744 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12744} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (516644569 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (634575453 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (870685349 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (156667759 / 31250000000000) ∧
    residualMomentBudget 6 ≤ (3078867603 / 500000000000000) ∧
    residualMomentBudget 12 ≤ (8448876811 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12744} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (32846527 / 1000000000000000) ∧ residualVarianceBudget ≤ (1546447 / 500000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12744 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((156667759 / 31250000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12744

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12744
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12744 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12744) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12744) : ℝ :=
  exp (hqKappa * (12744 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((73341 / 12500000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5867281 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12744} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (870685349 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8448876811 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8448876811 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8448876811 / 250000000000000) : ℝ) / ((73341 / 12500000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (23172693 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 12744} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (822118057 / 500000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((870685349 / 250000000000))) / ((73341 / 12500000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12744} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12744 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12744 * ((23172693 / 1000000000) : ℝ) ^ 2 / 2 + ((822118057 / 500000000)) ^ 2 * (1 + (23172693 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12744 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12744 * ((23172693 / 1000000000)) ^ 2 / 2 + ((822118057 / 500000000)) ^ 2 * (1 + (23172693 / 1000000000))) := by
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
  have hd : (2 * ((73341 / 12500000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (171418471 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (5876856443 / 50000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12744

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12745
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12745 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12745) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12745 : ℝ) * (12745 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12745) /
    ((12745 : ℝ) * (12745 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12745} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12745}
    (hw : WINDOW (paperDesignP 12745) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12745) c a v - lbar (paperDesignP 12745) c a| ^ (2 * q)
      ∂stdGauss (Fin (12745 - 1)) ∂muI 12745 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12745)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12745}
    (hw : WINDOW (paperDesignP 12745) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12745) c a v - gbar (paperDesignP 12745) c a| ^ (2 * q)
      ∂stdGauss (Fin (12745 - 1)) ∂muI 12745 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12745)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12745) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12745}
    (hw : WINDOW (paperDesignP 12745) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12745 - 1))).real
      {v | sgA (paperDesignP 12745) c a v < √(2 / (12745 : ℝ) * mixtureFloor)}
      ∂muI 12745 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12745 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12745 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12745) c
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

end BstLean.Part266.Row12745

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12745
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12745 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12745)
    (p : Ix 12745 × (Fin (12745 - 1) → ℝ)) :
    sgA (paperDesignP 12745) c p.1 p.2 ^ 2 ≤
      (2 / (12745 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12745).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12745) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12745 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12745 : ℝ) * _ ≤ 2 / 12745 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12745)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12745}
    (hw : WINDOW (paperDesignP 12745) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12745) c a v ^ 8
      ∂stdGauss (Fin (12745 - 1)) ∂muI 12745 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12745).prod (stdGauss (Fin (12745 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12745) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12745) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12745 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12745) c p.1 p.2)
      (√(2 / (12745 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12745)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12745 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12745) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12745}
    (hw : WINDOW (paperDesignP 12745) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12745) c a v -
      ∫ w, sA (paperDesignP 12745) c a w ∂stdGauss (Fin (12745 - 1))) ^ 2
      ∂stdGauss (Fin (12745 - 1))) ^ 2 ∂muI 12745 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12745) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12745

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12745
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12745}
    (hw : WINDOW (paperDesignP 12745) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12745).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12745) c M H xi)
    (hE : centreEnergy (paperDesignP 12745) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12745 : ℝ))))
    (hprice : massBound 12745 M H xi E u mixtureFloor ≤ 12745 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12745 - 1))).real
      {v | sgA (paperDesignP 12745) c a v < √(2 / (12745 : ℝ) * mixtureFloor)}
        ∂muI 12745 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12745).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12745) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12745) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12745)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12745

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12745
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12745) : ℝ :=
  (latitudeC / eR c) / ((12745 : ℝ) * (12745 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12745) / ((12745 : ℝ) * (12745 - 3))

theorem location_variance_on_event {c : Ret 12745}
    (hw : WINDOW (paperDesignP 12745) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12745) c a v - lbar (paperDesignP 12745) c a) ^ 2
      ∂stdGauss (Fin (12745 - 1))) ^ 2 ∂muI 12745 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12745)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12745}
    (hw : WINDOW (paperDesignP 12745) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12745) c a v - gbar (paperDesignP 12745) c a) ^ 2
      ∂stdGauss (Fin (12745 - 1))) ^ 2 ∂muI 12745 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12745)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12745}
    (hw : WINDOW (paperDesignP 12745) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12745 - 1))).real
      {v | sgA (paperDesignP 12745) c a v < √(2 / (12745 : ℝ) * mixtureFloor)}
      ∂muI 12745 ≤ lowMassBudget) :
    LatMom (paperDesignP 12745) c (√(2 / (12745 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12745

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12745
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

theorem location_budget_cap {c : Ret 12745} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12745 : ℝ) * (12745 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12745 : ℝ) * (12745 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12745 : ℝ) /
      ((12745 : ℝ) * (12745 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12745 : ℝ) * (12745 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12745 ≤ (2 * (16 / 5) / 12745 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12745} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (258302009 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (634525637 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (435308483 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (5012778121 / 1000000000000000) ∧
    residualMomentBudget 6 ≤ (24628041 / 4000000000000) ∧
    residualMomentBudget 12 ≤ (2111970451 / 250000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12745} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (8210343 / 250000000000000) ∧ residualVarianceBudget ≤ (1546083 / 500000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12745 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((5012778121 / 1000000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12745

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12745
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12745 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12745) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12745) : ℝ :=
  exp (hqKappa * (12745 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((117341 / 20000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5867051 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12745} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (435308483 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (2111970451 / 62500000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (2111970451 / 62500000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((2111970451 / 62500000000000) : ℝ) / ((117341 / 20000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11585431 / 500000000) := by
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

theorem hq_location_bounds {c : Ret 12745} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (164417143 / 100000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((435308483 / 125000000000))) / ((117341 / 20000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12745} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12745 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12745 * ((11585431 / 500000000) : ℝ) ^ 2 / 2 + ((164417143 / 100000000)) ^ 2 * (1 + (11585431 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12745 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12745 * ((11585431 / 500000000)) ^ 2 / 2 + ((164417143 / 100000000)) ^ 2 * (1 + (11585431 / 500000000))) := by
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
  have hd : (2 * ((117341 / 20000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (85712557 / 250000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (14693279829 / 125000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12745

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12746
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12746 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12746) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12746 : ℝ) * (12746 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12746) /
    ((12746 : ℝ) * (12746 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12746} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12746}
    (hw : WINDOW (paperDesignP 12746) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12746) c a v - lbar (paperDesignP 12746) c a| ^ (2 * q)
      ∂stdGauss (Fin (12746 - 1)) ∂muI 12746 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12746)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12746}
    (hw : WINDOW (paperDesignP 12746) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12746) c a v - gbar (paperDesignP 12746) c a| ^ (2 * q)
      ∂stdGauss (Fin (12746 - 1)) ∂muI 12746 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12746)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12746) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12746}
    (hw : WINDOW (paperDesignP 12746) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12746 - 1))).real
      {v | sgA (paperDesignP 12746) c a v < √(2 / (12746 : ℝ) * mixtureFloor)}
      ∂muI 12746 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12746 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12746 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12746) c
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

end BstLean.Part266.Row12746

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12746
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12746 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12746)
    (p : Ix 12746 × (Fin (12746 - 1) → ℝ)) :
    sgA (paperDesignP 12746) c p.1 p.2 ^ 2 ≤
      (2 / (12746 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12746).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12746) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12746 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12746 : ℝ) * _ ≤ 2 / 12746 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12746)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12746}
    (hw : WINDOW (paperDesignP 12746) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12746) c a v ^ 8
      ∂stdGauss (Fin (12746 - 1)) ∂muI 12746 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12746).prod (stdGauss (Fin (12746 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12746) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12746) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12746 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12746) c p.1 p.2)
      (√(2 / (12746 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12746)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12746 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12746) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12746}
    (hw : WINDOW (paperDesignP 12746) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12746) c a v -
      ∫ w, sA (paperDesignP 12746) c a w ∂stdGauss (Fin (12746 - 1))) ^ 2
      ∂stdGauss (Fin (12746 - 1))) ^ 2 ∂muI 12746 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12746) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12746

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12746
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12746}
    (hw : WINDOW (paperDesignP 12746) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12746).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12746) c M H xi)
    (hE : centreEnergy (paperDesignP 12746) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12746 : ℝ))))
    (hprice : massBound 12746 M H xi E u mixtureFloor ≤ 12746 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12746 - 1))).real
      {v | sgA (paperDesignP 12746) c a v < √(2 / (12746 : ℝ) * mixtureFloor)}
        ∂muI 12746 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12746).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12746) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12746) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12746)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12746

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12746
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12746) : ℝ :=
  (latitudeC / eR c) / ((12746 : ℝ) * (12746 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12746) / ((12746 : ℝ) * (12746 - 3))

theorem location_variance_on_event {c : Ret 12746}
    (hw : WINDOW (paperDesignP 12746) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12746) c a v - lbar (paperDesignP 12746) c a) ^ 2
      ∂stdGauss (Fin (12746 - 1))) ^ 2 ∂muI 12746 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12746)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12746}
    (hw : WINDOW (paperDesignP 12746) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12746) c a v - gbar (paperDesignP 12746) c a) ^ 2
      ∂stdGauss (Fin (12746 - 1))) ^ 2 ∂muI 12746 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12746)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12746}
    (hw : WINDOW (paperDesignP 12746) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12746 - 1))).real
      {v | sgA (paperDesignP 12746) c a v < √(2 / (12746 : ℝ) * mixtureFloor)}
      ∂muI 12746 ≤ lowMassBudget) :
    LatMom (paperDesignP 12746) c (√(2 / (12746 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12746

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12746
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

theorem location_budget_cap {c : Ret 12746} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12746 : ℝ) * (12746 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12746 : ℝ) * (12746 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12746 : ℝ) /
      ((12746 : ℝ) * (12746 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12746 : ℝ) * (12746 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12746 ≤ (2 * (16 / 5) / 12746 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12746} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (516563473 / 1000000000000) ∧
    locationMomentBudget c 6 ≤ (634475829 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (435274297 / 500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (501218807 / 100000000000000) ∧
    residualMomentBudget 6 ≤ (1539071359 / 250000000000000) ∧
    residualMomentBudget 12 ≤ (527930437 / 62500000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12746} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (32836219 / 1000000000000000) ∧ residualVarianceBudget ≤ (1545719 / 500000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12746 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((501218807 / 100000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12746

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12746
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12746 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12746) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12746) : ℝ :=
  exp (hqKappa * (12746 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((293341 / 50000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5866821 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12746} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (435274297 / 125000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (527930437 / 15625000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (527930437 / 15625000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((527930437 / 15625000000000) : ℝ) / ((293341 / 50000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (23169031 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 12746} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (41102669 / 25000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((435274297 / 125000000000))) / ((293341 / 50000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12746} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12746 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12746 * ((23169031 / 1000000000) : ℝ) ^ 2 / 2 + ((41102669 / 25000000)) ^ 2 * (1 + (23169031 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12746 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12746 * ((23169031 / 1000000000)) ^ 2 / 2 + ((41102669 / 25000000)) ^ 2 * (1 + (23169031 / 1000000000))) := by
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
  have hd : (2 * ((293341 / 50000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (68572703 / 200000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (58777674747 / 500000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12746

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12747
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12747 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12747) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12747 : ℝ) * (12747 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12747) /
    ((12747 : ℝ) * (12747 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12747} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12747}
    (hw : WINDOW (paperDesignP 12747) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12747) c a v - lbar (paperDesignP 12747) c a| ^ (2 * q)
      ∂stdGauss (Fin (12747 - 1)) ∂muI 12747 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12747)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12747}
    (hw : WINDOW (paperDesignP 12747) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12747) c a v - gbar (paperDesignP 12747) c a| ^ (2 * q)
      ∂stdGauss (Fin (12747 - 1)) ∂muI 12747 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12747)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12747) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12747}
    (hw : WINDOW (paperDesignP 12747) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12747 - 1))).real
      {v | sgA (paperDesignP 12747) c a v < √(2 / (12747 : ℝ) * mixtureFloor)}
      ∂muI 12747 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12747 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12747 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12747) c
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

end BstLean.Part266.Row12747

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12747
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12747 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12747)
    (p : Ix 12747 × (Fin (12747 - 1) → ℝ)) :
    sgA (paperDesignP 12747) c p.1 p.2 ^ 2 ≤
      (2 / (12747 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12747).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12747) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12747 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12747 : ℝ) * _ ≤ 2 / 12747 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12747)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12747}
    (hw : WINDOW (paperDesignP 12747) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12747) c a v ^ 8
      ∂stdGauss (Fin (12747 - 1)) ∂muI 12747 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12747).prod (stdGauss (Fin (12747 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12747) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12747) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12747 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12747) c p.1 p.2)
      (√(2 / (12747 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12747)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12747 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12747) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12747}
    (hw : WINDOW (paperDesignP 12747) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12747) c a v -
      ∫ w, sA (paperDesignP 12747) c a w ∂stdGauss (Fin (12747 - 1))) ^ 2
      ∂stdGauss (Fin (12747 - 1))) ^ 2 ∂muI 12747 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12747) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12747

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12747
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12747}
    (hw : WINDOW (paperDesignP 12747) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12747).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12747) c M H xi)
    (hE : centreEnergy (paperDesignP 12747) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12747 : ℝ))))
    (hprice : massBound 12747 M H xi E u mixtureFloor ≤ 12747 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12747 - 1))).real
      {v | sgA (paperDesignP 12747) c a v < √(2 / (12747 : ℝ) * mixtureFloor)}
        ∂muI 12747 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12747).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12747) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12747) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12747)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12747

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12747
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12747) : ℝ :=
  (latitudeC / eR c) / ((12747 : ℝ) * (12747 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12747) / ((12747 : ℝ) * (12747 - 3))

theorem location_variance_on_event {c : Ret 12747}
    (hw : WINDOW (paperDesignP 12747) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12747) c a v - lbar (paperDesignP 12747) c a) ^ 2
      ∂stdGauss (Fin (12747 - 1))) ^ 2 ∂muI 12747 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12747)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12747}
    (hw : WINDOW (paperDesignP 12747) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12747) c a v - gbar (paperDesignP 12747) c a) ^ 2
      ∂stdGauss (Fin (12747 - 1))) ^ 2 ∂muI 12747 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12747)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12747}
    (hw : WINDOW (paperDesignP 12747) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12747 - 1))).real
      {v | sgA (paperDesignP 12747) c a v < √(2 / (12747 : ℝ) * mixtureFloor)}
      ∂muI 12747 ≤ lowMassBudget) :
    LatMom (paperDesignP 12747) c (√(2 / (12747 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12747

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12747
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

theorem location_budget_cap {c : Ret 12747} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12747 : ℝ) * (12747 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12747 : ℝ) * (12747 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12747 : ℝ) /
      ((12747 : ℝ) * (12747 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12747 : ℝ) * (12747 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12747 ≤ (2 * (16 / 5) / 12747 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12747} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (258261467 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (634426029 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (108810029 / 125000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (1002319627 / 200000000000000) ∧
    residualMomentBudget 6 ≤ (1231112153 / 200000000000000) ∧
    residualMomentBudget 12 ≤ (67567139 / 8000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12747} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (16415533 / 500000000000000) ∧ residualVarianceBudget ≤ (309071 / 100000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12747 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((1002319627 / 200000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12747

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12747
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12747 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12747) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12747) : ℝ :=
  exp (hqKappa * (12747 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((586659 / 100000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5866591 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12747} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (108810029 / 31250000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (67567139 / 2000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (67567139 / 2000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((67567139 / 2000000000000) : ℝ) / ((586659 / 100000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (23167201 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 12747} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (328808421 / 200000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((108810029 / 31250000000))) / ((586659 / 100000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12747} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12747 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12747 * ((23167201 / 1000000000) : ℝ) ^ 2 / 2 + ((328808421 / 200000000)) ^ 2 * (1 + (23167201 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12747 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12747 * ((23167201 / 1000000000)) ^ 2 / 2 + ((328808421 / 200000000)) ^ 2 * (1 + (23167201 / 1000000000))) := by
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
  have hd : (2 * ((586659 / 100000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (171438401 / 500000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (117564461447 / 1000000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12747

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12748
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12748 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12748) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12748 : ℝ) * (12748 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12748) /
    ((12748 : ℝ) * (12748 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12748} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12748}
    (hw : WINDOW (paperDesignP 12748) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12748) c a v - lbar (paperDesignP 12748) c a| ^ (2 * q)
      ∂stdGauss (Fin (12748 - 1)) ∂muI 12748 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12748)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12748}
    (hw : WINDOW (paperDesignP 12748) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12748) c a v - gbar (paperDesignP 12748) c a| ^ (2 * q)
      ∂stdGauss (Fin (12748 - 1)) ∂muI 12748 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12748)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12748) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12748}
    (hw : WINDOW (paperDesignP 12748) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12748 - 1))).real
      {v | sgA (paperDesignP 12748) c a v < √(2 / (12748 : ℝ) * mixtureFloor)}
      ∂muI 12748 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12748 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12748 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12748) c
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

end BstLean.Part266.Row12748

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12748
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12748 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12748)
    (p : Ix 12748 × (Fin (12748 - 1) → ℝ)) :
    sgA (paperDesignP 12748) c p.1 p.2 ^ 2 ≤
      (2 / (12748 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12748).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12748) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12748 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12748 : ℝ) * _ ≤ 2 / 12748 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12748)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12748}
    (hw : WINDOW (paperDesignP 12748) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12748) c a v ^ 8
      ∂stdGauss (Fin (12748 - 1)) ∂muI 12748 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12748).prod (stdGauss (Fin (12748 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12748) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12748) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12748 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12748) c p.1 p.2)
      (√(2 / (12748 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12748)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12748 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12748) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12748}
    (hw : WINDOW (paperDesignP 12748) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12748) c a v -
      ∫ w, sA (paperDesignP 12748) c a w ∂stdGauss (Fin (12748 - 1))) ^ 2
      ∂stdGauss (Fin (12748 - 1))) ^ 2 ∂muI 12748 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12748) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12748

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12748
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12748}
    (hw : WINDOW (paperDesignP 12748) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12748).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12748) c M H xi)
    (hE : centreEnergy (paperDesignP 12748) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12748 : ℝ))))
    (hprice : massBound 12748 M H xi E u mixtureFloor ≤ 12748 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12748 - 1))).real
      {v | sgA (paperDesignP 12748) c a v < √(2 / (12748 : ℝ) * mixtureFloor)}
        ∂muI 12748 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12748).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12748) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12748) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12748)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12748

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12748
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12748) : ℝ :=
  (latitudeC / eR c) / ((12748 : ℝ) * (12748 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12748) / ((12748 : ℝ) * (12748 - 3))

theorem location_variance_on_event {c : Ret 12748}
    (hw : WINDOW (paperDesignP 12748) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12748) c a v - lbar (paperDesignP 12748) c a) ^ 2
      ∂stdGauss (Fin (12748 - 1))) ^ 2 ∂muI 12748 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12748)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12748}
    (hw : WINDOW (paperDesignP 12748) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12748) c a v - gbar (paperDesignP 12748) c a) ^ 2
      ∂stdGauss (Fin (12748 - 1))) ^ 2 ∂muI 12748 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12748)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12748}
    (hw : WINDOW (paperDesignP 12748) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12748 - 1))).real
      {v | sgA (paperDesignP 12748) c a v < √(2 / (12748 : ℝ) * mixtureFloor)}
      ∂muI 12748 ≤ lowMassBudget) :
    LatMom (paperDesignP 12748) c (√(2 / (12748 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12748

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12748
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

theorem location_budget_cap {c : Ret 12748} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12748 : ℝ) * (12748 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12748 : ℝ) * (12748 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12748 : ℝ) /
      ((12748 : ℝ) * (12748 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12748 : ℝ) * (12748 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12748 ≤ (2 * (16 / 5) / 12748 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12748} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (258241201 / 500000000000) ∧
    locationMomentBudget c 6 ≤ (634376237 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (870411881 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (1252752079 / 250000000000000) ∧
    residualMomentBudget 6 ≤ (1230967247 / 200000000000000) ∧
    residualMomentBudget 12 ≤ (8444897953 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12748} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (6565183 / 200000000000000) ∧ residualVarianceBudget ≤ (3089983 / 1000000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12748 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((1252752079 / 250000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12748

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12748
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12748 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12748) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12748) : ℝ :=
  exp (hqKappa * (12748 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((146659 / 25000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5866361 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12748} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (870411881 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8444897953 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8444897953 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8444897953 / 250000000000000) : ℝ) / ((146659 / 25000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (23165371 / 1000000000) := by
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

theorem hq_location_bounds {c : Ret 12748} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (328795493 / 200000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((870411881 / 250000000000))) / ((146659 / 25000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12748} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12748 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12748 * ((23165371 / 1000000000) : ℝ) ^ 2 / 2 + ((328795493 / 200000000)) ^ 2 * (1 + (23165371 / 1000000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12748 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12748 * ((23165371 / 1000000000)) ^ 2 / 2 + ((328795493 / 200000000)) ^ 2 * (1 + (23165371 / 1000000000))) := by
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
  have hd : (2 * ((146659 / 25000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (342890091 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (11757357449 / 100000) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12748

/-! The paid latitude event supplies all centered moments used by the original split. -/
namespace BstLean.Part266.Row12749
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part195 BstLean.Part212

noncomputable def latitudeC : ℝ := freshLatitudeConstant160 12749 4 (55 / 100)

noncomputable def locationMomentBudget (c : Ret 12749) (q : ℕ) : ℝ :=
  rotationConstant q * √((latitudeC / eR c) /
    ((12749 : ℝ) * (12749 - 1 - 2 * q)))

noncomputable def residualMomentBudget (q : ℕ) : ℝ :=
  rotationConstant q * √((2 * latitudeC / 12749) /
    ((12749 : ℝ) * (12749 - 1 - 2 * q)))

theorem locationMomentBudget_pos {c : Ret 12749} (he : 0 < eR c)
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

theorem location_moment_on_event {c : Ret 12749}
    (hw : WINDOW (paperDesignP 12749) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |lA (paperDesignP 12749) c a v - lbar (paperDesignP 12749) c a| ^ (2 * q)
      ∂stdGauss (Fin (12749 - 1)) ∂muI 12749 ≤ locationMomentBudget c q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_lambda (by norm_num) (paperDesignP 12749)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL hq hq12

theorem residual_moment_on_event {c : Ret 12749}
    (hw : WINDOW (paperDesignP 12749) c) (hc : c ∈ passEvent)
    {q : ℕ} (hq : 1 ≤ q) (hq12 : q ≤ 12) :
    ∫ a, ∫ v, |sgA (paperDesignP 12749) c a v - gbar (paperDesignP 12749) c a| ^ (2 * q)
      ∂stdGauss (Fin (12749 - 1)) ∂muI 12749 ≤ residualMomentBudget q ^ (2 * q) := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  exact fresh_LG_residual (by norm_num) (paperDesignP 12749)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL hq hq12

noncomputable def splitLocationWidth (c : Ret 12749) : ℝ := 4 * locationMomentBudget c 12
noncomputable def splitResidualWidth : ℝ := 4 * residualMomentBudget 12
noncomputable def lowMassBudget : ℝ := 5 / 10 ^ 12

theorem removal_of_low_mass {c : Ret 12749}
    (hw : WINDOW (paperDesignP 12749) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12749 - 1))).real
      {v | sgA (paperDesignP 12749) c a v < √(2 / (12749 : ℝ) * mixtureFloor)}
      ∂muI 12749 ≤ lowMassBudget) :
    ∫ a, removed (stdGauss (Fin (12749 - 1)))
      (rowSplit c (splitLocationWidth c) splitResidualWidth).good a ∂muI 12749 ≤
        removalBudget := by
  have hl := locationMomentBudget_pos he (by norm_num : 12 ≤ 12)
  have hs := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  have h := int_removed (by norm_num) (paperDesignP 12749) c
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

end BstLean.Part266.Row12749

/-! The existing energy and latitude events supply the scale-variance field of LatMom. -/
namespace BstLean.Part266.Row12749
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242

noncomputable def fullResidualBudget : ℝ := √(2 / (12749 : ℝ)) * locationNorm

theorem residual_sq_le_energy (c : Ret 12749)
    (p : Ix 12749 × (Fin (12749 - 1) → ℝ)) :
    sgA (paperDesignP 12749) c p.1 p.2 ^ 2 ≤
      (2 / (12749 : ℝ)) * wLatitude c p := by
  have hh := BstLean.Part162.normSq_res_le ((paperDesignP 12749).bA c.1 c.2.1.1)
    (hid2 (A1 c) (A2 c) (xLat c (latC (paperDesignP 12749) c p.1)
      (BstLean.Part53.unitF53 p.2)))
  unfold sgA sigX BstLean.Part134.sig
  rw [mul_pow, sq_sqrt (by norm_num [mA] : (0 : ℝ) ≤ 2 / (mA 12749 : ℝ)),
    sq_sqrt (normSq_nonneg _)]
  change 2 / (mA 12749 : ℝ) * _ ≤ 2 / 12749 *
    (normSq (hid2 (A1 c) (A2 c) _) / 12749)
  norm_num [mA]
  linarith

theorem full_residual_eighth {c : Ret 12749}
    (hw : WINDOW (paperDesignP 12749) c) (hc : c ∈ passEvent) :
    ∫ a, ∫ v, sgA (paperDesignP 12749) c a v ^ 8
      ∂stdGauss (Fin (12749 - 1)) ∂muI 12749 ≤ fullResidualBudget ^ 8 := by
  let μ := (muI 12749).prod (stdGauss (Fin (12749 - 1)))
  have hE := BstLean.Part222.energyMoment_on_event (by norm_num)
    (paperDesignP 12749) c (hc.1.1.1.1 hw.2.1)
  have h32 := energy_latitude_norm (by norm_num) c hw.1 hw.2.1 hE
  have h8 : LBound μ 8 (fun p => |√(wLatitude c p) - 1|)
      (BstLean.Part222.energyAllowance 12749) :=
    h32.lower (by norm_num) (by norm_num) (by norm_num) (by simp [μ])
  have h1 : LBound μ 8 (fun _ => (1 : ℝ)) 1 :=
    LBound.const (by norm_num : (8 : ℕ) ≠ 0) (by simp [μ]) (by norm_num)
  have hn := (h1.add (by norm_num) h8).scale (by norm_num : (8 : ℕ) ≠ 0)
    (sqrt_nonneg (2 / (12749 : ℝ)))
  have hs : LBound μ 8 (fun p => sgA (paperDesignP 12749) c p.1 p.2)
      (√(2 / (12749 : ℝ)) * (1 + BstLean.Part222.energyAllowance 12749)) := by
    apply hn.mono (measurable_sgA _ c)
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_of_nonneg (sgA_nonneg _ _ _ _), abs_of_nonneg (by positivity)]
    have hh := sqrt_le_sqrt (residual_sq_le_energy c p)
    rw [sqrt_sq_eq_abs, abs_of_nonneg (sgA_nonneg _ _ _ _), sqrt_mul (by norm_num)] at hh
    have ht := mul_le_mul_of_nonneg_left (le_abs_self (√(wLatitude c p) - 1))
      (sqrt_nonneg (2 / (12749 : ℝ)))
    nlinarith
  have hs' : LBound μ 8 (fun p => sgA (paperDesignP 12749) c p.1 p.2) fullResidualBudget := by
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

theorem scale_variance_on_event {c : Ret 12749}
    (hw : WINDOW (paperDesignP 12749) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sA (paperDesignP 12749) c a v -
      ∫ w, sA (paperDesignP 12749) c a w ∂stdGauss (Fin (12749 - 1))) ^ 2
      ∂stdGauss (Fin (12749 - 1))) ^ 2 ∂muI 12749 ≤ scaleVarianceBudget ^ 2 :=
  int_VS_le (by norm_num) (paperDesignP 12749) c
    (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
    (by unfold fullResidualBudget locationNorm; positivity)
    (residual_moment_on_event hw hc (by norm_num : 1 ≤ 4) (by norm_num))
    (full_residual_eighth hw hc)

end BstLean.Part266.Row12749

/-! The sharp residual-mass interface supplies the low-mass input of the chosen split. -/
namespace BstLean.Part266.Row12749
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222

theorem low_mass_of_interfaces {c : Ret 12749}
    (hw : WINDOW (paperDesignP 12749) c) (he : 0 < eR c)
    (hb0 : ∀ j, 0 ≤ (paperDesignP 12749).bA c.1 c.2.1.1 j)
    {M H xi E u : ℝ} (hI : WFInterfaces (paperDesignP 12749) c M H xi)
    (hE : centreEnergy (paperDesignP 12749) c ≤ E)
    (hu : 0 < u) (hu1 : u < 1) (hd : mixtureFloor < (1 - u) ^ 2)
    (hg : 0 < √((1 - u) ^ 2 - mixtureFloor) - (√E + √(xi / (12749 : ℝ))))
    (hprice : massBound 12749 M H xi E u mixtureFloor ≤ 12749 * lowMassBudget) :
    ∫ a, (stdGauss (Fin (12749 - 1))).real
      {v | sgA (paperDesignP 12749) c a v < √(2 / (12749 : ℝ) * mixtureFloor)}
        ∂muI 12749 ≤ lowMassBudget := by
  have hb : 0 < normSq ((paperDesignP 12749).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    unfold eR at he
    exact (div_pos_iff.mp he).elim (fun h => h.1) (fun h => by norm_num at h)
  have hm := sharp_residual_mass (by norm_num) (paperDesignP 12749) c hw.2.1 hb hb0
    hI hE hu hu1 hd hg
  have hl := latitude_mass_of_MASS (by norm_num) (paperDesignP 12749) c hw.1 hw.2.1
    (by norm_num [mixtureFloor]) hm
  exact hl.trans ((div_le_div_of_nonneg_right hprice (by norm_num : (0 : ℝ) ≤ 12749)).trans
    (by ring_nf; exact le_rfl))

end BstLean.Part266.Row12749

/-! A complete latitude-moment structure, conditional only on the low residual mass. -/
namespace BstLean.Part266.Row12749
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part212

noncomputable def locationVarianceBudget (c : Ret 12749) : ℝ :=
  (latitudeC / eR c) / ((12749 : ℝ) * (12749 - 3))

noncomputable def residualVarianceBudget : ℝ :=
  (2 * latitudeC / 12749) / ((12749 : ℝ) * (12749 - 3))

theorem location_variance_on_event {c : Ret 12749}
    (hw : WINDOW (paperDesignP 12749) c) (he : 0 < eR c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (lA (paperDesignP 12749) c a v - lbar (paperDesignP 12749) c a) ^ 2
      ∂stdGauss (Fin (12749 - 1))) ^ 2 ∂muI 12749 ≤ locationVarianceBudget c ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_lambda (by norm_num) (paperDesignP 12749)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row he hL
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  apply (sqrt_le_iff.mp hh).2

theorem residual_variance_on_event {c : Ret 12749}
    (hw : WINDOW (paperDesignP 12749) c) (hc : c ∈ passEvent) :
    ∫ a, (∫ v, (sgA (paperDesignP 12749) c a v - gbar (paperDesignP 12749) c a) ^ 2
      ∂stdGauss (Fin (12749 - 1))) ^ 2 ∂muI 12749 ≤ residualVarianceBudget ^ 2 := by
  have hL := freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hh := fresh_LG_variance_residual (by norm_num) (paperDesignP 12749)
    (paperDesign_agentCentre _ _ _ _) c fresh_latitude_constant_pos_row hL
  exact (sqrt_le_iff.mp hh).2

/-- All twenty-eight fields concern the original retained network and latitude measure. -/
noncomputable def latitudeMoments {c : Ret 12749}
    (hw : WINDOW (paperDesignP 12749) c) (he : 0 < eR c) (hc : c ∈ passEvent)
    (hmass : ∫ a, (stdGauss (Fin (12749 - 1))).real
      {v | sgA (paperDesignP 12749) c a v < √(2 / (12749 : ℝ) * mixtureFloor)}
      ∂muI 12749 ≤ lowMassBudget) :
    LatMom (paperDesignP 12749) c (√(2 / (12749 : ℝ) * mixtureFloor)) 24 where
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

end BstLean.Part266.Row12749

/-! Finite-dimensional rational moment enclosures for the HQ price. -/
namespace BstLean.Part266.Row12749
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

theorem location_budget_cap {c : Ret 12749} (he : (6 / 10 : ℝ) ≤ eR c)
    {q : ℕ} (hq : q ≤ 12) {R b : ℝ} (hR : 0 ≤ R) (hb : 0 ≤ b)
    (hr : rotationConstant q ≤ R)
    (hnum : R ^ 2 * ((16 / 3 : ℝ) / ((12749 : ℝ) * (12749 - 1 - 2 * q))) ≤ b ^ 2) :
    locationMomentBudget c q ≤ b := by
  have he0 : 0 < eR c := by linarith
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12749 : ℝ) * (12749 - 1 - 2 * q) := by nlinarith
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
    (hnum : R ^ 2 * ((2 * (16 / 5) / 12749 : ℝ) /
      ((12749 : ℝ) * (12749 - 1 - 2 * q))) ≤ b ^ 2) : residualMomentBudget q ≤ b := by
  have hC : 0 < latitudeC := fresh_latitude_constant_pos_row
  have hCu : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hqR : (q : ℝ) ≤ 12 := by exact_mod_cast hq
  have hd : 0 < (12749 : ℝ) * (12749 - 1 - 2 * q) := by nlinarith
  have hce : 2 * latitudeC / 12749 ≤ (2 * (16 / 5) / 12749 : ℝ) := by linarith
  apply le_of_pow_le_pow_left₀ (by norm_num : (2 : ℕ) ≠ 0) hb
  unfold residualMomentBudget
  rw [mul_pow, sq_sqrt (by positivity)]
  exact (mul_le_mul (pow_le_pow_left₀ (rotationConstant_nonneg q) hr 2)
    (div_le_div_of_nonneg_right hce hd.le) (by positivity) (sq_nonneg R)).trans hnum

theorem location_budgets_row {c : Ret 12749} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationMomentBudget c 4 ≤ (129110469 / 250000000000) ∧
    locationMomentBudget c 6 ≤ (634326453 / 1000000000000) ∧
    locationMomentBudget c 12 ≤ (870343541 / 1000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact location_budget_cap he (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem residual_budgets_row :
    residualMomentBudget 4 ≤ (1252604653 / 250000000000000) ∧
    residualMomentBudget 6 ≤ (769263981 / 125000000000000) ∧
    residualMomentBudget 12 ≤ (8443903727 / 1000000000000000) := by
  refine ⟨?_, ?_, ?_⟩
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_four (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_six (by norm_num)
  · exact residual_budget_cap (by norm_num) (by norm_num) (by norm_num)
      rotation_twelve (by norm_num)

theorem variance_budgets_row {c : Ret 12749} (he : (6 / 10 : ℝ) ≤ eR c) :
    locationVarianceBudget c ≤ (6564153 / 200000000000000) ∧ residualVarianceBudget ≤ (386157 / 125000000000000000) := by
  have hC : latitudeC ≤ 16 / 5 := latitude_constant_sharp_row
  have hce : latitudeC / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by linarith : 0 < eR c)]
    linarith
  unfold locationVarianceBudget residualVarianceBudget
  constructor <;> linarith

theorem full_residual_budget_row : fullResidualBudget ≤ 1282 / 10 ^ 5 := by
  have hs : √(2 / (12749 : ℝ)) ≤ 12794 / 10 ^ 6 := sqrt_le_iff.mpr (by norm_num)
  unfold fullResidualBudget locationNorm
  linarith

theorem scale_variance_budget_row : scaleVarianceBudget ≤ 188 / 10 ^ 16 := by
  have hs := residual_budgets_row.1
  have hs0 := (residualMomentBudget_pos (by norm_num : 4 ≤ 12)).le
  have hE := full_residual_budget_row
  have hE0 : 0 ≤ fullResidualBudget := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * ((1252604653 / 250000000000000) : ℝ) ^ 2 * (1282 / 10 ^ 5) ^ 2 := by gcongr
    _ ≤ _ := by norm_num

end BstLean.Part266.Row12749

/-! Scalar guards for the original good-transverse split. -/
namespace BstLean.Part266.Row12749
open BstLean.Part252
open Real
open BstLean.Part157 BstLean.Part169 BstLean.Part162

noncomputable def rowSigma : ℝ := √(2 / (12749 : ℝ) * mixtureFloor)
noncomputable def hqCentreCap : ℝ := 1918 / 1000
noncomputable def hqEpsilon : ℝ := eps0 splitResidualWidth rowSigma
noncomputable def hqKappa : ℝ := (1 - hqEpsilon ^ 2)⁻¹
noncomputable def hqLocation (c : Ret 12749) : ℝ :=
  √hqCentreCap * (2 * splitLocationWidth c) / rowSigma
noncomputable def hqExp (c : Ret 12749) : ℝ :=
  exp (hqKappa * (12749 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)))

theorem sigma_bounds : ((586613 / 100000000) : ℝ) ≤ rowSigma ∧ rowSigma ≤ (5866131 / 1000000000) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor]
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor]

theorem sigma_pos : 0 < rowSigma := by linarith [sigma_bounds.1]

theorem split_width_bounds {c : Ret 12749} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < splitLocationWidth c ∧ splitLocationWidth c ≤ (870343541 / 250000000000) ∧
    0 < splitResidualWidth ∧ splitResidualWidth ≤ (8443903727 / 250000000000000) := by
  have hl := (location_budgets_row he).2.2
  have hs := residual_budgets_row.2.2
  have hl0 := locationMomentBudget_pos (by linarith : 0 < eR c) (by norm_num : 12 ≤ 12)
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num) hl0, by linarith,
    mul_pos (by norm_num) hs0, by linarith⟩

theorem residual_width_bounds : 0 < splitResidualWidth ∧ splitResidualWidth ≤ (8443903727 / 250000000000000) := by
  have hs := residual_budgets_row.2.2
  have hs0 := residualMomentBudget_pos (by norm_num : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num) hs0, by linarith⟩

theorem width_ratio_bounds : 0 ≤ splitResidualWidth / rowSigma ∧
    splitResidualWidth / rowSigma ≤ ((8443903727 / 250000000000000) : ℝ) / ((586613 / 100000000)) := by
  refine ⟨div_nonneg residual_width_bounds.1.le sigma_pos.le, ?_⟩
  exact div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) sigma_bounds.1

theorem hq_epsilon_bounds : 0 ≤ hqEpsilon ∧ hqEpsilon ≤ (11581771 / 500000000) := by
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

theorem hq_location_bounds {c : Ret 12749} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ hqLocation c ∧ hqLocation c ≤ (821956421 / 500000000) := by
  have hw := split_width_bounds he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap])
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by linarith [hw.1])) sigma_pos.le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * ((870343541 / 250000000000))) / ((586613 / 100000000)) := by
      apply div_le_div₀ (by positivity) _ (by norm_num) sigma_bounds.1
      exact mul_le_mul hs (by linarith [hw.2.1]) (by linarith [hw.1]) (by norm_num)
    _ ≤ _ := by norm_num

theorem hq_exponential_bounds {c : Ret 12749} (he : (6 / 10 : ℝ) ≤ eR c) :
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
  have hb : 12749 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon) ≤
      12749 * ((11581771 / 500000000) : ℝ) ^ 2 / 2 + ((821956421 / 500000000)) ^ 2 * (1 + (11581771 / 500000000)) := by
    exact add_le_add (by linarith) (mul_le_mul hL2 (by linarith) (by linarith) (by norm_num))
  have hcap : hqKappa * (12749 * hqEpsilon ^ 2 / 2 + hqLocation c ^ 2 * (1 + hqEpsilon)) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12749 * ((11581771 / 500000000)) ^ 2 / 2 + ((821956421 / 500000000)) ^ 2 * (1 + (11581771 / 500000000))) := by
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
  have hd : (2 * ((586613 / 100000000)) * (998 / 1000) : ℝ) ≤ 2 * rowSigma * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left sigma_bounds.1 (by norm_num)) hs
      (by norm_num) (by linarith)
  exact (div_le_div₀ (by norm_num) residual_width_bounds.2 (by norm_num) hd).trans
    (by norm_num)

theorem cE_width_bounds : 0 ≤ cEw splitResidualWidth rowSigma ∧
    cEw splitResidualWidth rowSigma ≤ (342903381 / 1000000) := by
  have hσ0 := sigma_pos
  have hw0 := residual_width_bounds.1
  have hσ := sigma_bounds
  have hw := residual_width_bounds.2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

theorem cV_width_bounds : 0 ≤ cVw splitResidualWidth rowSigma ∧
    cVw splitResidualWidth rowSigma ≤ (7348918039 / 62500) := by
  have hσ0 := sigma_pos
  have hr := width_ratio_bounds
  have hσ := sigma_bounds
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  nlinarith

end BstLean.Part266.Row12749
