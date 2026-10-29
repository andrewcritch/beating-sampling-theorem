-- Dimension arguments made explicit by p285-interval-explicit.py.
import BstLean.Part285IntervalPilotA
import BstLean.Part285IntervalRoot14125


/-! HQ estimates for every dimension in 14425–14724. Generated from a band record. -/
namespace BstLean.Part285.Interval.HQ14425
open MeasureTheory Real
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part134 BstLean.Part157 BstLean.Part160 BstLean.Part161
open BstLean.Part130 BstLean.Part150 BstLean.Part157 BstLean.Part156 BstLean.Part164
open BstLean.Part130 BstLean.Part152 BstLean.Part212
open BstLean.Part130 BstLean.Part153 BstLean.Part154 BstLean.Part157 BstLean.Part160
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part169
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part162 BstLean.Part169
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part130 BstLean.Part157 BstLean.Part169 BstLean.Part206
open BstLean.Part150 (c1F c2F)
open BstLean.Part156
open BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part157 BstLean.Part169
open BstLean.Part157 BstLean.Part169 BstLean.Part162
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part180
open BstLean.Part157 BstLean.Part169 BstLean.Part162 BstLean.Part195
open BstLean.Part159
open BstLean.Part162 (psiA)
open BstLean.Part162 BstLean.Part169 BstLean.Part188 BstLean.Part222
open BstLean.Part162 BstLean.Part180
open BstLean.Part169
open BstLean.Part169 BstLean.Part195 BstLean.Part212
open BstLean.Part169 BstLean.Part212
open BstLean.Part169 BstLean.Part242
open BstLean.Part195 BstLean.Part222
open BstLean.Part211
open BstLean.Part212
open BstLean.Part220 BstLean.Part223 BstLean.Part242
open BstLean.Part29 (stdGauss)
open BstLean.Part53 (unitF53)
open Real
open Real MeasureTheory
open Real Set
open scoped ENNReal
open BstLean.Part285.Interval.PilotA
open BstLean.Part252 (positiveOutputEvent)
variable {n : ℕ} [Fact (14425 ≤ n ∧ n ≤ 14724)]

local instance globalBand : Fact (12000 ≤ n ∧ n ≤ 16199) := by
  have h : 14425 ≤ n ∧ n ≤ 14724 := Fact.out
  exact ⟨by omega⟩

macro "band_bounds14425" : tactic => do
  let n := Lean.mkIdent `n
  let b := Lean.mkIdent `bandBounds
  let l := Lean.mkIdent `bandLower
  let u := Lean.mkIdent `bandUpper
  `(tactic| (have $b : 14425 ≤ $n ∧ $n ≤ 14724 := Fact.out
             have $l : (14425 : ℝ) ≤ $n := by
               exact_mod_cast (Fact.out : 14425 ≤ $n ∧ $n ≤ 14724).1
             have $u : ($n : ℝ) ≤ 14724 := by
               exact_mod_cast (Fact.out : 14425 ≤ $n ∧ $n ≤ 14724).2))

macro "band_num14425" : tactic =>
  `(tactic| (band_bounds14425
             try simp (disch := omega) only [Nat.cast_sub, Nat.cast_ofNat] at *
             try constructor
             all_goals first | omega | positivity | interval_num | (field_simp <;> nlinarith) | nlinarith))

macro "band_linarith14425" : tactic =>
  `(tactic| first | linarith | band_num14425)
macro "band_linarith14425" "[" args:term,* "]" : tactic =>
  `(tactic| first | linarith [$args,*] | band_num14425)
macro "band_nlinarith14425" : tactic =>
  `(tactic| first | nlinarith | band_num14425)
macro "band_nlinarith14425" "[" args:term,* "]" : tactic =>
  `(tactic| first | nlinarith [$args,*] | band_num14425)

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1576077929 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (20865971 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ (295701 / 1000000000000)
  displacement : 0 ≤ D ∧ D ≤ (105429 / 62500000)
  energy_four : 0 ≤ e4 ∧ e4 ≤ (825771 / 500000000)
  location_four : 0 ≤ d4 ∧ d4 ≤ (123105811 / 1000000000)
  energy_six : 0 ≤ e6 ∧ e6 ≤ (2028491 / 1000000000)
  location_six : 0 ≤ d6 ∧ d6 ≤ (75601777 / 500000000)

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ n L ε Exp A D e4 d4 e6 d6 ≤ (8582483 / 1000000000000) := by
  band_bounds14425
  have hκ := h.kappa
  have hL := h.location
  have hε := h.epsilon
  have hX := h.exponential
  have hA := h.energy
  have hD := h.displacement
  have he4 := h.energy_four
  have hd4 := h.location_four
  have he6 := h.energy_six
  have hd6 := h.location_six
  have hκ0 := hκ.1
  have hκ1 := hκ.2
  have hL0 := hL.1
  have hL1 := hL.2
  have hε0 := hε.1
  have hε1 := hε.2
  have hX0 := hX.1
  have hX1 := hX.2
  have hA0 := hA.1
  have hA1 := hA.2
  have hD0 := hD.1
  have hD1 := hD.2
  have he40 := he4.1
  have he41 := he4.2
  have hd40 := hd4.1
  have hd41 := hd4.2
  have he60 := he6.1
  have he61 := he6.2
  have hd60 := hd6.1
  have hd61 := hd6.2
  have hs : √(A * D) ≤ (5583499 / 250000000000) := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num <;> try band_num14425, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num <;> try band_num14425)).trans (by norm_num <;> try band_num14425)
  have hT2 : κ * (n * A / 2 + D + L * √(A * D)) ≤ (487864237 / 125000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (n * ((295701 / 1000000000000)) / 2 +
          (105429 / 62500000) + ((1576077929 / 1000000000)) * ((5583499 / 250000000000))) := by gcongr
      _ ≤ _ := by norm_num <;> try band_num14425
  have hT4 : tK κ n L e4 d4 ≤ (35591560851 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (n / 2 * ((825771 / 500000000)) ^ 2 +
          ((123105811 / 1000000000)) ^ 2 + ((1576077929 / 1000000000)) * ((123105811 / 1000000000)) * ((825771 / 500000000))) := by gcongr
      _ ≤ _ := by norm_num <;> try band_num14425
  have hT6 : tK κ n L e6 d6 ≤ (26846269719 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (n / 2 * ((2028491 / 1000000000)) ^ 2 +
          ((75601777 / 500000000)) ^ 2 + ((1576077929 / 1000000000)) * ((75601777 / 500000000)) * ((2028491 / 1000000000))) := by gcongr
      _ ≤ _ := by norm_num <;> try band_num14425
  have hT20 : 0 ≤ κ * (n * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ n L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ n L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (n * ((295701 / 1000000000000)) ^ 2 / 4 +
        (1 + (20865971 / 1000000000)) * ((295701 / 1000000000000)) * ((105429 / 62500000))) +
      ((487864237 / 125000000000)) ^ 2 / 2 + ((487864237 / 125000000000)) * ((35591560851 / 1000000000000)) ^ 2 / 6 +
      ((35591560851 / 1000000000000)) ^ 4 / 24 + ((35591560851 / 1000000000000)) ^ 2 * ((26846269719 / 500000000000)) ^ 3 / 120 +
      2187 * ((26846269719 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num <;> try band_num14425

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP n ε (85 / 100) (64 / 100) A D e6 d6 ≤ (91957 / 125000000000) := by
  band_bounds14425
  have hε := h.epsilon
  have hA := h.energy
  have hD := h.displacement
  have he6 := h.energy_six
  have hd6 := h.location_six
  have hε0 := hε.1
  have hε1 := hε.2
  have hA0 := hA.1
  have hA1 := hA.2
  have hD0 := hD.1
  have hD1 := hD.2
  have he60 := he6.1
  have he61 := he6.2
  have hd60 := hd6.1
  have hd61 := hd6.2
  have hε1 : 0 < 1 - ε := by band_linarith14425
  have hsA : √A ≤ (108756793 / 200000000000) := sqrt_le_iff.mpr ⟨by norm_num <;> try band_num14425, by band_linarith14425⟩
  have hsD : √D ≤ (20535724969 / 500000000000) := sqrt_le_iff.mpr ⟨by norm_num <;> try band_num14425, by band_linarith14425⟩
  unfold cubP
  calc
    _ ≤ (((n : ℝ) * ((1 + 3 * ((20865971 / 1000000000))) / (4 * (1 - (20865971 / 1000000000))))) ^ 3 *
        (((295701 / 1000000000000)) * ((108756793 / 200000000000)) * ((2028491 / 1000000000)) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (20865971 / 1000000000)))) ^ 3 *
          (((105429 / 62500000)) * ((20535724969 / 500000000000)) * ((75601777 / 500000000)) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (n * ((295701 / 1000000000000)) ^ 2 + 2 * ((295701 / 1000000000000)) * ((105429 / 62500000))) /
        ((1 - (20865971 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num <;> try band_num14425

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ n L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP n ε (85 / 100) (64 / 100) A D e6 d6) ≤ (328473 / 200000000) := by
  band_bounds14425
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num <;> try band_num14425, ?_⟩
  have hc := (fluct_chi_price (n := n)) h
  have hq := (fluct_cubic_price (n := n)) h
  all_goals band_linarith14425

theorem location_budgets_row {c : Ret n} (he : (6 / 10 : ℝ) ≤ eR c) :
    (locationMomentBudget (n := n)) c 4 ≤ ((228209611 / 500000000000)) ∧
    (locationMomentBudget (n := n)) c 6 ≤ ((560592613 / 1000000000000)) ∧
    (locationMomentBudget (n := n)) c 12 ≤ ((769132999 / 1000000000000)) := by
  band_bounds14425
  refine ⟨?_, ?_, ?_⟩
  · exact (location_budget_cap (n := n)) he (by norm_num <;> try band_num14425) (by norm_num <;> try band_num14425) (by norm_num <;> try band_num14425)
      rotation_four (by norm_num <;> try band_num14425)
  · exact (location_budget_cap (n := n)) he (by norm_num <;> try band_num14425) (by norm_num <;> try band_num14425) (by norm_num <;> try band_num14425)
      rotation_six (by norm_num <;> try band_num14425)
  · exact (location_budget_cap (n := n)) he (by norm_num <;> try band_num14425) (by norm_num <;> try band_num14425) (by norm_num <;> try band_num14425)
      rotation_twelve (by norm_num <;> try band_num14425)

theorem residual_budgets_row :
    (residualMomentBudget (n := n)) 4 ≤ ((166516253 / 40000000000000)) ∧
    (residualMomentBudget (n := n)) 6 ≤ ((1278262627 / 250000000000000)) ∧
    (residualMomentBudget (n := n)) 12 ≤ ((7015104689 / 1000000000000000)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact (residual_budget_cap (n := n)) (by norm_num <;> try band_num14425) (by norm_num <;> try band_num14425) (by norm_num <;> try band_num14425)
      rotation_four (by norm_num <;> try band_num14425)
  · exact (residual_budget_cap (n := n)) (by norm_num <;> try band_num14425) (by norm_num <;> try band_num14425) (by norm_num <;> try band_num14425)
      rotation_six (by norm_num <;> try band_num14425)
  · exact (residual_budget_cap (n := n)) (by norm_num <;> try band_num14425) (by norm_num <;> try band_num14425) (by norm_num <;> try band_num14425)
      rotation_twelve (by norm_num <;> try band_num14425)

theorem variance_budgets_row {c : Ret n} (he : (6 / 10 : ℝ) ≤ eR c) :
    (locationVarianceBudget (n := n)) c ≤ ((25636423 / 1000000000000000)) ∧ (residualVarianceBudget (n := n)) ≤ ((1066333 / 500000000000000000)) := by
  band_bounds14425
  have hC : (latitudeC (n := n)) ≤ 16 / 5 := (latitude_constant_sharp_row (n := n))
  have hce : (latitudeC (n := n)) / eR c ≤ 16 / 3 := by
    rw [div_le_iff₀ (by band_linarith14425 : 0 < eR c)]
    all_goals band_linarith14425
  unfold locationVarianceBudget residualVarianceBudget
  constructor
  · exact (div_le_div_of_nonneg_right hce (by band_num14425)).trans (by band_num14425)
  · band_linarith14425

theorem full_residual_budget_row : (fullResidualBudget (n := n)) ≤ ((59 / 5000)) := by
  band_bounds14425
  have hs : √(2 / (n : ℝ)) ≤ ((471 / 40000)) := sqrt_le_iff.mpr (by norm_num <;> try band_num14425)
  unfold fullResidualBudget locationNorm
  all_goals band_linarith14425

theorem scale_variance_budget_row : (scaleVarianceBudget (n := n)) ≤ ((2413 / 250000000000000000)) := by
  have hs := (residual_budgets_row (n := n)).1
  have hs0 := ((residualMomentBudget_pos (n := n)) (by norm_num <;> try band_num14425 : 4 ≤ 12)).le
  have hE := (full_residual_budget_row (n := n))
  have hE0 : 0 ≤ (fullResidualBudget (n := n)) := by unfold fullResidualBudget locationNorm; positivity
  unfold scaleVarianceBudget
  calc
    _ ≤ 4 * (((166516253 / 40000000000000)) : ℝ) ^ 2 * (((59 / 5000))) ^ 2 := by gcongr
    _ ≤ _ := by norm_num <;> try band_num14425

noncomputable def rowSigma : ℝ := √(2 / (n : ℝ) * mixtureFloor)

noncomputable def hqCentreCap : ℝ := (959 / 500)

noncomputable def hqEpsilon : ℝ := eps0 (splitResidualWidth (n := n)) (rowSigma (n := n))

noncomputable def hqKappa : ℝ := (1 - (hqEpsilon (n := n)) ^ 2)⁻¹

noncomputable def hqLocation (c : Ret n) : ℝ :=
  √hqCentreCap * (2 * (splitLocationWidth (n := n)) c) / (rowSigma (n := n))

noncomputable def hqExp (c : Ret n) : ℝ :=
  exp ((hqKappa (n := n)) * (n * (hqEpsilon (n := n)) ^ 2 / 2 + (hqLocation (n := n)) c ^ 2 * (1 + (hqEpsilon (n := n)))))

theorem sigma_bounds : (((5407089 / 1000000000)) : ℝ) ≤ (rowSigma (n := n)) ∧ (rowSigma (n := n)) ≤ ((2731421 / 500000000)) := by
  constructor
  · apply le_sqrt_of_sq_le
    norm_num [mixtureFloor] <;> try band_num14425
  · apply sqrt_le_iff.mpr
    norm_num [mixtureFloor] <;> try band_num14425

theorem sigma_pos : 0 < (rowSigma (n := n)) := by band_linarith14425 [(sigma_bounds (n := n)).1]

theorem split_width_bounds {c : Ret n} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 < (splitLocationWidth (n := n)) c ∧ (splitLocationWidth (n := n)) c ≤ ((769132999 / 250000000000)) ∧
    0 < (splitResidualWidth (n := n)) ∧ (splitResidualWidth (n := n)) ≤ ((7015104689 / 250000000000000)) := by
  band_bounds14425
  have hl := ((location_budgets_row (n := n)) he).2.2
  have hs := (residual_budgets_row (n := n)).2.2
  have hl0 := (locationMomentBudget_pos (n := n)) (by band_linarith14425 : 0 < eR c) (by norm_num <;> try band_num14425 : 12 ≤ 12)
  have hs0 := (residualMomentBudget_pos (n := n)) (by norm_num <;> try band_num14425 : 12 ≤ 12)
  unfold splitLocationWidth splitResidualWidth
  exact ⟨mul_pos (by norm_num <;> try band_num14425) hl0, by band_linarith14425,
    mul_pos (by norm_num <;> try band_num14425) hs0, by band_linarith14425⟩

theorem residual_width_bounds : 0 < (splitResidualWidth (n := n)) ∧ (splitResidualWidth (n := n)) ≤ ((7015104689 / 250000000000000)) := by
  have hs := (residual_budgets_row (n := n)).2.2
  have hs0 := (residualMomentBudget_pos (n := n)) (by norm_num <;> try band_num14425 : 12 ≤ 12)
  unfold splitResidualWidth
  exact ⟨mul_pos (by norm_num <;> try band_num14425) hs0, by band_linarith14425⟩

theorem width_ratio_bounds : 0 ≤ (splitResidualWidth (n := n)) / (rowSigma (n := n)) ∧
    (splitResidualWidth (n := n)) / (rowSigma (n := n)) ≤ (((7015104689 / 250000000000000)) : ℝ) / (((5407089 / 1000000000))) := by
  refine ⟨div_nonneg (residual_width_bounds (n := n)).1.le (sigma_pos (n := n)).le, ?_⟩
  exact div_le_div₀ (by norm_num <;> try band_num14425) (residual_width_bounds (n := n)).2 (by norm_num <;> try band_num14425) (sigma_bounds (n := n)).1

theorem hq_epsilon_bounds : 0 ≤ (hqEpsilon (n := n)) ∧ (hqEpsilon (n := n)) ≤ ((20865971 / 1000000000)) := by
  have hr := (width_ratio_bounds (n := n))
  unfold hqEpsilon eps0
  rw [mul_div_assoc]
  constructor <;> band_nlinarith14425

theorem hq_kappa_bounds : 0 ≤ (hqKappa (n := n)) ∧ (hqKappa (n := n)) ≤ 1001 / 1000 := by
  have he := (hq_epsilon_bounds (n := n))
  have hden : 0 < 1 - (hqEpsilon (n := n)) ^ 2 := by band_nlinarith14425
  refine ⟨inv_nonneg.mpr hden.le, ?_⟩
  unfold hqKappa
  rw [inv_eq_one_div, div_le_iff₀ hden]
  all_goals band_nlinarith14425

theorem hq_location_bounds {c : Ret n} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ (hqLocation (n := n)) c ∧ (hqLocation (n := n)) c ≤ ((1576077929 / 1000000000)) := by
  band_bounds14425
  have hw := (split_width_bounds (n := n)) he
  have hs : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap] <;> try band_num14425)
  have hs0 := sqrt_nonneg hqCentreCap
  unfold hqLocation
  refine ⟨div_nonneg (mul_nonneg hs0 (by band_linarith14425 [hw.1])) (sigma_pos (n := n)).le, ?_⟩
  calc
    _ ≤ (1385 / 1000 : ℝ) * (2 * (((769132999 / 250000000000)))) / (((5407089 / 1000000000))) := by
      apply div_le_div₀ (by positivity) _ (by norm_num <;> try band_num14425) (sigma_bounds (n := n)).1
      exact mul_le_mul hs (by band_linarith14425 [hw.2.1]) (by band_linarith14425 [hw.1]) (by norm_num <;> try band_num14425)
    _ ≤ _ := by norm_num <;> try band_num14425

theorem hq_exponential_bounds {c : Ret n} (he : (6 / 10 : ℝ) ≤ eR c) :
    0 ≤ (hqExp (n := n)) c ∧ (hqExp (n := n)) c ≤ 2187 := by
  band_bounds14425
  have hκ := (hq_kappa_bounds (n := n))
  have hε := (hq_epsilon_bounds (n := n))
  have hL := (hq_location_bounds (n := n)) he
  have hk0 := hκ.1
  have he0 := hε.1
  have hl0 := hL.1
  have hk1 := hκ.2
  have he1 := hε.2
  have hl1 := hL.2
  have hε2 := pow_le_pow_left₀ he0 he1 2
  have hL2 := pow_le_pow_left₀ hl0 hl1 2
  have hb : n * (hqEpsilon (n := n)) ^ 2 / 2 + (hqLocation (n := n)) c ^ 2 * (1 + (hqEpsilon (n := n))) ≤
      n * (((20865971 / 1000000000)) : ℝ) ^ 2 / 2 + (((1576077929 / 1000000000))) ^ 2 * (1 + ((20865971 / 1000000000))) := by
    exact add_le_add (by band_linarith14425) (mul_le_mul hL2 (by band_linarith14425) (by band_linarith14425) (by norm_num <;> try band_num14425))
  have hcap : (hqKappa (n := n)) * (n * (hqEpsilon (n := n)) ^ 2 / 2 + (hqLocation (n := n)) c ^ 2 * (1 + (hqEpsilon (n := n)))) ≤ 7 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (n * (((20865971 / 1000000000))) ^ 2 / 2 + (((1576077929 / 1000000000))) ^ 2 * (1 + ((20865971 / 1000000000)))) := by
        exact mul_le_mul hk1 hb
          (add_nonneg (div_nonneg (mul_nonneg (by norm_num <;> try band_num14425) (sq_nonneg _)) (by norm_num <;> try band_num14425))
            (mul_nonneg (sq_nonneg _) (by band_linarith14425))) (by norm_num <;> try band_num14425)
      _ ≤ _ := by norm_num <;> try band_num14425
  have h7 : exp (7 : ℝ) ≤ 2187 := by
    have h := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le exp_one_lt_three.le 7
    rw [← exp_nat_mul] at h
    norm_num at h ⊢
    exact h
  exact ⟨(exp_pos _).le, (exp_le_exp.mpr hcap).trans h7⟩

theorem inverse_eta_bound : (1 - eta)⁻¹ ≤ (1003 / 1000 : ℝ) := by norm_num [eta] <;> try band_num14425

theorem iota_bounds {p : ℕ} (hp : p = 8 ∨ p = 12) : 0 ≤ iotaP eta p ∧ iotaP eta p ≤ 1001 / 1000 := by
  refine ⟨(iotaP_pos eta_lt_one p).le, ?_⟩
  rcases hp with rfl | rfl
  · apply le_of_pow_le_pow_left₀ (by norm_num <;> try band_num14425 : (8 : ℕ) ≠ 0) (by norm_num <;> try band_num14425 : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num <;> try band_num14425)]
    norm_num [eta] <;> try band_num14425
  · apply le_of_pow_le_pow_left₀ (by norm_num <;> try band_num14425 : (12 : ℕ) ≠ 0) (by norm_num <;> try band_num14425 : (0 : ℝ) ≤ 1001 / 1000)
    rw [iotaP_pow eta_lt_one (by norm_num <;> try band_num14425)]
    norm_num [eta] <;> try band_num14425

theorem c2_eta_bounds : 0 ≤ c2η eta ∧ c2η eta ≤ 52 / 1000 := by
  exact ⟨sqrt_nonneg _, sqrt_le_iff.mpr (by norm_num [eta] <;> try band_num14425)⟩

theorem c3_eta_bounds : 0 ≤ c3η eta (splitResidualWidth (n := n)) (rowSigma (n := n)) ∧
    c3η eta (splitResidualWidth (n := n)) (rowSigma (n := n)) ≤ 32 / 10000 := by
  have hs : (998 / 1000 : ℝ) ≤ √(1 - eta) := le_sqrt_of_sq_le (by norm_num [eta] <;> try band_num14425)
  have hs0 : 0 < √(1 - eta) := by band_linarith14425
  have hσ0 := (sigma_pos (n := n))
  unfold c3η
  refine ⟨div_nonneg (residual_width_bounds (n := n)).1.le (by positivity), ?_⟩
  have hd : (2 * (((5407089 / 1000000000))) * (998 / 1000) : ℝ) ≤ 2 * (rowSigma (n := n)) * √(1 - eta) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_left (sigma_bounds (n := n)).1 (by norm_num <;> try band_num14425)) hs
      (by norm_num <;> try band_num14425) (by band_linarith14425)
  exact (div_le_div₀ (by norm_num <;> try band_num14425) (residual_width_bounds (n := n)).2 (by norm_num <;> try band_num14425) hd).trans
    (by norm_num <;> try band_num14425)

theorem cE_width_bounds : 0 ≤ cEw (splitResidualWidth (n := n)) (rowSigma (n := n)) ∧
    cEw (splitResidualWidth (n := n)) (rowSigma (n := n)) ≤ ((375618251 / 1000000)) := by
  have hσ0 := (sigma_pos (n := n))
  have hw0 := (residual_width_bounds (n := n)).1
  have hσ := (sigma_bounds (n := n))
  have hw := (residual_width_bounds (n := n)).2
  unfold cEw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  all_goals band_nlinarith14425

theorem cV_width_bounds : 0 ≤ cVw (splitResidualWidth (n := n)) (rowSigma (n := n)) ∧
    cVw (splitResidualWidth (n := n)) (rowSigma (n := n)) ≤ ((138238462463 / 1000000)) := by
  have hσ0 := (sigma_pos (n := n))
  have hr := (width_ratio_bounds (n := n))
  have hσ := (sigma_bounds (n := n))
  unfold cVw
  refine ⟨by positivity, ?_⟩
  rw [div_le_iff₀ (sq_pos_of_pos hσ0)]
  all_goals band_nlinarith14425

noncomputable def hqEnergy : ℝ :=
  cVw (splitResidualWidth (n := n)) (rowSigma (n := n)) * ((1 - eta)⁻¹ * (residualVarianceBudget (n := n)))

noncomputable def hqDisplacement (c : Ret n) : ℝ :=
  hqCentreCap / (rowSigma (n := n)) ^ 2 * ((1 - eta)⁻¹ * (locationVarianceBudget (n := n)) c)

noncomputable def hqEnergyMoment (p : ℕ) : ℝ :=
  cEw (splitResidualWidth (n := n)) (rowSigma (n := n)) *
    ((iotaP eta p + c2η eta + c3η eta (splitResidualWidth (n := n)) (rowSigma (n := n))) * (residualMomentBudget (n := n)) (p / 2))

noncomputable def hqLocationMoment (c : Ret n) (p : ℕ) : ℝ :=
  √hqCentreCap / (rowSigma (n := n)) * ((iotaP eta p + c2η eta) * (locationMomentBudget (n := n)) c (p / 2))

theorem hq_price_certificate {c : Ret n} (he : (6 / 10 : ℝ) ≤ eR c) :
    FluctPriceBounds (hqKappa (n := n)) ((hqLocation (n := n)) c) (hqEpsilon (n := n)) ((hqExp (n := n)) c) (hqEnergy (n := n))
      ((hqDisplacement (n := n)) c) ((hqEnergyMoment (n := n)) 8) ((hqLocationMoment (n := n)) c 8)
      ((hqEnergyMoment (n := n)) 12) ((hqLocationMoment (n := n)) c 12) := by
  band_bounds14425
  obtain ⟨hV0, hV1⟩ := (cV_width_bounds (n := n))
  obtain ⟨hE0, hE1⟩ := (cE_width_bounds (n := n))
  obtain ⟨hi80, hi81⟩ := iota_bounds (Or.inl rfl : 8 = 8 ∨ 8 = 12)
  obtain ⟨hi120, hi121⟩ := iota_bounds (Or.inr rfl : 12 = 8 ∨ 12 = 12)
  obtain ⟨hc20, hc21⟩ := c2_eta_bounds
  obtain ⟨hc30, hc31⟩ := (c3_eta_bounds (n := n))
  obtain ⟨hVl, hVs⟩ := (variance_budgets_row (n := n)) he
  obtain ⟨hl4, hl6, hl12⟩ := (location_budgets_row (n := n)) he
  obtain ⟨hs4, hs6, hs12⟩ := (residual_budgets_row (n := n))
  have he0 : 0 < eR c := by band_linarith14425
  have hC : 0 < (latitudeC (n := n)) := (fresh_latitude_constant_pos_row (n := n))
  have hVl0 : 0 ≤ (locationVarianceBudget (n := n)) c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num <;> try band_num14425)
  have hVs0 : 0 ≤ (residualVarianceBudget (n := n)) :=
    div_nonneg (div_nonneg (mul_nonneg (by norm_num <;> try band_num14425) hC.le) (by norm_num <;> try band_num14425)) (by norm_num <;> try band_num14425)
  have hl40 := ((locationMomentBudget_pos (n := n)) he0 (by norm_num <;> try band_num14425 : 4 ≤ 12)).le
  have hl60 := ((locationMomentBudget_pos (n := n)) he0 (by norm_num <;> try band_num14425 : 6 ≤ 12)).le
  have hs40 := ((residualMomentBudget_pos (n := n)) (by norm_num <;> try band_num14425 : 4 ≤ 12)).le
  have hs60 := ((residualMomentBudget_pos (n := n)) (by norm_num <;> try band_num14425 : 6 ≤ 12)).le
  have hinv := inverse_eta_bound
  have hinv0 : 0 ≤ (1 - eta)⁻¹ := by norm_num [eta] <;> try band_num14425
  have hσ0 := (sigma_pos (n := n))
  have hσ := (sigma_bounds (n := n)).1
  have hca0 : 0 ≤ hqCentreCap := by norm_num [hqCentreCap] <;> try band_num14425
  have hroot0 := sqrt_nonneg hqCentreCap
  have hroot : √hqCentreCap ≤ 1385 / 1000 := sqrt_le_iff.mpr (by norm_num [hqCentreCap] <;> try band_num14425)
  have hk := (hq_kappa_bounds (n := n))
  have hloc := (hq_location_bounds (n := n)) he
  have heps := (hq_epsilon_bounds (n := n))
  have hexp := (hq_exponential_bounds (n := n)) he
  simp only [hqEnergy, hqDisplacement, hqEnergyMoment, hqLocationMoment, Nat.reduceDiv]
  generalize cVw (splitResidualWidth (n := n)) (rowSigma (n := n)) = v at *
  generalize cEw (splitResidualWidth (n := n)) (rowSigma (n := n)) = w at *
  generalize (residualVarianceBudget (n := n)) = vs at *
  generalize (locationVarianceBudget (n := n)) c = vl at *
  generalize (residualMomentBudget (n := n)) 4 = s4 at *
  generalize (residualMomentBudget (n := n)) 6 = s6 at *
  generalize (locationMomentBudget (n := n)) c 4 = l4 at *
  generalize (locationMomentBudget (n := n)) c 6 = l6 at *
  generalize iotaP eta 8 = i8 at *
  generalize iotaP eta 12 = i12 at *
  generalize c2η eta = c2 at *
  generalize c3η eta (splitResidualWidth (n := n)) (rowSigma (n := n)) = c3 at *
  generalize (rowSigma (n := n)) = sigma at *
  refine ⟨hk, hloc, heps, hexp,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (((138238462463 / 1000000)) : ℝ) * ((1003 / 1000) * (((1066333 / 500000000000000000)))) := by gcongr
      _ ≤ _ := by norm_num <;> try band_num14425
  · refine ⟨by positivity, ?_⟩
    unfold hqCentreCap
    calc
      _ ≤ ((959 / 500) : ℝ) / (((5407089 / 1000000000))) ^ 2 * ((1003 / 1000) * (((25636423 / 1000000000000000)))) := by
        gcongr
      _ ≤ _ := by norm_num <;> try band_num14425
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (((375618251 / 1000000)) : ℝ) * ((1001 / 1000 + 52 / 1000 + 32 / 10000) * (((166516253 / 40000000000000)))) := by gcongr
      _ ≤ _ := by norm_num <;> try band_num14425
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (((5407089 / 1000000000))) * ((1001 / 1000 + 52 / 1000) * (((228209611 / 500000000000)))) := by
        gcongr
      _ ≤ _ := by norm_num <;> try band_num14425
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (((375618251 / 1000000)) : ℝ) * ((1001 / 1000 + 52 / 1000 + 32 / 10000) * (((1278262627 / 250000000000000)))) := by gcongr
      _ ≤ _ := by norm_num <;> try band_num14425
  · refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (1385 / 1000 : ℝ) / (((5407089 / 1000000000))) * ((1001 / 1000 + 52 / 1000) * (((560592613 / 1000000000000)))) := by
        gcongr
      _ ≤ _ := by norm_num <;> try band_num14425

noncomputable def splitRemovedBudget (c : Ret n) : ℝ :=
  Bpap ((splitLocationWidth (n := n)) c) (splitResidualWidth (n := n)) ((locationMomentBudget (n := n)) c 12)
    ((residualMomentBudget (n := n)) 12) lowMassBudget 24

theorem splitRemovedBudget_bounds {c : Ret n} (he : 0 < eR c) :
    0 ≤ (splitRemovedBudget (n := n)) c ∧ (splitRemovedBudget (n := n)) c ≤ removalBudget := by
  band_bounds14425
  have hl := (locationMomentBudget_pos (n := n)) he (by norm_num <;> try band_num14425 : 12 ≤ 12)
  have hs := (residualMomentBudget_pos (n := n)) (by norm_num <;> try band_num14425 : 12 ≤ 12)
  have hratl : (locationMomentBudget (n := n)) c 12 / (splitLocationWidth (n := n)) c = 1 / 4 := by
    unfold splitLocationWidth
    field_simp [hl.ne']
  have hrats : (residualMomentBudget (n := n)) 12 / (splitResidualWidth (n := n)) = 1 / 4 := by
    unfold splitResidualWidth
    field_simp [hs.ne']
  unfold splitRemovedBudget Bpap
  rw [hratl, hrats]
  norm_num [lowMassBudget, removalBudget, eta] <;> try band_num14425

theorem hq_displacement_root {c : Ret n} (he : (6 / 10 : ℝ) ≤ eR c)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : B ≤ removalBudget) :
    √(Dpap n B hqCentreCap ((locationVarianceBudget (n := n)) c) (scaleVarianceBudget (n := n)) eta (rowSigma (n := n))) ≤
      (115797 / 500000000) := by
  band_bounds14425
  have hroot : √B ≤ 247 / 10 ^ 8 := sqrt_le_iff.mpr ⟨by norm_num <;> try band_num14425,
    hB.trans (by norm_num [removalBudget, eta] <;> try band_num14425)⟩
  have hVl := ((variance_budgets_row (n := n)) he).1
  have hVS := (scale_variance_budget_row (n := n))
  have hC : 0 < (latitudeC (n := n)) := (fresh_latitude_constant_pos_row (n := n))
  have he0 : 0 < eR c := by band_linarith14425
  have hVl0 : 0 ≤ (locationVarianceBudget (n := n)) c :=
    div_nonneg (div_nonneg hC.le he0.le) (by norm_num <;> try band_num14425)
  have hVS0 : 0 ≤ (scaleVarianceBudget (n := n)) :=
    mul_nonneg (mul_nonneg (by norm_num <;> try band_num14425) (sq_nonneg _)) (sq_nonneg _)
  have hσ0 := (sigma_pos (n := n))
  have hσ := (sigma_bounds (n := n)).1
  have hη0 : 0 < 1 - eta := by norm_num [eta] <;> try band_num14425
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num <;> try band_num14425, ?_⟩
  unfold Dpap hqCentreCap
  generalize (locationVarianceBudget (n := n)) c = vl at *
  generalize (scaleVarianceBudget (n := n)) = vs at *
  generalize (rowSigma (n := n)) = sigma at *
  calc
    _ ≤ (247 / 10 ^ 8 : ℝ) * (((959 / 500)) * (((25636423 / 1000000000000000))) /
        (2 * (1 - eta) * (((5407089 / 1000000000))) ^ 2) +
        n * (((2413 / 250000000000000000))) / (8 * (1 - eta) ^ 2 * (((5407089 / 1000000000))) ^ 4)) := by
      gcongr <;> norm_num <;> try band_num14425
    _ ≤ _ := by norm_num [eta] <;> try band_num14425

theorem hq_root_price {c : Ret n} (he : (6 / 10 : ℝ) ≤ eR c)
    (hw : BstLean.Part161.WINDOW (paperDesignP n) c) (hc : c ∈ (passEvent (n := n)))
    (hmass : ∫ a, (BstLean.Part29.stdGauss (Fin (n - 1))).real
      {v | sgA (paperDesignP n) c a v < (rowSigma (n := n))} ∂BstLean.Part161.muI n ≤ lowMassBudget) :
    rootFLH ((splitLocationWidth (n := n)) c) (splitResidualWidth (n := n)) eta hqCentreCap (85 / 100) (64 / 100)
      ((latitudeMoments (n := n)) hw (by band_linarith14425) hc hmass) ≤ (48549 / 25000000) := by
  band_bounds14425
  have he0 : 0 < eR c := by band_linarith14425
  have hB := (splitRemovedBudget_bounds (n := n)) he0
  have hr : √(2 * (1 + eta⁻¹) * (splitRemovedBudget (n := n)) c) ≤ 68 / 10 ^ 6 := by
    rw [← removal_root]
    apply sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hB.2 (by norm_num [eta] <;> try band_num14425)
  have hm := (fluct_mixture_root (n := n)) ((hq_price_certificate (n := n)) he)
  have hd := (hq_displacement_root (n := n)) he hB.1 hB.2
  change √(2 * (1 + eta⁻¹) * (splitRemovedBudget (n := n)) c) +
    √(priceC (hqKappa (n := n)) n ((hqLocation (n := n)) c) (hqEpsilon (n := n)) ((hqExp (n := n)) c) (hqEnergy (n := n)) ((hqDisplacement (n := n)) c)
      ((hqEnergyMoment (n := n)) 8) ((hqLocationMoment (n := n)) c 8) ((hqEnergyMoment (n := n)) 12) ((hqLocationMoment (n := n)) c 12) / 4 +
      3 / 4 * cubP n (hqEpsilon (n := n)) (85 / 100) (64 / 100) (hqEnergy (n := n)) ((hqDisplacement (n := n)) c)
        ((hqEnergyMoment (n := n)) 12) ((hqLocationMoment (n := n)) c 12)) +
      √(Dpap n ((splitRemovedBudget (n := n)) c) hqCentreCap ((locationVarianceBudget (n := n)) c)
        (scaleVarianceBudget (n := n)) eta (rowSigma (n := n))) ≤ _
  all_goals band_linarith14425

def LowResidualMass (c : Ret n) : Prop :=
  ∫ a, (stdGauss (Fin (n - 1))).real
    {v | sgA (paperDesignP n) c a v < (rowSigma (n := n))} ∂muI n ≤ lowMassBudget

noncomputable def hqSplit (c : Ret n) : SplitData n :=
  (rowSplit (n := n)) c ((splitLocationWidth (n := n)) c) (splitResidualWidth (n := n))

theorem hq_output_bounds {c : Ret n}
    (hw : WINDOW (paperDesignP n) c) (ha : c ∈ (analyticBase (n := n)))
    (hp : c ∈ positiveOutputEvent (paperCentres n)) :
    0 < normSq c.2.1.2 ∧ normSq c.2.1.2 ≤ hqCentreCap := by
  band_bounds14425
  have he := (centre_energy_range (n := n)) hw ha
  have hpass := (analyticBaseCertificate (n := n)).pass_fields ha
  have hcap := (pass_centre_of_events (n := n)) c hpass
  have hb : 0 < normSq ((paperCentres n).bA c.1 c.2.1.1) := by
    change 0 < normSq (bR c)
    have he0 : 0 < eR c := by band_linarith14425
    unfold eR at he0
    exact (div_pos_iff.mp he0).elim (fun h => h.1)
      (fun h => by have hn := Nat.cast_nonneg (α := ℝ) n; linarith [h.2])
  refine ⟨hp hb, ?_⟩
  have heq : (2 / (n : ℝ)) * eR c * n * chi = 2 * eR c * chi := by
    have hp : (0 : ℝ) < n := by band_num14425
    field_simp
  rw [heq] at hcap
  norm_num [chi, hqCentreCap] at hcap ⊢
  all_goals band_linarith14425 [he.2]

theorem hq_fluctuation {c : Ret n} (t : ℝ)
    (hw : WINDOW (paperDesignP n) c) (ha : c ∈ (analyticBase (n := n)))
    (hp : c ∈ positiveOutputEvent (paperCentres n)) (hm : (LowResidualMass (n := n)) c) :
    FLUCT_hyp (paperDesignP n) t c ((hqSplit (n := n)) c) ((48549 / 25000000)) := by
  band_bounds14425
  have he := ((centre_energy_range (n := n)) hw ha).1
  have he0 : 0 < eR c := by band_linarith14425
  have hc := (analyticBaseCertificate (n := n)).pass_fields ha
  have ho := (hq_output_bounds (n := n)) hw ha hp
  have hs := (split_width_bounds (n := n)) he
  exact BstLean.Part180.fluct_of_latMom_hq (by norm_num <;> try band_num14425) (paperDesignP n) c t
    hs.1 hs.2.2.1 (sigma_pos (n := n)) eta_pos eta_lt_one ho.1 ho.2
    (by change (hqEpsilon (n := n)) < 1; band_linarith14425 [(hq_epsilon_bounds (n := n)).2] :
      eps0 (splitResidualWidth (n := n)) (rowSigma (n := n)) < 1)
    ((latitudeMoments (n := n)) hw he0 hc hm) (by norm_num <;> try band_num14425 : (0 : ℝ) < 85 / 100)
    (by norm_num <;> try band_num14425) (by norm_num <;> try band_num14425 : (0 : ℝ) < 64 / 100) (by norm_num <;> try band_num14425)
    ((hq_root_price (n := n)) he hw hc hm)

end BstLean.Part285.Interval.HQ14425
