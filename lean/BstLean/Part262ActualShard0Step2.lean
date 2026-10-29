import BstLean.Part262ActualShard0Step1


/-! Rational enclosures for the HQ fluctuation price at dimension 12225. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12225 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12225 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12225 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12225 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12225 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12225 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12225 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12225 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12225 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12225 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12225 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12225 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12225 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12225 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12225 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12225 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12225

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12225 ∧ √12225 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12225 ∧ 1000000 ≤ Jz 12225 := by
  have hr : (1105 / 10 : ℝ) ≤ √12225 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12225 : ℝ) * √12225 ≤ (⌈(12225 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12225
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12225 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12225 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12225 : ℝ) = (⌈(12225 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12225 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12225 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12225) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12225 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12225 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12225 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12225 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12225 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12225 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12225) :
    (12225 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12225 * √(qB 12225))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12225 * √(qB 12225) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12225 : ℝ) * √(qB 12225) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12225) :
    (12225 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12225 * √(qB 12225))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12225 : ℝ) * √(qB 12225) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12225 : ℝ) * (√12225 *
      (c1F (exp (1 / 2) / 12) (Jz 12225) * (186 / 10000) / Jz 12225)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12225)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12225 : ℝ) * (√12225 *
      (c1F (exp (1 / 2) / 12) (Jz 12225) * (186 / 10000) / Jz 12225)) =
      (12225 * (√12225 * c1F (exp (1 / 2) / 12) (Jz 12225)) * (186 / 10000)) /
        Jz 12225 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12225)]
  nlinarith

theorem row_energy_rule :
    (12225 : ℝ) * (12225 *
      (c2F (exp (1 / 2) / 12) (Jz 12225) * (186 / 10000) ^ 2 / Jz 12225)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12225)]
  nlinarith

end BstLean.Part262.Row12225

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12225) (hc : A1 c ∈ BstLean.Part153.Eop 12225) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12225 : ℝ)) ≤ (3197647397 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12225 : ℝ) + 2 * √12225 ≤ (3111533361 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12225 : ℝ) ≤ (55283361 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12225)
    (hc : A1 c ∈ BstLean.Part153.Eop 12225) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12225 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12225 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12225))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12225) (K : Set (Ix 12225)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12225 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12225 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12225) (hw : WINDOW (paperDesignP 12225) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12225)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12225) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12225 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12225 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12225 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12225 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12225) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12225)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12225)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12225

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12225) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12225 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12225) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12225) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12225 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12225 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12225 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12225}
    (hw : WINDOW (paperDesignP 12225) c) (hc : c ∈ tableEvent) (K : Set (Ix 12225)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12225) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12225)) : Prop where
  charge : (retDist (paperCentres 12225)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12225)} (h : TablePayment H) :
    (retDist (paperCentres 12225)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12225)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12225

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12225) (i : Fin 4) (a : Ix 12225) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12225) (a : Ix 12225) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12225) : Prop where
  moment : ∀ i, MomentBound (muI 12225) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12225} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12225) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12225

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12225) : Prop where
  location : LBound (muI 12225) 12
    (fun a => conditionalVariance (stdGauss (Fin (12225 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12225) 12
    (fun a => conditionalVariance (stdGauss (Fin (12225 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12225) (hw : WINDOW (paperDesignP 12225) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12225 4 (55 / 100) /
      (12225 : ℝ) / ((12225 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12225

/-! The dimension-12225 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12225
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12225) (wl ws : ℝ) : SplitData 12225 :=
  BstLean.Part162.dPaper (paperDesignP 12225) c wl ws
    (√(2 / (12225 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12225 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12225 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12225) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12225) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12225 : ℝ)) * eR c * 12225 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12225) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12225 - 1)))
    (rowSplit c wl ws).good a ∂muI 12225 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12225) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12225 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12225) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12225 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12225) c (rowSplit c wl ws),
    hellG2 12225 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12225 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12225} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12225} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12225 t c BstLean.Part259.agent12225.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12225} (R : RootSource t c) :
    |√(QStand (paperDesignP 12225) t c) - √(qTilde (paperDesignP 12225) t c)| ≤
      BstLean.Part259.agent12225.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12225

/-! Rational enclosures for the HQ fluctuation price at dimension 12227. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12227 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12227 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12227 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12227 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12227 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12227 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12227 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12227 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12227 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12227 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12227 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12227 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12227 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12227 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12227 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12227 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12227

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12227 ∧ √12227 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12227 ∧ 1000000 ≤ Jz 12227 := by
  have hr : (1105 / 10 : ℝ) ≤ √12227 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12227 : ℝ) * √12227 ≤ (⌈(12227 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12227
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12227 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12227 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12227 : ℝ) = (⌈(12227 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12227 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12227 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12227) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12227 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12227 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12227 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12227 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12227 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12227 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12227) :
    (12227 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12227 * √(qB 12227))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12227 * √(qB 12227) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12227 : ℝ) * √(qB 12227) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12227) :
    (12227 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12227 * √(qB 12227))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12227 : ℝ) * √(qB 12227) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12227 : ℝ) * (√12227 *
      (c1F (exp (1 / 2) / 12) (Jz 12227) * (186 / 10000) / Jz 12227)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12227)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12227 : ℝ) * (√12227 *
      (c1F (exp (1 / 2) / 12) (Jz 12227) * (186 / 10000) / Jz 12227)) =
      (12227 * (√12227 * c1F (exp (1 / 2) / 12) (Jz 12227)) * (186 / 10000)) /
        Jz 12227 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12227)]
  nlinarith

theorem row_energy_rule :
    (12227 : ℝ) * (12227 *
      (c2F (exp (1 / 2) / 12) (Jz 12227) * (186 / 10000) ^ 2 / Jz 12227)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12227)]
  nlinarith

end BstLean.Part262.Row12227

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12227) (hc : A1 c ∈ BstLean.Part153.Eop 12227) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12227 : ℝ)) ≤ (3197385863 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12227 : ℝ) + 2 * √12227 ≤ (3112037883 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12227 : ℝ) ≤ (55287883 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12227)
    (hc : A1 c ∈ BstLean.Part153.Eop 12227) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12227 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12227 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12227))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12227) (K : Set (Ix 12227)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12227 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12227 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12227) (hw : WINDOW (paperDesignP 12227) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12227)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12227) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12227 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12227 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12227 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12227 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12227) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12227)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12227)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12227

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12227) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12227 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12227) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12227) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12227 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12227 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12227 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12227}
    (hw : WINDOW (paperDesignP 12227) c) (hc : c ∈ tableEvent) (K : Set (Ix 12227)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12227) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12227)) : Prop where
  charge : (retDist (paperCentres 12227)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12227)} (h : TablePayment H) :
    (retDist (paperCentres 12227)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12227)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12227

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12227) (i : Fin 4) (a : Ix 12227) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12227) (a : Ix 12227) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12227) : Prop where
  moment : ∀ i, MomentBound (muI 12227) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12227} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12227) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12227

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12227) : Prop where
  location : LBound (muI 12227) 12
    (fun a => conditionalVariance (stdGauss (Fin (12227 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12227) 12
    (fun a => conditionalVariance (stdGauss (Fin (12227 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12227) (hw : WINDOW (paperDesignP 12227) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12227 4 (55 / 100) /
      (12227 : ℝ) / ((12227 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12227

/-! The dimension-12227 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12227
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12227) (wl ws : ℝ) : SplitData 12227 :=
  BstLean.Part162.dPaper (paperDesignP 12227) c wl ws
    (√(2 / (12227 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12227 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12227 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12227) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12227) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12227 : ℝ)) * eR c * 12227 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12227) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12227 - 1)))
    (rowSplit c wl ws).good a ∂muI 12227 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12227) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12227 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12227) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12227 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12227) c (rowSplit c wl ws),
    hellG2 12227 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12227 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12227} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12227} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12227 t c BstLean.Part259.agent12227.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12227} (R : RootSource t c) :
    |√(QStand (paperDesignP 12227) t c) - √(qTilde (paperDesignP 12227) t c)| ≤
      BstLean.Part259.agent12227.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12227

/-! Rational enclosures for the HQ fluctuation price at dimension 12228. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12228 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12228 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12228 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12228 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12228 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12228 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12228 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12228 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12228 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12228 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12228 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12228 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12228 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12228 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12228 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12228 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12228

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12228 ∧ √12228 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12228 ∧ 1000000 ≤ Jz 12228 := by
  have hr : (1105 / 10 : ℝ) ≤ √12228 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12228 : ℝ) * √12228 ≤ (⌈(12228 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12228
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12228 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12228 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12228 : ℝ) = (⌈(12228 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12228 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12228 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12228) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12228 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12228 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12228 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12228 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12228 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12228 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12228) :
    (12228 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12228 * √(qB 12228))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12228 * √(qB 12228) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12228 : ℝ) * √(qB 12228) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12228) :
    (12228 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12228 * √(qB 12228))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12228 : ℝ) * √(qB 12228) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12228 : ℝ) * (√12228 *
      (c1F (exp (1 / 2) / 12) (Jz 12228) * (186 / 10000) / Jz 12228)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12228)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12228 : ℝ) * (√12228 *
      (c1F (exp (1 / 2) / 12) (Jz 12228) * (186 / 10000) / Jz 12228)) =
      (12228 * (√12228 * c1F (exp (1 / 2) / 12) (Jz 12228)) * (186 / 10000)) /
        Jz 12228 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12228)]
  nlinarith

theorem row_energy_rule :
    (12228 : ℝ) * (12228 *
      (c2F (exp (1 / 2) / 12) (Jz 12228) * (186 / 10000) ^ 2 / Jz 12228)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12228)]
  nlinarith

end BstLean.Part262.Row12228

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12228) (hc : A1 c ∈ BstLean.Part153.Eop 12228) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12228 : ℝ)) ≤ (39965689 / 3125000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12228 : ℝ) + 2 * √12228 ≤ (194518134 / 15625) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12228 : ℝ) ≤ (1727817 / 15625))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12228)
    (hc : A1 c ∈ BstLean.Part153.Eop 12228) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12228 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12228 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12228))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12228) (K : Set (Ix 12228)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12228 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12228 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12228) (hw : WINDOW (paperDesignP 12228) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12228)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12228) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12228 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12228 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12228 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12228 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12228) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12228)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12228)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12228

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12228) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12228 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12228) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12228) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12228 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12228 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12228 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12228}
    (hw : WINDOW (paperDesignP 12228) c) (hc : c ∈ tableEvent) (K : Set (Ix 12228)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12228) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12228)) : Prop where
  charge : (retDist (paperCentres 12228)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12228)} (h : TablePayment H) :
    (retDist (paperCentres 12228)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12228)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12228

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12228) (i : Fin 4) (a : Ix 12228) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12228) (a : Ix 12228) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12228) : Prop where
  moment : ∀ i, MomentBound (muI 12228) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12228} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12228) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12228

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12228) : Prop where
  location : LBound (muI 12228) 12
    (fun a => conditionalVariance (stdGauss (Fin (12228 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12228) 12
    (fun a => conditionalVariance (stdGauss (Fin (12228 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12228) (hw : WINDOW (paperDesignP 12228) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12228 4 (55 / 100) /
      (12228 : ℝ) / ((12228 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12228

/-! The dimension-12228 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12228
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12228) (wl ws : ℝ) : SplitData 12228 :=
  BstLean.Part162.dPaper (paperDesignP 12228) c wl ws
    (√(2 / (12228 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12228 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12228 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12228) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12228) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12228 : ℝ)) * eR c * 12228 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12228) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12228 - 1)))
    (rowSplit c wl ws).good a ∂muI 12228 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12228) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12228 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12228) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12228 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12228) c (rowSplit c wl ws),
    hellG2 12228 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12228 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12228} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12228} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12228 t c BstLean.Part259.agent12228.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12228} (R : RootSource t c) :
    |√(QStand (paperDesignP 12228) t c) - √(qTilde (paperDesignP 12228) t c)| ≤
      BstLean.Part259.agent12228.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12228

/-! Rational enclosures for the HQ fluctuation price at dimension 12229. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12229 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12229 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12229 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12229 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12229 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12229 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12229 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12229 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12229 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12229 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12229 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12229 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12229 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12229 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12229 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12229 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12229

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12229 ∧ √12229 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12229 ∧ 1000000 ≤ Jz 12229 := by
  have hr : (1105 / 10 : ℝ) ≤ √12229 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12229 : ℝ) * √12229 ≤ (⌈(12229 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12229
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12229 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12229 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12229 : ℝ) = (⌈(12229 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12229 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12229 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12229) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12229 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12229 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12229 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12229 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12229 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12229 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12229) :
    (12229 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12229 * √(qB 12229))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12229 * √(qB 12229) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12229 : ℝ) * √(qB 12229) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12229) :
    (12229 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12229 * √(qB 12229))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12229 : ℝ) * √(qB 12229) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12229 : ℝ) * (√12229 *
      (c1F (exp (1 / 2) / 12) (Jz 12229) * (186 / 10000) / Jz 12229)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12229)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12229 : ℝ) * (√12229 *
      (c1F (exp (1 / 2) / 12) (Jz 12229) * (186 / 10000) / Jz 12229)) =
      (12229 * (√12229 * c1F (exp (1 / 2) / 12) (Jz 12229)) * (186 / 10000)) /
        Jz 12229 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12229)]
  nlinarith

theorem row_energy_rule :
    (12229 : ℝ) * (12229 *
      (c2F (exp (1 / 2) / 12) (Jz 12229) * (186 / 10000) ^ 2 / Jz 12229)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12229)]
  nlinarith

end BstLean.Part262.Row12229

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12229) (hc : A1 c ∈ BstLean.Part153.Eop 12229) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12229 : ℝ)) ≤ (3197124393 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12229 : ℝ) + 2 * √12229 ≤ (622508481 / 50000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12229 : ℝ) ≤ (11058481 / 100000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12229)
    (hc : A1 c ∈ BstLean.Part153.Eop 12229) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12229 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12229 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12229))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12229) (K : Set (Ix 12229)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12229 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12229 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12229) (hw : WINDOW (paperDesignP 12229) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12229)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12229) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12229 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12229 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12229 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12229 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12229) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12229)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12229)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12229

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12229) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12229 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12229) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12229) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12229 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12229 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12229 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12229}
    (hw : WINDOW (paperDesignP 12229) c) (hc : c ∈ tableEvent) (K : Set (Ix 12229)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12229) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12229)) : Prop where
  charge : (retDist (paperCentres 12229)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12229)} (h : TablePayment H) :
    (retDist (paperCentres 12229)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12229)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12229

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12229) (i : Fin 4) (a : Ix 12229) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12229) (a : Ix 12229) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12229) : Prop where
  moment : ∀ i, MomentBound (muI 12229) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12229} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12229) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12229

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12229) : Prop where
  location : LBound (muI 12229) 12
    (fun a => conditionalVariance (stdGauss (Fin (12229 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12229) 12
    (fun a => conditionalVariance (stdGauss (Fin (12229 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12229) (hw : WINDOW (paperDesignP 12229) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12229 4 (55 / 100) /
      (12229 : ℝ) / ((12229 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12229

/-! The dimension-12229 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12229
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12229) (wl ws : ℝ) : SplitData 12229 :=
  BstLean.Part162.dPaper (paperDesignP 12229) c wl ws
    (√(2 / (12229 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12229 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12229 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12229) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12229) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12229 : ℝ)) * eR c * 12229 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12229) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12229 - 1)))
    (rowSplit c wl ws).good a ∂muI 12229 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12229) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12229 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12229) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12229 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12229) c (rowSplit c wl ws),
    hellG2 12229 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12229 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12229} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12229} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12229 t c BstLean.Part259.agent12229.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12229} (R : RootSource t c) :
    |√(QStand (paperDesignP 12229) t c) - √(qTilde (paperDesignP 12229) t c)| ≤
      BstLean.Part259.agent12229.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12229

/-! Rational enclosures for the HQ fluctuation price at dimension 12230. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12230 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12230 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12230 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12230 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12230 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12230 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12230 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12230 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12230 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12230 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12230 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12230 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12230 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12230 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12230 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12230 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12230

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12230 ∧ √12230 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12230 ∧ 1000000 ≤ Jz 12230 := by
  have hr : (1105 / 10 : ℝ) ≤ √12230 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12230 : ℝ) * √12230 ≤ (⌈(12230 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12230
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12230 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12230 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12230 : ℝ) = (⌈(12230 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12230 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12230 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12230) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12230 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12230 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12230 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12230 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12230 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12230 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12230) :
    (12230 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12230 * √(qB 12230))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12230 * √(qB 12230) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12230 : ℝ) * √(qB 12230) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12230) :
    (12230 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12230 * √(qB 12230))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12230 : ℝ) * √(qB 12230) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12230 : ℝ) * (√12230 *
      (c1F (exp (1 / 2) / 12) (Jz 12230) * (186 / 10000) / Jz 12230)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12230)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12230 : ℝ) * (√12230 *
      (c1F (exp (1 / 2) / 12) (Jz 12230) * (186 / 10000) / Jz 12230)) =
      (12230 * (√12230 * c1F (exp (1 / 2) / 12) (Jz 12230)) * (186 / 10000)) /
        Jz 12230 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12230)]
  nlinarith

theorem row_energy_rule :
    (12230 : ℝ) * (12230 *
      (c2F (exp (1 / 2) / 12) (Jz 12230) * (186 / 10000) ^ 2 / Jz 12230)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12230)]
  nlinarith

end BstLean.Part262.Row12230

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12230) (hc : A1 c ∈ BstLean.Part153.Eop 12230) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12230 : ℝ)) ≤ (1598496841 / 125000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12230 : ℝ) + 2 * √12230 ≤ (6225589331 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12230 : ℝ) ≤ (110589331 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12230)
    (hc : A1 c ∈ BstLean.Part153.Eop 12230) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12230 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12230 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12230))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12230) (K : Set (Ix 12230)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12230 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12230 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12230) (hw : WINDOW (paperDesignP 12230) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12230)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12230) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12230 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12230 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12230 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12230 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12230) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12230)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12230)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12230

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12230) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12230 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12230) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12230) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12230 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12230 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12230 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12230}
    (hw : WINDOW (paperDesignP 12230) c) (hc : c ∈ tableEvent) (K : Set (Ix 12230)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12230) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12230)) : Prop where
  charge : (retDist (paperCentres 12230)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12230)} (h : TablePayment H) :
    (retDist (paperCentres 12230)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12230)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12230

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12230) (i : Fin 4) (a : Ix 12230) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12230) (a : Ix 12230) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12230) : Prop where
  moment : ∀ i, MomentBound (muI 12230) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12230} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12230) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12230

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12230) : Prop where
  location : LBound (muI 12230) 12
    (fun a => conditionalVariance (stdGauss (Fin (12230 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12230) 12
    (fun a => conditionalVariance (stdGauss (Fin (12230 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12230) (hw : WINDOW (paperDesignP 12230) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12230 4 (55 / 100) /
      (12230 : ℝ) / ((12230 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12230

/-! The dimension-12230 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12230
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12230) (wl ws : ℝ) : SplitData 12230 :=
  BstLean.Part162.dPaper (paperDesignP 12230) c wl ws
    (√(2 / (12230 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12230 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12230 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12230) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12230) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12230 : ℝ)) * eR c * 12230 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12230) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12230 - 1)))
    (rowSplit c wl ws).good a ∂muI 12230 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12230) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12230 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12230) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12230 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12230) c (rowSplit c wl ws),
    hellG2 12230 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12230 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12230} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12230} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12230 t c BstLean.Part259.agent12230.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12230} (R : RootSource t c) :
    |√(QStand (paperDesignP 12230) t c) - √(qTilde (paperDesignP 12230) t c)| ≤
      BstLean.Part259.agent12230.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12230

/-! Rational enclosures for the HQ fluctuation price at dimension 12231. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12231 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12231 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12231 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12231 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12231 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12231 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12231 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12231 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12231 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12231 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12231 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12231 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12231 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12231 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12231 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12231 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12231

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12231 ∧ √12231 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12231 ∧ 1000000 ≤ Jz 12231 := by
  have hr : (1105 / 10 : ℝ) ≤ √12231 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12231 : ℝ) * √12231 ≤ (⌈(12231 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12231
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12231 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12231 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12231 : ℝ) = (⌈(12231 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12231 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12231 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12231) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12231 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12231 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12231 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12231 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12231 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12231 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12231) :
    (12231 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12231 * √(qB 12231))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12231 * √(qB 12231) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12231 : ℝ) * √(qB 12231) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12231) :
    (12231 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12231 * √(qB 12231))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12231 : ℝ) * √(qB 12231) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12231 : ℝ) * (√12231 *
      (c1F (exp (1 / 2) / 12) (Jz 12231) * (186 / 10000) / Jz 12231)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12231)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12231 : ℝ) * (√12231 *
      (c1F (exp (1 / 2) / 12) (Jz 12231) * (186 / 10000) / Jz 12231)) =
      (12231 * (√12231 * c1F (exp (1 / 2) / 12) (Jz 12231)) * (186 / 10000)) /
        Jz 12231 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12231)]
  nlinarith

theorem row_energy_rule :
    (12231 : ℝ) * (12231 *
      (c2F (exp (1 / 2) / 12) (Jz 12231) * (186 / 10000) ^ 2 / Jz 12231)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12231)]
  nlinarith

end BstLean.Part262.Row12231

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12231) (hc : A1 c ∈ BstLean.Part153.Eop 12231) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12231 : ℝ)) ≤ (3196862987 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12231 : ℝ) + 2 * √12231 ≤ (1556523463 / 125000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12231 : ℝ) ≤ (27648463 / 250000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12231)
    (hc : A1 c ∈ BstLean.Part153.Eop 12231) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12231 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12231 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12231))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12231) (K : Set (Ix 12231)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12231 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12231 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12231) (hw : WINDOW (paperDesignP 12231) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12231)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12231) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12231 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12231 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12231 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12231 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12231) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12231)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12231)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12231

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12231) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12231 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12231) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12231) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12231 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12231 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12231 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12231}
    (hw : WINDOW (paperDesignP 12231) c) (hc : c ∈ tableEvent) (K : Set (Ix 12231)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12231) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12231)) : Prop where
  charge : (retDist (paperCentres 12231)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12231)} (h : TablePayment H) :
    (retDist (paperCentres 12231)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12231)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12231

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12231) (i : Fin 4) (a : Ix 12231) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12231) (a : Ix 12231) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12231) : Prop where
  moment : ∀ i, MomentBound (muI 12231) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12231} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12231) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12231

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12231) : Prop where
  location : LBound (muI 12231) 12
    (fun a => conditionalVariance (stdGauss (Fin (12231 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12231) 12
    (fun a => conditionalVariance (stdGauss (Fin (12231 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12231) (hw : WINDOW (paperDesignP 12231) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12231 4 (55 / 100) /
      (12231 : ℝ) / ((12231 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12231

/-! The dimension-12231 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12231
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12231) (wl ws : ℝ) : SplitData 12231 :=
  BstLean.Part162.dPaper (paperDesignP 12231) c wl ws
    (√(2 / (12231 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12231 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12231 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12231) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12231) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12231 : ℝ)) * eR c * 12231 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12231) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12231 - 1)))
    (rowSplit c wl ws).good a ∂muI 12231 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12231) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12231 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12231) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12231 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12231) c (rowSplit c wl ws),
    hellG2 12231 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12231 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12231} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12231} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12231 t c BstLean.Part259.agent12231.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12231} (R : RootSource t c) :
    |√(QStand (paperDesignP 12231) t c) - √(qTilde (paperDesignP 12231) t c)| ≤
      BstLean.Part259.agent12231.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12231

/-! Rational enclosures for the HQ fluctuation price at dimension 12232. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12232 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12232 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12232 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12232 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12232 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12232 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12232 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12232 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12232 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12232 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12232 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12232 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12232 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12232 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12232 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12232 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12232

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12232 ∧ √12232 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12232 ∧ 1000000 ≤ Jz 12232 := by
  have hr : (1105 / 10 : ℝ) ≤ √12232 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12232 : ℝ) * √12232 ≤ (⌈(12232 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12232
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12232 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12232 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12232 : ℝ) = (⌈(12232 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12232 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12232 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12232) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12232 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12232 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12232 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12232 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12232 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12232 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12232) :
    (12232 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12232 * √(qB 12232))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12232 * √(qB 12232) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12232 : ℝ) * √(qB 12232) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12232) :
    (12232 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12232 * √(qB 12232))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12232 : ℝ) * √(qB 12232) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12232 : ℝ) * (√12232 *
      (c1F (exp (1 / 2) / 12) (Jz 12232) * (186 / 10000) / Jz 12232)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12232)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12232 : ℝ) * (√12232 *
      (c1F (exp (1 / 2) / 12) (Jz 12232) * (186 / 10000) / Jz 12232)) =
      (12232 * (√12232 * c1F (exp (1 / 2) / 12) (Jz 12232)) * (186 / 10000)) /
        Jz 12232 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12232)]
  nlinarith

theorem row_energy_rule :
    (12232 : ℝ) * (12232 *
      (c2F (exp (1 / 2) / 12) (Jz 12232) * (186 / 10000) ^ 2 / Jz 12232)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12232)]
  nlinarith

end BstLean.Part262.Row12232

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12232) (hc : A1 c ∈ BstLean.Part153.Eop 12232) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12232 : ℝ)) ≤ (12786929233 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12232 : ℝ) + 2 * √12232 ≤ (6226598373 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12232 : ℝ) ≤ (110598373 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12232)
    (hc : A1 c ∈ BstLean.Part153.Eop 12232) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12232 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12232 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12232))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12232) (K : Set (Ix 12232)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12232 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12232 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12232) (hw : WINDOW (paperDesignP 12232) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12232)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12232) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12232 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12232 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12232 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12232 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12232) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12232)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12232)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12232

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12232) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12232 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12232) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12232) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12232 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12232 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12232 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12232}
    (hw : WINDOW (paperDesignP 12232) c) (hc : c ∈ tableEvent) (K : Set (Ix 12232)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12232) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12232)) : Prop where
  charge : (retDist (paperCentres 12232)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12232)} (h : TablePayment H) :
    (retDist (paperCentres 12232)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12232)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12232

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12232) (i : Fin 4) (a : Ix 12232) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12232) (a : Ix 12232) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12232) : Prop where
  moment : ∀ i, MomentBound (muI 12232) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12232} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12232) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12232

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12232) : Prop where
  location : LBound (muI 12232) 12
    (fun a => conditionalVariance (stdGauss (Fin (12232 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12232) 12
    (fun a => conditionalVariance (stdGauss (Fin (12232 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12232) (hw : WINDOW (paperDesignP 12232) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12232 4 (55 / 100) /
      (12232 : ℝ) / ((12232 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12232

/-! The dimension-12232 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12232
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12232) (wl ws : ℝ) : SplitData 12232 :=
  BstLean.Part162.dPaper (paperDesignP 12232) c wl ws
    (√(2 / (12232 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12232 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12232 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12232) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12232) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12232 : ℝ)) * eR c * 12232 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12232) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12232 - 1)))
    (rowSplit c wl ws).good a ∂muI 12232 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12232) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12232 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12232) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12232 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12232) c (rowSplit c wl ws),
    hellG2 12232 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12232 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12232} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12232} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12232 t c BstLean.Part259.agent12232.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12232} (R : RootSource t c) :
    |√(QStand (paperDesignP 12232) t c) - √(qTilde (paperDesignP 12232) t c)| ≤
      BstLean.Part259.agent12232.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12232

/-! Rational enclosures for the HQ fluctuation price at dimension 12233. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12233 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12233 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12233 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12233 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12233 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12233 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12233 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12233 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12233 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12233 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12233 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12233 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12233 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12233 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12233 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12233 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12233

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12233 ∧ √12233 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12233 ∧ 1000000 ≤ Jz 12233 := by
  have hr : (1105 / 10 : ℝ) ≤ √12233 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12233 : ℝ) * √12233 ≤ (⌈(12233 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12233
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12233 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12233 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12233 : ℝ) = (⌈(12233 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12233 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12233 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12233) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12233 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12233 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12233 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12233 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12233 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12233 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12233) :
    (12233 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12233 * √(qB 12233))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12233 * √(qB 12233) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12233 : ℝ) * √(qB 12233) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12233) :
    (12233 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12233 * √(qB 12233))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12233 : ℝ) * √(qB 12233) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12233 : ℝ) * (√12233 *
      (c1F (exp (1 / 2) / 12) (Jz 12233) * (186 / 10000) / Jz 12233)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12233)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12233 : ℝ) * (√12233 *
      (c1F (exp (1 / 2) / 12) (Jz 12233) * (186 / 10000) / Jz 12233)) =
      (12233 * (√12233 * c1F (exp (1 / 2) / 12) (Jz 12233)) * (186 / 10000)) /
        Jz 12233 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12233)]
  nlinarith

theorem row_energy_rule :
    (12233 : ℝ) * (12233 *
      (c2F (exp (1 / 2) / 12) (Jz 12233) * (186 / 10000) ^ 2 / Jz 12233)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12233)]
  nlinarith

end BstLean.Part262.Row12233

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12233) (hc : A1 c ∈ BstLean.Part153.Eop 12233) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12233 : ℝ)) ≤ (12786406581 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12233 : ℝ) + 2 * √12233 ≤ (3113551447 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12233 : ℝ) ≤ (55301447 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12233)
    (hc : A1 c ∈ BstLean.Part153.Eop 12233) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12233 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12233 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12233))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12233) (K : Set (Ix 12233)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12233 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12233 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12233) (hw : WINDOW (paperDesignP 12233) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12233)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12233) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12233 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12233 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12233 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12233 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12233) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12233)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12233)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12233

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12233) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12233 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12233) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12233) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12233 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12233 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12233 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12233}
    (hw : WINDOW (paperDesignP 12233) c) (hc : c ∈ tableEvent) (K : Set (Ix 12233)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12233) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12233)) : Prop where
  charge : (retDist (paperCentres 12233)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12233)} (h : TablePayment H) :
    (retDist (paperCentres 12233)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12233)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12233

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12233) (i : Fin 4) (a : Ix 12233) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12233) (a : Ix 12233) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12233) : Prop where
  moment : ∀ i, MomentBound (muI 12233) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12233} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12233) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12233

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12233) : Prop where
  location : LBound (muI 12233) 12
    (fun a => conditionalVariance (stdGauss (Fin (12233 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12233) 12
    (fun a => conditionalVariance (stdGauss (Fin (12233 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12233) (hw : WINDOW (paperDesignP 12233) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12233 4 (55 / 100) /
      (12233 : ℝ) / ((12233 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12233

/-! The dimension-12233 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12233
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12233) (wl ws : ℝ) : SplitData 12233 :=
  BstLean.Part162.dPaper (paperDesignP 12233) c wl ws
    (√(2 / (12233 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12233 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12233 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12233) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12233) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12233 : ℝ)) * eR c * 12233 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12233) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12233 - 1)))
    (rowSplit c wl ws).good a ∂muI 12233 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12233) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12233 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12233) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12233 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12233) c (rowSplit c wl ws),
    hellG2 12233 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12233 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12233} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12233} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12233 t c BstLean.Part259.agent12233.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12233} (R : RootSource t c) :
    |√(QStand (paperDesignP 12233) t c) - √(qTilde (paperDesignP 12233) t c)| ≤
      BstLean.Part259.agent12233.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12233

/-! Rational enclosures for the HQ fluctuation price at dimension 12234. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12234 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12234 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12234 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12234 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12234 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12234 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12234 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12234 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12234 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12234 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12234 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12234 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12234 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12234 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12234 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12234 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12234

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12234 ∧ √12234 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12234 ∧ 1000000 ≤ Jz 12234 := by
  have hr : (1105 / 10 : ℝ) ≤ √12234 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12234 : ℝ) * √12234 ≤ (⌈(12234 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12234
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12234 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12234 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12234 : ℝ) = (⌈(12234 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12234 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12234 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12234) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12234 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12234 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12234 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12234 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12234 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12234 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12234) :
    (12234 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12234 * √(qB 12234))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12234 * √(qB 12234) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12234 : ℝ) * √(qB 12234) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12234) :
    (12234 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12234 * √(qB 12234))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12234 : ℝ) * √(qB 12234) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12234 : ℝ) * (√12234 *
      (c1F (exp (1 / 2) / 12) (Jz 12234) * (186 / 10000) / Jz 12234)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12234)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12234 : ℝ) * (√12234 *
      (c1F (exp (1 / 2) / 12) (Jz 12234) * (186 / 10000) / Jz 12234)) =
      (12234 * (√12234 * c1F (exp (1 / 2) / 12) (Jz 12234)) * (186 / 10000)) /
        Jz 12234 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12234)]
  nlinarith

theorem row_energy_rule :
    (12234 : ℝ) * (12234 *
      (c2F (exp (1 / 2) / 12) (Jz 12234) * (186 / 10000) ^ 2 / Jz 12234)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12234)]
  nlinarith

end BstLean.Part262.Row12234

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12234) (hc : A1 c ∈ BstLean.Part153.Eop 12234) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12234 : ℝ)) ≤ (6392941997 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12234 : ℝ) + 2 * √12234 ≤ (3113803707 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12234 : ℝ) ≤ (55303707 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12234)
    (hc : A1 c ∈ BstLean.Part153.Eop 12234) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12234 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12234 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12234))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12234) (K : Set (Ix 12234)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12234 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12234 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12234) (hw : WINDOW (paperDesignP 12234) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12234)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12234) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12234 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12234 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12234 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12234 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12234) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12234)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12234)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12234

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12234) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12234 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12234) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12234) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12234 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12234 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12234 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12234}
    (hw : WINDOW (paperDesignP 12234) c) (hc : c ∈ tableEvent) (K : Set (Ix 12234)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12234) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12234)) : Prop where
  charge : (retDist (paperCentres 12234)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12234)} (h : TablePayment H) :
    (retDist (paperCentres 12234)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12234)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12234

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12234) (i : Fin 4) (a : Ix 12234) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12234) (a : Ix 12234) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12234) : Prop where
  moment : ∀ i, MomentBound (muI 12234) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12234} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12234) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12234

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12234) : Prop where
  location : LBound (muI 12234) 12
    (fun a => conditionalVariance (stdGauss (Fin (12234 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12234) 12
    (fun a => conditionalVariance (stdGauss (Fin (12234 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12234) (hw : WINDOW (paperDesignP 12234) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12234 4 (55 / 100) /
      (12234 : ℝ) / ((12234 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12234

/-! The dimension-12234 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12234
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12234) (wl ws : ℝ) : SplitData 12234 :=
  BstLean.Part162.dPaper (paperDesignP 12234) c wl ws
    (√(2 / (12234 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12234 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12234 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12234) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12234) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12234 : ℝ)) * eR c * 12234 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12234) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12234 - 1)))
    (rowSplit c wl ws).good a ∂muI 12234 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12234) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12234 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12234) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12234 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12234) c (rowSplit c wl ws),
    hellG2 12234 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12234 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12234} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12234} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12234 t c BstLean.Part259.agent12234.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12234} (R : RootSource t c) :
    |√(QStand (paperDesignP 12234) t c) - √(qTilde (paperDesignP 12234) t c)| ≤
      BstLean.Part259.agent12234.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12234

/-! Rational enclosures for the HQ fluctuation price at dimension 12235. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12235 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12235 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12235 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12235 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12235 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12235 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12235 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12235 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12235 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12235 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12235 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12235 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12235 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12235 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12235 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12235 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12235

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12235 ∧ √12235 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12235 ∧ 1000000 ≤ Jz 12235 := by
  have hr : (1105 / 10 : ℝ) ≤ √12235 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12235 : ℝ) * √12235 ≤ (⌈(12235 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12235
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12235 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12235 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12235 : ℝ) = (⌈(12235 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12235 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12235 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12235) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12235 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12235 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12235 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12235 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12235 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12235 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12235) :
    (12235 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12235 * √(qB 12235))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12235 * √(qB 12235) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12235 : ℝ) * √(qB 12235) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12235) :
    (12235 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12235 * √(qB 12235))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12235 : ℝ) * √(qB 12235) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12235 : ℝ) * (√12235 *
      (c1F (exp (1 / 2) / 12) (Jz 12235) * (186 / 10000) / Jz 12235)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12235)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12235 : ℝ) * (√12235 *
      (c1F (exp (1 / 2) / 12) (Jz 12235) * (186 / 10000) / Jz 12235)) =
      (12235 * (√12235 * c1F (exp (1 / 2) / 12) (Jz 12235)) * (186 / 10000)) /
        Jz 12235 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12235)]
  nlinarith

theorem row_energy_rule :
    (12235 : ℝ) * (12235 *
      (c2F (exp (1 / 2) / 12) (Jz 12235) * (186 / 10000) ^ 2 / Jz 12235)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12235)]
  nlinarith

end BstLean.Part262.Row12235

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12235) (hc : A1 c ∈ BstLean.Part153.Eop 12235) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12235 : ℝ)) ≤ (12785361471 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12235 : ℝ) + 2 * √12235 ≤ (1245622387 / 100000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12235 : ℝ) ≤ (22122387 / 200000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12235)
    (hc : A1 c ∈ BstLean.Part153.Eop 12235) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12235 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12235 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12235))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12235) (K : Set (Ix 12235)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12235 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12235 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12235) (hw : WINDOW (paperDesignP 12235) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12235)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12235) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12235 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12235 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12235 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12235 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12235) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12235)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12235)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12235

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12235) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12235 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12235) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12235) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12235 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12235 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12235 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12235}
    (hw : WINDOW (paperDesignP 12235) c) (hc : c ∈ tableEvent) (K : Set (Ix 12235)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12235) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12235)) : Prop where
  charge : (retDist (paperCentres 12235)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12235)} (h : TablePayment H) :
    (retDist (paperCentres 12235)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12235)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12235

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12235) (i : Fin 4) (a : Ix 12235) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12235) (a : Ix 12235) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12235) : Prop where
  moment : ∀ i, MomentBound (muI 12235) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12235} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12235) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12235

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12235) : Prop where
  location : LBound (muI 12235) 12
    (fun a => conditionalVariance (stdGauss (Fin (12235 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12235) 12
    (fun a => conditionalVariance (stdGauss (Fin (12235 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12235) (hw : WINDOW (paperDesignP 12235) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12235 4 (55 / 100) /
      (12235 : ℝ) / ((12235 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12235

/-! The dimension-12235 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12235
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12235) (wl ws : ℝ) : SplitData 12235 :=
  BstLean.Part162.dPaper (paperDesignP 12235) c wl ws
    (√(2 / (12235 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12235 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12235 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12235) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12235) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12235 : ℝ)) * eR c * 12235 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12235) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12235 - 1)))
    (rowSplit c wl ws).good a ∂muI 12235 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12235) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12235 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12235) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12235 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12235) c (rowSplit c wl ws),
    hellG2 12235 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12235 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12235} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12235} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12235 t c BstLean.Part259.agent12235.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12235} (R : RootSource t c) :
    |√(QStand (paperDesignP 12235) t c) - √(qTilde (paperDesignP 12235) t c)| ≤
      BstLean.Part259.agent12235.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12235

/-! Rational enclosures for the HQ fluctuation price at dimension 12236. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12236 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12236 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12236 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12236 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12236 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12236 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12236 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12236 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12236 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12236 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12236 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12236 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12236 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12236 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12236 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12236 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12236

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12236 ∧ √12236 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12236 ∧ 1000000 ≤ Jz 12236 := by
  have hr : (1105 / 10 : ℝ) ≤ √12236 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12236 : ℝ) * √12236 ≤ (⌈(12236 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12236
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12236 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12236 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12236 : ℝ) = (⌈(12236 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12236 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12236 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12236) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12236 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12236 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12236 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12236 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12236 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12236 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12236) :
    (12236 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12236 * √(qB 12236))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12236 * √(qB 12236) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12236 : ℝ) * √(qB 12236) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12236) :
    (12236 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12236 * √(qB 12236))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12236 : ℝ) * √(qB 12236) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12236 : ℝ) * (√12236 *
      (c1F (exp (1 / 2) / 12) (Jz 12236) * (186 / 10000) / Jz 12236)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12236)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12236 : ℝ) * (√12236 *
      (c1F (exp (1 / 2) / 12) (Jz 12236) * (186 / 10000) / Jz 12236)) =
      (12236 * (√12236 * c1F (exp (1 / 2) / 12) (Jz 12236)) * (186 / 10000)) /
        Jz 12236 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12236)]
  nlinarith

theorem row_energy_rule :
    (12236 : ℝ) * (12236 *
      (c2F (exp (1 / 2) / 12) (Jz 12236) * (186 / 10000) ^ 2 / Jz 12236)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12236)]
  nlinarith

end BstLean.Part262.Row12236

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12236) (hc : A1 c ∈ BstLean.Part153.Eop 12236) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12236 : ℝ)) ≤ (12784839011 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12236 : ℝ) + 2 * √12236 ≤ (1245723291 / 100000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12236 : ℝ) ≤ (22123291 / 200000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12236)
    (hc : A1 c ∈ BstLean.Part153.Eop 12236) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12236 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12236 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12236))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12236) (K : Set (Ix 12236)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12236 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12236 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12236) (hw : WINDOW (paperDesignP 12236) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12236)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12236) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12236 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12236 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12236 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12236 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12236) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12236)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12236)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12236

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12236) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12236 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12236) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12236) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12236 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12236 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12236 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12236}
    (hw : WINDOW (paperDesignP 12236) c) (hc : c ∈ tableEvent) (K : Set (Ix 12236)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12236) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12236)) : Prop where
  charge : (retDist (paperCentres 12236)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12236)} (h : TablePayment H) :
    (retDist (paperCentres 12236)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12236)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12236

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12236) (i : Fin 4) (a : Ix 12236) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12236) (a : Ix 12236) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12236) : Prop where
  moment : ∀ i, MomentBound (muI 12236) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12236} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12236) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12236

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12236) : Prop where
  location : LBound (muI 12236) 12
    (fun a => conditionalVariance (stdGauss (Fin (12236 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12236) 12
    (fun a => conditionalVariance (stdGauss (Fin (12236 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12236) (hw : WINDOW (paperDesignP 12236) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12236 4 (55 / 100) /
      (12236 : ℝ) / ((12236 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12236

/-! The dimension-12236 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12236
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12236) (wl ws : ℝ) : SplitData 12236 :=
  BstLean.Part162.dPaper (paperDesignP 12236) c wl ws
    (√(2 / (12236 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12236 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12236 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12236) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12236) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12236 : ℝ)) * eR c * 12236 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12236) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12236 - 1)))
    (rowSplit c wl ws).good a ∂muI 12236 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12236) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12236 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12236) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12236 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12236) c (rowSplit c wl ws),
    hellG2 12236 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12236 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12236} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12236} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12236 t c BstLean.Part259.agent12236.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12236} (R : RootSource t c) :
    |√(QStand (paperDesignP 12236) t c) - √(qTilde (paperDesignP 12236) t c)| ≤
      BstLean.Part259.agent12236.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12236

/-! Rational enclosures for the HQ fluctuation price at dimension 12237. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12237 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12237 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12237 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12237 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12237 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12237 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12237 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12237 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12237 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12237 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12237 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12237 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12237 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12237 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12237 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12237 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12237

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12237 ∧ √12237 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12237 ∧ 1000000 ≤ Jz 12237 := by
  have hr : (1105 / 10 : ℝ) ≤ √12237 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12237 : ℝ) * √12237 ≤ (⌈(12237 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12237
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12237 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12237 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12237 : ℝ) = (⌈(12237 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12237 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12237 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12237) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12237 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12237 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12237 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12237 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12237 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12237 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12237) :
    (12237 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12237 * √(qB 12237))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12237 * √(qB 12237) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12237 : ℝ) * √(qB 12237) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12237) :
    (12237 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12237 * √(qB 12237))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12237 : ℝ) * √(qB 12237) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12237 : ℝ) * (√12237 *
      (c1F (exp (1 / 2) / 12) (Jz 12237) * (186 / 10000) / Jz 12237)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12237)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12237 : ℝ) * (√12237 *
      (c1F (exp (1 / 2) / 12) (Jz 12237) * (186 / 10000) / Jz 12237)) =
      (12237 * (√12237 * c1F (exp (1 / 2) / 12) (Jz 12237)) * (186 / 10000)) /
        Jz 12237 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12237)]
  nlinarith

theorem row_energy_rule :
    (12237 : ℝ) * (12237 *
      (c2F (exp (1 / 2) / 12) (Jz 12237) * (186 / 10000) ^ 2 / Jz 12237)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12237)]
  nlinarith

end BstLean.Part262.Row12237

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12237) (hc : A1 c ∈ BstLean.Part153.Eop 12237) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12237 : ℝ)) ≤ (1598039577 / 125000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12237 : ℝ) + 2 * √12237 ≤ (249164839 / 20000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12237 : ℝ) ≤ (4424839 / 40000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12237)
    (hc : A1 c ∈ BstLean.Part153.Eop 12237) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12237 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12237 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12237))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12237) (K : Set (Ix 12237)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12237 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12237 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12237) (hw : WINDOW (paperDesignP 12237) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12237)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12237) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12237 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12237 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12237 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12237 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12237) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12237)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12237)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12237

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12237) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12237 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12237) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12237) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12237 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12237 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12237 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12237}
    (hw : WINDOW (paperDesignP 12237) c) (hc : c ∈ tableEvent) (K : Set (Ix 12237)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12237) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12237)) : Prop where
  charge : (retDist (paperCentres 12237)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12237)} (h : TablePayment H) :
    (retDist (paperCentres 12237)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12237)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12237

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12237) (i : Fin 4) (a : Ix 12237) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12237) (a : Ix 12237) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12237) : Prop where
  moment : ∀ i, MomentBound (muI 12237) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12237} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12237) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12237

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12237) : Prop where
  location : LBound (muI 12237) 12
    (fun a => conditionalVariance (stdGauss (Fin (12237 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12237) 12
    (fun a => conditionalVariance (stdGauss (Fin (12237 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12237) (hw : WINDOW (paperDesignP 12237) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12237 4 (55 / 100) /
      (12237 : ℝ) / ((12237 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12237

/-! The dimension-12237 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12237
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12237) (wl ws : ℝ) : SplitData 12237 :=
  BstLean.Part162.dPaper (paperDesignP 12237) c wl ws
    (√(2 / (12237 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12237 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12237 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12237) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12237) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12237 : ℝ)) * eR c * 12237 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12237) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12237 - 1)))
    (rowSplit c wl ws).good a ∂muI 12237 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12237) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12237 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12237) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12237 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12237) c (rowSplit c wl ws),
    hellG2 12237 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12237 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12237} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12237} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12237 t c BstLean.Part259.agent12237.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12237} (R : RootSource t c) :
    |√(QStand (paperDesignP 12237) t c) - √(qTilde (paperDesignP 12237) t c)| ≤
      BstLean.Part259.agent12237.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12237

/-! Rational enclosures for the HQ fluctuation price at dimension 12238. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12238 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12238 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12238 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12238 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12238 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12238 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12238 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12238 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12238 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12238 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12238 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12238 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12238 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12238 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12238 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12238 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12238

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12238 ∧ √12238 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12238 ∧ 1000000 ≤ Jz 12238 := by
  have hr : (1105 / 10 : ℝ) ≤ √12238 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12238 : ℝ) * √12238 ≤ (⌈(12238 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12238
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12238 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12238 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12238 : ℝ) = (⌈(12238 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12238 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12238 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12238) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12238 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12238 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12238 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12238 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12238 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12238 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12238) :
    (12238 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12238 * √(qB 12238))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12238 * √(qB 12238) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12238 : ℝ) * √(qB 12238) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12238) :
    (12238 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12238 * √(qB 12238))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12238 : ℝ) * √(qB 12238) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12238 : ℝ) * (√12238 *
      (c1F (exp (1 / 2) / 12) (Jz 12238) * (186 / 10000) / Jz 12238)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12238)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12238 : ℝ) * (√12238 *
      (c1F (exp (1 / 2) / 12) (Jz 12238) * (186 / 10000) / Jz 12238)) =
      (12238 * (√12238 * c1F (exp (1 / 2) / 12) (Jz 12238)) * (186 / 10000)) /
        Jz 12238 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12238)]
  nlinarith

theorem row_energy_rule :
    (12238 : ℝ) * (12238 *
      (c2F (exp (1 / 2) / 12) (Jz 12238) * (186 / 10000) ^ 2 / Jz 12238)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12238)]
  nlinarith

end BstLean.Part262.Row12238

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12238) (hc : A1 c ∈ BstLean.Part153.Eop 12238) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12238 : ℝ)) ≤ (2556758857 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12238 : ℝ) + 2 * √12238 ≤ (1245925099 / 100000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12238 : ℝ) ≤ (22125099 / 200000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12238)
    (hc : A1 c ∈ BstLean.Part153.Eop 12238) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12238 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12238 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12238))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12238) (K : Set (Ix 12238)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12238 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12238 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12238) (hw : WINDOW (paperDesignP 12238) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12238)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12238) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12238 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12238 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12238 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12238 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12238) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12238)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12238)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12238

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12238) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12238 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12238) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12238) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12238 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12238 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12238 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12238}
    (hw : WINDOW (paperDesignP 12238) c) (hc : c ∈ tableEvent) (K : Set (Ix 12238)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12238) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12238)) : Prop where
  charge : (retDist (paperCentres 12238)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12238)} (h : TablePayment H) :
    (retDist (paperCentres 12238)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12238)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12238

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12238) (i : Fin 4) (a : Ix 12238) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12238) (a : Ix 12238) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12238) : Prop where
  moment : ∀ i, MomentBound (muI 12238) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12238} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12238) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12238

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12238) : Prop where
  location : LBound (muI 12238) 12
    (fun a => conditionalVariance (stdGauss (Fin (12238 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12238) 12
    (fun a => conditionalVariance (stdGauss (Fin (12238 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12238) (hw : WINDOW (paperDesignP 12238) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12238 4 (55 / 100) /
      (12238 : ℝ) / ((12238 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12238

/-! The dimension-12238 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12238
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12238) (wl ws : ℝ) : SplitData 12238 :=
  BstLean.Part162.dPaper (paperDesignP 12238) c wl ws
    (√(2 / (12238 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12238 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12238 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12238) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12238) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12238 : ℝ)) * eR c * 12238 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12238) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12238 - 1)))
    (rowSplit c wl ws).good a ∂muI 12238 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12238) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12238 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12238) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12238 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12238) c (rowSplit c wl ws),
    hellG2 12238 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12238 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12238} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12238} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12238 t c BstLean.Part259.agent12238.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12238} (R : RootSource t c) :
    |√(QStand (paperDesignP 12238) t c) - √(qTilde (paperDesignP 12238) t c)| ≤
      BstLean.Part259.agent12238.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12238

/-! Rational enclosures for the HQ fluctuation price at dimension 12239. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12239 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12239 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12239 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12239 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12239 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12239 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12239 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12239 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12239 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12239 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12239 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12239 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12239 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12239 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12239 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12239 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12239

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12239 ∧ √12239 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12239 ∧ 1000000 ≤ Jz 12239 := by
  have hr : (1105 / 10 : ℝ) ≤ √12239 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12239 : ℝ) * √12239 ≤ (⌈(12239 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12239
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12239 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12239 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12239 : ℝ) = (⌈(12239 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12239 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12239 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12239) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12239 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12239 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12239 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12239 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12239 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12239 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12239) :
    (12239 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12239 * √(qB 12239))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12239 * √(qB 12239) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12239 : ℝ) * √(qB 12239) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12239) :
    (12239 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12239 * √(qB 12239))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12239 : ℝ) * √(qB 12239) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12239 : ℝ) * (√12239 *
      (c1F (exp (1 / 2) / 12) (Jz 12239) * (186 / 10000) / Jz 12239)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12239)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12239 : ℝ) * (√12239 *
      (c1F (exp (1 / 2) / 12) (Jz 12239) * (186 / 10000) / Jz 12239)) =
      (12239 * (√12239 * c1F (exp (1 / 2) / 12) (Jz 12239)) * (186 / 10000)) /
        Jz 12239 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12239)]
  nlinarith

theorem row_energy_rule :
    (12239 : ℝ) * (12239 *
      (c2F (exp (1 / 2) / 12) (Jz 12239) * (186 / 10000) ^ 2 / Jz 12239)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12239)]
  nlinarith

end BstLean.Part262.Row12239

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12239) (hc : A1 c ∈ BstLean.Part153.Eop 12239) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12239 : ℝ)) ≤ (6391636009 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12239 : ℝ) + 2 * √12239 ≤ (1246026003 / 100000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12239 : ℝ) ≤ (22126003 / 200000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12239)
    (hc : A1 c ∈ BstLean.Part153.Eop 12239) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12239 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12239 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12239))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12239) (K : Set (Ix 12239)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12239 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12239 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12239) (hw : WINDOW (paperDesignP 12239) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12239)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12239) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12239 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12239 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12239 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12239 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12239) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12239)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12239)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12239

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12239) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12239 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12239) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12239) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12239 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12239 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12239 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12239}
    (hw : WINDOW (paperDesignP 12239) c) (hc : c ∈ tableEvent) (K : Set (Ix 12239)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12239) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12239)) : Prop where
  charge : (retDist (paperCentres 12239)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12239)} (h : TablePayment H) :
    (retDist (paperCentres 12239)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12239)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12239

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12239) (i : Fin 4) (a : Ix 12239) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12239) (a : Ix 12239) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12239) : Prop where
  moment : ∀ i, MomentBound (muI 12239) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12239} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12239) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12239

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12239) : Prop where
  location : LBound (muI 12239) 12
    (fun a => conditionalVariance (stdGauss (Fin (12239 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12239) 12
    (fun a => conditionalVariance (stdGauss (Fin (12239 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12239) (hw : WINDOW (paperDesignP 12239) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12239 4 (55 / 100) /
      (12239 : ℝ) / ((12239 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12239

/-! The dimension-12239 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12239
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12239) (wl ws : ℝ) : SplitData 12239 :=
  BstLean.Part162.dPaper (paperDesignP 12239) c wl ws
    (√(2 / (12239 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12239 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12239 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12239) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12239) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12239 : ℝ)) * eR c * 12239 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12239) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12239 - 1)))
    (rowSplit c wl ws).good a ∂muI 12239 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12239) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12239 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12239) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12239 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12239) c (rowSplit c wl ws),
    hellG2 12239 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12239 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12239} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12239} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12239 t c BstLean.Part259.agent12239.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12239} (R : RootSource t c) :
    |√(QStand (paperDesignP 12239) t c) - √(qTilde (paperDesignP 12239) t c)| ≤
      BstLean.Part259.agent12239.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12239

/-! Rational enclosures for the HQ fluctuation price at dimension 12240. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12240 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12240 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12240 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12240 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12240 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12240 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12240 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12240 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12240 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12240 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12240 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12240 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12240 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12240 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12240 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12240 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12240

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12240 ∧ √12240 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12240 ∧ 1000000 ≤ Jz 12240 := by
  have hr : (1105 / 10 : ℝ) ≤ √12240 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12240 : ℝ) * √12240 ≤ (⌈(12240 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12240
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12240 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12240 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12240 : ℝ) = (⌈(12240 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12240 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12240 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12240) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12240 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12240 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12240 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12240 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12240 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12240 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12240) :
    (12240 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12240 * √(qB 12240))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12240 * √(qB 12240) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12240 : ℝ) * √(qB 12240) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12240) :
    (12240 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12240 * √(qB 12240))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12240 : ℝ) * √(qB 12240) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12240 : ℝ) * (√12240 *
      (c1F (exp (1 / 2) / 12) (Jz 12240) * (186 / 10000) / Jz 12240)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12240)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12240 : ℝ) * (√12240 *
      (c1F (exp (1 / 2) / 12) (Jz 12240) * (186 / 10000) / Jz 12240)) =
      (12240 * (√12240 * c1F (exp (1 / 2) / 12) (Jz 12240)) * (186 / 10000)) /
        Jz 12240 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12240)]
  nlinarith

theorem row_energy_rule :
    (12240 : ℝ) * (12240 *
      (c2F (exp (1 / 2) / 12) (Jz 12240) * (186 / 10000) ^ 2 / Jz 12240)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12240)]
  nlinarith

end BstLean.Part262.Row12240

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12240) (hc : A1 c ∈ BstLean.Part153.Eop 12240) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12240 : ℝ)) ≤ (2556549963 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12240 : ℝ) + 2 * √12240 ≤ (3115317267 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12240 : ℝ) ≤ (55317267 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12240)
    (hc : A1 c ∈ BstLean.Part153.Eop 12240) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12240 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12240 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12240))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12240) (K : Set (Ix 12240)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12240 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12240 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12240) (hw : WINDOW (paperDesignP 12240) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12240)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12240) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12240 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12240 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12240 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12240 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12240) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12240)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12240)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12240

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12240) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12240 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12240) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12240) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12240 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12240 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12240 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12240}
    (hw : WINDOW (paperDesignP 12240) c) (hc : c ∈ tableEvent) (K : Set (Ix 12240)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12240) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12240)) : Prop where
  charge : (retDist (paperCentres 12240)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12240)} (h : TablePayment H) :
    (retDist (paperCentres 12240)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12240)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12240

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12240) (i : Fin 4) (a : Ix 12240) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12240) (a : Ix 12240) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12240) : Prop where
  moment : ∀ i, MomentBound (muI 12240) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12240} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12240) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12240

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12240) : Prop where
  location : LBound (muI 12240) 12
    (fun a => conditionalVariance (stdGauss (Fin (12240 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12240) 12
    (fun a => conditionalVariance (stdGauss (Fin (12240 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12240) (hw : WINDOW (paperDesignP 12240) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12240 4 (55 / 100) /
      (12240 : ℝ) / ((12240 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12240

/-! The dimension-12240 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12240
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12240) (wl ws : ℝ) : SplitData 12240 :=
  BstLean.Part162.dPaper (paperDesignP 12240) c wl ws
    (√(2 / (12240 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12240 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12240 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12240) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12240) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12240 : ℝ)) * eR c * 12240 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12240) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12240 - 1)))
    (rowSplit c wl ws).good a ∂muI 12240 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12240) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12240 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12240) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12240 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12240) c (rowSplit c wl ws),
    hellG2 12240 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12240 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12240} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12240} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12240 t c BstLean.Part259.agent12240.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12240} (R : RootSource t c) :
    |√(QStand (paperDesignP 12240) t c) - √(qTilde (paperDesignP 12240) t c)| ≤
      BstLean.Part259.agent12240.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12240

/-! Rational enclosures for the HQ fluctuation price at dimension 12241. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12241 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12241 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12241 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12241 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12241 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12241 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12241 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12241 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12241 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12241 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12241 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12241 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12241 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12241 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12241 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12241 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12241

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12241 ∧ √12241 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12241 ∧ 1000000 ≤ Jz 12241 := by
  have hr : (1105 / 10 : ℝ) ≤ √12241 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12241 : ℝ) * √12241 ≤ (⌈(12241 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12241
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12241 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12241 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12241 : ℝ) = (⌈(12241 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12241 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12241 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12241) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12241 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12241 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12241 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12241 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12241 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12241 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12241) :
    (12241 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12241 * √(qB 12241))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12241 * √(qB 12241) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12241 : ℝ) * √(qB 12241) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12241) :
    (12241 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12241 * √(qB 12241))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12241 : ℝ) * √(qB 12241) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12241 : ℝ) * (√12241 *
      (c1F (exp (1 / 2) / 12) (Jz 12241) * (186 / 10000) / Jz 12241)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12241)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12241 : ℝ) * (√12241 *
      (c1F (exp (1 / 2) / 12) (Jz 12241) * (186 / 10000) / Jz 12241)) =
      (12241 * (√12241 * c1F (exp (1 / 2) / 12) (Jz 12241)) * (186 / 10000)) /
        Jz 12241 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12241)]
  nlinarith

theorem row_energy_rule :
    (12241 : ℝ) * (12241 *
      (c2F (exp (1 / 2) / 12) (Jz 12241) * (186 / 10000) ^ 2 / Jz 12241)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12241)]
  nlinarith

end BstLean.Part262.Row12241

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12241) (hc : A1 c ∈ BstLean.Part153.Eop 12241) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12241 : ℝ)) ≤ (511289107 / 40000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12241 : ℝ) + 2 * √12241 ≤ (6231139053 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12241 : ℝ) ≤ (110639053 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12241)
    (hc : A1 c ∈ BstLean.Part153.Eop 12241) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12241 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12241 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12241))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12241) (K : Set (Ix 12241)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12241 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12241 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12241) (hw : WINDOW (paperDesignP 12241) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12241)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12241) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12241 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12241 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12241 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12241 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12241) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12241)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12241)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12241

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12241) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12241 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12241) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12241) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12241 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12241 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12241 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12241}
    (hw : WINDOW (paperDesignP 12241) c) (hc : c ∈ tableEvent) (K : Set (Ix 12241)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12241) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12241)) : Prop where
  charge : (retDist (paperCentres 12241)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12241)} (h : TablePayment H) :
    (retDist (paperCentres 12241)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12241)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12241

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12241) (i : Fin 4) (a : Ix 12241) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12241) (a : Ix 12241) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12241) : Prop where
  moment : ∀ i, MomentBound (muI 12241) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12241} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12241) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12241

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12241) : Prop where
  location : LBound (muI 12241) 12
    (fun a => conditionalVariance (stdGauss (Fin (12241 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12241) 12
    (fun a => conditionalVariance (stdGauss (Fin (12241 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12241) (hw : WINDOW (paperDesignP 12241) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12241 4 (55 / 100) /
      (12241 : ℝ) / ((12241 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12241

/-! The dimension-12241 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12241
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12241) (wl ws : ℝ) : SplitData 12241 :=
  BstLean.Part162.dPaper (paperDesignP 12241) c wl ws
    (√(2 / (12241 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12241 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12241 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12241) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12241) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12241 : ℝ)) * eR c * 12241 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12241) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12241 - 1)))
    (rowSplit c wl ws).good a ∂muI 12241 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12241) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12241 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12241) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12241 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12241) c (rowSplit c wl ws),
    hellG2 12241 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12241 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12241} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12241} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12241 t c BstLean.Part259.agent12241.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12241} (R : RootSource t c) :
    |√(QStand (paperDesignP 12241) t c) - √(qTilde (paperDesignP 12241) t c)| ≤
      BstLean.Part259.agent12241.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12241

/-! Rational enclosures for the HQ fluctuation price at dimension 12242. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12242 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12242 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12242 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12242 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12242 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12242 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12242 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12242 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12242 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12242 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12242 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12242 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12242 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12242 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12242 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12242 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12242

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12242 ∧ √12242 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12242 ∧ 1000000 ≤ Jz 12242 := by
  have hr : (1105 / 10 : ℝ) ≤ √12242 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12242 : ℝ) * √12242 ≤ (⌈(12242 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12242
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12242 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12242 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12242 : ℝ) = (⌈(12242 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12242 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12242 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12242) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12242 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12242 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12242 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12242 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12242 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12242 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12242) :
    (12242 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12242 * √(qB 12242))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12242 * √(qB 12242) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12242 : ℝ) * √(qB 12242) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12242) :
    (12242 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12242 * √(qB 12242))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12242 : ℝ) * √(qB 12242) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12242 : ℝ) * (√12242 *
      (c1F (exp (1 / 2) / 12) (Jz 12242) * (186 / 10000) / Jz 12242)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12242)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12242 : ℝ) * (√12242 *
      (c1F (exp (1 / 2) / 12) (Jz 12242) * (186 / 10000) / Jz 12242)) =
      (12242 * (√12242 * c1F (exp (1 / 2) / 12) (Jz 12242)) * (186 / 10000)) /
        Jz 12242 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12242)]
  nlinarith

theorem row_energy_rule :
    (12242 : ℝ) * (12242 *
      (c2F (exp (1 / 2) / 12) (Jz 12242) * (186 / 10000) ^ 2 / Jz 12242)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12242)]
  nlinarith

end BstLean.Part262.Row12242

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12242) (hc : A1 c ∈ BstLean.Part153.Eop 12242) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12242 : ℝ)) ≤ (3994283 / 312500000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12242 : ℝ) + 2 * √12242 ≤ (1557910893 / 125000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12242 : ℝ) ≤ (27660893 / 250000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12242)
    (hc : A1 c ∈ BstLean.Part153.Eop 12242) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12242 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12242 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12242))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12242) (K : Set (Ix 12242)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12242 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12242 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12242) (hw : WINDOW (paperDesignP 12242) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12242)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12242) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12242 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12242 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12242 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12242 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12242) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12242)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12242)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12242

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12242) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12242 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12242) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12242) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12242 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12242 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12242 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12242}
    (hw : WINDOW (paperDesignP 12242) c) (hc : c ∈ tableEvent) (K : Set (Ix 12242)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12242) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12242)) : Prop where
  charge : (retDist (paperCentres 12242)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12242)} (h : TablePayment H) :
    (retDist (paperCentres 12242)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12242)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12242

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12242) (i : Fin 4) (a : Ix 12242) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12242) (a : Ix 12242) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12242) : Prop where
  moment : ∀ i, MomentBound (muI 12242) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12242} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12242) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12242

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12242) : Prop where
  location : LBound (muI 12242) 12
    (fun a => conditionalVariance (stdGauss (Fin (12242 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12242) 12
    (fun a => conditionalVariance (stdGauss (Fin (12242 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12242) (hw : WINDOW (paperDesignP 12242) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12242 4 (55 / 100) /
      (12242 : ℝ) / ((12242 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12242

/-! The dimension-12242 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12242
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12242) (wl ws : ℝ) : SplitData 12242 :=
  BstLean.Part162.dPaper (paperDesignP 12242) c wl ws
    (√(2 / (12242 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12242 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12242 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12242) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12242) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12242 : ℝ)) * eR c * 12242 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12242) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12242 - 1)))
    (rowSplit c wl ws).good a ∂muI 12242 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12242) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12242 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12242) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12242 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12242) c (rowSplit c wl ws),
    hellG2 12242 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12242 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12242} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12242} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12242 t c BstLean.Part259.agent12242.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12242} (R : RootSource t c) :
    |√(QStand (paperDesignP 12242) t c) - √(qTilde (paperDesignP 12242) t c)| ≤
      BstLean.Part259.agent12242.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12242

/-! Rational enclosures for the HQ fluctuation price at dimension 12243. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12243 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12243 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12243 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12243 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12243 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12243 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12243 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12243 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12243 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12243 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12243 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12243 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12243 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12243 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12243 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12243 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12243

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12243 ∧ √12243 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12243 ∧ 1000000 ≤ Jz 12243 := by
  have hr : (1105 / 10 : ℝ) ≤ √12243 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12243 : ℝ) * √12243 ≤ (⌈(12243 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12243
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12243 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12243 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12243 : ℝ) = (⌈(12243 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12243 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12243 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12243) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12243 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12243 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12243 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12243 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12243 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12243 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12243) :
    (12243 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12243 * √(qB 12243))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12243 * √(qB 12243) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12243 : ℝ) * √(qB 12243) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12243) :
    (12243 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12243 * √(qB 12243))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12243 : ℝ) * √(qB 12243) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12243 : ℝ) * (√12243 *
      (c1F (exp (1 / 2) / 12) (Jz 12243) * (186 / 10000) / Jz 12243)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12243)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12243 : ℝ) * (√12243 *
      (c1F (exp (1 / 2) / 12) (Jz 12243) * (186 / 10000) / Jz 12243)) =
      (12243 * (√12243 * c1F (exp (1 / 2) / 12) (Jz 12243)) * (186 / 10000)) /
        Jz 12243 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12243)]
  nlinarith

theorem row_energy_rule :
    (12243 : ℝ) * (12243 *
      (c2F (exp (1 / 2) / 12) (Jz 12243) * (186 / 10000) ^ 2 / Jz 12243)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12243)]
  nlinarith

end BstLean.Part262.Row12243

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12243) (hc : A1 c ∈ BstLean.Part153.Eop 12243) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12243 : ℝ)) ≤ (12781183589 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12243 : ℝ) + 2 * √12243 ≤ (6232148091 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12243 : ℝ) ≤ (110648091 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12243)
    (hc : A1 c ∈ BstLean.Part153.Eop 12243) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12243 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12243 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12243))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12243) (K : Set (Ix 12243)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12243 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12243 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12243) (hw : WINDOW (paperDesignP 12243) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12243)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12243) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12243 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12243 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12243 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12243 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12243) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12243)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12243)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12243

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12243) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12243 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12243) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12243) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12243 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12243 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12243 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12243}
    (hw : WINDOW (paperDesignP 12243) c) (hc : c ∈ tableEvent) (K : Set (Ix 12243)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12243) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12243)) : Prop where
  charge : (retDist (paperCentres 12243)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12243)} (h : TablePayment H) :
    (retDist (paperCentres 12243)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12243)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12243

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12243) (i : Fin 4) (a : Ix 12243) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12243) (a : Ix 12243) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12243) : Prop where
  moment : ∀ i, MomentBound (muI 12243) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12243} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12243) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12243

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12243) : Prop where
  location : LBound (muI 12243) 12
    (fun a => conditionalVariance (stdGauss (Fin (12243 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12243) 12
    (fun a => conditionalVariance (stdGauss (Fin (12243 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12243) (hw : WINDOW (paperDesignP 12243) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12243 4 (55 / 100) /
      (12243 : ℝ) / ((12243 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12243

/-! The dimension-12243 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12243
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12243) (wl ws : ℝ) : SplitData 12243 :=
  BstLean.Part162.dPaper (paperDesignP 12243) c wl ws
    (√(2 / (12243 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12243 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12243 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12243) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12243) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12243 : ℝ)) * eR c * 12243 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12243) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12243 - 1)))
    (rowSplit c wl ws).good a ∂muI 12243 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12243) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12243 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12243) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12243 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12243) c (rowSplit c wl ws),
    hellG2 12243 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12243 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12243} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12243} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12243 t c BstLean.Part259.agent12243.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12243} (R : RootSource t c) :
    |√(QStand (paperDesignP 12243) t c) - √(qTilde (paperDesignP 12243) t c)| ≤
      BstLean.Part259.agent12243.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12243

/-! Rational enclosures for the HQ fluctuation price at dimension 12244. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12244 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12244 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12244 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12244 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12244 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12244 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12244 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12244 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12244 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12244 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12244 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12244 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12244 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12244 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12244 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12244 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12244

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12244 ∧ √12244 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12244 ∧ 1000000 ≤ Jz 12244 := by
  have hr : (1105 / 10 : ℝ) ≤ √12244 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12244 : ℝ) * √12244 ≤ (⌈(12244 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12244
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12244 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12244 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12244 : ℝ) = (⌈(12244 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12244 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12244 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12244) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12244 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12244 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12244 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12244 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12244 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12244 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12244) :
    (12244 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12244 * √(qB 12244))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12244 * √(qB 12244) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12244 : ℝ) * √(qB 12244) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12244) :
    (12244 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12244 * √(qB 12244))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12244 : ℝ) * √(qB 12244) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12244 : ℝ) * (√12244 *
      (c1F (exp (1 / 2) / 12) (Jz 12244) * (186 / 10000) / Jz 12244)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12244)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12244 : ℝ) * (√12244 *
      (c1F (exp (1 / 2) / 12) (Jz 12244) * (186 / 10000) / Jz 12244)) =
      (12244 * (√12244 * c1F (exp (1 / 2) / 12) (Jz 12244)) * (186 / 10000)) /
        Jz 12244 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12244)]
  nlinarith

theorem row_energy_rule :
    (12244 : ℝ) * (12244 *
      (c2F (exp (1 / 2) / 12) (Jz 12244) * (186 / 10000) ^ 2 / Jz 12244)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12244)]
  nlinarith

end BstLean.Part262.Row12244

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12244) (hc : A1 c ∈ BstLean.Part153.Eop 12244) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12244 : ℝ)) ≤ (6390330821 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12244 : ℝ) + 2 * √12244 ≤ (623265261 / 50000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12244 : ℝ) ≤ (11065261 / 100000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12244)
    (hc : A1 c ∈ BstLean.Part153.Eop 12244) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12244 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12244 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12244))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12244) (K : Set (Ix 12244)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12244 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12244 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12244) (hw : WINDOW (paperDesignP 12244) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12244)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12244) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12244 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12244 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12244 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12244 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12244) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12244)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12244)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12244

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12244) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12244 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12244) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12244) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12244 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12244 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12244 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12244}
    (hw : WINDOW (paperDesignP 12244) c) (hc : c ∈ tableEvent) (K : Set (Ix 12244)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12244) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12244)) : Prop where
  charge : (retDist (paperCentres 12244)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12244)} (h : TablePayment H) :
    (retDist (paperCentres 12244)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12244)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12244

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12244) (i : Fin 4) (a : Ix 12244) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12244) (a : Ix 12244) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12244) : Prop where
  moment : ∀ i, MomentBound (muI 12244) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12244} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12244) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12244

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12244) : Prop where
  location : LBound (muI 12244) 12
    (fun a => conditionalVariance (stdGauss (Fin (12244 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12244) 12
    (fun a => conditionalVariance (stdGauss (Fin (12244 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12244) (hw : WINDOW (paperDesignP 12244) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12244 4 (55 / 100) /
      (12244 : ℝ) / ((12244 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12244

/-! The dimension-12244 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12244
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12244) (wl ws : ℝ) : SplitData 12244 :=
  BstLean.Part162.dPaper (paperDesignP 12244) c wl ws
    (√(2 / (12244 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12244 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12244 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12244) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12244) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12244 : ℝ)) * eR c * 12244 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12244) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12244 - 1)))
    (rowSplit c wl ws).good a ∂muI 12244 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12244) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12244 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12244) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12244 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12244) c (rowSplit c wl ws),
    hellG2 12244 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12244 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12244} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12244} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12244 t c BstLean.Part259.agent12244.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12244} (R : RootSource t c) :
    |√(QStand (paperDesignP 12244) t c) - √(qTilde (paperDesignP 12244) t c)| ≤
      BstLean.Part259.agent12244.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12244

/-! Rational enclosures for the HQ fluctuation price at dimension 12245. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12245 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12245 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12245 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12245 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12245 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12245 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12245 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12245 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12245 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12245 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12245 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12245 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12245 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12245 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12245 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12245 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12245

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12245 ∧ √12245 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12245 ∧ 1000000 ≤ Jz 12245 := by
  have hr : (1105 / 10 : ℝ) ≤ √12245 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12245 : ℝ) * √12245 ≤ (⌈(12245 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12245
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12245 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12245 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12245 : ℝ) = (⌈(12245 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12245 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12245 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12245) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12245 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12245 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12245 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12245 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12245 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12245 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12245) :
    (12245 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12245 * √(qB 12245))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12245 * √(qB 12245) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12245 : ℝ) * √(qB 12245) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12245) :
    (12245 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12245 * √(qB 12245))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12245 : ℝ) * √(qB 12245) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12245 : ℝ) * (√12245 *
      (c1F (exp (1 / 2) / 12) (Jz 12245) * (186 / 10000) / Jz 12245)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12245)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12245 : ℝ) * (√12245 *
      (c1F (exp (1 / 2) / 12) (Jz 12245) * (186 / 10000) / Jz 12245)) =
      (12245 * (√12245 * c1F (exp (1 / 2) / 12) (Jz 12245)) * (186 / 10000)) /
        Jz 12245 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12245)]
  nlinarith

theorem row_energy_rule :
    (12245 : ℝ) * (12245 *
      (c2F (exp (1 / 2) / 12) (Jz 12245) * (186 / 10000) ^ 2 / Jz 12245)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12245)]
  nlinarith

end BstLean.Part262.Row12245

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12245) (hc : A1 c ∈ BstLean.Part153.Eop 12245) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12245 : ℝ)) ≤ (6390069879 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12245 : ℝ) + 2 * √12245 ≤ (6233157129 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12245 : ℝ) ≤ (110657129 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12245)
    (hc : A1 c ∈ BstLean.Part153.Eop 12245) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12245 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12245 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12245))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12245) (K : Set (Ix 12245)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12245 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12245 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12245) (hw : WINDOW (paperDesignP 12245) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12245)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12245) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12245 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12245 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12245 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12245 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12245) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12245)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12245)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12245

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12245) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12245 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12245) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12245) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12245 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12245 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12245 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12245}
    (hw : WINDOW (paperDesignP 12245) c) (hc : c ∈ tableEvent) (K : Set (Ix 12245)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12245) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12245)) : Prop where
  charge : (retDist (paperCentres 12245)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12245)} (h : TablePayment H) :
    (retDist (paperCentres 12245)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12245)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12245

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12245) (i : Fin 4) (a : Ix 12245) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12245) (a : Ix 12245) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12245) : Prop where
  moment : ∀ i, MomentBound (muI 12245) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12245} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12245) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12245

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12245) : Prop where
  location : LBound (muI 12245) 12
    (fun a => conditionalVariance (stdGauss (Fin (12245 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12245) 12
    (fun a => conditionalVariance (stdGauss (Fin (12245 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12245) (hw : WINDOW (paperDesignP 12245) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12245 4 (55 / 100) /
      (12245 : ℝ) / ((12245 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12245

/-! The dimension-12245 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12245
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12245) (wl ws : ℝ) : SplitData 12245 :=
  BstLean.Part162.dPaper (paperDesignP 12245) c wl ws
    (√(2 / (12245 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12245 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12245 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12245) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12245) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12245 : ℝ)) * eR c * 12245 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12245) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12245 - 1)))
    (rowSplit c wl ws).good a ∂muI 12245 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12245) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12245 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12245) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12245 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12245) c (rowSplit c wl ws),
    hellG2 12245 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12245 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12245} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12245} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12245 t c BstLean.Part259.agent12245.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12245} (R : RootSource t c) :
    |√(QStand (paperDesignP 12245) t c) - √(qTilde (paperDesignP 12245) t c)| ≤
      BstLean.Part259.agent12245.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12245

/-! Rational enclosures for the HQ fluctuation price at dimension 12246. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12246 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12246 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12246 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12246 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12246 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12246 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12246 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12246 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12246 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12246 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12246 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12246 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12246 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12246 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12246 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12246 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12246

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12246 ∧ √12246 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12246 ∧ 1000000 ≤ Jz 12246 := by
  have hr : (1105 / 10 : ℝ) ≤ √12246 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12246 : ℝ) * √12246 ≤ (⌈(12246 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12246
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12246 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12246 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12246 : ℝ) = (⌈(12246 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12246 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12246 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12246) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12246 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12246 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12246 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12246 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12246 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12246 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12246) :
    (12246 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12246 * √(qB 12246))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12246 * √(qB 12246) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12246 : ℝ) * √(qB 12246) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12246) :
    (12246 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12246 * √(qB 12246))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12246 : ℝ) * √(qB 12246) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12246 : ℝ) * (√12246 *
      (c1F (exp (1 / 2) / 12) (Jz 12246) * (186 / 10000) / Jz 12246)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12246)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12246 : ℝ) * (√12246 *
      (c1F (exp (1 / 2) / 12) (Jz 12246) * (186 / 10000) / Jz 12246)) =
      (12246 * (√12246 * c1F (exp (1 / 2) / 12) (Jz 12246)) * (186 / 10000)) /
        Jz 12246 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12246)]
  nlinarith

theorem row_energy_rule :
    (12246 : ℝ) * (12246 *
      (c2F (exp (1 / 2) / 12) (Jz 12246) * (186 / 10000) ^ 2 / Jz 12246)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12246)]
  nlinarith

end BstLean.Part262.Row12246

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12246) (hc : A1 c ∈ BstLean.Part153.Eop 12246) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12246 : ℝ)) ≤ (12779617939 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12246 : ℝ) + 2 * √12246 ≤ (6233661647 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12246 : ℝ) ≤ (110661647 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12246)
    (hc : A1 c ∈ BstLean.Part153.Eop 12246) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12246 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12246 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12246))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12246) (K : Set (Ix 12246)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12246 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12246 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12246) (hw : WINDOW (paperDesignP 12246) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12246)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12246) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12246 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12246 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12246 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12246 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12246) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12246)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12246)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12246

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12246) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12246 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12246) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12246) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12246 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12246 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12246 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12246}
    (hw : WINDOW (paperDesignP 12246) c) (hc : c ∈ tableEvent) (K : Set (Ix 12246)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12246) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12246)) : Prop where
  charge : (retDist (paperCentres 12246)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12246)} (h : TablePayment H) :
    (retDist (paperCentres 12246)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12246)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12246

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12246) (i : Fin 4) (a : Ix 12246) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12246) (a : Ix 12246) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12246) : Prop where
  moment : ∀ i, MomentBound (muI 12246) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12246} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12246) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12246

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12246) : Prop where
  location : LBound (muI 12246) 12
    (fun a => conditionalVariance (stdGauss (Fin (12246 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12246) 12
    (fun a => conditionalVariance (stdGauss (Fin (12246 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12246) (hw : WINDOW (paperDesignP 12246) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12246 4 (55 / 100) /
      (12246 : ℝ) / ((12246 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12246

/-! The dimension-12246 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12246
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12246) (wl ws : ℝ) : SplitData 12246 :=
  BstLean.Part162.dPaper (paperDesignP 12246) c wl ws
    (√(2 / (12246 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12246 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12246 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12246) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12246) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12246 : ℝ)) * eR c * 12246 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12246) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12246 - 1)))
    (rowSplit c wl ws).good a ∂muI 12246 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12246) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12246 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12246) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12246 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12246) c (rowSplit c wl ws),
    hellG2 12246 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12246 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12246} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12246} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12246 t c BstLean.Part259.agent12246.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12246} (R : RootSource t c) :
    |√(QStand (paperDesignP 12246) t c) - √(qTilde (paperDesignP 12246) t c)| ≤
      BstLean.Part259.agent12246.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12246

/-! Rational enclosures for the HQ fluctuation price at dimension 12247. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12247 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12247 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12247 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12247 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12247 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12247 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12247 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12247 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12247 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12247 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12247 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12247 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12247 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12247 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12247 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12247 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12247

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12247 ∧ √12247 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12247 ∧ 1000000 ≤ Jz 12247 := by
  have hr : (1105 / 10 : ℝ) ≤ √12247 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12247 : ℝ) * √12247 ≤ (⌈(12247 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12247
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12247 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12247 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12247 : ℝ) = (⌈(12247 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12247 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12247 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12247) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12247 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12247 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12247 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12247 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12247 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12247 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12247) :
    (12247 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12247 * √(qB 12247))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12247 * √(qB 12247) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12247 : ℝ) * √(qB 12247) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12247) :
    (12247 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12247 * √(qB 12247))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12247 : ℝ) * √(qB 12247) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12247 : ℝ) * (√12247 *
      (c1F (exp (1 / 2) / 12) (Jz 12247) * (186 / 10000) / Jz 12247)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12247)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12247 : ℝ) * (√12247 *
      (c1F (exp (1 / 2) / 12) (Jz 12247) * (186 / 10000) / Jz 12247)) =
      (12247 * (√12247 * c1F (exp (1 / 2) / 12) (Jz 12247)) * (186 / 10000)) /
        Jz 12247 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12247)]
  nlinarith

theorem row_energy_rule :
    (12247 : ℝ) * (12247 *
      (c2F (exp (1 / 2) / 12) (Jz 12247) * (186 / 10000) ^ 2 / Jz 12247)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12247)]
  nlinarith

end BstLean.Part262.Row12247

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12247) (hc : A1 c ∈ BstLean.Part153.Eop 12247) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12247 : ℝ)) ≤ (1597387023 / 125000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12247 : ℝ) + 2 * √12247 ≤ (1246833233 / 100000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12247 : ℝ) ≤ (22133233 / 200000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12247)
    (hc : A1 c ∈ BstLean.Part153.Eop 12247) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12247 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12247 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12247))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12247) (K : Set (Ix 12247)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12247 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12247 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12247) (hw : WINDOW (paperDesignP 12247) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12247)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12247) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12247 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12247 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12247 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12247 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12247) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12247)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12247)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12247

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12247) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12247 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12247) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12247) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12247 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12247 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12247 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12247}
    (hw : WINDOW (paperDesignP 12247) c) (hc : c ∈ tableEvent) (K : Set (Ix 12247)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12247) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12247)) : Prop where
  charge : (retDist (paperCentres 12247)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12247)} (h : TablePayment H) :
    (retDist (paperCentres 12247)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12247)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12247

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12247) (i : Fin 4) (a : Ix 12247) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12247) (a : Ix 12247) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12247) : Prop where
  moment : ∀ i, MomentBound (muI 12247) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12247} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12247) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12247

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12247) : Prop where
  location : LBound (muI 12247) 12
    (fun a => conditionalVariance (stdGauss (Fin (12247 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12247) 12
    (fun a => conditionalVariance (stdGauss (Fin (12247 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12247) (hw : WINDOW (paperDesignP 12247) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12247 4 (55 / 100) /
      (12247 : ℝ) / ((12247 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12247

/-! The dimension-12247 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12247
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12247) (wl ws : ℝ) : SplitData 12247 :=
  BstLean.Part162.dPaper (paperDesignP 12247) c wl ws
    (√(2 / (12247 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12247 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12247 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12247) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12247) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12247 : ℝ)) * eR c * 12247 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12247) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12247 - 1)))
    (rowSplit c wl ws).good a ∂muI 12247 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12247) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12247 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12247) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12247 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12247) c (rowSplit c wl ws),
    hellG2 12247 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12247 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12247} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12247} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12247 t c BstLean.Part259.agent12247.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12247} (R : RootSource t c) :
    |√(QStand (paperDesignP 12247) t c) - √(qTilde (paperDesignP 12247) t c)| ≤
      BstLean.Part259.agent12247.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12247

/-! Rational enclosures for the HQ fluctuation price at dimension 12248. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12248 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12248 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12248 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12248 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12248 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12248 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12248 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12248 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12248 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12248 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12248 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12248 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12248 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12248 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12248 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12248 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12248

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12248 ∧ √12248 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12248 ∧ 1000000 ≤ Jz 12248 := by
  have hr : (1105 / 10 : ℝ) ≤ √12248 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12248 : ℝ) * √12248 ≤ (⌈(12248 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12248
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12248 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12248 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12248 : ℝ) = (⌈(12248 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12248 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12248 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12248) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12248 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12248 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12248 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12248 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12248 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12248 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12248) :
    (12248 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12248 * √(qB 12248))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12248 * √(qB 12248) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12248 : ℝ) * √(qB 12248) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12248) :
    (12248 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12248 * √(qB 12248))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12248 : ℝ) * √(qB 12248) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12248 : ℝ) * (√12248 *
      (c1F (exp (1 / 2) / 12) (Jz 12248) * (186 / 10000) / Jz 12248)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12248)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12248 : ℝ) * (√12248 *
      (c1F (exp (1 / 2) / 12) (Jz 12248) * (186 / 10000) / Jz 12248)) =
      (12248 * (√12248 * c1F (exp (1 / 2) / 12) (Jz 12248)) * (186 / 10000)) /
        Jz 12248 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12248)]
  nlinarith

theorem row_energy_rule :
    (12248 : ℝ) * (12248 *
      (c2F (exp (1 / 2) / 12) (Jz 12248) * (186 / 10000) ^ 2 / Jz 12248)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12248)]
  nlinarith

end BstLean.Part262.Row12248

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12248) (hc : A1 c ∈ BstLean.Part153.Eop 12248) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12248 : ℝ)) ≤ (3194643623 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12248 : ℝ) + 2 * √12248 ≤ (6234670683 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12248 : ℝ) ≤ (110670683 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12248)
    (hc : A1 c ∈ BstLean.Part153.Eop 12248) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12248 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12248 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12248))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12248) (K : Set (Ix 12248)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12248 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12248 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12248) (hw : WINDOW (paperDesignP 12248) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12248)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12248) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12248 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12248 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12248 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12248 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12248) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12248)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12248)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12248

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12248) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12248 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12248) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12248) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12248 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12248 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12248 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12248}
    (hw : WINDOW (paperDesignP 12248) c) (hc : c ∈ tableEvent) (K : Set (Ix 12248)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12248) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12248)) : Prop where
  charge : (retDist (paperCentres 12248)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12248)} (h : TablePayment H) :
    (retDist (paperCentres 12248)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12248)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12248

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12248) (i : Fin 4) (a : Ix 12248) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12248) (a : Ix 12248) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12248) : Prop where
  moment : ∀ i, MomentBound (muI 12248) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12248} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12248) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12248

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12248) : Prop where
  location : LBound (muI 12248) 12
    (fun a => conditionalVariance (stdGauss (Fin (12248 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12248) 12
    (fun a => conditionalVariance (stdGauss (Fin (12248 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12248) (hw : WINDOW (paperDesignP 12248) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12248 4 (55 / 100) /
      (12248 : ℝ) / ((12248 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12248

/-! The dimension-12248 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12248
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12248) (wl ws : ℝ) : SplitData 12248 :=
  BstLean.Part162.dPaper (paperDesignP 12248) c wl ws
    (√(2 / (12248 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12248 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12248 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12248) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12248) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12248 : ℝ)) * eR c * 12248 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12248) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12248 - 1)))
    (rowSplit c wl ws).good a ∂muI 12248 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12248) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12248 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12248) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12248 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12248) c (rowSplit c wl ws),
    hellG2 12248 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12248 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12248} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12248} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12248 t c BstLean.Part259.agent12248.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12248} (R : RootSource t c) :
    |√(QStand (paperDesignP 12248) t c) - √(qTilde (paperDesignP 12248) t c)| ≤
      BstLean.Part259.agent12248.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12248

/-! Rational enclosures for the HQ fluctuation price at dimension 12249. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ 171 / 100
  epsilon : 0 ≤ ε ∧ ε ≤ 25 / 1000
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 235 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12249 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hs : √(A * D) ≤ 29 / 10 ^ 6 := by
    apply sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    exact (mul_le_mul hA.2 hD.2 hD.1 (by norm_num)).trans (by norm_num)
  have hT2 : κ * (12249 * A / 2 + D + L * √(A * D)) ≤ 452 / 100000 := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12249 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + (171 / 100) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12249 L e4 d4 ≤ 411 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12249 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + (171 / 100) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12249 L e6 d6 ≤ 618 / 10000 := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12249 / 2 * (235 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + (171 / 100) * (164 / 1000) * (235 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12249 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12249 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12249 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12249 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + 25 / 1000) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      (452 / 100000) ^ 2 / 2 + (452 / 100000) * (411 / 10000) ^ 2 / 6 +
      (411 / 10000) ^ 4 / 24 + (411 / 10000) ^ 2 * (618 / 10000) ^ 3 / 120 +
      2187 * (618 / 10000) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12249 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
  have hε1 : 0 < 1 - ε := by linarith
  have hsA : √A ≤ 638 / 10 ^ 6 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have hsD : √D ≤ 45 / 1000 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  unfold cubP
  calc
    _ ≤ (((12249 : ℝ) * ((1 + 3 * (25 / 1000)) / (4 * (1 - 25 / 1000)))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (235 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - 25 / 1000))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12249 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - 25 / 1000) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12249 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12249 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part262.Row12249

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : (110 : ℝ) ≤ √12249 ∧ √12249 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12249 ∧ 1000000 ≤ Jz 12249 := by
  have hr : (1105 / 10 : ℝ) ≤ √12249 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12249 : ℝ) * √12249 ≤ (⌈(12249 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12249
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12249 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12249 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12249 : ℝ) = (⌈(12249 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12249 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12249 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12249) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12249 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12249 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12249 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12249 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12249 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12249 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12249) :
    (12249 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12249 * √(qB 12249))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12249 * √(qB 12249) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12249 : ℝ) * √(qB 12249) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12249) :
    (12249 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12249 * √(qB 12249))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12249 : ℝ) * √(qB 12249) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12249 : ℝ) * (√12249 *
      (c1F (exp (1 / 2) / 12) (Jz 12249) * (186 / 10000) / Jz 12249)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12249)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12249 : ℝ) * (√12249 *
      (c1F (exp (1 / 2) / 12) (Jz 12249) * (186 / 10000) / Jz 12249)) =
      (12249 * (√12249 * c1F (exp (1 / 2) / 12) (Jz 12249)) * (186 / 10000)) /
        Jz 12249 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12249)]
  nlinarith

theorem row_energy_rule :
    (12249 : ℝ) * (12249 *
      (c2F (exp (1 / 2) / 12) (Jz 12249) * (186 / 10000) ^ 2 / Jz 12249)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12249)]
  nlinarith

end BstLean.Part262.Row12249

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12249) (hc : A1 c ∈ BstLean.Part153.Eop 12249) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12249 : ℝ)) ≤ (49914269 / 3906250000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12249 : ℝ) + 2 * √12249 ≤ (6235175201 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12249 : ℝ) ≤ (110675201 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12249)
    (hc : A1 c ∈ BstLean.Part153.Eop 12249) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12249 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12249 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12249))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12249) (K : Set (Ix 12249)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12249 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12249 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12249) (hw : WINDOW (paperDesignP 12249) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12249)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12249) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12249 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12249 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12249 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12249 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12249) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    (by norm_num) iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12249)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12249)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part262.Row12249

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12249) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12249 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12249) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12249) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12249 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12249 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12249 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
    ext c
    simp only [tableEvent, mem_setOf_eq, mem_union, mem_compl_iff, mem_inter_iff]
    constructor
    · intro h
      by_cases hw : BstLean.Part170.windowW c.1
      · exact Or.inr (h hw)
      · exact Or.inl hw
    · intro h hw
      exact h.elim (fun hn => False.elim (hn hw)) id
  rw [heq]
  exact hw.compl.union (hf.inter he)

theorem exactTableMoments_of_event {c : Ret 12249}
    (hw : WINDOW (paperDesignP 12249) c) (hc : c ∈ tableEvent) (K : Set (Ix 12249)) :
    ExactTableMoments c K := by
  have hθ := window_winC (by norm_num) c hw
  have h := hc hθ
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have hF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) Set.univ
  have hE := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) Set.univ
  rw [integrableOn_univ] at hF hE
  refine ⟨?_, ?_⟩
  · exact (setIntegral_le_integral hF (Filter.Eventually.of_forall fun a => by positivity)).trans h.1
  · exact (setIntegral_le_integral hE (Filter.Eventually.of_forall fun a => by positivity)).trans h.2

def proposedBaseEvent : Set (Ret 12249) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12249)) : Prop where
  charge : (retDist (paperCentres 12249)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12249)} (h : TablePayment H) :
    (retDist (paperCentres 12249)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12249)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part262.Row12249

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def actualFourError (c : Ret 12249) (i : Fin 4) (a : Ix 12249) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12249) (a : Ix 12249) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12249) : Prop where
  moment : ∀ i, MomentBound (muI 12249) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12249} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12249) 8 (actualFourError c i)
      (fourAllowances i) := (h.moment i).lower (by norm_num)
        (by fin_cases i <;> norm_num [biasOrder]) (by simp)
  have hF := (hb 0).add (by norm_num) (hb 1)
  have hW := (hb 2).add (by norm_num) (hb 3)
  have heF : (fun a => actualFourError c 0 a + actualFourError c 1 a) = exF c :=
    funext fun a => (actualFour_decomposition c a).1
  have heW : (fun a => actualFourError c 2 a + actualFourError c 3 a) = exW c :=
    funext fun a => (actualFour_decomposition c a).2
  rw [heF] at hF
  rw [heW] at hW
  have hFi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hF.power (k := 2) (r := 4))).squareIntegral
  have hWi := (LBound.ofMoment (by norm_num : (2 : ℕ) ≠ 0)
    (hW.power (k := 2) (r := 4))).squareIntegral
  simp only [← pow_mul] at hFi hWi
  intro _
  constructor
  · exact hFi.2.trans (by norm_num [fourAllowances])
  · exact hWi.2.trans (by norm_num [fourAllowances])

end BstLean.Part262.Row12249

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part162
open BstLean.Part169 BstLean.Part242
open BstLean.Part53 (unitF53)

theorem fLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C) (he : 0 < eR c)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have h := lambda_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC he hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) he.le
  have hf : (fun a => eR c * latitudeVariance (paperDesignP n) c (lamX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => fLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => fLatitude c (a, v)) = fun v => √(eR c) *
        lamX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      exact fX_eq_lam c _
    rw [hfun, conditionalVariance_scale, sq_sqrt he.le]
    rfl
  rw [hf] at hh
  have hc : eR c * ((C / (normSq ((paperDesignP n).bA c.1 c.2.1.1) / n)) /
      n / ((n : ℝ) - 2)) = C / n / ((n : ℝ) - 2) := by
    change eR c * (C / eR c / n / ((n : ℝ) - 2)) = _
    field_simp
  rwa [hc] at hh

theorem zLatitude_variance_norm12 {n : ℕ} (hn : 3 ≤ n) (c : Ret n)
    {C : ℝ} (hC : 0 ≤ C)
    (hk : agKey (paperDesignP n) c ∈ BstLean.Part212.latitudeEvent n
      (ENNReal.ofReal (C / n))) :
    LBound (muI n) 12
      (fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)))
      (C / n / ((n : ℝ) - 2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hγ : (0 : ℝ) < 2 / n := by positivity
  have h := residual_variance_norm12 hn (paperDesignP n)
    (paperDesign_agentCentre _ _ _ _) c hC hk
  have hh := h.scale (by norm_num : (12 : ℕ) ≠ 0) (sq_nonneg (√(2 / (n : ℝ)))⁻¹)
  have hf : (fun a => (√(2 / (n : ℝ)))⁻¹ ^ 2 *
      latitudeVariance (paperDesignP n) c (sigX (paperDesignP n) c) a) =
      fun a => conditionalVariance (stdGauss (Fin (n - 1))) (fun v => zLatitude c (a, v)) := by
    funext a
    have hfun : (fun v => zLatitude c (a, v)) = fun v => (√(2 / (n : ℝ)))⁻¹ *
        sigX (paperDesignP n) c (xLat c (latC (paperDesignP n) c a) (unitF53 v)) := by
      funext v
      simp only [zLatitude, sgA, div_eq_mul_inv, mul_comm]
    rw [hfun, conditionalVariance_scale]
    rfl
  rw [hf] at hh
  have hc : (√(2 / (n : ℝ)))⁻¹ ^ 2 * ((2 * C / n) / n / ((n : ℝ) - 2)) =
      C / n / ((n : ℝ) - 2) := by
    rw [inv_pow, sq_sqrt hγ.le]
    field_simp
    <;> ring
  rwa [hc] at hh

noncomputable def varianceTwelve : ℝ := 1 / 46000000

structure LatitudeVarianceCertificate (c : Ret 12249) : Prop where
  location : LBound (muI 12249) 12
    (fun a => conditionalVariance (stdGauss (Fin (12249 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12249) 12
    (fun a => conditionalVariance (stdGauss (Fin (12249 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12249) (hw : WINDOW (paperDesignP 12249) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12249 4 (55 / 100) /
      (12249 : ℝ) / ((12249 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part262.Row12249

/-! The dimension-12249 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part262.Row12249
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12249) (wl ws : ℝ) : SplitData 12249 :=
  BstLean.Part162.dPaper (paperDesignP 12249) c wl ws
    (√(2 / (12249 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12249 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12249 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12249) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12249) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12249 : ℝ)) * eR c * 12249 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12249) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12249 - 1)))
    (rowSplit c wl ws).good a ∂muI 12249 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12249) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12249 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12249) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12249 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12249) c (rowSplit c wl ws),
    hellG2 12249 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12249 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12249} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12249} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12249 t c BstLean.Part259.agent12249.root where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := energyError
  af := locationError
  Hf := locationNorm
  Cv := varianceNorm
  B := removalBudget
  mix := mixtureRoot
  displacement := displacementBudget
  window := R.window
  passes := row_pass_inputs R
  fluctuation := by
    refine ⟨removalBudget, mixtureRoot ^ 2, displacementBudget,
      R.removal, R.mixture, R.displacement, ?_⟩
    rw [Real.sqrt_sq (by norm_num [mixtureRoot])]
  scalar := root_reserve

theorem replacement_of_source {t : ℝ} {c : Ret 12249} (R : RootSource t c) :
    |√(QStand (paperDesignP 12249) t c) - √(qTilde (paperDesignP 12249) t c)| ≤
      BstLean.Part259.agent12249.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part262.Row12249
