import BstLean.Part266Shard14Step1


/-! Rational enclosures for the HQ fluctuation price at dimension 12700. -/
namespace BstLean.Part266.Row12700
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1647087543 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11626759 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12700 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12700 * A / 2 + D + L * √(A * D)) ≤ (917489681 / 200000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12700 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1647087543 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12700 L e4 d4 ≤ (10389939629 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12700 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1647087543 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12700 L e6 d6 ≤ (15740837303 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12700 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1647087543 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12700 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12700 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12700 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12700 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11626759 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((917489681 / 200000000000)) ^ 2 / 2 + ((917489681 / 200000000000)) * ((10389939629 / 250000000000)) ^ 2 / 6 +
      ((10389939629 / 250000000000)) ^ 4 / 24 + ((10389939629 / 250000000000)) ^ 2 * ((15740837303 / 250000000000)) ^ 3 / 120 +
      2187 * ((15740837303 / 250000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12700 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12700 : ℝ) * ((1 + 3 * ((11626759 / 500000000))) / (4 * (1 - (11626759 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11626759 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12700 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11626759 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12700 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12700 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12700

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12700
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((28173569 / 250000) : ℝ) ≤ √12700 ∧ √12700 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1431216 : ℝ) ≤ Jz 12700 ∧ 1000000 ≤ Jz 12700 := by
  have hr : ((28173569 / 250000) : ℝ) ≤ √12700 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12700 : ℝ) * √12700 ≤ (⌈(12700 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12700
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12700 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12700 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12700 : ℝ) = (⌈(12700 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1431216 : ℝ) ≤ Jz 12700 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12700 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12700) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12700 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12700 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12700 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12700 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12700 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12700 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12700) :
    (12700 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12700 * √(qB 12700))) ≤
      (268175263 / 500000000000) := by
  have hden : ((28173569 / 250000) : ℝ) * (63 / 100) ≤ √12700 * √(qB 12700) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12700 : ℝ) * √(qB 12700) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12700) :
    (12700 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12700 * √(qB 12700))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12700 : ℝ) * √(qB 12700) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12700 : ℝ) * (√12700 *
      (c1F (exp (1 / 2) / 12) (Jz 12700) * (186 / 10000) / Jz 12700)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12700)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12700 : ℝ) * (√12700 *
      (c1F (exp (1 / 2) / 12) (Jz 12700) * (186 / 10000) / Jz 12700)) =
      (12700 * (√12700 * c1F (exp (1 / 2) / 12) (Jz 12700)) * (186 / 10000)) /
        Jz 12700 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12700)]
  nlinarith

theorem row_energy_rule :
    (12700 : ℝ) * (12700 *
      (c2F (exp (1 / 2) / 12) (Jz 12700) * (186 / 10000) ^ 2 / Jz 12700)) ≤
      (3508897299 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12700)]
  nlinarith

end BstLean.Part266.Row12700

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12700
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12700) (hc : A1 c ∈ BstLean.Part153.Eop 12700) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12700 : ℝ)) ≤ (12549116103 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12700 : ℝ) + 2 * √12700 ≤ (6462694277 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12700 : ℝ) ≤ (112694277 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12700)
    (hc : A1 c ∈ BstLean.Part153.Eop 12700) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12700 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12700 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12700))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12700) (K : Set (Ix 12700)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12700 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12700 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12700) (hw : WINDOW (paperDesignP 12700) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12700)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12700) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12700 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12700 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12700 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12700 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12700) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12700)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12700)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12700

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12700
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12700) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12700 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12700) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12700) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12700 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12700 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12700 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12700}
    (hw : WINDOW (paperDesignP 12700) c) (hc : c ∈ tableEvent) (K : Set (Ix 12700)) :
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

def proposedBaseEvent : Set (Ret 12700) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12700)) : Prop where
  charge : (retDist (paperCentres 12700)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12700)} (h : TablePayment H) :
    (retDist (paperCentres 12700)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12700)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12700

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12700
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12700) (i : Fin 4) (a : Ix 12700) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12700) (a : Ix 12700) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12700) : Prop where
  moment : ∀ i, MomentBound (muI 12700) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12700} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12700) 8 (actualFourError c i)
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

end BstLean.Part266.Row12700

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12700
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

structure LatitudeVarianceCertificate (c : Ret 12700) : Prop where
  location : LBound (muI 12700) 12
    (fun a => conditionalVariance (stdGauss (Fin (12700 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12700) 12
    (fun a => conditionalVariance (stdGauss (Fin (12700 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12700) (hw : WINDOW (paperDesignP 12700) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12700 4 (55 / 100) /
      (12700 : ℝ) / ((12700 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12700

/-! The dimension-12700 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12700
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12700) (wl ws : ℝ) : SplitData 12700 :=
  BstLean.Part162.dPaper (paperDesignP 12700) c wl ws
    (√(2 / (12700 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12700 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12700 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12700) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12700) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12700 : ℝ)) * eR c * 12700 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12700) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12700 - 1)))
    (rowSplit c wl ws).good a ∂muI 12700 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12700) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12700 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12700) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12700 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12700) c (rowSplit c wl ws),
    hellG2 12700 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12700 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12700} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12700} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12700 t c BstLean.Part266.agent12700.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12700} (R : RootSource t c) :
    |√(QStand (paperDesignP 12700) t c) - √(qTilde (paperDesignP 12700) t c)| ≤
      BstLean.Part266.agent12700.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12700

/-! Rational enclosures for the HQ fluctuation price at dimension 12701. -/
namespace BstLean.Part266.Row12701
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (823511233 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23251673 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12701 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12701 * A / 2 + D + L * √(A * D)) ≤ (4587649719 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12701 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((823511233 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12701 L e4 d4 ≤ (10390396731 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12701 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((823511233 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12701 L e6 d6 ≤ (1967690987 / 31250000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12701 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((823511233 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12701 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12701 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12701 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12701 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23251673 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4587649719 / 1000000000000)) ^ 2 / 2 + ((4587649719 / 1000000000000)) * ((10390396731 / 250000000000)) ^ 2 / 6 +
      ((10390396731 / 250000000000)) ^ 4 / 24 + ((10390396731 / 250000000000)) ^ 2 * ((1967690987 / 31250000000)) ^ 3 / 120 +
      2187 * ((1967690987 / 31250000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12701 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12701 : ℝ) * ((1 + 3 * ((23251673 / 1000000000))) / (4 * (1 - (23251673 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23251673 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12701 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23251673 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12701 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12701 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12701

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12701
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((112698713 / 1000000) : ℝ) ≤ √12701 ∧ √12701 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1431385 : ℝ) ≤ Jz 12701 ∧ 1000000 ≤ Jz 12701 := by
  have hr : ((112698713 / 1000000) : ℝ) ≤ √12701 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12701 : ℝ) * √12701 ≤ (⌈(12701 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12701
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12701 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12701 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12701 : ℝ) = (⌈(12701 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1431385 : ℝ) ≤ Jz 12701 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12701 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12701) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12701 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12701 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12701 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12701 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12701 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12701 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12701) :
    (12701 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12701 * √(qB 12701))) ≤
      (13409291 / 25000000000) := by
  have hden : ((112698713 / 1000000) : ℝ) * (63 / 100) ≤ √12701 * √(qB 12701) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12701 : ℝ) * √(qB 12701) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12701) :
    (12701 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12701 * √(qB 12701))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12701 : ℝ) * √(qB 12701) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12701 : ℝ) * (√12701 *
      (c1F (exp (1 / 2) / 12) (Jz 12701) * (186 / 10000) / Jz 12701)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12701)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12701 : ℝ) * (√12701 *
      (c1F (exp (1 / 2) / 12) (Jz 12701) * (186 / 10000) / Jz 12701)) =
      (12701 * (√12701 * c1F (exp (1 / 2) / 12) (Jz 12701)) * (186 / 10000)) /
        Jz 12701 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12701)]
  nlinarith

theorem row_energy_rule :
    (12701 : ℝ) * (12701 *
      (c2F (exp (1 / 2) / 12) (Jz 12701) * (186 / 10000) ^ 2 / Jz 12701)) ≤
      (3509035551 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12701)]
  nlinarith

end BstLean.Part266.Row12701

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12701
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12701) (hc : A1 c ∈ BstLean.Part153.Eop 12701) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12701 : ℝ)) ≤ (12548622073 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12701 : ℝ) + 2 * √12701 ≤ (3231599357 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12701 : ℝ) ≤ (56349357 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12701)
    (hc : A1 c ∈ BstLean.Part153.Eop 12701) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12701 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12701 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12701))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12701) (K : Set (Ix 12701)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12701 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12701 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12701) (hw : WINDOW (paperDesignP 12701) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12701)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12701) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12701 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12701 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12701 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12701 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12701) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12701)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12701)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12701

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12701
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12701) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12701 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12701) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12701) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12701 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12701 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12701 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12701}
    (hw : WINDOW (paperDesignP 12701) c) (hc : c ∈ tableEvent) (K : Set (Ix 12701)) :
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

def proposedBaseEvent : Set (Ret 12701) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12701)) : Prop where
  charge : (retDist (paperCentres 12701)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12701)} (h : TablePayment H) :
    (retDist (paperCentres 12701)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12701)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12701

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12701
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12701) (i : Fin 4) (a : Ix 12701) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12701) (a : Ix 12701) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12701) : Prop where
  moment : ∀ i, MomentBound (muI 12701) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12701} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12701) 8 (actualFourError c i)
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

end BstLean.Part266.Row12701

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12701
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

structure LatitudeVarianceCertificate (c : Ret 12701) : Prop where
  location : LBound (muI 12701) 12
    (fun a => conditionalVariance (stdGauss (Fin (12701 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12701) 12
    (fun a => conditionalVariance (stdGauss (Fin (12701 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12701) (hw : WINDOW (paperDesignP 12701) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12701 4 (55 / 100) /
      (12701 : ℝ) / ((12701 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12701

/-! The dimension-12701 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12701
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12701) (wl ws : ℝ) : SplitData 12701 :=
  BstLean.Part162.dPaper (paperDesignP 12701) c wl ws
    (√(2 / (12701 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12701 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12701 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12701) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12701) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12701 : ℝ)) * eR c * 12701 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12701) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12701 - 1)))
    (rowSplit c wl ws).good a ∂muI 12701 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12701) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12701 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12701) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12701 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12701) c (rowSplit c wl ws),
    hellG2 12701 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12701 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12701} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12701} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12701 t c BstLean.Part266.agent12701.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12701} (R : RootSource t c) :
    |√(QStand (paperDesignP 12701) t c) - √(qTilde (paperDesignP 12701) t c)| ≤
      BstLean.Part266.agent12701.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12701

/-! Rational enclosures for the HQ fluctuation price at dimension 12702. -/
namespace BstLean.Part266.Row12702
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (329391481 / 200000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23249829 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12702 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12702 * A / 2 + D + L * √(A * D)) ≤ (4587851033 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12702 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((329391481 / 200000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12702 L e4 d4 ≤ (41563415337 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12702 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((329391481 / 200000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12702 L e6 d6 ≤ (62968873963 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12702 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((329391481 / 200000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12702 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12702 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12702 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12702 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23249829 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4587851033 / 1000000000000)) ^ 2 / 2 + ((4587851033 / 1000000000000)) * ((41563415337 / 1000000000000)) ^ 2 / 6 +
      ((41563415337 / 1000000000000)) ^ 4 / 24 + ((41563415337 / 1000000000000)) ^ 2 * ((62968873963 / 1000000000000)) ^ 3 / 120 +
      2187 * ((62968873963 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12702 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12702 : ℝ) * ((1 + 3 * ((23249829 / 1000000000))) / (4 * (1 - (23249829 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23249829 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12702 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23249829 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12702 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12702 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12702

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12702
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((112703149 / 1000000) : ℝ) ≤ √12702 ∧ √12702 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1431554 : ℝ) ≤ Jz 12702 ∧ 1000000 ≤ Jz 12702 := by
  have hr : ((112703149 / 1000000) : ℝ) ≤ √12702 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12702 : ℝ) * √12702 ≤ (⌈(12702 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12702
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12702 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12702 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12702 : ℝ) = (⌈(12702 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1431554 : ℝ) ≤ Jz 12702 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12702 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12702) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12702 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12702 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12702 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12702 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12702 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12702 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12702) :
    (12702 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12702 * √(qB 12702))) ≤
      (536392757 / 1000000000000) := by
  have hden : ((112703149 / 1000000) : ℝ) * (63 / 100) ≤ √12702 * √(qB 12702) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12702 : ℝ) * √(qB 12702) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12702) :
    (12702 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12702 * √(qB 12702))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12702 : ℝ) * √(qB 12702) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12702 : ℝ) * (√12702 *
      (c1F (exp (1 / 2) / 12) (Jz 12702) * (186 / 10000) / Jz 12702)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12702)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12702 : ℝ) * (√12702 *
      (c1F (exp (1 / 2) / 12) (Jz 12702) * (186 / 10000) / Jz 12702)) =
      (12702 * (√12702 * c1F (exp (1 / 2) / 12) (Jz 12702)) * (186 / 10000)) /
        Jz 12702 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12702)]
  nlinarith

theorem row_energy_rule :
    (12702 : ℝ) * (12702 *
      (c2F (exp (1 / 2) / 12) (Jz 12702) * (186 / 10000) ^ 2 / Jz 12702)) ≤
      (1754586907 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12702)]
  nlinarith

end BstLean.Part266.Row12702

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12702
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12702) (hc : A1 c ∈ BstLean.Part153.Eop 12702) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12702 : ℝ)) ≤ (12548128101 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12702 : ℝ) + 2 * √12702 ≤ (129274063 / 10000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12702 : ℝ) ≤ (2254063 / 20000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12702)
    (hc : A1 c ∈ BstLean.Part153.Eop 12702) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12702 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12702 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12702))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12702) (K : Set (Ix 12702)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12702 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12702 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12702) (hw : WINDOW (paperDesignP 12702) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12702)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12702) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12702 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12702 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12702 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12702 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12702) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12702)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12702)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12702

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12702
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12702) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12702 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12702) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12702) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12702 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12702 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12702 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12702}
    (hw : WINDOW (paperDesignP 12702) c) (hc : c ∈ tableEvent) (K : Set (Ix 12702)) :
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

def proposedBaseEvent : Set (Ret 12702) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12702)) : Prop where
  charge : (retDist (paperCentres 12702)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12702)} (h : TablePayment H) :
    (retDist (paperCentres 12702)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12702)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12702

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12702
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12702) (i : Fin 4) (a : Ix 12702) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12702) (a : Ix 12702) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12702) : Prop where
  moment : ∀ i, MomentBound (muI 12702) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12702} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12702) 8 (actualFourError c i)
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

end BstLean.Part266.Row12702

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12702
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

structure LatitudeVarianceCertificate (c : Ret 12702) : Prop where
  location : LBound (muI 12702) 12
    (fun a => conditionalVariance (stdGauss (Fin (12702 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12702) 12
    (fun a => conditionalVariance (stdGauss (Fin (12702 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12702) (hw : WINDOW (paperDesignP 12702) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12702 4 (55 / 100) /
      (12702 : ℝ) / ((12702 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12702

/-! The dimension-12702 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12702
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12702) (wl ws : ℝ) : SplitData 12702 :=
  BstLean.Part162.dPaper (paperDesignP 12702) c wl ws
    (√(2 / (12702 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12702 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12702 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12702) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12702) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12702 : ℝ)) * eR c * 12702 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12702) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12702 - 1)))
    (rowSplit c wl ws).good a ∂muI 12702 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12702) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12702 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12702) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12702 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12702) c (rowSplit c wl ws),
    hellG2 12702 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12702 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12702} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12702} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12702 t c BstLean.Part266.agent12702.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12702} (R : RootSource t c) :
    |√(QStand (paperDesignP 12702) t c) - √(qTilde (paperDesignP 12702) t c)| ≤
      BstLean.Part266.agent12702.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12702

/-! Rational enclosures for the HQ fluctuation price at dimension 12703. -/
namespace BstLean.Part266.Row12703
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (10293079 / 6250000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23247989 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12703 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12703 * A / 2 + D + L * √(A * D)) ≤ (1147013089 / 250000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12703 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((10293079 / 6250000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12703 L e4 d4 ≤ (1662609753 / 40000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12703 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((10293079 / 6250000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12703 L e6 d6 ≤ (7871454557 / 125000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12703 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((10293079 / 6250000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12703 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12703 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12703 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12703 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23247989 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((1147013089 / 250000000000)) ^ 2 / 2 + ((1147013089 / 250000000000)) * ((1662609753 / 40000000000)) ^ 2 / 6 +
      ((1662609753 / 40000000000)) ^ 4 / 24 + ((1662609753 / 40000000000)) ^ 2 * ((7871454557 / 125000000000)) ^ 3 / 120 +
      2187 * ((7871454557 / 125000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12703 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12703 : ℝ) * ((1 + 3 * ((23247989 / 1000000000))) / (4 * (1 - (23247989 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23247989 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12703 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23247989 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12703 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12703 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12703

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12703
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((56353793 / 500000) : ℝ) ≤ √12703 ∧ √12703 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1431723 : ℝ) ≤ Jz 12703 ∧ 1000000 ≤ Jz 12703 := by
  have hr : ((56353793 / 500000) : ℝ) ≤ √12703 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12703 : ℝ) * √12703 ≤ (⌈(12703 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12703
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12703 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12703 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12703 : ℝ) = (⌈(12703 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1431723 : ℝ) ≤ Jz 12703 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12703 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12703) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12703 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12703 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12703 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12703 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12703 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12703 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12703) :
    (12703 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12703 * √(qB 12703))) ≤
      (134103467 / 250000000000) := by
  have hden : ((56353793 / 500000) : ℝ) * (63 / 100) ≤ √12703 * √(qB 12703) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12703 : ℝ) * √(qB 12703) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12703) :
    (12703 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12703 * √(qB 12703))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12703 : ℝ) * √(qB 12703) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12703 : ℝ) * (√12703 *
      (c1F (exp (1 / 2) / 12) (Jz 12703) * (186 / 10000) / Jz 12703)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12703)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12703 : ℝ) * (√12703 *
      (c1F (exp (1 / 2) / 12) (Jz 12703) * (186 / 10000) / Jz 12703)) =
      (12703 * (√12703 * c1F (exp (1 / 2) / 12) (Jz 12703)) * (186 / 10000)) /
        Jz 12703 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12703)]
  nlinarith

theorem row_energy_rule :
    (12703 : ℝ) * (12703 *
      (c2F (exp (1 / 2) / 12) (Jz 12703) * (186 / 10000) ^ 2 / Jz 12703)) ≤
      (438664011 / 125000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12703)]
  nlinarith

end BstLean.Part266.Row12703

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12703
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12703) (hc : A1 c ∈ BstLean.Part153.Eop 12703) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12703 : ℝ)) ≤ (12547634187 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12703 : ℝ) + 2 * √12703 ≤ (6464207587 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12703 : ℝ) ≤ (112707587 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12703)
    (hc : A1 c ∈ BstLean.Part153.Eop 12703) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12703 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12703 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12703))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12703) (K : Set (Ix 12703)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12703 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12703 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12703) (hw : WINDOW (paperDesignP 12703) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12703)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12703) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12703 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12703 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12703 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12703 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12703) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12703)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12703)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12703

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12703
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12703) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12703 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12703) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12703) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12703 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12703 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12703 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12703}
    (hw : WINDOW (paperDesignP 12703) c) (hc : c ∈ tableEvent) (K : Set (Ix 12703)) :
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

def proposedBaseEvent : Set (Ret 12703) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12703)) : Prop where
  charge : (retDist (paperCentres 12703)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12703)} (h : TablePayment H) :
    (retDist (paperCentres 12703)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12703)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12703

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12703
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12703) (i : Fin 4) (a : Ix 12703) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12703) (a : Ix 12703) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12703) : Prop where
  moment : ∀ i, MomentBound (muI 12703) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12703} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12703) 8 (actualFourError c i)
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

end BstLean.Part266.Row12703

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12703
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

structure LatitudeVarianceCertificate (c : Ret 12703) : Prop where
  location : LBound (muI 12703) 12
    (fun a => conditionalVariance (stdGauss (Fin (12703 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12703) 12
    (fun a => conditionalVariance (stdGauss (Fin (12703 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12703) (hw : WINDOW (paperDesignP 12703) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12703 4 (55 / 100) /
      (12703 : ℝ) / ((12703 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12703

/-! The dimension-12703 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12703
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12703) (wl ws : ℝ) : SplitData 12703 :=
  BstLean.Part162.dPaper (paperDesignP 12703) c wl ws
    (√(2 / (12703 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12703 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12703 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12703) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12703) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12703 : ℝ)) * eR c * 12703 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12703) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12703 - 1)))
    (rowSplit c wl ws).good a ∂muI 12703 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12703) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12703 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12703) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12703 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12703) c (rowSplit c wl ws),
    hellG2 12703 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12703 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12703} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12703} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12703 t c BstLean.Part266.agent12703.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12703} (R : RootSource t c) :
    |√(QStand (paperDesignP 12703) t c) - √(qTilde (paperDesignP 12703) t c)| ≤
      BstLean.Part266.agent12703.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12703

/-! Rational enclosures for the HQ fluctuation price at dimension 12704. -/
namespace BstLean.Part266.Row12704
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (205853451 / 125000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (4649229 / 200000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12704 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12704 * A / 2 + D + L * √(A * D)) ≤ (4588253671 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12704 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((205853451 / 125000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12704 L e4 d4 ≤ (8313414449 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12704 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((205853451 / 125000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12704 L e6 d6 ≤ (12594879769 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12704 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((205853451 / 125000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12704 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12704 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12704 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12704 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (4649229 / 200000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4588253671 / 1000000000000)) ^ 2 / 2 + ((4588253671 / 1000000000000)) * ((8313414449 / 200000000000)) ^ 2 / 6 +
      ((8313414449 / 200000000000)) ^ 4 / 24 + ((8313414449 / 200000000000)) ^ 2 * ((12594879769 / 200000000000)) ^ 3 / 120 +
      2187 * ((12594879769 / 200000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12704 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12704 : ℝ) * ((1 + 3 * ((4649229 / 200000000))) / (4 * (1 - (4649229 / 200000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (4649229 / 200000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12704 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (4649229 / 200000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12704 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12704 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12704

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12704
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((56356011 / 500000) : ℝ) ≤ √12704 ∧ √12704 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1431892 : ℝ) ≤ Jz 12704 ∧ 1000000 ≤ Jz 12704 := by
  have hr : ((56356011 / 500000) : ℝ) ≤ √12704 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12704 : ℝ) * √12704 ≤ (⌈(12704 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12704
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12704 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12704 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12704 : ℝ) = (⌈(12704 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1431892 : ℝ) ≤ Jz 12704 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12704 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12704) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12704 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12704 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12704 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12704 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12704 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12704 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12704) :
    (12704 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12704 * √(qB 12704))) ≤
      (268217491 / 500000000000) := by
  have hden : ((56356011 / 500000) : ℝ) * (63 / 100) ≤ √12704 * √(qB 12704) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12704 : ℝ) * √(qB 12704) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12704) :
    (12704 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12704 * √(qB 12704))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12704 : ℝ) * √(qB 12704) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12704 : ℝ) * (√12704 *
      (c1F (exp (1 / 2) / 12) (Jz 12704) * (186 / 10000) / Jz 12704)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12704)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12704 : ℝ) * (√12704 *
      (c1F (exp (1 / 2) / 12) (Jz 12704) * (186 / 10000) / Jz 12704)) =
      (12704 * (√12704 * c1F (exp (1 / 2) / 12) (Jz 12704)) * (186 / 10000)) /
        Jz 12704 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12704)]
  nlinarith

theorem row_energy_rule :
    (12704 : ℝ) * (12704 *
      (c2F (exp (1 / 2) / 12) (Jz 12704) * (186 / 10000) ^ 2 / Jz 12704)) ≤
      (3509450373 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12704)]
  nlinarith

end BstLean.Part266.Row12704

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12704
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12704) (hc : A1 c ∈ BstLean.Part153.Eop 12704) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12704 : ℝ)) ≤ (12547140331 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12704 : ℝ) + 2 * √12704 ≤ (6464712023 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12704 : ℝ) ≤ (112712023 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12704)
    (hc : A1 c ∈ BstLean.Part153.Eop 12704) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12704 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12704 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12704))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12704) (K : Set (Ix 12704)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12704 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12704 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12704) (hw : WINDOW (paperDesignP 12704) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12704)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12704) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12704 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12704 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12704 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12704 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12704) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12704)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12704)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12704

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12704
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12704) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12704 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12704) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12704) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12704 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12704 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12704 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12704}
    (hw : WINDOW (paperDesignP 12704) c) (hc : c ∈ tableEvent) (K : Set (Ix 12704)) :
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

def proposedBaseEvent : Set (Ret 12704) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12704)) : Prop where
  charge : (retDist (paperCentres 12704)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12704)} (h : TablePayment H) :
    (retDist (paperCentres 12704)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12704)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12704

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12704
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12704) (i : Fin 4) (a : Ix 12704) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12704) (a : Ix 12704) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12704) : Prop where
  moment : ∀ i, MomentBound (muI 12704) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12704} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12704) 8 (actualFourError c i)
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

end BstLean.Part266.Row12704

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12704
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

structure LatitudeVarianceCertificate (c : Ret 12704) : Prop where
  location : LBound (muI 12704) 12
    (fun a => conditionalVariance (stdGauss (Fin (12704 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12704) 12
    (fun a => conditionalVariance (stdGauss (Fin (12704 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12704) (hw : WINDOW (paperDesignP 12704) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12704 4 (55 / 100) /
      (12704 : ℝ) / ((12704 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12704

/-! The dimension-12704 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12704
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12704) (wl ws : ℝ) : SplitData 12704 :=
  BstLean.Part162.dPaper (paperDesignP 12704) c wl ws
    (√(2 / (12704 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12704 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12704 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12704) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12704) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12704 : ℝ)) * eR c * 12704 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12704) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12704 - 1)))
    (rowSplit c wl ws).good a ∂muI 12704 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12704) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12704 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12704) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12704 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12704) c (rowSplit c wl ws),
    hellG2 12704 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12704 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12704} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12704} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12704 t c BstLean.Part266.agent12704.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12704} (R : RootSource t c) :
    |√(QStand (paperDesignP 12704) t c) - √(qTilde (paperDesignP 12704) t c)| ≤
      BstLean.Part266.agent12704.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12704

/-! Rational enclosures for the HQ fluctuation price at dimension 12705. -/
namespace BstLean.Part266.Row12705
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (51461331 / 31250000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11622151 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12705 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12705 * A / 2 + D + L * √(A * D)) ≤ (4588454987 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12705 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((51461331 / 31250000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12705 L e4 d4 ≤ (41568900669 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12705 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((51461331 / 31250000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12705 L e6 d6 ≤ (62977161241 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12705 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((51461331 / 31250000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12705 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12705 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12705 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12705 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11622151 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4588454987 / 1000000000000)) ^ 2 / 2 + ((4588454987 / 1000000000000)) * ((41568900669 / 1000000000000)) ^ 2 / 6 +
      ((41568900669 / 1000000000000)) ^ 4 / 24 + ((41568900669 / 1000000000000)) ^ 2 * ((62977161241 / 1000000000000)) ^ 3 / 120 +
      2187 * ((62977161241 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12705 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12705 : ℝ) * ((1 + 3 * ((11622151 / 500000000))) / (4 * (1 - (11622151 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11622151 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12705 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11622151 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12705 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12705 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12705

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12705
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((56358229 / 500000) : ℝ) ≤ √12705 ∧ √12705 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1432061 : ℝ) ≤ Jz 12705 ∧ 1000000 ≤ Jz 12705 := by
  have hr : ((56358229 / 500000) : ℝ) ≤ √12705 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12705 : ℝ) * √12705 ≤ (⌈(12705 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12705
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12705 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12705 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12705 : ℝ) = (⌈(12705 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1432061 : ℝ) ≤ Jz 12705 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12705 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12705) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12705 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12705 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12705 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12705 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12705 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12705 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12705) :
    (12705 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12705 * √(qB 12705))) ≤
      (107291219 / 200000000000) := by
  have hden : ((56358229 / 500000) : ℝ) * (63 / 100) ≤ √12705 * √(qB 12705) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12705 : ℝ) * √(qB 12705) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12705) :
    (12705 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12705 * √(qB 12705))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12705 : ℝ) * √(qB 12705) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12705 : ℝ) * (√12705 *
      (c1F (exp (1 / 2) / 12) (Jz 12705) * (186 / 10000) / Jz 12705)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12705)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12705 : ℝ) * (√12705 *
      (c1F (exp (1 / 2) / 12) (Jz 12705) * (186 / 10000) / Jz 12705)) =
      (12705 * (√12705 * c1F (exp (1 / 2) / 12) (Jz 12705)) * (186 / 10000)) /
        Jz 12705 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12705)]
  nlinarith

theorem row_energy_rule :
    (12705 : ℝ) * (12705 *
      (c2F (exp (1 / 2) / 12) (Jz 12705) * (186 / 10000) ^ 2 / Jz 12705)) ≤
      (877397167 / 250000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12705)]
  nlinarith

end BstLean.Part266.Row12705

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12705
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12705) (hc : A1 c ∈ BstLean.Part153.Eop 12705) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12705 : ℝ)) ≤ (6273323267 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12705 : ℝ) + 2 * √12705 ≤ (6465216459 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12705 : ℝ) ≤ (112716459 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12705)
    (hc : A1 c ∈ BstLean.Part153.Eop 12705) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12705 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12705 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12705))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12705) (K : Set (Ix 12705)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12705 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12705 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12705) (hw : WINDOW (paperDesignP 12705) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12705)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12705) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12705 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12705 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12705 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12705 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12705) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12705)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12705)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12705

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12705
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12705) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12705 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12705) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12705) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12705 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12705 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12705 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12705}
    (hw : WINDOW (paperDesignP 12705) c) (hc : c ∈ tableEvent) (K : Set (Ix 12705)) :
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

def proposedBaseEvent : Set (Ret 12705) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12705)) : Prop where
  charge : (retDist (paperCentres 12705)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12705)} (h : TablePayment H) :
    (retDist (paperCentres 12705)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12705)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12705

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12705
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12705) (i : Fin 4) (a : Ix 12705) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12705) (a : Ix 12705) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12705) : Prop where
  moment : ∀ i, MomentBound (muI 12705) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12705} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12705) 8 (actualFourError c i)
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

end BstLean.Part266.Row12705

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12705
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

structure LatitudeVarianceCertificate (c : Ret 12705) : Prop where
  location : LBound (muI 12705) 12
    (fun a => conditionalVariance (stdGauss (Fin (12705 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12705) 12
    (fun a => conditionalVariance (stdGauss (Fin (12705 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12705) (hw : WINDOW (paperDesignP 12705) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12705 4 (55 / 100) /
      (12705 : ℝ) / ((12705 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12705

/-! The dimension-12705 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12705
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12705) (wl ws : ℝ) : SplitData 12705 :=
  BstLean.Part162.dPaper (paperDesignP 12705) c wl ws
    (√(2 / (12705 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12705 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12705 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12705) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12705) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12705 : ℝ)) * eR c * 12705 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12705) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12705 - 1)))
    (rowSplit c wl ws).good a ∂muI 12705 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12705) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12705 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12705) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12705 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12705) c (rowSplit c wl ws),
    hellG2 12705 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12705 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12705} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12705} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12705 t c BstLean.Part266.agent12705.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12705} (R : RootSource t c) :
    |√(QStand (paperDesignP 12705) t c) - √(qTilde (paperDesignP 12705) t c)| ≤
      BstLean.Part266.agent12705.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12705

/-! Rational enclosures for the HQ fluctuation price at dimension 12706. -/
namespace BstLean.Part266.Row12706
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (823348937 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23242463 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12706 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12706 * A / 2 + D + L * √(A * D)) ≤ (4588656311 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12706 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((823348937 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12706 L e4 d4 ≤ (4157072917 / 100000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12706 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((823348937 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12706 L e6 d6 ≤ (7872490469 / 125000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12706 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((823348937 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12706 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12706 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12706 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12706 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23242463 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4588656311 / 1000000000000)) ^ 2 / 2 + ((4588656311 / 1000000000000)) * ((4157072917 / 100000000000)) ^ 2 / 6 +
      ((4157072917 / 100000000000)) ^ 4 / 24 + ((4157072917 / 100000000000)) ^ 2 * ((7872490469 / 125000000000)) ^ 3 / 120 +
      2187 * ((7872490469 / 125000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12706 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12706 : ℝ) * ((1 + 3 * ((23242463 / 1000000000))) / (4 * (1 - (23242463 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23242463 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12706 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23242463 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12706 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12706 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12706

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12706
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((56360447 / 500000) : ℝ) ≤ √12706 ∧ √12706 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1432230 : ℝ) ≤ Jz 12706 ∧ 1000000 ≤ Jz 12706 := by
  have hr : ((56360447 / 500000) : ℝ) ≤ √12706 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12706 : ℝ) * √12706 ≤ (⌈(12706 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12706
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12706 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12706 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12706 : ℝ) = (⌈(12706 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1432230 : ℝ) ≤ Jz 12706 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12706 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12706) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12706 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12706 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12706 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12706 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12706 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12706 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12706) :
    (12706 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12706 * √(qB 12706))) ≤
      (268238603 / 500000000000) := by
  have hden : ((56360447 / 500000) : ℝ) * (63 / 100) ≤ √12706 * √(qB 12706) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12706 : ℝ) * √(qB 12706) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12706) :
    (12706 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12706 * √(qB 12706))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12706 : ℝ) * √(qB 12706) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12706 : ℝ) * (√12706 *
      (c1F (exp (1 / 2) / 12) (Jz 12706) * (186 / 10000) / Jz 12706)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12706)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12706 : ℝ) * (√12706 *
      (c1F (exp (1 / 2) / 12) (Jz 12706) * (186 / 10000) / Jz 12706)) =
      (12706 * (√12706 * c1F (exp (1 / 2) / 12) (Jz 12706)) * (186 / 10000)) /
        Jz 12706 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12706)]
  nlinarith

theorem row_energy_rule :
    (12706 : ℝ) * (12706 *
      (c2F (exp (1 / 2) / 12) (Jz 12706) * (186 / 10000) ^ 2 / Jz 12706)) ≤
      (140389079 / 40000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12706)]
  nlinarith

end BstLean.Part266.Row12706

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12706
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12706) (hc : A1 c ∈ BstLean.Part153.Eop 12706) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12706 : ℝ)) ≤ (2509230559 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12706 : ℝ) + 2 * √12706 ≤ (1293144179 / 100000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12706 : ℝ) ≤ (22544179 / 200000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12706)
    (hc : A1 c ∈ BstLean.Part153.Eop 12706) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12706 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12706 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12706))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12706) (K : Set (Ix 12706)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12706 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12706 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12706) (hw : WINDOW (paperDesignP 12706) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12706)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12706) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12706 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12706 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12706 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12706 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12706) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12706)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12706)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12706

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12706
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12706) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12706 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12706) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12706) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12706 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12706 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12706 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12706}
    (hw : WINDOW (paperDesignP 12706) c) (hc : c ∈ tableEvent) (K : Set (Ix 12706)) :
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

def proposedBaseEvent : Set (Ret 12706) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12706)) : Prop where
  charge : (retDist (paperCentres 12706)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12706)} (h : TablePayment H) :
    (retDist (paperCentres 12706)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12706)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12706

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12706
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12706) (i : Fin 4) (a : Ix 12706) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12706) (a : Ix 12706) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12706) : Prop where
  moment : ∀ i, MomentBound (muI 12706) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12706} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12706) 8 (actualFourError c i)
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

end BstLean.Part266.Row12706

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12706
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

structure LatitudeVarianceCertificate (c : Ret 12706) : Prop where
  location : LBound (muI 12706) 12
    (fun a => conditionalVariance (stdGauss (Fin (12706 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12706) 12
    (fun a => conditionalVariance (stdGauss (Fin (12706 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12706) (hw : WINDOW (paperDesignP 12706) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12706 4 (55 / 100) /
      (12706 : ℝ) / ((12706 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12706

/-! The dimension-12706 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12706
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12706) (wl ws : ℝ) : SplitData 12706 :=
  BstLean.Part162.dPaper (paperDesignP 12706) c wl ws
    (√(2 / (12706 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12706 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12706 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12706) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12706) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12706 : ℝ)) * eR c * 12706 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12706) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12706 - 1)))
    (rowSplit c wl ws).good a ∂muI 12706 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12706) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12706 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12706) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12706 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12706) c (rowSplit c wl ws),
    hellG2 12706 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12706 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12706} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12706} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12706 t c BstLean.Part266.agent12706.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12706} (R : RootSource t c) :
    |√(QStand (paperDesignP 12706) t c) - √(qTilde (paperDesignP 12706) t c)| ≤
      BstLean.Part266.agent12706.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12706

/-! Rational enclosures for the HQ fluctuation price at dimension 12707. -/
namespace BstLean.Part266.Row12707
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1646632889 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23240621 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12707 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12707 * A / 2 + D + L * √(A * D)) ≤ (1147214407 / 250000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12707 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1646632889 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12707 L e4 d4 ≤ (20786278801 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12707 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1646632889 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12707 L e6 d6 ≤ (787283577 / 12500000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12707 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1646632889 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12707 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12707 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12707 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12707 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23240621 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((1147214407 / 250000000000)) ^ 2 / 2 + ((1147214407 / 250000000000)) * ((20786278801 / 500000000000)) ^ 2 / 6 +
      ((20786278801 / 500000000000)) ^ 4 / 24 + ((20786278801 / 500000000000)) ^ 2 * ((787283577 / 12500000000)) ^ 3 / 120 +
      2187 * ((787283577 / 12500000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12707 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12707 : ℝ) * ((1 + 3 * ((23240621 / 1000000000))) / (4 * (1 - (23240621 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23240621 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12707 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23240621 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12707 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12707 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12707

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12707
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((112725329 / 1000000) : ℝ) ≤ √12707 ∧ √12707 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1432399 : ℝ) ≤ Jz 12707 ∧ 1000000 ≤ Jz 12707 := by
  have hr : ((112725329 / 1000000) : ℝ) ≤ √12707 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12707 : ℝ) * √12707 ≤ (⌈(12707 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12707
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12707 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12707 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12707 : ℝ) = (⌈(12707 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1432399 : ℝ) ≤ Jz 12707 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12707 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12707) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12707 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12707 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12707 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12707 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12707 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12707 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12707) :
    (12707 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12707 * √(qB 12707))) ≤
      (536498319 / 1000000000000) := by
  have hden : ((112725329 / 1000000) : ℝ) * (63 / 100) ≤ √12707 * √(qB 12707) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12707 : ℝ) * √(qB 12707) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12707) :
    (12707 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12707 * √(qB 12707))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12707 : ℝ) * √(qB 12707) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12707 : ℝ) * (√12707 *
      (c1F (exp (1 / 2) / 12) (Jz 12707) * (186 / 10000) / Jz 12707)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12707)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12707 : ℝ) * (√12707 *
      (c1F (exp (1 / 2) / 12) (Jz 12707) * (186 / 10000) / Jz 12707)) =
      (12707 * (√12707 * c1F (exp (1 / 2) / 12) (Jz 12707)) * (186 / 10000)) /
        Jz 12707 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12707)]
  nlinarith

theorem row_energy_rule :
    (12707 : ℝ) * (12707 *
      (c2F (exp (1 / 2) / 12) (Jz 12707) * (186 / 10000) ^ 2 / Jz 12707)) ≤
      (877466323 / 250000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12707)]
  nlinarith

end BstLean.Part266.Row12707

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12707
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12707) (hc : A1 c ∈ BstLean.Part153.Eop 12707) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12707 : ℝ)) ≤ (6272829557 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12707 : ℝ) + 2 * √12707 ≤ (646622533 / 50000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12707 : ℝ) ≤ (11272533 / 100000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12707)
    (hc : A1 c ∈ BstLean.Part153.Eop 12707) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12707 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12707 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12707))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12707) (K : Set (Ix 12707)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12707 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12707 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12707) (hw : WINDOW (paperDesignP 12707) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12707)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12707) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12707 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12707 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12707 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12707 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12707) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12707)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12707)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12707

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12707
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12707) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12707 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12707) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12707) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12707 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12707 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12707 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12707}
    (hw : WINDOW (paperDesignP 12707) c) (hc : c ∈ tableEvent) (K : Set (Ix 12707)) :
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

def proposedBaseEvent : Set (Ret 12707) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12707)) : Prop where
  charge : (retDist (paperCentres 12707)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12707)} (h : TablePayment H) :
    (retDist (paperCentres 12707)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12707)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12707

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12707
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12707) (i : Fin 4) (a : Ix 12707) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12707) (a : Ix 12707) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12707) : Prop where
  moment : ∀ i, MomentBound (muI 12707) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12707} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12707) 8 (actualFourError c i)
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

end BstLean.Part266.Row12707

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12707
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

structure LatitudeVarianceCertificate (c : Ret 12707) : Prop where
  location : LBound (muI 12707) 12
    (fun a => conditionalVariance (stdGauss (Fin (12707 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12707) 12
    (fun a => conditionalVariance (stdGauss (Fin (12707 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12707) (hw : WINDOW (paperDesignP 12707) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12707 4 (55 / 100) /
      (12707 : ℝ) / ((12707 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12707

/-! The dimension-12707 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12707
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12707) (wl ws : ℝ) : SplitData 12707 :=
  BstLean.Part162.dPaper (paperDesignP 12707) c wl ws
    (√(2 / (12707 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12707 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12707 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12707) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12707) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12707 : ℝ)) * eR c * 12707 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12707) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12707 - 1)))
    (rowSplit c wl ws).good a ∂muI 12707 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12707) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12707 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12707) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12707 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12707) c (rowSplit c wl ws),
    hellG2 12707 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12707 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12707} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12707} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12707 t c BstLean.Part266.agent12707.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12707} (R : RootSource t c) :
    |√(QStand (paperDesignP 12707) t c) - √(qTilde (paperDesignP 12707) t c)| ≤
      BstLean.Part266.agent12707.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12707

/-! Rational enclosures for the HQ fluctuation price at dimension 12708. -/
namespace BstLean.Part266.Row12708
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (823283959 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23238779 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12708 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12708 * A / 2 + D + L * √(A * D)) ≤ (917811789 / 200000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12708 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((823283959 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12708 L e4 d4 ≤ (41574386037 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12708 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((823283959 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12708 L e6 d6 ≤ (31492724287 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12708 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((823283959 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12708 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12708 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12708 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12708 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23238779 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((917811789 / 200000000000)) ^ 2 / 2 + ((917811789 / 200000000000)) * ((41574386037 / 1000000000000)) ^ 2 / 6 +
      ((41574386037 / 1000000000000)) ^ 4 / 24 + ((41574386037 / 1000000000000)) ^ 2 * ((31492724287 / 500000000000)) ^ 3 / 120 +
      2187 * ((31492724287 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12708 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12708 : ℝ) * ((1 + 3 * ((23238779 / 1000000000))) / (4 * (1 - (23238779 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23238779 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12708 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23238779 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12708 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12708 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12708

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12708
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((22545953 / 200000) : ℝ) ≤ √12708 ∧ √12708 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1432568 : ℝ) ≤ Jz 12708 ∧ 1000000 ≤ Jz 12708 := by
  have hr : ((22545953 / 200000) : ℝ) ≤ √12708 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12708 : ℝ) * √12708 ≤ (⌈(12708 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12708
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12708 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12708 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12708 : ℝ) = (⌈(12708 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1432568 : ℝ) ≤ Jz 12708 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12708 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12708) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12708 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12708 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12708 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12708 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12708 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12708 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12708) :
    (12708 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12708 * √(qB 12708))) ≤
      (536519427 / 1000000000000) := by
  have hden : ((22545953 / 200000) : ℝ) * (63 / 100) ≤ √12708 * √(qB 12708) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12708 : ℝ) * √(qB 12708) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12708) :
    (12708 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12708 * √(qB 12708))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12708 : ℝ) * √(qB 12708) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12708 : ℝ) * (√12708 *
      (c1F (exp (1 / 2) / 12) (Jz 12708) * (186 / 10000) / Jz 12708)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12708)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12708 : ℝ) * (√12708 *
      (c1F (exp (1 / 2) / 12) (Jz 12708) * (186 / 10000) / Jz 12708)) =
      (12708 * (√12708 * c1F (exp (1 / 2) / 12) (Jz 12708)) * (186 / 10000)) /
        Jz 12708 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12708)]
  nlinarith

theorem row_energy_rule :
    (12708 : ℝ) * (12708 *
      (c2F (exp (1 / 2) / 12) (Jz 12708) * (186 / 10000) ^ 2 / Jz 12708)) ≤
      (175500181 / 50000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12708)]
  nlinarith

end BstLean.Part266.Row12708

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12708
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12708) (hc : A1 c ∈ BstLean.Part153.Eop 12708) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12708 : ℝ)) ≤ (3136291373 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12708 : ℝ) + 2 * √12708 ≤ (3233364883 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12708 : ℝ) ≤ (56364883 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12708)
    (hc : A1 c ∈ BstLean.Part153.Eop 12708) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12708 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12708 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12708))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12708) (K : Set (Ix 12708)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12708 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12708 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12708) (hw : WINDOW (paperDesignP 12708) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12708)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12708) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12708 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12708 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12708 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12708 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12708) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12708)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12708)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12708

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12708
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12708) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12708 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12708) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12708) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12708 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12708 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12708 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12708}
    (hw : WINDOW (paperDesignP 12708) c) (hc : c ∈ tableEvent) (K : Set (Ix 12708)) :
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

def proposedBaseEvent : Set (Ret 12708) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12708)) : Prop where
  charge : (retDist (paperCentres 12708)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12708)} (h : TablePayment H) :
    (retDist (paperCentres 12708)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12708)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12708

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12708
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12708) (i : Fin 4) (a : Ix 12708) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12708) (a : Ix 12708) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12708) : Prop where
  moment : ∀ i, MomentBound (muI 12708) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12708} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12708) 8 (actualFourError c i)
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

end BstLean.Part266.Row12708

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12708
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

structure LatitudeVarianceCertificate (c : Ret 12708) : Prop where
  location : LBound (muI 12708) 12
    (fun a => conditionalVariance (stdGauss (Fin (12708 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12708) 12
    (fun a => conditionalVariance (stdGauss (Fin (12708 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12708) (hw : WINDOW (paperDesignP 12708) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12708 4 (55 / 100) /
      (12708 : ℝ) / ((12708 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12708

/-! The dimension-12708 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12708
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12708) (wl ws : ℝ) : SplitData 12708 :=
  BstLean.Part162.dPaper (paperDesignP 12708) c wl ws
    (√(2 / (12708 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12708 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12708 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12708) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12708) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12708 : ℝ)) * eR c * 12708 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12708) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12708 - 1)))
    (rowSplit c wl ws).good a ∂muI 12708 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12708) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12708 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12708) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12708 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12708) c (rowSplit c wl ws),
    hellG2 12708 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12708 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12708} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12708} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12708 t c BstLean.Part266.agent12708.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12708} (R : RootSource t c) :
    |√(QStand (paperDesignP 12708) t c) - √(qTilde (paperDesignP 12708) t c)| ≤
      BstLean.Part266.agent12708.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12708

/-! Rational enclosures for the HQ fluctuation price at dimension 12709. -/
namespace BstLean.Part266.Row12709
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (411625741 / 250000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11618469 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12709 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12709 * A / 2 + D + L * √(A * D)) ≤ (2294630131 / 500000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12709 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((411625741 / 250000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12709 L e4 d4 ≤ (41576214477 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12709 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((411625741 / 250000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12709 L e6 d6 ≤ (62988210993 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12709 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((411625741 / 250000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12709 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12709 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12709 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12709 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11618469 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((2294630131 / 500000000000)) ^ 2 / 2 + ((2294630131 / 500000000000)) * ((41576214477 / 1000000000000)) ^ 2 / 6 +
      ((41576214477 / 1000000000000)) ^ 4 / 24 + ((41576214477 / 1000000000000)) ^ 2 * ((62988210993 / 1000000000000)) ^ 3 / 120 +
      2187 * ((62988210993 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12709 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12709 : ℝ) * ((1 + 3 * ((11618469 / 500000000))) / (4 * (1 - (11618469 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11618469 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12709 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11618469 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12709 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12709 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12709

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12709
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((563671 / 5000) : ℝ) ≤ √12709 ∧ √12709 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1432737 : ℝ) ≤ Jz 12709 ∧ 1000000 ≤ Jz 12709 := by
  have hr : ((563671 / 5000) : ℝ) ≤ √12709 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12709 : ℝ) * √12709 ≤ (⌈(12709 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12709
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12709 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12709 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12709 : ℝ) = (⌈(12709 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1432737 : ℝ) ≤ Jz 12709 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12709 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12709) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12709 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12709 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12709 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12709 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12709 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12709 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12709) :
    (12709 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12709 * √(qB 12709))) ≤
      (536540537 / 1000000000000) := by
  have hden : ((563671 / 5000) : ℝ) * (63 / 100) ≤ √12709 * √(qB 12709) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12709 : ℝ) * √(qB 12709) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12709) :
    (12709 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12709 * √(qB 12709))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12709 : ℝ) * √(qB 12709) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12709 : ℝ) * (√12709 *
      (c1F (exp (1 / 2) / 12) (Jz 12709) * (186 / 10000) / Jz 12709)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12709)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12709 : ℝ) * (√12709 *
      (c1F (exp (1 / 2) / 12) (Jz 12709) * (186 / 10000) / Jz 12709)) =
      (12709 * (√12709 * c1F (exp (1 / 2) / 12) (Jz 12709)) * (186 / 10000)) /
        Jz 12709 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12709)]
  nlinarith

theorem row_energy_rule :
    (12709 : ℝ) * (12709 *
      (c2F (exp (1 / 2) / 12) (Jz 12709) * (186 / 10000) ^ 2 / Jz 12709)) ≤
      (3510141959 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12709)]
  nlinarith

end BstLean.Part266.Row12709

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12709
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12709) (hc : A1 c ∈ BstLean.Part153.Eop 12709) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12709 : ℝ)) ≤ (1568083991 / 125000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12709 : ℝ) + 2 * √12709 ≤ (6467234201 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12709 : ℝ) ≤ (112734201 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12709)
    (hc : A1 c ∈ BstLean.Part153.Eop 12709) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12709 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12709 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12709))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12709) (K : Set (Ix 12709)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12709 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12709 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12709) (hw : WINDOW (paperDesignP 12709) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12709)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12709) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12709 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12709 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12709 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12709 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12709) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12709)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12709)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12709

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12709
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12709) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12709 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12709) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12709) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12709 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12709 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12709 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12709}
    (hw : WINDOW (paperDesignP 12709) c) (hc : c ∈ tableEvent) (K : Set (Ix 12709)) :
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

def proposedBaseEvent : Set (Ret 12709) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12709)) : Prop where
  charge : (retDist (paperCentres 12709)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12709)} (h : TablePayment H) :
    (retDist (paperCentres 12709)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12709)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12709

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12709
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12709) (i : Fin 4) (a : Ix 12709) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12709) (a : Ix 12709) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12709) : Prop where
  moment : ∀ i, MomentBound (muI 12709) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12709} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12709) 8 (actualFourError c i)
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

end BstLean.Part266.Row12709

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12709
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

structure LatitudeVarianceCertificate (c : Ret 12709) : Prop where
  location : LBound (muI 12709) 12
    (fun a => conditionalVariance (stdGauss (Fin (12709 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12709) 12
    (fun a => conditionalVariance (stdGauss (Fin (12709 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12709) (hw : WINDOW (paperDesignP 12709) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12709 4 (55 / 100) /
      (12709 : ℝ) / ((12709 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12709

/-! The dimension-12709 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12709
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12709) (wl ws : ℝ) : SplitData 12709 :=
  BstLean.Part162.dPaper (paperDesignP 12709) c wl ws
    (√(2 / (12709 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12709 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12709 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12709) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12709) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12709 : ℝ)) * eR c * 12709 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12709) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12709 - 1)))
    (rowSplit c wl ws).good a ∂muI 12709 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12709) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12709 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12709) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12709 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12709) c (rowSplit c wl ws),
    hellG2 12709 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12709 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12709} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12709} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12709 t c BstLean.Part266.agent12709.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12709} (R : RootSource t c) :
    |√(QStand (paperDesignP 12709) t c) - √(qTilde (paperDesignP 12709) t c)| ≤
      BstLean.Part266.agent12709.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12709

/-! Rational enclosures for the HQ fluctuation price at dimension 12710. -/
namespace BstLean.Part266.Row12710
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (823219013 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23235097 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12710 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12710 * A / 2 + D + L * √(A * D)) ≤ (229473079 / 50000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12710 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((823219013 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12710 L e4 d4 ≤ (41578042921 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12710 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((823219013 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12710 L e6 d6 ≤ (62990973419 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12710 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((823219013 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12710 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12710 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12710 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12710 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23235097 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((229473079 / 50000000000)) ^ 2 / 2 + ((229473079 / 50000000000)) * ((41578042921 / 1000000000000)) ^ 2 / 6 +
      ((41578042921 / 1000000000000)) ^ 4 / 24 + ((41578042921 / 1000000000000)) ^ 2 * ((62990973419 / 1000000000000)) ^ 3 / 120 +
      2187 * ((62990973419 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12710 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12710 : ℝ) * ((1 + 3 * ((23235097 / 1000000000))) / (4 * (1 - (23235097 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23235097 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12710 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23235097 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12710 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12710 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12710

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12710
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((22547727 / 200000) : ℝ) ≤ √12710 ∧ √12710 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1432907 : ℝ) ≤ Jz 12710 ∧ 1000000 ≤ Jz 12710 := by
  have hr : ((22547727 / 200000) : ℝ) ≤ √12710 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12710 : ℝ) * √12710 ≤ (⌈(12710 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12710
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12710 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12710 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12710 : ℝ) = (⌈(12710 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1432907 : ℝ) ≤ Jz 12710 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12710 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12710) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12710 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12710 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12710 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12710 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12710 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12710 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12710) :
    (12710 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12710 * √(qB 12710))) ≤
      (268280823 / 500000000000) := by
  have hden : ((22547727 / 200000) : ℝ) * (63 / 100) ≤ √12710 * √(qB 12710) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12710 : ℝ) * √(qB 12710) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12710) :
    (12710 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12710 * √(qB 12710))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12710 : ℝ) * √(qB 12710) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12710 : ℝ) * (√12710 *
      (c1F (exp (1 / 2) / 12) (Jz 12710) * (186 / 10000) / Jz 12710)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12710)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12710 : ℝ) * (√12710 *
      (c1F (exp (1 / 2) / 12) (Jz 12710) * (186 / 10000) / Jz 12710)) =
      (12710 * (√12710 * c1F (exp (1 / 2) / 12) (Jz 12710)) * (186 / 10000)) /
        Jz 12710 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12710)]
  nlinarith

theorem row_energy_rule :
    (12710 : ℝ) * (12710 *
      (c2F (exp (1 / 2) / 12) (Jz 12710) * (186 / 10000) ^ 2 / Jz 12710)) ≤
      (3510277859 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12710)]
  nlinarith

end BstLean.Part266.Row12710

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12710
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12710) (hc : A1 c ∈ BstLean.Part153.Eop 12710) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12710 : ℝ)) ≤ (6272089211 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12710 : ℝ) + 2 * √12710 ≤ (1616934659 / 125000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12710 : ℝ) ≤ (28184659 / 250000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12710)
    (hc : A1 c ∈ BstLean.Part153.Eop 12710) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12710 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12710 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12710))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12710) (K : Set (Ix 12710)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12710 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12710 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12710) (hw : WINDOW (paperDesignP 12710) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12710)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12710) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12710 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12710 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12710 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12710 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12710) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12710)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12710)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12710

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12710
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12710) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12710 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12710) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12710) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12710 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12710 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12710 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12710}
    (hw : WINDOW (paperDesignP 12710) c) (hc : c ∈ tableEvent) (K : Set (Ix 12710)) :
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

def proposedBaseEvent : Set (Ret 12710) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12710)) : Prop where
  charge : (retDist (paperCentres 12710)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12710)} (h : TablePayment H) :
    (retDist (paperCentres 12710)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12710)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12710

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12710
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12710) (i : Fin 4) (a : Ix 12710) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12710) (a : Ix 12710) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12710) : Prop where
  moment : ∀ i, MomentBound (muI 12710) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12710} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12710) 8 (actualFourError c i)
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

end BstLean.Part266.Row12710

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12710
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

structure LatitudeVarianceCertificate (c : Ret 12710) : Prop where
  location : LBound (muI 12710) 12
    (fun a => conditionalVariance (stdGauss (Fin (12710 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12710) 12
    (fun a => conditionalVariance (stdGauss (Fin (12710 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12710) (hw : WINDOW (paperDesignP 12710) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12710 4 (55 / 100) /
      (12710 : ℝ) / ((12710 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12710

/-! The dimension-12710 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12710
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12710) (wl ws : ℝ) : SplitData 12710 :=
  BstLean.Part162.dPaper (paperDesignP 12710) c wl ws
    (√(2 / (12710 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12710 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12710 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12710) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12710) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12710 : ℝ)) * eR c * 12710 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12710) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12710 - 1)))
    (rowSplit c wl ws).good a ∂muI 12710 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12710) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12710 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12710) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12710 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12710) c (rowSplit c wl ws),
    hellG2 12710 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12710 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12710} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12710} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12710 t c BstLean.Part266.agent12710.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12710} (R : RootSource t c) :
    |√(QStand (paperDesignP 12710) t c) - √(qTilde (paperDesignP 12710) t c)| ≤
      BstLean.Part266.agent12710.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12710

/-! Rational enclosures for the HQ fluctuation price at dimension 12711. -/
namespace BstLean.Part266.Row12711
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (823186551 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (2904157 / 125000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12711 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12711 * A / 2 + D + L * √(A * D)) ≤ (2294831449 / 500000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12711 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((823186551 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12711 L e4 d4 ≤ (41579871369 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12711 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((823186551 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12711 L e6 d6 ≤ (62993735851 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12711 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((823186551 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12711 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12711 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12711 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12711 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (2904157 / 125000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((2294831449 / 500000000000)) ^ 2 / 2 + ((2294831449 / 500000000000)) * ((41579871369 / 1000000000000)) ^ 2 / 6 +
      ((41579871369 / 1000000000000)) ^ 4 / 24 + ((41579871369 / 1000000000000)) ^ 2 * ((62993735851 / 1000000000000)) ^ 3 / 120 +
      2187 * ((62993735851 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12711 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12711 : ℝ) * ((1 + 3 * ((2904157 / 125000000))) / (4 * (1 - (2904157 / 125000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (2904157 / 125000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12711 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (2904157 / 125000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12711 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12711 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12711

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12711
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((11274307 / 100000) : ℝ) ≤ √12711 ∧ √12711 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1433076 : ℝ) ≤ Jz 12711 ∧ 1000000 ≤ Jz 12711 := by
  have hr : ((11274307 / 100000) : ℝ) ≤ √12711 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12711 : ℝ) * √12711 ≤ (⌈(12711 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12711
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12711 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12711 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12711 : ℝ) = (⌈(12711 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1433076 : ℝ) ≤ Jz 12711 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12711 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12711) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12711 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12711 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12711 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12711 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12711 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12711 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12711) :
    (12711 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12711 * √(qB 12711))) ≤
      (536582753 / 1000000000000) := by
  have hden : ((11274307 / 100000) : ℝ) * (63 / 100) ≤ √12711 * √(qB 12711) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12711 : ℝ) * √(qB 12711) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12711) :
    (12711 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12711 * √(qB 12711))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12711 : ℝ) * √(qB 12711) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12711 : ℝ) * (√12711 *
      (c1F (exp (1 / 2) / 12) (Jz 12711) * (186 / 10000) / Jz 12711)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12711)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12711 : ℝ) * (√12711 *
      (c1F (exp (1 / 2) / 12) (Jz 12711) * (186 / 10000) / Jz 12711)) =
      (12711 * (√12711 * c1F (exp (1 / 2) / 12) (Jz 12711)) * (186 / 10000)) /
        Jz 12711 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12711)]
  nlinarith

theorem row_energy_rule :
    (12711 : ℝ) * (12711 *
      (c2F (exp (1 / 2) / 12) (Jz 12711) * (186 / 10000) ^ 2 / Jz 12711)) ≤
      (175520811 / 50000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12711)]
  nlinarith

end BstLean.Part266.Row12711

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12711
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12711) (hc : A1 c ∈ BstLean.Part153.Eop 12711) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12711 : ℝ)) ≤ (501747399 / 40000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12711 : ℝ) + 2 * √12711 ≤ (6468243071 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12711 : ℝ) ≤ (112743071 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12711)
    (hc : A1 c ∈ BstLean.Part153.Eop 12711) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12711 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12711 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12711))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12711) (K : Set (Ix 12711)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12711 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12711 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12711) (hw : WINDOW (paperDesignP 12711) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12711)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12711) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12711 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12711 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12711 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12711 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12711) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12711)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12711)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12711

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12711
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12711) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12711 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12711) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12711) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12711 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12711 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12711 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12711}
    (hw : WINDOW (paperDesignP 12711) c) (hc : c ∈ tableEvent) (K : Set (Ix 12711)) :
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

def proposedBaseEvent : Set (Ret 12711) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12711)) : Prop where
  charge : (retDist (paperCentres 12711)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12711)} (h : TablePayment H) :
    (retDist (paperCentres 12711)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12711)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12711

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12711
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12711) (i : Fin 4) (a : Ix 12711) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12711) (a : Ix 12711) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12711) : Prop where
  moment : ∀ i, MomentBound (muI 12711) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12711} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12711) 8 (actualFourError c i)
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

end BstLean.Part266.Row12711

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12711
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

structure LatitudeVarianceCertificate (c : Ret 12711) : Prop where
  location : LBound (muI 12711) 12
    (fun a => conditionalVariance (stdGauss (Fin (12711 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12711) 12
    (fun a => conditionalVariance (stdGauss (Fin (12711 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12711) (hw : WINDOW (paperDesignP 12711) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12711 4 (55 / 100) /
      (12711 : ℝ) / ((12711 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12711

/-! The dimension-12711 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12711
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12711) (wl ws : ℝ) : SplitData 12711 :=
  BstLean.Part162.dPaper (paperDesignP 12711) c wl ws
    (√(2 / (12711 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12711 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12711 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12711) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12711) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12711 : ℝ)) * eR c * 12711 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12711) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12711 - 1)))
    (rowSplit c wl ws).good a ∂muI 12711 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12711) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12711 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12711) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12711 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12711) c (rowSplit c wl ws),
    hellG2 12711 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12711 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12711} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12711} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12711 t c BstLean.Part266.agent12711.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12711} (R : RootSource t c) :
    |√(QStand (paperDesignP 12711) t c) - √(qTilde (paperDesignP 12711) t c)| ≤
      BstLean.Part266.agent12711.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12711

/-! Rational enclosures for the HQ fluctuation price at dimension 12712. -/
namespace BstLean.Part266.Row12712
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1646308193 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (2903927 / 125000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12712 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12712 * A / 2 + D + L * √(A * D)) ≤ (4589864217 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12712 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1646308193 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12712 L e4 d4 ≤ (2079084991 / 50000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12712 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1646308193 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12712 L e6 d6 ≤ (3937281143 / 62500000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12712 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1646308193 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12712 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12712 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12712 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12712 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (2903927 / 125000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4589864217 / 1000000000000)) ^ 2 / 2 + ((4589864217 / 1000000000000)) * ((2079084991 / 50000000000)) ^ 2 / 6 +
      ((2079084991 / 50000000000)) ^ 4 / 24 + ((2079084991 / 50000000000)) ^ 2 * ((3937281143 / 62500000000)) ^ 3 / 120 +
      2187 * ((3937281143 / 62500000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12712 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12712 : ℝ) * ((1 + 3 * ((2903927 / 125000000))) / (4 * (1 - (2903927 / 125000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (2903927 / 125000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12712 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (2903927 / 125000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12712 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12712 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12712

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12712
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((22549501 / 200000) : ℝ) ≤ √12712 ∧ √12712 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1433245 : ℝ) ≤ Jz 12712 ∧ 1000000 ≤ Jz 12712 := by
  have hr : ((22549501 / 200000) : ℝ) ≤ √12712 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12712 : ℝ) * √12712 ≤ (⌈(12712 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12712
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12712 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12712 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12712 : ℝ) = (⌈(12712 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1433245 : ℝ) ≤ Jz 12712 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12712 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12712) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12712 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12712 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12712 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12712 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12712 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12712 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12712) :
    (12712 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12712 * √(qB 12712))) ≤
      (536603859 / 1000000000000) := by
  have hden : ((22549501 / 200000) : ℝ) * (63 / 100) ≤ √12712 * √(qB 12712) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12712 : ℝ) * √(qB 12712) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12712) :
    (12712 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12712 * √(qB 12712))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12712 : ℝ) * √(qB 12712) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12712 : ℝ) * (√12712 *
      (c1F (exp (1 / 2) / 12) (Jz 12712) * (186 / 10000) / Jz 12712)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12712)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12712 : ℝ) * (√12712 *
      (c1F (exp (1 / 2) / 12) (Jz 12712) * (186 / 10000) / Jz 12712)) =
      (12712 * (√12712 * c1F (exp (1 / 2) / 12) (Jz 12712)) * (186 / 10000)) /
        Jz 12712 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12712)]
  nlinarith

theorem row_energy_rule :
    (12712 : ℝ) * (12712 *
      (c2F (exp (1 / 2) / 12) (Jz 12712) * (186 / 10000) ^ 2 / Jz 12712)) ≤
      (3510554591 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12712)]
  nlinarith

end BstLean.Part266.Row12712

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12712
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12712) (hc : A1 c ∈ BstLean.Part153.Eop 12712) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12712 : ℝ)) ≤ (2508638317 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12712 : ℝ) + 2 * √12712 ≤ (3234373753 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12712 : ℝ) ≤ (56373753 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12712)
    (hc : A1 c ∈ BstLean.Part153.Eop 12712) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12712 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12712 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12712))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12712) (K : Set (Ix 12712)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12712 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12712 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12712) (hw : WINDOW (paperDesignP 12712) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12712)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12712) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12712 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12712 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12712 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12712 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12712) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12712)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12712)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12712

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12712
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12712) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12712 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12712) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12712) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12712 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12712 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12712 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12712}
    (hw : WINDOW (paperDesignP 12712) c) (hc : c ∈ tableEvent) (K : Set (Ix 12712)) :
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

def proposedBaseEvent : Set (Ret 12712) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12712)) : Prop where
  charge : (retDist (paperCentres 12712)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12712)} (h : TablePayment H) :
    (retDist (paperCentres 12712)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12712)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12712

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12712
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12712) (i : Fin 4) (a : Ix 12712) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12712) (a : Ix 12712) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12712) : Prop where
  moment : ∀ i, MomentBound (muI 12712) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12712} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12712) 8 (actualFourError c i)
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

end BstLean.Part266.Row12712

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12712
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

structure LatitudeVarianceCertificate (c : Ret 12712) : Prop where
  location : LBound (muI 12712) 12
    (fun a => conditionalVariance (stdGauss (Fin (12712 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12712) 12
    (fun a => conditionalVariance (stdGauss (Fin (12712 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12712) (hw : WINDOW (paperDesignP 12712) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12712 4 (55 / 100) /
      (12712 : ℝ) / ((12712 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12712

/-! The dimension-12712 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12712
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12712) (wl ws : ℝ) : SplitData 12712 :=
  BstLean.Part162.dPaper (paperDesignP 12712) c wl ws
    (√(2 / (12712 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12712 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12712 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12712) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12712) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12712 : ℝ)) * eR c * 12712 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12712) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12712 - 1)))
    (rowSplit c wl ws).good a ∂muI 12712 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12712) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12712 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12712) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12712 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12712) c (rowSplit c wl ws),
    hellG2 12712 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12712 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12712} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12712} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12712 t c BstLean.Part266.agent12712.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12712} (R : RootSource t c) :
    |√(QStand (paperDesignP 12712) t c) - √(qTilde (paperDesignP 12712) t c)| ≤
      BstLean.Part266.agent12712.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12712

/-! Rational enclosures for the HQ fluctuation price at dimension 12713. -/
namespace BstLean.Part266.Row12713
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (16462433 / 10000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (2903697 / 125000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12713 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12713 * A / 2 + D + L * √(A * D)) ≤ (35859887 / 7812500000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12713 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((16462433 / 10000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12713 L e4 d4 ≤ (10395882069 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12713 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((16462433 / 10000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12713 L e6 d6 ≤ (15749815183 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12713 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((16462433 / 10000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12713 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12713 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12713 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12713 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (2903697 / 125000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((35859887 / 7812500000)) ^ 2 / 2 + ((35859887 / 7812500000)) * ((10395882069 / 250000000000)) ^ 2 / 6 +
      ((10395882069 / 250000000000)) ^ 4 / 24 + ((10395882069 / 250000000000)) ^ 2 * ((15749815183 / 250000000000)) ^ 3 / 120 +
      2187 * ((15749815183 / 250000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12713 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12713 : ℝ) * ((1 + 3 * ((2903697 / 125000000))) / (4 * (1 - (2903697 / 125000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (2903697 / 125000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12713 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (2903697 / 125000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12713 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12713 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12713

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12713
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((5637597 / 50000) : ℝ) ≤ √12713 ∧ √12713 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1433414 : ℝ) ≤ Jz 12713 ∧ 1000000 ≤ Jz 12713 := by
  have hr : ((5637597 / 50000) : ℝ) ≤ √12713 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12713 : ℝ) * √12713 ≤ (⌈(12713 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12713
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12713 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12713 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12713 : ℝ) = (⌈(12713 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1433414 : ℝ) ≤ Jz 12713 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12713 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12713) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12713 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12713 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12713 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12713 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12713 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12713 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12713) :
    (12713 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12713 * √(qB 12713))) ≤
      (536624963 / 1000000000000) := by
  have hden : ((5637597 / 50000) : ℝ) * (63 / 100) ≤ √12713 * √(qB 12713) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12713 : ℝ) * √(qB 12713) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12713) :
    (12713 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12713 * √(qB 12713))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12713 : ℝ) * √(qB 12713) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12713 : ℝ) * (√12713 *
      (c1F (exp (1 / 2) / 12) (Jz 12713) * (186 / 10000) / Jz 12713)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12713)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12713 : ℝ) * (√12713 *
      (c1F (exp (1 / 2) / 12) (Jz 12713) * (186 / 10000) / Jz 12713)) =
      (12713 * (√12713 * c1F (exp (1 / 2) / 12) (Jz 12713)) * (186 / 10000)) /
        Jz 12713 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12713)]
  nlinarith

theorem row_energy_rule :
    (12713 : ℝ) * (12713 *
      (c2F (exp (1 / 2) / 12) (Jz 12713) * (186 / 10000) ^ 2 / Jz 12713)) ≤
      (1755346487 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12713)]
  nlinarith

end BstLean.Part266.Row12713

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12713
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12713) (hc : A1 c ∈ BstLean.Part153.Eop 12713) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12713 : ℝ)) ≤ (6271349127 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12713 : ℝ) + 2 * √12713 ≤ (6469251941 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12713 : ℝ) ≤ (112751941 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12713)
    (hc : A1 c ∈ BstLean.Part153.Eop 12713) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12713 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12713 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12713))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12713) (K : Set (Ix 12713)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12713 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12713 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12713) (hw : WINDOW (paperDesignP 12713) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12713)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12713) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12713 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12713 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12713 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12713 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12713) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12713)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12713)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12713

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12713
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12713) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12713 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12713) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12713) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12713 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12713 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12713 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12713}
    (hw : WINDOW (paperDesignP 12713) c) (hc : c ∈ tableEvent) (K : Set (Ix 12713)) :
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

def proposedBaseEvent : Set (Ret 12713) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12713)) : Prop where
  charge : (retDist (paperCentres 12713)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12713)} (h : TablePayment H) :
    (retDist (paperCentres 12713)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12713)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12713

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12713
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12713) (i : Fin 4) (a : Ix 12713) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12713) (a : Ix 12713) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12713) : Prop where
  moment : ∀ i, MomentBound (muI 12713) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12713} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12713) 8 (actualFourError c i)
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

end BstLean.Part266.Row12713

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12713
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

structure LatitudeVarianceCertificate (c : Ret 12713) : Prop where
  location : LBound (muI 12713) 12
    (fun a => conditionalVariance (stdGauss (Fin (12713 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12713) 12
    (fun a => conditionalVariance (stdGauss (Fin (12713 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12713) (hw : WINDOW (paperDesignP 12713) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12713 4 (55 / 100) /
      (12713 : ℝ) / ((12713 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12713

/-! The dimension-12713 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12713
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12713) (wl ws : ℝ) : SplitData 12713 :=
  BstLean.Part162.dPaper (paperDesignP 12713) c wl ws
    (√(2 / (12713 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12713 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12713 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12713) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12713) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12713 : ℝ)) * eR c * 12713 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12713) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12713 - 1)))
    (rowSplit c wl ws).good a ∂muI 12713 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12713) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12713 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12713) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12713 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12713) c (rowSplit c wl ws),
    hellG2 12713 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12713 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12713} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12713} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12713 t c BstLean.Part266.agent12713.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12713} (R : RootSource t c) :
    |√(QStand (paperDesignP 12713) t c) - √(qTilde (paperDesignP 12713) t c)| ≤
      BstLean.Part266.agent12713.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12713

/-! Rational enclosures for the HQ fluctuation price at dimension 12714. -/
namespace BstLean.Part266.Row12714
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1646178703 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (1161387 / 50000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12714 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12714 * A / 2 + D + L * √(A * D)) ≤ (286891679 / 62500000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12714 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1646178703 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12714 L e4 d4 ≤ (41585356807 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12714 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1646178703 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12714 L e6 d6 ≤ (6300202329 / 100000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12714 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1646178703 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12714 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12714 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12714 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12714 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (1161387 / 50000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((286891679 / 62500000000)) ^ 2 / 2 + ((286891679 / 62500000000)) * ((41585356807 / 1000000000000)) ^ 2 / 6 +
      ((41585356807 / 1000000000000)) ^ 4 / 24 + ((41585356807 / 1000000000000)) ^ 2 * ((6300202329 / 100000000000)) ^ 3 / 120 +
      2187 * ((6300202329 / 100000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12714 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12714 : ℝ) * ((1 + 3 * ((1161387 / 50000000))) / (4 * (1 - (1161387 / 50000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (1161387 / 50000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12714 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (1161387 / 50000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12714 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12714 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12714

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12714
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((56378187 / 500000) : ℝ) ≤ √12714 ∧ √12714 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1433583 : ℝ) ≤ Jz 12714 ∧ 1000000 ≤ Jz 12714 := by
  have hr : ((56378187 / 500000) : ℝ) ≤ √12714 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12714 : ℝ) * √12714 ≤ (⌈(12714 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12714
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12714 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12714 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12714 : ℝ) = (⌈(12714 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1433583 : ℝ) ≤ Jz 12714 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12714 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12714) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12714 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12714 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12714 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12714 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12714 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12714 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12714) :
    (12714 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12714 * √(qB 12714))) ≤
      (53664607 / 100000000000) := by
  have hden : ((56378187 / 500000) : ℝ) * (63 / 100) ≤ √12714 * √(qB 12714) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12714 : ℝ) * √(qB 12714) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12714) :
    (12714 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12714 * √(qB 12714))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12714 : ℝ) * √(qB 12714) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12714 : ℝ) * (√12714 *
      (c1F (exp (1 / 2) / 12) (Jz 12714) * (186 / 10000) / Jz 12714)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12714)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12714 : ℝ) * (√12714 *
      (c1F (exp (1 / 2) / 12) (Jz 12714) * (186 / 10000) / Jz 12714)) =
      (12714 * (√12714 * c1F (exp (1 / 2) / 12) (Jz 12714)) * (186 / 10000)) /
        Jz 12714 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12714)]
  nlinarith

theorem row_energy_rule :
    (12714 : ℝ) * (12714 *
      (c2F (exp (1 / 2) / 12) (Jz 12714) * (186 / 10000) ^ 2 / Jz 12714)) ≤
      (3510831367 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12714)]
  nlinarith

end BstLean.Part266.Row12714

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12714
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12714) (hc : A1 c ∈ BstLean.Part153.Eop 12714) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12714 : ℝ)) ≤ (12542204981 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12714 : ℝ) + 2 * √12714 ≤ (51758051 / 4000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12714 : ℝ) ≤ (902051 / 8000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12714)
    (hc : A1 c ∈ BstLean.Part153.Eop 12714) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12714 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12714 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12714))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12714) (K : Set (Ix 12714)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12714 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12714 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12714) (hw : WINDOW (paperDesignP 12714) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12714)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12714) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12714 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12714 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12714 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12714 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12714) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12714)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12714)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12714

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12714
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12714) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12714 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12714) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12714) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12714 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12714 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12714 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12714}
    (hw : WINDOW (paperDesignP 12714) c) (hc : c ∈ tableEvent) (K : Set (Ix 12714)) :
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

def proposedBaseEvent : Set (Ret 12714) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12714)) : Prop where
  charge : (retDist (paperCentres 12714)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12714)} (h : TablePayment H) :
    (retDist (paperCentres 12714)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12714)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12714

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12714
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12714) (i : Fin 4) (a : Ix 12714) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12714) (a : Ix 12714) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12714) : Prop where
  moment : ∀ i, MomentBound (muI 12714) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12714} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12714) 8 (actualFourError c i)
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

end BstLean.Part266.Row12714

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12714
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

structure LatitudeVarianceCertificate (c : Ret 12714) : Prop where
  location : LBound (muI 12714) 12
    (fun a => conditionalVariance (stdGauss (Fin (12714 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12714) 12
    (fun a => conditionalVariance (stdGauss (Fin (12714 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12714) (hw : WINDOW (paperDesignP 12714) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12714 4 (55 / 100) /
      (12714 : ℝ) / ((12714 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12714

/-! The dimension-12714 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12714
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12714) (wl ws : ℝ) : SplitData 12714 :=
  BstLean.Part162.dPaper (paperDesignP 12714) c wl ws
    (√(2 / (12714 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12714 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12714 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12714) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12714) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12714 : ℝ)) * eR c * 12714 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12714) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12714 - 1)))
    (rowSplit c wl ws).good a ∂muI 12714 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12714) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12714 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12714) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12714 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12714) c (rowSplit c wl ws),
    hellG2 12714 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12714 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12714} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12714} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12714 t c BstLean.Part266.agent12714.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12714} (R : RootSource t c) :
    |√(QStand (paperDesignP 12714) t c) - √(qTilde (paperDesignP 12714) t c)| ≤
      BstLean.Part266.agent12714.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12714

/-! Rational enclosures for the HQ fluctuation price at dimension 12715. -/
namespace BstLean.Part266.Row12715
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1646113841 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23225901 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12715 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12715 * A / 2 + D + L * √(A * D)) ≤ (573808523 / 125000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12715 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1646113841 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12715 L e4 d4 ≤ (41587185271 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12715 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1646113841 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12715 L e6 d6 ≤ (12600957149 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12715 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1646113841 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12715 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12715 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12715 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12715 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23225901 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((573808523 / 125000000000)) ^ 2 / 2 + ((573808523 / 125000000000)) * ((41587185271 / 1000000000000)) ^ 2 / 6 +
      ((41587185271 / 1000000000000)) ^ 4 / 24 + ((41587185271 / 1000000000000)) ^ 2 * ((12600957149 / 200000000000)) ^ 3 / 120 +
      2187 * ((12600957149 / 200000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12715 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12715 : ℝ) * ((1 + 3 * ((23225901 / 1000000000))) / (4 * (1 - (23225901 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23225901 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12715 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23225901 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12715 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12715 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12715

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12715
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((14095101 / 125000) : ℝ) ≤ √12715 ∧ √12715 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1433752 : ℝ) ≤ Jz 12715 ∧ 1000000 ≤ Jz 12715 := by
  have hr : ((14095101 / 125000) : ℝ) ≤ √12715 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12715 : ℝ) * √12715 ≤ (⌈(12715 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12715
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12715 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12715 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12715 : ℝ) = (⌈(12715 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1433752 : ℝ) ≤ Jz 12715 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12715 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12715) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12715 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12715 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12715 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12715 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12715 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12715 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12715) :
    (12715 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12715 * √(qB 12715))) ≤
      (21466687 / 40000000000) := by
  have hden : ((14095101 / 125000) : ℝ) * (63 / 100) ≤ √12715 * √(qB 12715) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12715 : ℝ) * √(qB 12715) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12715) :
    (12715 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12715 * √(qB 12715))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12715 : ℝ) * √(qB 12715) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12715 : ℝ) * (√12715 *
      (c1F (exp (1 / 2) / 12) (Jz 12715) * (186 / 10000) / Jz 12715)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12715)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12715 : ℝ) * (√12715 *
      (c1F (exp (1 / 2) / 12) (Jz 12715) * (186 / 10000) / Jz 12715)) =
      (12715 * (√12715 * c1F (exp (1 / 2) / 12) (Jz 12715)) * (186 / 10000)) /
        Jz 12715 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12715)]
  nlinarith

theorem row_energy_rule :
    (12715 : ℝ) * (12715 *
      (c2F (exp (1 / 2) / 12) (Jz 12715) * (186 / 10000) ^ 2 / Jz 12715)) ≤
      (3510969771 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12715)]
  nlinarith

end BstLean.Part266.Row12715

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12715
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12715) (hc : A1 c ∈ BstLean.Part153.Eop 12715) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12715 : ℝ)) ≤ (6270855883 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12715 : ℝ) + 2 * √12715 ≤ (6470260809 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12715 : ℝ) ≤ (112760809 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12715)
    (hc : A1 c ∈ BstLean.Part153.Eop 12715) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12715 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12715 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12715))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12715) (K : Set (Ix 12715)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12715 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12715 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12715) (hw : WINDOW (paperDesignP 12715) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12715)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12715) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12715 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12715 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12715 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12715 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12715) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12715)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12715)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12715

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12715
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12715) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12715 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12715) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12715) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12715 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12715 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12715 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12715}
    (hw : WINDOW (paperDesignP 12715) c) (hc : c ∈ tableEvent) (K : Set (Ix 12715)) :
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

def proposedBaseEvent : Set (Ret 12715) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12715)) : Prop where
  charge : (retDist (paperCentres 12715)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12715)} (h : TablePayment H) :
    (retDist (paperCentres 12715)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12715)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12715

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12715
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12715) (i : Fin 4) (a : Ix 12715) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12715) (a : Ix 12715) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12715) : Prop where
  moment : ∀ i, MomentBound (muI 12715) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12715} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12715) 8 (actualFourError c i)
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

end BstLean.Part266.Row12715

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12715
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

structure LatitudeVarianceCertificate (c : Ret 12715) : Prop where
  location : LBound (muI 12715) 12
    (fun a => conditionalVariance (stdGauss (Fin (12715 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12715) 12
    (fun a => conditionalVariance (stdGauss (Fin (12715 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12715) (hw : WINDOW (paperDesignP 12715) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12715 4 (55 / 100) /
      (12715 : ℝ) / ((12715 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12715

/-! The dimension-12715 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12715
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12715) (wl ws : ℝ) : SplitData 12715 :=
  BstLean.Part162.dPaper (paperDesignP 12715) c wl ws
    (√(2 / (12715 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12715 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12715 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12715) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12715) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12715 : ℝ)) * eR c * 12715 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12715) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12715 - 1)))
    (rowSplit c wl ws).good a ∂muI 12715 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12715) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12715 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12715) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12715 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12715) c (rowSplit c wl ws),
    hellG2 12715 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12715 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12715} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12715} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12715 t c BstLean.Part266.agent12715.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12715} (R : RootSource t c) :
    |√(QStand (paperDesignP 12715) t c) - √(qTilde (paperDesignP 12715) t c)| ≤
      BstLean.Part266.agent12715.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12715

/-! Rational enclosures for the HQ fluctuation price at dimension 12716. -/
namespace BstLean.Part266.Row12716
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1646048713 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23224059 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12716 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12716 * A / 2 + D + L * √(A * D)) ≤ (4590669497 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12716 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1646048713 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12716 L e4 d4 ≤ (20794506833 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12716 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1646048713 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12716 L e6 d6 ≤ (31503774049 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12716 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1646048713 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12716 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12716 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12716 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12716 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23224059 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4590669497 / 1000000000000)) ^ 2 / 2 + ((4590669497 / 1000000000000)) * ((20794506833 / 500000000000)) ^ 2 / 6 +
      ((20794506833 / 500000000000)) ^ 4 / 24 + ((20794506833 / 500000000000)) ^ 2 * ((31503774049 / 500000000000)) ^ 3 / 120 +
      2187 * ((31503774049 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12716 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12716 : ℝ) * ((1 + 3 * ((23224059 / 1000000000))) / (4 * (1 - (23224059 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23224059 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12716 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23224059 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12716 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12716 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12716

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12716
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((56382621 / 500000) : ℝ) ≤ √12716 ∧ √12716 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1433921 : ℝ) ≤ Jz 12716 ∧ 1000000 ≤ Jz 12716 := by
  have hr : ((56382621 / 500000) : ℝ) ≤ √12716 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12716 : ℝ) * √12716 ≤ (⌈(12716 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12716
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12716 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12716 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12716 : ℝ) = (⌈(12716 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1433921 : ℝ) ≤ Jz 12716 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12716 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12716) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12716 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12716 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12716 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12716 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12716 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12716 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12716) :
    (12716 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12716 * √(qB 12716))) ≤
      (536688279 / 1000000000000) := by
  have hden : ((56382621 / 500000) : ℝ) * (63 / 100) ≤ √12716 * √(qB 12716) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12716 : ℝ) * √(qB 12716) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12716) :
    (12716 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12716 * √(qB 12716))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12716 : ℝ) * √(qB 12716) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12716 : ℝ) * (√12716 *
      (c1F (exp (1 / 2) / 12) (Jz 12716) * (186 / 10000) / Jz 12716)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12716)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12716 : ℝ) * (√12716 *
      (c1F (exp (1 / 2) / 12) (Jz 12716) * (186 / 10000) / Jz 12716)) =
      (12716 * (√12716 * c1F (exp (1 / 2) / 12) (Jz 12716)) * (186 / 10000)) /
        Jz 12716 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12716)]
  nlinarith

theorem row_energy_rule :
    (12716 : ℝ) * (12716 *
      (c2F (exp (1 / 2) / 12) (Jz 12716) * (186 / 10000) ^ 2 / Jz 12716)) ≤
      (1755554093 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12716)]
  nlinarith

end BstLean.Part266.Row12716

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12716
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12716) (hc : A1 c ∈ BstLean.Part153.Eop 12716) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12716 : ℝ)) ≤ (1254121861 / 100000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12716 : ℝ) + 2 * √12716 ≤ (6470765243 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12716 : ℝ) ≤ (112765243 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12716)
    (hc : A1 c ∈ BstLean.Part153.Eop 12716) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12716 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12716 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12716))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12716) (K : Set (Ix 12716)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12716 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12716 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12716) (hw : WINDOW (paperDesignP 12716) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12716)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12716) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12716 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12716 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12716 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12716 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12716) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12716)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12716)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12716

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12716
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12716) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12716 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12716) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12716) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12716 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12716 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12716 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12716}
    (hw : WINDOW (paperDesignP 12716) c) (hc : c ∈ tableEvent) (K : Set (Ix 12716)) :
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

def proposedBaseEvent : Set (Ret 12716) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12716)) : Prop where
  charge : (retDist (paperCentres 12716)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12716)} (h : TablePayment H) :
    (retDist (paperCentres 12716)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12716)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12716

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12716
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12716) (i : Fin 4) (a : Ix 12716) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12716) (a : Ix 12716) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12716) : Prop where
  moment : ∀ i, MomentBound (muI 12716) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12716} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12716) 8 (actualFourError c i)
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

end BstLean.Part266.Row12716

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12716
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

structure LatitudeVarianceCertificate (c : Ret 12716) : Prop where
  location : LBound (muI 12716) 12
    (fun a => conditionalVariance (stdGauss (Fin (12716 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12716) 12
    (fun a => conditionalVariance (stdGauss (Fin (12716 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12716) (hw : WINDOW (paperDesignP 12716) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12716 4 (55 / 100) /
      (12716 : ℝ) / ((12716 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12716

/-! The dimension-12716 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12716
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12716) (wl ws : ℝ) : SplitData 12716 :=
  BstLean.Part162.dPaper (paperDesignP 12716) c wl ws
    (√(2 / (12716 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12716 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12716 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12716) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12716) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12716 : ℝ)) * eR c * 12716 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12716) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12716 - 1)))
    (rowSplit c wl ws).good a ∂muI 12716 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12716) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12716 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12716) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12716 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12716) c (rowSplit c wl ws),
    hellG2 12716 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12716 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12716} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12716} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12716 t c BstLean.Part266.agent12716.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12716} (R : RootSource t c) :
    |√(QStand (paperDesignP 12716) t c) - √(qTilde (paperDesignP 12716) t c)| ≤
      BstLean.Part266.agent12716.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12716

/-! Rational enclosures for the HQ fluctuation price at dimension 12717. -/
namespace BstLean.Part266.Row12717
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1645983881 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (1161111 / 50000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12717 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12717 * A / 2 + D + L * √(A * D)) ≤ (2295435409 / 500000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12717 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1645983881 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12717 L e4 d4 ≤ (41590842137 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12717 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1645983881 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12717 L e6 d6 ≤ (12602062113 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12717 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1645983881 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12717 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12717 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12717 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12717 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (1161111 / 50000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((2295435409 / 500000000000)) ^ 2 / 2 + ((2295435409 / 500000000000)) * ((41590842137 / 1000000000000)) ^ 2 / 6 +
      ((41590842137 / 1000000000000)) ^ 4 / 24 + ((41590842137 / 1000000000000)) ^ 2 * ((12602062113 / 200000000000)) ^ 3 / 120 +
      2187 * ((12602062113 / 200000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12717 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12717 : ℝ) * ((1 + 3 * ((1161111 / 50000000))) / (4 * (1 - (1161111 / 50000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (1161111 / 50000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12717 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (1161111 / 50000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12717 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12717 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12717

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12717
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((28192419 / 250000) : ℝ) ≤ √12717 ∧ √12717 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1434090 : ℝ) ≤ Jz 12717 ∧ 1000000 ≤ Jz 12717 := by
  have hr : ((28192419 / 250000) : ℝ) ≤ √12717 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12717 : ℝ) * √12717 ≤ (⌈(12717 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12717
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12717 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12717 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12717 : ℝ) = (⌈(12717 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1434090 : ℝ) ≤ Jz 12717 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12717 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12717) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12717 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12717 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12717 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12717 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12717 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12717 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12717) :
    (12717 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12717 * √(qB 12717))) ≤
      (536709381 / 1000000000000) := by
  have hden : ((28192419 / 250000) : ℝ) * (63 / 100) ≤ √12717 * √(qB 12717) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12717 : ℝ) * √(qB 12717) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12717) :
    (12717 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12717 * √(qB 12717))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12717 : ℝ) * √(qB 12717) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12717 : ℝ) * (√12717 *
      (c1F (exp (1 / 2) / 12) (Jz 12717) * (186 / 10000) / Jz 12717)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12717)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12717 : ℝ) * (√12717 *
      (c1F (exp (1 / 2) / 12) (Jz 12717) * (186 / 10000) / Jz 12717)) =
      (12717 * (√12717 * c1F (exp (1 / 2) / 12) (Jz 12717)) * (186 / 10000)) /
        Jz 12717 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12717)]
  nlinarith

theorem row_energy_rule :
    (12717 : ℝ) * (12717 *
      (c2F (exp (1 / 2) / 12) (Jz 12717) * (186 / 10000) ^ 2 / Jz 12717)) ≤
      (3511246611 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12717)]
  nlinarith

end BstLean.Part266.Row12717

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12717
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12717) (hc : A1 c ∈ BstLean.Part153.Eop 12717) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12717 : ℝ)) ≤ (12540725511 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12717 : ℝ) + 2 * √12717 ≤ (6471269677 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12717 : ℝ) ≤ (112769677 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12717)
    (hc : A1 c ∈ BstLean.Part153.Eop 12717) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12717 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12717 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12717))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12717) (K : Set (Ix 12717)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12717 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12717 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12717) (hw : WINDOW (paperDesignP 12717) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12717)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12717) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12717 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12717 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12717 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12717 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12717) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12717)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12717)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12717

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12717
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12717) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12717 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12717) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12717) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12717 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12717 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12717 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12717}
    (hw : WINDOW (paperDesignP 12717) c) (hc : c ∈ tableEvent) (K : Set (Ix 12717)) :
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

def proposedBaseEvent : Set (Ret 12717) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12717)) : Prop where
  charge : (retDist (paperCentres 12717)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12717)} (h : TablePayment H) :
    (retDist (paperCentres 12717)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12717)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12717

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12717
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12717) (i : Fin 4) (a : Ix 12717) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12717) (a : Ix 12717) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12717) : Prop where
  moment : ∀ i, MomentBound (muI 12717) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12717} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12717) 8 (actualFourError c i)
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

end BstLean.Part266.Row12717

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12717
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

structure LatitudeVarianceCertificate (c : Ret 12717) : Prop where
  location : LBound (muI 12717) 12
    (fun a => conditionalVariance (stdGauss (Fin (12717 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12717) 12
    (fun a => conditionalVariance (stdGauss (Fin (12717 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12717) (hw : WINDOW (paperDesignP 12717) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12717 4 (55 / 100) /
      (12717 : ℝ) / ((12717 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12717

/-! The dimension-12717 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12717
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12717) (wl ws : ℝ) : SplitData 12717 :=
  BstLean.Part162.dPaper (paperDesignP 12717) c wl ws
    (√(2 / (12717 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12717 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12717 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12717) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12717) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12717 : ℝ)) * eR c * 12717 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12717) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12717 - 1)))
    (rowSplit c wl ws).good a ∂muI 12717 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12717) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12717 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12717) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12717 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12717) c (rowSplit c wl ws),
    hellG2 12717 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12717 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12717} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12717} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12717 t c BstLean.Part266.agent12717.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12717} (R : RootSource t c) :
    |√(QStand (paperDesignP 12717) t c) - √(qTilde (paperDesignP 12717) t c)| ≤
      BstLean.Part266.agent12717.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12717

/-! Rational enclosures for the HQ fluctuation price at dimension 12718. -/
namespace BstLean.Part266.Row12718
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (329183813 / 200000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11610191 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12718 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12718 * A / 2 + D + L * √(A * D)) ≤ (4591072139 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12718 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((329183813 / 200000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12718 L e4 d4 ≤ (10398167653 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12718 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((329183813 / 200000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12718 L e6 d6 ≤ (31506536519 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12718 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((329183813 / 200000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12718 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12718 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12718 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12718 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11610191 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4591072139 / 1000000000000)) ^ 2 / 2 + ((4591072139 / 1000000000000)) * ((10398167653 / 250000000000)) ^ 2 / 6 +
      ((10398167653 / 250000000000)) ^ 4 / 24 + ((10398167653 / 250000000000)) ^ 2 * ((31506536519 / 500000000000)) ^ 3 / 120 +
      2187 * ((31506536519 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12718 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12718 : ℝ) * ((1 + 3 * ((11610191 / 500000000))) / (4 * (1 - (11610191 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11610191 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12718 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11610191 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12718 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12718 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12718

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12718
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((11277411 / 100000) : ℝ) ≤ √12718 ∧ √12718 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1434260 : ℝ) ≤ Jz 12718 ∧ 1000000 ≤ Jz 12718 := by
  have hr : ((11277411 / 100000) : ℝ) ≤ √12718 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12718 : ℝ) * √12718 ≤ (⌈(12718 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12718
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12718 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12718 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12718 : ℝ) = (⌈(12718 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1434260 : ℝ) ≤ Jz 12718 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12718 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12718) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12718 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12718 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12718 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12718 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12718 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12718 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12718) :
    (12718 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12718 * √(qB 12718))) ≤
      (536730481 / 1000000000000) := by
  have hden : ((11277411 / 100000) : ℝ) * (63 / 100) ≤ √12718 * √(qB 12718) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12718 : ℝ) * √(qB 12718) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12718) :
    (12718 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12718 * √(qB 12718))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12718 : ℝ) * √(qB 12718) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12718 : ℝ) * (√12718 *
      (c1F (exp (1 / 2) / 12) (Jz 12718) * (186 / 10000) / Jz 12718)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12718)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12718 : ℝ) * (√12718 *
      (c1F (exp (1 / 2) / 12) (Jz 12718) * (186 / 10000) / Jz 12718)) =
      (12718 * (√12718 * c1F (exp (1 / 2) / 12) (Jz 12718)) * (186 / 10000)) /
        Jz 12718 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12718)]
  nlinarith

theorem row_energy_rule :
    (12718 : ℝ) * (12718 *
      (c2F (exp (1 / 2) / 12) (Jz 12718) * (186 / 10000) ^ 2 / Jz 12718)) ≤
      (3511382599 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12718)]
  nlinarith

end BstLean.Part266.Row12718

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12718
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12718) (hc : A1 c ∈ BstLean.Part153.Eop 12718) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12718 : ℝ)) ≤ (12540232471 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12718 : ℝ) + 2 * √12718 ≤ (6471774111 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12718 : ℝ) ≤ (112774111 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12718)
    (hc : A1 c ∈ BstLean.Part153.Eop 12718) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12718 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12718 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12718))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12718) (K : Set (Ix 12718)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12718 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12718 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12718) (hw : WINDOW (paperDesignP 12718) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12718)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12718) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12718 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12718 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12718 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12718 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12718) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12718)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12718)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12718

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12718
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12718) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12718 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12718) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12718) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12718 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12718 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12718 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12718}
    (hw : WINDOW (paperDesignP 12718) c) (hc : c ∈ tableEvent) (K : Set (Ix 12718)) :
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

def proposedBaseEvent : Set (Ret 12718) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12718)) : Prop where
  charge : (retDist (paperCentres 12718)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12718)} (h : TablePayment H) :
    (retDist (paperCentres 12718)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12718)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12718

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12718
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12718) (i : Fin 4) (a : Ix 12718) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12718) (a : Ix 12718) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12718) : Prop where
  moment : ∀ i, MomentBound (muI 12718) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12718} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12718) 8 (actualFourError c i)
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

end BstLean.Part266.Row12718

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12718
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

structure LatitudeVarianceCertificate (c : Ret 12718) : Prop where
  location : LBound (muI 12718) 12
    (fun a => conditionalVariance (stdGauss (Fin (12718 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12718) 12
    (fun a => conditionalVariance (stdGauss (Fin (12718 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12718) (hw : WINDOW (paperDesignP 12718) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12718 4 (55 / 100) /
      (12718 : ℝ) / ((12718 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12718

/-! The dimension-12718 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12718
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12718) (wl ws : ℝ) : SplitData 12718 :=
  BstLean.Part162.dPaper (paperDesignP 12718) c wl ws
    (√(2 / (12718 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12718 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12718 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12718) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12718) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12718 : ℝ)) * eR c * 12718 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12718) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12718 - 1)))
    (rowSplit c wl ws).good a ∂muI 12718 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12718) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12718 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12718) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12718 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12718) c (rowSplit c wl ws),
    hellG2 12718 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12718 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12718} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12718} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12718 t c BstLean.Part266.agent12718.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12718} (R : RootSource t c) :
    |√(QStand (paperDesignP 12718) t c) - √(qTilde (paperDesignP 12718) t c)| ≤
      BstLean.Part266.agent12718.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12718

/-! Rational enclosures for the HQ fluctuation price at dimension 12719. -/
namespace BstLean.Part266.Row12719
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (205731783 / 125000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (4643709 / 200000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12719 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12719 * A / 2 + D + L * √(A * D)) ≤ (4591273461 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12719 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((205731783 / 125000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12719 L e4 d4 ≤ (41594499091 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12719 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((205731783 / 125000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12719 L e6 d6 ≤ (63015835517 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12719 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((205731783 / 125000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12719 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12719 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12719 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12719 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (4643709 / 200000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4591273461 / 1000000000000)) ^ 2 / 2 + ((4591273461 / 1000000000000)) * ((41594499091 / 1000000000000)) ^ 2 / 6 +
      ((41594499091 / 1000000000000)) ^ 4 / 24 + ((41594499091 / 1000000000000)) ^ 2 * ((63015835517 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63015835517 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12719 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12719 : ℝ) * ((1 + 3 * ((4643709 / 200000000))) / (4 * (1 - (4643709 / 200000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (4643709 / 200000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12719 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (4643709 / 200000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12719 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12719 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12719

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12719
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((7048659 / 62500) : ℝ) ≤ √12719 ∧ √12719 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1434429 : ℝ) ≤ Jz 12719 ∧ 1000000 ≤ Jz 12719 := by
  have hr : ((7048659 / 62500) : ℝ) ≤ √12719 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12719 : ℝ) * √12719 ≤ (⌈(12719 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12719
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12719 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12719 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12719 : ℝ) = (⌈(12719 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1434429 : ℝ) ≤ Jz 12719 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12719 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12719) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12719 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12719 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12719 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12719 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12719 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12719 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12719) :
    (12719 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12719 * √(qB 12719))) ≤
      (26837579 / 50000000000) := by
  have hden : ((7048659 / 62500) : ℝ) * (63 / 100) ≤ √12719 * √(qB 12719) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12719 : ℝ) * √(qB 12719) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12719) :
    (12719 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12719 * √(qB 12719))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12719 : ℝ) * √(qB 12719) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12719 : ℝ) * (√12719 *
      (c1F (exp (1 / 2) / 12) (Jz 12719) * (186 / 10000) / Jz 12719)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12719)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12719 : ℝ) * (√12719 *
      (c1F (exp (1 / 2) / 12) (Jz 12719) * (186 / 10000) / Jz 12719)) =
      (12719 * (√12719 * c1F (exp (1 / 2) / 12) (Jz 12719)) * (186 / 10000)) /
        Jz 12719 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12719)]
  nlinarith

theorem row_energy_rule :
    (12719 : ℝ) * (12719 *
      (c2F (exp (1 / 2) / 12) (Jz 12719) * (186 / 10000) ^ 2 / Jz 12719)) ≤
      (3511521047 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12719)]
  nlinarith

end BstLean.Part266.Row12719

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12719
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12719) (hc : A1 c ∈ BstLean.Part153.Eop 12719) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12719 : ℝ)) ≤ (12539739489 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12719 : ℝ) + 2 * √12719 ≤ (1294455709 / 100000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12719 : ℝ) ≤ (22555709 / 200000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12719)
    (hc : A1 c ∈ BstLean.Part153.Eop 12719) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12719 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12719 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12719))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12719) (K : Set (Ix 12719)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12719 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12719 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12719) (hw : WINDOW (paperDesignP 12719) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12719)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12719) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12719 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12719 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12719 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12719 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12719) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12719)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12719)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12719

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12719
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12719) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12719 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12719) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12719) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12719 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12719 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12719 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12719}
    (hw : WINDOW (paperDesignP 12719) c) (hc : c ∈ tableEvent) (K : Set (Ix 12719)) :
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

def proposedBaseEvent : Set (Ret 12719) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12719)) : Prop where
  charge : (retDist (paperCentres 12719)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12719)} (h : TablePayment H) :
    (retDist (paperCentres 12719)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12719)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12719

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12719
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12719) (i : Fin 4) (a : Ix 12719) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12719) (a : Ix 12719) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12719) : Prop where
  moment : ∀ i, MomentBound (muI 12719) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12719} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12719) 8 (actualFourError c i)
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

end BstLean.Part266.Row12719

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12719
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

structure LatitudeVarianceCertificate (c : Ret 12719) : Prop where
  location : LBound (muI 12719) 12
    (fun a => conditionalVariance (stdGauss (Fin (12719 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12719) 12
    (fun a => conditionalVariance (stdGauss (Fin (12719 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12719) (hw : WINDOW (paperDesignP 12719) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12719 4 (55 / 100) /
      (12719 : ℝ) / ((12719 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12719

/-! The dimension-12719 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12719
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12719) (wl ws : ℝ) : SplitData 12719 :=
  BstLean.Part162.dPaper (paperDesignP 12719) c wl ws
    (√(2 / (12719 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12719 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12719 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12719) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12719) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12719 : ℝ)) * eR c * 12719 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12719) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12719 - 1)))
    (rowSplit c wl ws).good a ∂muI 12719 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12719) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12719 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12719) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12719 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12719) c (rowSplit c wl ws),
    hellG2 12719 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12719 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12719} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12719} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12719 t c BstLean.Part266.agent12719.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12719} (R : RootSource t c) :
    |√(QStand (paperDesignP 12719) t c) - √(qTilde (paperDesignP 12719) t c)| ≤
      BstLean.Part266.agent12719.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12719

/-! Rational enclosures for the HQ fluctuation price at dimension 12720. -/
namespace BstLean.Part266.Row12720
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (822894739 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (5804177 / 250000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12720 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12720 * A / 2 + D + L * √(A * D)) ≤ (4591474783 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12720 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((822894739 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12720 L e4 d4 ≤ (20798163787 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12720 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((822894739 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12720 L e6 d6 ≤ (31509299001 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12720 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((822894739 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12720 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12720 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12720 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12720 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (5804177 / 250000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4591474783 / 1000000000000)) ^ 2 / 2 + ((4591474783 / 1000000000000)) * ((20798163787 / 500000000000)) ^ 2 / 6 +
      ((20798163787 / 500000000000)) ^ 4 / 24 + ((20798163787 / 500000000000)) ^ 2 * ((31509299001 / 500000000000)) ^ 3 / 120 +
      2187 * ((31509299001 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12720 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12720 : ℝ) * ((1 + 3 * ((5804177 / 250000000))) / (4 * (1 - (5804177 / 250000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (5804177 / 250000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12720 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (5804177 / 250000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12720 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12720 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12720

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12720
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((112782977 / 1000000) : ℝ) ≤ √12720 ∧ √12720 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1434598 : ℝ) ≤ Jz 12720 ∧ 1000000 ≤ Jz 12720 := by
  have hr : ((112782977 / 1000000) : ℝ) ≤ √12720 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12720 : ℝ) * √12720 ≤ (⌈(12720 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12720
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12720 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12720 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12720 : ℝ) = (⌈(12720 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1434598 : ℝ) ≤ Jz 12720 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12720 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12720) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12720 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12720 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12720 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12720 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12720 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12720 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12720) :
    (12720 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12720 * √(qB 12720))) ≤
      (268386341 / 500000000000) := by
  have hden : ((112782977 / 1000000) : ℝ) * (63 / 100) ≤ √12720 * √(qB 12720) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12720 : ℝ) * √(qB 12720) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12720) :
    (12720 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12720 * √(qB 12720))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12720 : ℝ) * √(qB 12720) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12720 : ℝ) * (√12720 *
      (c1F (exp (1 / 2) / 12) (Jz 12720) * (186 / 10000) / Jz 12720)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12720)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12720 : ℝ) * (√12720 *
      (c1F (exp (1 / 2) / 12) (Jz 12720) * (186 / 10000) / Jz 12720)) =
      (12720 * (√12720 * c1F (exp (1 / 2) / 12) (Jz 12720)) * (186 / 10000)) /
        Jz 12720 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12720)]
  nlinarith

theorem row_energy_rule :
    (12720 : ℝ) * (12720 *
      (c2F (exp (1 / 2) / 12) (Jz 12720) * (186 / 10000) ^ 2 / Jz 12720)) ≤
      (702331901 / 200000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12720)]
  nlinarith

end BstLean.Part266.Row12720

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12720
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12720) (hc : A1 c ∈ BstLean.Part153.Eop 12720) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12720 : ℝ)) ≤ (2507849313 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12720 : ℝ) + 2 * √12720 ≤ (3236391489 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12720 : ℝ) ≤ (56391489 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12720)
    (hc : A1 c ∈ BstLean.Part153.Eop 12720) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12720 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12720 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12720))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12720) (K : Set (Ix 12720)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12720 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12720 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12720) (hw : WINDOW (paperDesignP 12720) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12720)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12720) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12720 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12720 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12720 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12720 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12720) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12720)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12720)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12720

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12720
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12720) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12720 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12720) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12720) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12720 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12720 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12720 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12720}
    (hw : WINDOW (paperDesignP 12720) c) (hc : c ∈ tableEvent) (K : Set (Ix 12720)) :
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

def proposedBaseEvent : Set (Ret 12720) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12720)) : Prop where
  charge : (retDist (paperCentres 12720)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12720)} (h : TablePayment H) :
    (retDist (paperCentres 12720)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12720)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12720

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12720
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12720) (i : Fin 4) (a : Ix 12720) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12720) (a : Ix 12720) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12720) : Prop where
  moment : ∀ i, MomentBound (muI 12720) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12720} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12720) 8 (actualFourError c i)
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

end BstLean.Part266.Row12720

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12720
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

structure LatitudeVarianceCertificate (c : Ret 12720) : Prop where
  location : LBound (muI 12720) 12
    (fun a => conditionalVariance (stdGauss (Fin (12720 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12720) 12
    (fun a => conditionalVariance (stdGauss (Fin (12720 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12720) (hw : WINDOW (paperDesignP 12720) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12720 4 (55 / 100) /
      (12720 : ℝ) / ((12720 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12720

/-! The dimension-12720 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12720
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12720) (wl ws : ℝ) : SplitData 12720 :=
  BstLean.Part162.dPaper (paperDesignP 12720) c wl ws
    (√(2 / (12720 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12720 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12720 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12720) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12720) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12720 : ℝ)) * eR c * 12720 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12720) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12720 - 1)))
    (rowSplit c wl ws).good a ∂muI 12720 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12720) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12720 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12720) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12720 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12720) c (rowSplit c wl ws),
    hellG2 12720 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12720 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12720} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12720} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12720 t c BstLean.Part266.agent12720.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12720} (R : RootSource t c) :
    |√(QStand (paperDesignP 12720) t c) - √(qTilde (paperDesignP 12720) t c)| ≤
      BstLean.Part266.agent12720.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12720

/-! Rational enclosures for the HQ fluctuation price at dimension 12721. -/
namespace BstLean.Part266.Row12721
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1645724707 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23214871 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12721 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12721 * A / 2 + D + L * √(A * D)) ≤ (2295838053 / 500000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12721 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1645724707 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12721 L e4 d4 ≤ (41598156061 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12721 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1645724707 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12721 L e6 d6 ≤ (63021360493 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12721 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1645724707 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12721 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12721 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12721 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12721 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23214871 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((2295838053 / 500000000000)) ^ 2 / 2 + ((2295838053 / 500000000000)) * ((41598156061 / 1000000000000)) ^ 2 / 6 +
      ((41598156061 / 1000000000000)) ^ 4 / 24 + ((41598156061 / 1000000000000)) ^ 2 * ((63021360493 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63021360493 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12721 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12721 : ℝ) * ((1 + 3 * ((23214871 / 1000000000))) / (4 * (1 - (23214871 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23214871 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12721 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23214871 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12721 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12721 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12721

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12721
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((11278741 / 100000) : ℝ) ≤ √12721 ∧ √12721 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1434767 : ℝ) ≤ Jz 12721 ∧ 1000000 ≤ Jz 12721 := by
  have hr : ((11278741 / 100000) : ℝ) ≤ √12721 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12721 : ℝ) * √12721 ≤ (⌈(12721 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12721
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12721 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12721 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12721 : ℝ) = (⌈(12721 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1434767 : ℝ) ≤ Jz 12721 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12721 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12721) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12721 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12721 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12721 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12721 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12721 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12721 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12721) :
    (12721 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12721 * √(qB 12721))) ≤
      (268396891 / 500000000000) := by
  have hden : ((11278741 / 100000) : ℝ) * (63 / 100) ≤ √12721 * √(qB 12721) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12721 : ℝ) * √(qB 12721) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12721) :
    (12721 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12721 * √(qB 12721))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12721 : ℝ) * √(qB 12721) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12721 : ℝ) * (√12721 *
      (c1F (exp (1 / 2) / 12) (Jz 12721) * (186 / 10000) / Jz 12721)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12721)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12721 : ℝ) * (√12721 *
      (c1F (exp (1 / 2) / 12) (Jz 12721) * (186 / 10000) / Jz 12721)) =
      (12721 * (√12721 * c1F (exp (1 / 2) / 12) (Jz 12721)) * (186 / 10000)) /
        Jz 12721 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12721)]
  nlinarith

theorem row_energy_rule :
    (12721 : ℝ) * (12721 *
      (c2F (exp (1 / 2) / 12) (Jz 12721) * (186 / 10000) ^ 2 / Jz 12721)) ≤
      (1755898987 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12721)]
  nlinarith

end BstLean.Part266.Row12721

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12721
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12721) (hc : A1 c ∈ BstLean.Part153.Eop 12721) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12721 : ℝ)) ≤ (12538753699 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12721 : ℝ) + 2 * √12721 ≤ (6473287411 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12721 : ℝ) ≤ (112787411 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12721)
    (hc : A1 c ∈ BstLean.Part153.Eop 12721) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12721 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12721 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12721))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12721) (K : Set (Ix 12721)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12721 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12721 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12721) (hw : WINDOW (paperDesignP 12721) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12721)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12721) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12721 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12721 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12721 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12721 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12721) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12721)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12721)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12721

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12721
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12721) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12721 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12721) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12721) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12721 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12721 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12721 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12721}
    (hw : WINDOW (paperDesignP 12721) c) (hc : c ∈ tableEvent) (K : Set (Ix 12721)) :
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

def proposedBaseEvent : Set (Ret 12721) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12721)) : Prop where
  charge : (retDist (paperCentres 12721)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12721)} (h : TablePayment H) :
    (retDist (paperCentres 12721)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12721)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12721

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12721
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12721) (i : Fin 4) (a : Ix 12721) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12721) (a : Ix 12721) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12721) : Prop where
  moment : ∀ i, MomentBound (muI 12721) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12721} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12721) 8 (actualFourError c i)
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

end BstLean.Part266.Row12721

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12721
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

structure LatitudeVarianceCertificate (c : Ret 12721) : Prop where
  location : LBound (muI 12721) 12
    (fun a => conditionalVariance (stdGauss (Fin (12721 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12721) 12
    (fun a => conditionalVariance (stdGauss (Fin (12721 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12721) (hw : WINDOW (paperDesignP 12721) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12721 4 (55 / 100) /
      (12721 : ℝ) / ((12721 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12721

/-! The dimension-12721 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12721
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12721) (wl ws : ℝ) : SplitData 12721 :=
  BstLean.Part162.dPaper (paperDesignP 12721) c wl ws
    (√(2 / (12721 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12721 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12721 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12721) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12721) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12721 : ℝ)) * eR c * 12721 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12721) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12721 - 1)))
    (rowSplit c wl ws).good a ∂muI 12721 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12721) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12721 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12721) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12721 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12721) c (rowSplit c wl ws),
    hellG2 12721 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12721 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12721} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12721} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12721 t c BstLean.Part266.agent12721.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12721} (R : RootSource t c) :
    |√(QStand (paperDesignP 12721) t c) - √(qTilde (paperDesignP 12721) t c)| ≤
      BstLean.Part266.agent12721.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12721

/-! Rational enclosures for the HQ fluctuation price at dimension 12722. -/
namespace BstLean.Part266.Row12722
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1645659953 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (4642607 / 200000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12722 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12722 * A / 2 + D + L * √(A * D)) ≤ (4591877429 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12722 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1645659953 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12722 L e4 d4 ≤ (5199998069 / 125000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12722 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1645659953 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12722 L e6 d6 ≤ (63024122991 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12722 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1645659953 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12722 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12722 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12722 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12722 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (4642607 / 200000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4591877429 / 1000000000000)) ^ 2 / 2 + ((4591877429 / 1000000000000)) * ((5199998069 / 125000000000)) ^ 2 / 6 +
      ((5199998069 / 125000000000)) ^ 4 / 24 + ((5199998069 / 125000000000)) ^ 2 * ((63024122991 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63024122991 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12722 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12722 : ℝ) * ((1 + 3 * ((4642607 / 200000000))) / (4 * (1 - (4642607 / 200000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (4642607 / 200000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12722 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (4642607 / 200000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12722 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12722 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12722

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12722
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((112791843 / 1000000) : ℝ) ≤ √12722 ∧ √12722 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1434936 : ℝ) ≤ Jz 12722 ∧ 1000000 ≤ Jz 12722 := by
  have hr : ((112791843 / 1000000) : ℝ) ≤ √12722 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12722 : ℝ) * √12722 ≤ (⌈(12722 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12722
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12722 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12722 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12722 : ℝ) = (⌈(12722 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1434936 : ℝ) ≤ Jz 12722 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12722 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12722) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12722 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12722 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12722 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12722 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12722 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12722 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12722) :
    (12722 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12722 * √(qB 12722))) ≤
      (3355093 / 6250000000) := by
  have hden : ((112791843 / 1000000) : ℝ) * (63 / 100) ≤ √12722 * √(qB 12722) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12722 : ℝ) * √(qB 12722) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12722) :
    (12722 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12722 * √(qB 12722))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12722 : ℝ) * √(qB 12722) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12722 : ℝ) * (√12722 *
      (c1F (exp (1 / 2) / 12) (Jz 12722) * (186 / 10000) / Jz 12722)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12722)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12722 : ℝ) * (√12722 *
      (c1F (exp (1 / 2) / 12) (Jz 12722) * (186 / 10000) / Jz 12722)) =
      (12722 * (√12722 * c1F (exp (1 / 2) / 12) (Jz 12722)) * (186 / 10000)) /
        Jz 12722 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12722)]
  nlinarith

theorem row_energy_rule :
    (12722 : ℝ) * (12722 *
      (c2F (exp (1 / 2) / 12) (Jz 12722) * (186 / 10000) ^ 2 / Jz 12722)) ≤
      (1755968227 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12722)]
  nlinarith

end BstLean.Part266.Row12722

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12722
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12722) (hc : A1 c ∈ BstLean.Part153.Eop 12722) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12722 : ℝ)) ≤ (12538260891 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12722 : ℝ) + 2 * √12722 ≤ (1618447961 / 125000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12722 : ℝ) ≤ (28197961 / 250000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12722)
    (hc : A1 c ∈ BstLean.Part153.Eop 12722) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12722 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12722 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12722))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12722) (K : Set (Ix 12722)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12722 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12722 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12722) (hw : WINDOW (paperDesignP 12722) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12722)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12722) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12722 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12722 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12722 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12722 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12722) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12722)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12722)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12722

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12722
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12722) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12722 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12722) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12722) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12722 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12722 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12722 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12722}
    (hw : WINDOW (paperDesignP 12722) c) (hc : c ∈ tableEvent) (K : Set (Ix 12722)) :
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

def proposedBaseEvent : Set (Ret 12722) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12722)) : Prop where
  charge : (retDist (paperCentres 12722)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12722)} (h : TablePayment H) :
    (retDist (paperCentres 12722)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12722)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12722

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12722
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12722) (i : Fin 4) (a : Ix 12722) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12722) (a : Ix 12722) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12722) : Prop where
  moment : ∀ i, MomentBound (muI 12722) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12722} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12722) 8 (actualFourError c i)
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

end BstLean.Part266.Row12722

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12722
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

structure LatitudeVarianceCertificate (c : Ret 12722) : Prop where
  location : LBound (muI 12722) 12
    (fun a => conditionalVariance (stdGauss (Fin (12722 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12722) 12
    (fun a => conditionalVariance (stdGauss (Fin (12722 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12722) (hw : WINDOW (paperDesignP 12722) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12722 4 (55 / 100) /
      (12722 : ℝ) / ((12722 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12722

/-! The dimension-12722 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12722
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12722) (wl ws : ℝ) : SplitData 12722 :=
  BstLean.Part162.dPaper (paperDesignP 12722) c wl ws
    (√(2 / (12722 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12722 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12722 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12722) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12722) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12722 : ℝ)) * eR c * 12722 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12722) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12722 - 1)))
    (rowSplit c wl ws).good a ∂muI 12722 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12722) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12722 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12722) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12722 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12722) c (rowSplit c wl ws),
    hellG2 12722 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12722 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12722} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12722} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12722 t c BstLean.Part266.agent12722.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12722} (R : RootSource t c) :
    |√(QStand (paperDesignP 12722) t c) - √(qTilde (paperDesignP 12722) t c)| ≤
      BstLean.Part266.agent12722.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12722

/-! Rational enclosures for the HQ fluctuation price at dimension 12723. -/
namespace BstLean.Part266.Row12723
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1645595213 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23211199 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12723 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12723 * A / 2 + D + L * √(A * D)) ≤ (4592078753 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12723 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1645595213 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12723 L e4 d4 ≤ (41601813047 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12723 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1645595213 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12723 L e6 d6 ≤ (63026885493 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12723 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1645595213 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12723 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12723 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12723 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12723 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23211199 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4592078753 / 1000000000000)) ^ 2 / 2 + ((4592078753 / 1000000000000)) * ((41601813047 / 1000000000000)) ^ 2 / 6 +
      ((41601813047 / 1000000000000)) ^ 4 / 24 + ((41601813047 / 1000000000000)) ^ 2 * ((63026885493 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63026885493 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12723 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12723 : ℝ) * ((1 + 3 * ((23211199 / 1000000000))) / (4 * (1 - (23211199 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23211199 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12723 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23211199 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12723 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12723 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12723

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12723
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((28199069 / 250000) : ℝ) ≤ √12723 ∧ √12723 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1435106 : ℝ) ≤ Jz 12723 ∧ 1000000 ≤ Jz 12723 := by
  have hr : ((28199069 / 250000) : ℝ) ≤ √12723 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12723 : ℝ) * √12723 ≤ (⌈(12723 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12723
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12723 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12723 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12723 : ℝ) = (⌈(12723 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1435106 : ℝ) ≤ Jz 12723 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12723 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12723) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12723 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12723 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12723 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12723 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12723 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12723 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12723) :
    (12723 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12723 * √(qB 12723))) ≤
      (536835977 / 1000000000000) := by
  have hden : ((28199069 / 250000) : ℝ) * (63 / 100) ≤ √12723 * √(qB 12723) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12723 : ℝ) * √(qB 12723) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12723) :
    (12723 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12723 * √(qB 12723))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12723 : ℝ) * √(qB 12723) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12723 : ℝ) * (√12723 *
      (c1F (exp (1 / 2) / 12) (Jz 12723) * (186 / 10000) / Jz 12723)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12723)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12723 : ℝ) * (√12723 *
      (c1F (exp (1 / 2) / 12) (Jz 12723) * (186 / 10000) / Jz 12723)) =
      (12723 * (√12723 * c1F (exp (1 / 2) / 12) (Jz 12723)) * (186 / 10000)) /
        Jz 12723 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12723)]
  nlinarith

theorem row_energy_rule :
    (12723 : ℝ) * (12723 *
      (c2F (exp (1 / 2) / 12) (Jz 12723) * (186 / 10000) ^ 2 / Jz 12723)) ≤
      (3512072497 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12723)]
  nlinarith

end BstLean.Part266.Row12723

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12723
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12723) (hc : A1 c ∈ BstLean.Part153.Eop 12723) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12723 : ℝ)) ≤ (6268884071 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12723 : ℝ) + 2 * √12723 ≤ (6474296277 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12723 : ℝ) ≤ (112796277 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12723)
    (hc : A1 c ∈ BstLean.Part153.Eop 12723) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12723 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12723 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12723))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12723) (K : Set (Ix 12723)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12723 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12723 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12723) (hw : WINDOW (paperDesignP 12723) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12723)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12723) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12723 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12723 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12723 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12723 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12723) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12723)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12723)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12723

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12723
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12723) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12723 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12723) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12723) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12723 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12723 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12723 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12723}
    (hw : WINDOW (paperDesignP 12723) c) (hc : c ∈ tableEvent) (K : Set (Ix 12723)) :
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

def proposedBaseEvent : Set (Ret 12723) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12723)) : Prop where
  charge : (retDist (paperCentres 12723)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12723)} (h : TablePayment H) :
    (retDist (paperCentres 12723)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12723)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12723

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12723
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12723) (i : Fin 4) (a : Ix 12723) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12723) (a : Ix 12723) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12723) : Prop where
  moment : ∀ i, MomentBound (muI 12723) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12723} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12723) 8 (actualFourError c i)
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

end BstLean.Part266.Row12723

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12723
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

structure LatitudeVarianceCertificate (c : Ret 12723) : Prop where
  location : LBound (muI 12723) 12
    (fun a => conditionalVariance (stdGauss (Fin (12723 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12723) 12
    (fun a => conditionalVariance (stdGauss (Fin (12723 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12723) (hw : WINDOW (paperDesignP 12723) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12723 4 (55 / 100) /
      (12723 : ℝ) / ((12723 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12723

/-! The dimension-12723 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12723
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12723) (wl ws : ℝ) : SplitData 12723 :=
  BstLean.Part162.dPaper (paperDesignP 12723) c wl ws
    (√(2 / (12723 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12723 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12723 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12723) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12723) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12723 : ℝ)) * eR c * 12723 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12723) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12723 - 1)))
    (rowSplit c wl ws).good a ∂muI 12723 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12723) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12723 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12723) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12723 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12723) c (rowSplit c wl ws),
    hellG2 12723 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12723 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12723} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12723} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12723 t c BstLean.Part266.agent12723.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12723} (R : RootSource t c) :
    |√(QStand (paperDesignP 12723) t c) - √(qTilde (paperDesignP 12723) t c)| ≤
      BstLean.Part266.agent12723.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12723

/-! Rational enclosures for the HQ fluctuation price at dimension 12724. -/
namespace BstLean.Part266.Row12724
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (51422819 / 31250000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23209359 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12724 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12724 * A / 2 + D + L * √(A * D)) ≤ (4592280069 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12724 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((51422819 / 31250000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12724 L e4 d4 ≤ (20801820737 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12724 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((51422819 / 31250000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12724 L e6 d6 ≤ (63029647893 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12724 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((51422819 / 31250000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12724 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12724 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12724 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12724 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23209359 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4592280069 / 1000000000000)) ^ 2 / 2 + ((4592280069 / 1000000000000)) * ((20801820737 / 500000000000)) ^ 2 / 6 +
      ((20801820737 / 500000000000)) ^ 4 / 24 + ((20801820737 / 500000000000)) ^ 2 * ((63029647893 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63029647893 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12724 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12724 : ℝ) * ((1 + 3 * ((23209359 / 1000000000))) / (4 * (1 - (23209359 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23209359 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12724 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23209359 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12724 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12724 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12724

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12724
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((112800709 / 1000000) : ℝ) ≤ √12724 ∧ √12724 ≤ 113 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1435275 : ℝ) ≤ Jz 12724 ∧ 1000000 ≤ Jz 12724 := by
  have hr : ((112800709 / 1000000) : ℝ) ≤ √12724 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12724 : ℝ) * √12724 ≤ (⌈(12724 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12724
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12724 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12724 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12724 : ℝ) = (⌈(12724 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1435275 : ℝ) ≤ Jz 12724 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12724 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12724) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12724 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12724 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12724 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12724 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12724 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12724 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12724) :
    (12724 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12724 * √(qB 12724))) ≤
      (33553567 / 62500000000) := by
  have hden : ((112800709 / 1000000) : ℝ) * (63 / 100) ≤ √12724 * √(qB 12724) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12724 : ℝ) * √(qB 12724) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12724) :
    (12724 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12724 * √(qB 12724))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12724 : ℝ) * √(qB 12724) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12724 : ℝ) * (√12724 *
      (c1F (exp (1 / 2) / 12) (Jz 12724) * (186 / 10000) / Jz 12724)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12724)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 113)
  have he : (12724 : ℝ) * (√12724 *
      (c1F (exp (1 / 2) / 12) (Jz 12724) * (186 / 10000) / Jz 12724)) =
      (12724 * (√12724 * c1F (exp (1 / 2) / 12) (Jz 12724)) * (186 / 10000)) /
        Jz 12724 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12724)]
  nlinarith

theorem row_energy_rule :
    (12724 : ℝ) * (12724 *
      (c2F (exp (1 / 2) / 12) (Jz 12724) * (186 / 10000) ^ 2 / Jz 12724)) ≤
      (1756105499 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12724)]
  nlinarith

end BstLean.Part266.Row12724

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12724
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12724) (hc : A1 c ∈ BstLean.Part153.Eop 12724) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12724 : ℝ)) ≤ (250745509 / 20000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12724 : ℝ) + 2 * √12724 ≤ (647480071 / 50000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12724 : ℝ) ≤ (11280071 / 100000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12724)
    (hc : A1 c ∈ BstLean.Part153.Eop 12724) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12724 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12724 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12724))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12724) (K : Set (Ix 12724)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12724 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12724 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12724) (hw : WINDOW (paperDesignP 12724) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12724)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12724) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12724 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12724 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12724 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12724 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12724) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12724)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12724)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12724

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12724
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12724) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12724 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12724) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12724) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12724 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12724 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12724 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12724}
    (hw : WINDOW (paperDesignP 12724) c) (hc : c ∈ tableEvent) (K : Set (Ix 12724)) :
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

def proposedBaseEvent : Set (Ret 12724) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12724)) : Prop where
  charge : (retDist (paperCentres 12724)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12724)} (h : TablePayment H) :
    (retDist (paperCentres 12724)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12724)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12724

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12724
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12724) (i : Fin 4) (a : Ix 12724) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12724) (a : Ix 12724) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12724) : Prop where
  moment : ∀ i, MomentBound (muI 12724) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12724} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12724) 8 (actualFourError c i)
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

end BstLean.Part266.Row12724

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12724
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

structure LatitudeVarianceCertificate (c : Ret 12724) : Prop where
  location : LBound (muI 12724) 12
    (fun a => conditionalVariance (stdGauss (Fin (12724 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12724) 12
    (fun a => conditionalVariance (stdGauss (Fin (12724 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12724) (hw : WINDOW (paperDesignP 12724) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12724 4 (55 / 100) /
      (12724 : ℝ) / ((12724 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12724

/-! The dimension-12724 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12724
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12724) (wl ws : ℝ) : SplitData 12724 :=
  BstLean.Part162.dPaper (paperDesignP 12724) c wl ws
    (√(2 / (12724 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12724 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12724 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12724) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12724) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12724 : ℝ)) * eR c * 12724 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12724) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12724 - 1)))
    (rowSplit c wl ws).good a ∂muI 12724 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12724) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12724 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12724) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12724 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12724) c (rowSplit c wl ws),
    hellG2 12724 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12724 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12724} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12724} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12724 t c BstLean.Part266.agent12724.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12724} (R : RootSource t c) :
    |√(QStand (paperDesignP 12724) t c) - √(qTilde (paperDesignP 12724) t c)| ≤
      BstLean.Part266.agent12724.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12724
