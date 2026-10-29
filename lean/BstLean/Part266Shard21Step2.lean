import BstLean.Part266Shard21Step1


/-! Rational enclosures for the HQ fluctuation price at dimension 12875. -/
namespace BstLean.Part266.Row12875
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1635833409 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (5733837 / 250000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12875 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12875 * A / 2 + D + L * √(A * D)) ≤ (2311341117 / 500000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12875 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1635833409 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12875 L e4 d4 ≤ (20939882173 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12875 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1635833409 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12875 L e6 d6 ≤ (15861704099 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12875 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1635833409 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12875 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12875 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12875 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12875 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (5733837 / 250000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((2311341117 / 500000000000)) ^ 2 / 2 + ((2311341117 / 500000000000)) * ((20939882173 / 500000000000)) ^ 2 / 6 +
      ((20939882173 / 500000000000)) ^ 4 / 24 + ((20939882173 / 500000000000)) ^ 2 * ((15861704099 / 250000000000)) ^ 3 / 120 +
      2187 * ((15861704099 / 250000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12875 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12875 : ℝ) * ((1 + 3 * ((5733837 / 250000000))) / (4 * (1 - (5733837 / 250000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (5733837 / 250000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12875 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (5733837 / 250000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12875 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12875 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12875

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12875
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113468057 / 1000000) : ℝ) ≤ √12875 ∧ √12875 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1460900 : ℝ) ≤ Jz 12875 ∧ 1000000 ≤ Jz 12875 := by
  have hr : ((113468057 / 1000000) : ℝ) ≤ √12875 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12875 : ℝ) * √12875 ≤ (⌈(12875 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12875
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12875 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12875 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12875 : ℝ) = (⌈(12875 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1460900 : ℝ) ≤ Jz 12875 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12875 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12875) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12875 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12875 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12875 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12875 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12875 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12875 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12875) :
    (12875 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12875 * √(qB 12875))) ≤
      (67918287 / 125000000000) := by
  have hden : ((113468057 / 1000000) : ℝ) * (63 / 100) ≤ √12875 * √(qB 12875) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12875 : ℝ) * √(qB 12875) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12875) :
    (12875 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12875 * √(qB 12875))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12875 : ℝ) * √(qB 12875) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12875 : ℝ) * (√12875 *
      (c1F (exp (1 / 2) / 12) (Jz 12875) * (186 / 10000) / Jz 12875)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12875)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12875 : ℝ) * (√12875 *
      (c1F (exp (1 / 2) / 12) (Jz 12875) * (186 / 10000) / Jz 12875)) =
      (12875 * (√12875 * c1F (exp (1 / 2) / 12) (Jz 12875)) * (186 / 10000)) /
        Jz 12875 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12875)]
  nlinarith

theorem row_energy_rule :
    (12875 : ℝ) * (12875 *
      (c2F (exp (1 / 2) / 12) (Jz 12875) * (186 / 10000) ^ 2 / Jz 12875)) ≤
      (1766494903 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12875)]
  nlinarith

end BstLean.Part266.Row12875

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12875
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12875) (hc : A1 c ∈ BstLean.Part153.Eop 12875) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12875 : ℝ)) ≤ (12463539057 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12875 : ℝ) + 2 * √12875 ≤ (3275484029 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12875 : ℝ) ≤ (56734029 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12875)
    (hc : A1 c ∈ BstLean.Part153.Eop 12875) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12875 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12875 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12875))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12875) (K : Set (Ix 12875)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12875 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12875 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12875) (hw : WINDOW (paperDesignP 12875) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12875)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12875) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12875 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12875 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12875 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12875 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12875) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12875)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12875)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12875

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12875
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12875) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12875 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12875) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12875) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12875 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12875 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12875 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12875}
    (hw : WINDOW (paperDesignP 12875) c) (hc : c ∈ tableEvent) (K : Set (Ix 12875)) :
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

def proposedBaseEvent : Set (Ret 12875) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12875)) : Prop where
  charge : (retDist (paperCentres 12875)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12875)} (h : TablePayment H) :
    (retDist (paperCentres 12875)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12875)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12875

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12875
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12875) (i : Fin 4) (a : Ix 12875) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12875) (a : Ix 12875) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12875) : Prop where
  moment : ∀ i, MomentBound (muI 12875) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12875} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12875) 8 (actualFourError c i)
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

end BstLean.Part266.Row12875

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12875
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

structure LatitudeVarianceCertificate (c : Ret 12875) : Prop where
  location : LBound (muI 12875) 12
    (fun a => conditionalVariance (stdGauss (Fin (12875 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12875) 12
    (fun a => conditionalVariance (stdGauss (Fin (12875 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12875) (hw : WINDOW (paperDesignP 12875) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12875 4 (55 / 100) /
      (12875 : ℝ) / ((12875 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12875

/-! The dimension-12875 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12875
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12875) (wl ws : ℝ) : SplitData 12875 :=
  BstLean.Part162.dPaper (paperDesignP 12875) c wl ws
    (√(2 / (12875 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12875 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12875 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12875) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12875) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12875 : ℝ)) * eR c * 12875 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12875) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12875 - 1)))
    (rowSplit c wl ws).good a ∂muI 12875 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12875) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12875 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12875) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12875 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12875) c (rowSplit c wl ws),
    hellG2 12875 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12875 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12875} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12875} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12875 t c BstLean.Part266.agent12875.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12875} (R : RootSource t c) :
    |√(QStand (paperDesignP 12875) t c) - √(qTilde (paperDesignP 12875) t c)| ≤
      BstLean.Part266.agent12875.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12875

/-! Rational enclosures for the HQ fluctuation price at dimension 12876. -/
namespace BstLean.Part266.Row12876
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (408942463 / 250000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (5733389 / 250000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12876 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12876 * A / 2 + D + L * √(A * D)) ≤ (577860449 / 125000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12876 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((408942463 / 250000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12876 L e4 d4 ≤ (41881593143 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12876 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((408942463 / 250000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12876 L e6 d6 ≤ (63449579357 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12876 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((408942463 / 250000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12876 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12876 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12876 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12876 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (5733389 / 250000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((577860449 / 125000000000)) ^ 2 / 2 + ((577860449 / 125000000000)) * ((41881593143 / 1000000000000)) ^ 2 / 6 +
      ((41881593143 / 1000000000000)) ^ 4 / 24 + ((41881593143 / 1000000000000)) ^ 2 * ((63449579357 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63449579357 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12876 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12876 : ℝ) * ((1 + 3 * ((5733389 / 250000000))) / (4 * (1 - (5733389 / 250000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (5733389 / 250000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12876 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (5733389 / 250000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12876 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12876 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12876

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12876
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113472463 / 1000000) : ℝ) ≤ √12876 ∧ √12876 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1461070 : ℝ) ≤ Jz 12876 ∧ 1000000 ≤ Jz 12876 := by
  have hr : ((113472463 / 1000000) : ℝ) ≤ √12876 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12876 : ℝ) * √12876 ≤ (⌈(12876 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12876
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12876 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12876 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12876 : ℝ) = (⌈(12876 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1461070 : ℝ) ≤ Jz 12876 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12876 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12876) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12876 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12876 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12876 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12876 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12876 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12876 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12876) :
    (12876 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12876 * √(qB 12876))) ≤
      (271683699 / 500000000000) := by
  have hden : ((113472463 / 1000000) : ℝ) * (63 / 100) ≤ √12876 * √(qB 12876) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12876 : ℝ) * √(qB 12876) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12876) :
    (12876 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12876 * √(qB 12876))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12876 : ℝ) * √(qB 12876) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12876 : ℝ) * (√12876 *
      (c1F (exp (1 / 2) / 12) (Jz 12876) * (186 / 10000) / Jz 12876)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12876)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12876 : ℝ) * (√12876 *
      (c1F (exp (1 / 2) / 12) (Jz 12876) * (186 / 10000) / Jz 12876)) =
      (12876 * (√12876 * c1F (exp (1 / 2) / 12) (Jz 12876)) * (186 / 10000)) /
        Jz 12876 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12876)]
  nlinarith

theorem row_energy_rule :
    (12876 : ℝ) * (12876 *
      (c2F (exp (1 / 2) / 12) (Jz 12876) * (186 / 10000) ^ 2 / Jz 12876)) ≤
      (3533127503 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12876)]
  nlinarith

end BstLean.Part266.Row12876

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12876
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12876) (hc : A1 c ∈ BstLean.Part153.Eop 12876) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12876 : ℝ)) ≤ (2492611013 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12876 : ℝ) + 2 * √12876 ≤ (409467029 / 31250) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12876 : ℝ) ≤ (7092029 / 62500))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12876)
    (hc : A1 c ∈ BstLean.Part153.Eop 12876) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12876 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12876 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12876))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12876) (K : Set (Ix 12876)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12876 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12876 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12876) (hw : WINDOW (paperDesignP 12876) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12876)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12876) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12876 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12876 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12876 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12876 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12876) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12876)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12876)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12876

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12876
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12876) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12876 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12876) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12876) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12876 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12876 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12876 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12876}
    (hw : WINDOW (paperDesignP 12876) c) (hc : c ∈ tableEvent) (K : Set (Ix 12876)) :
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

def proposedBaseEvent : Set (Ret 12876) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12876)) : Prop where
  charge : (retDist (paperCentres 12876)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12876)} (h : TablePayment H) :
    (retDist (paperCentres 12876)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12876)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12876

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12876
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12876) (i : Fin 4) (a : Ix 12876) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12876) (a : Ix 12876) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12876) : Prop where
  moment : ∀ i, MomentBound (muI 12876) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12876} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12876) 8 (actualFourError c i)
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

end BstLean.Part266.Row12876

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12876
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

structure LatitudeVarianceCertificate (c : Ret 12876) : Prop where
  location : LBound (muI 12876) 12
    (fun a => conditionalVariance (stdGauss (Fin (12876 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12876) 12
    (fun a => conditionalVariance (stdGauss (Fin (12876 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12876) (hw : WINDOW (paperDesignP 12876) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12876 4 (55 / 100) /
      (12876 : ℝ) / ((12876 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12876

/-! The dimension-12876 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12876
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12876) (wl ws : ℝ) : SplitData 12876 :=
  BstLean.Part162.dPaper (paperDesignP 12876) c wl ws
    (√(2 / (12876 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12876 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12876 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12876) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12876) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12876 : ℝ)) * eR c * 12876 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12876) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12876 - 1)))
    (rowSplit c wl ws).good a ∂muI 12876 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12876) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12876 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12876) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12876 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12876) c (rowSplit c wl ws),
    hellG2 12876 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12876 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12876} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12876} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12876 t c BstLean.Part266.agent12876.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12876} (R : RootSource t c) :
    |√(QStand (paperDesignP 12876) t c) - √(qTilde (paperDesignP 12876) t c)| ≤
      BstLean.Part266.agent12876.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12876

/-! Rational enclosures for the HQ fluctuation price at dimension 12877. -/
namespace BstLean.Part266.Row12877
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (408926507 / 250000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22931761 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12877 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12877 * A / 2 + D + L * √(A * D)) ≤ (2311542471 / 500000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12877 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((408926507 / 250000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12877 L e4 d4 ≤ (2617713867 / 62500000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12877 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((408926507 / 250000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12877 L e6 d6 ≤ (12690468443 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12877 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((408926507 / 250000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12877 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12877 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12877 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12877 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22931761 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((2311542471 / 500000000000)) ^ 2 / 2 + ((2311542471 / 500000000000)) * ((2617713867 / 62500000000)) ^ 2 / 6 +
      ((2617713867 / 62500000000)) ^ 4 / 24 + ((2617713867 / 62500000000)) ^ 2 * ((12690468443 / 200000000000)) ^ 3 / 120 +
      2187 * ((12690468443 / 200000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12877 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12877 : ℝ) * ((1 + 3 * ((22931761 / 1000000000))) / (4 * (1 - (22931761 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22931761 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12877 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22931761 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12877 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12877 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12877

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12877
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113476869 / 1000000) : ℝ) ≤ √12877 ∧ √12877 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1461240 : ℝ) ≤ Jz 12877 ∧ 1000000 ≤ Jz 12877 := by
  have hr : ((113476869 / 1000000) : ℝ) ≤ √12877 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12877 : ℝ) * √12877 ≤ (⌈(12877 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12877
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12877 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12877 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12877 : ℝ) = (⌈(12877 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1461240 : ℝ) ≤ Jz 12877 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12877 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12877) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12877 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12877 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12877 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12877 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12877 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12877 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12877) :
    (12877 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12877 * √(qB 12877))) ≤
      (543388499 / 1000000000000) := by
  have hden : ((113476869 / 1000000) : ℝ) * (63 / 100) ≤ √12877 * √(qB 12877) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12877 : ℝ) * √(qB 12877) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12877) :
    (12877 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12877 * √(qB 12877))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12877 : ℝ) * √(qB 12877) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12877 : ℝ) * (√12877 *
      (c1F (exp (1 / 2) / 12) (Jz 12877) * (186 / 10000) / Jz 12877)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12877)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12877 : ℝ) * (√12877 *
      (c1F (exp (1 / 2) / 12) (Jz 12877) * (186 / 10000) / Jz 12877)) =
      (12877 * (√12877 * c1F (exp (1 / 2) / 12) (Jz 12877)) * (186 / 10000)) /
        Jz 12877 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12877)]
  nlinarith

theorem row_energy_rule :
    (12877 : ℝ) * (12877 *
      (c2F (exp (1 / 2) / 12) (Jz 12877) * (186 / 10000) ^ 2 / Jz 12877)) ≤
      (353326521 / 100000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12877)]
  nlinarith

end BstLean.Part266.Row12877

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12877
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12877) (hc : A1 c ∈ BstLean.Part153.Eop 12877) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12877 : ℝ)) ≤ (1557821391 / 125000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12877 : ℝ) + 2 * √12877 ≤ (655197687 / 50000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12877 : ℝ) ≤ (11347687 / 100000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12877)
    (hc : A1 c ∈ BstLean.Part153.Eop 12877) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12877 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12877 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12877))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12877) (K : Set (Ix 12877)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12877 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12877 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12877) (hw : WINDOW (paperDesignP 12877) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12877)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12877) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12877 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12877 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12877 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12877 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12877) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12877)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12877)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12877

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12877
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12877) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12877 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12877) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12877) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12877 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12877 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12877 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12877}
    (hw : WINDOW (paperDesignP 12877) c) (hc : c ∈ tableEvent) (K : Set (Ix 12877)) :
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

def proposedBaseEvent : Set (Ret 12877) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12877)) : Prop where
  charge : (retDist (paperCentres 12877)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12877)} (h : TablePayment H) :
    (retDist (paperCentres 12877)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12877)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12877

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12877
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12877) (i : Fin 4) (a : Ix 12877) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12877) (a : Ix 12877) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12877) : Prop where
  moment : ∀ i, MomentBound (muI 12877) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12877} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12877) 8 (actualFourError c i)
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

end BstLean.Part266.Row12877

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12877
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

structure LatitudeVarianceCertificate (c : Ret 12877) : Prop where
  location : LBound (muI 12877) 12
    (fun a => conditionalVariance (stdGauss (Fin (12877 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12877) 12
    (fun a => conditionalVariance (stdGauss (Fin (12877 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12877) (hw : WINDOW (paperDesignP 12877) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12877 4 (55 / 100) /
      (12877 : ℝ) / ((12877 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12877

/-! The dimension-12877 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12877
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12877) (wl ws : ℝ) : SplitData 12877 :=
  BstLean.Part162.dPaper (paperDesignP 12877) c wl ws
    (√(2 / (12877 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12877 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12877 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12877) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12877) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12877 : ℝ)) * eR c * 12877 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12877) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12877 - 1)))
    (rowSplit c wl ws).good a ∂muI 12877 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12877) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12877 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12877) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12877 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12877) c (rowSplit c wl ws),
    hellG2 12877 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12877 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12877} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12877} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12877 t c BstLean.Part266.agent12877.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12877} (R : RootSource t c) :
    |√(QStand (paperDesignP 12877) t c) - √(qTilde (paperDesignP 12877) t c)| ≤
      BstLean.Part266.agent12877.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12877

/-! Rational enclosures for the HQ fluctuation price at dimension 12878. -/
namespace BstLean.Part266.Row12878
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1635642501 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (2292997 / 100000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12878 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12878 * A / 2 + D + L * √(A * D)) ≤ (4623286301 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12878 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1635642501 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12878 L e4 d4 ≤ (41885250677 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12878 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1635642501 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12878 L e6 d6 ≤ (15863776297 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12878 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1635642501 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12878 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12878 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12878 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12878 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (2292997 / 100000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4623286301 / 1000000000000)) ^ 2 / 2 + ((4623286301 / 1000000000000)) * ((41885250677 / 1000000000000)) ^ 2 / 6 +
      ((41885250677 / 1000000000000)) ^ 4 / 24 + ((41885250677 / 1000000000000)) ^ 2 * ((15863776297 / 250000000000)) ^ 3 / 120 +
      2187 * ((15863776297 / 250000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12878 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12878 : ℝ) * ((1 + 3 * ((2292997 / 100000000))) / (4 * (1 - (2292997 / 100000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (2292997 / 100000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12878 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (2292997 / 100000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12878 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12878 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12878

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12878
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((4539251 / 40000) : ℝ) ≤ √12878 ∧ √12878 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1461410 : ℝ) ≤ Jz 12878 ∧ 1000000 ≤ Jz 12878 := by
  have hr : ((4539251 / 40000) : ℝ) ≤ √12878 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12878 : ℝ) * √12878 ≤ (⌈(12878 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12878
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12878 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12878 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12878 : ℝ) = (⌈(12878 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1461410 : ℝ) ≤ Jz 12878 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12878 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12878) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12878 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12878 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12878 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12878 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12878 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12878 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12878) :
    (12878 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12878 * √(qB 12878))) ≤
      (543409599 / 1000000000000) := by
  have hden : ((4539251 / 40000) : ℝ) * (63 / 100) ≤ √12878 * √(qB 12878) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12878 : ℝ) * √(qB 12878) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12878) :
    (12878 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12878 * √(qB 12878))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12878 : ℝ) * √(qB 12878) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12878 : ℝ) * (√12878 *
      (c1F (exp (1 / 2) / 12) (Jz 12878) * (186 / 10000) / Jz 12878)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12878)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12878 : ℝ) * (√12878 *
      (c1F (exp (1 / 2) / 12) (Jz 12878) * (186 / 10000) / Jz 12878)) =
      (12878 * (√12878 * c1F (exp (1 / 2) / 12) (Jz 12878)) * (186 / 10000)) /
        Jz 12878 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12878)]
  nlinarith

theorem row_energy_rule :
    (12878 : ℝ) * (12878 *
      (c2F (exp (1 / 2) / 12) (Jz 12878) * (186 / 10000) ^ 2 / Jz 12878)) ≤
      (3533402929 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12878)]
  nlinarith

end BstLean.Part266.Row12878

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12878
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12878) (hc : A1 c ∈ BstLean.Part153.Eop 12878) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12878 : ℝ)) ≤ (778880453 / 62500000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12878 : ℝ) + 2 * √12878 ≤ (1638120319 / 125000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12878 : ℝ) ≤ (28370319 / 250000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12878)
    (hc : A1 c ∈ BstLean.Part153.Eop 12878) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12878 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12878 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12878))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12878) (K : Set (Ix 12878)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12878 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12878 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12878) (hw : WINDOW (paperDesignP 12878) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12878)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12878) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12878 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12878 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12878 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12878 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12878) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12878)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12878)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12878

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12878
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12878) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12878 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12878) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12878) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12878 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12878 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12878 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12878}
    (hw : WINDOW (paperDesignP 12878) c) (hc : c ∈ tableEvent) (K : Set (Ix 12878)) :
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

def proposedBaseEvent : Set (Ret 12878) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12878)) : Prop where
  charge : (retDist (paperCentres 12878)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12878)} (h : TablePayment H) :
    (retDist (paperCentres 12878)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12878)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12878

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12878
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12878) (i : Fin 4) (a : Ix 12878) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12878) (a : Ix 12878) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12878) : Prop where
  moment : ∀ i, MomentBound (muI 12878) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12878} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12878) 8 (actualFourError c i)
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

end BstLean.Part266.Row12878

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12878
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

structure LatitudeVarianceCertificate (c : Ret 12878) : Prop where
  location : LBound (muI 12878) 12
    (fun a => conditionalVariance (stdGauss (Fin (12878 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12878) 12
    (fun a => conditionalVariance (stdGauss (Fin (12878 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12878) (hw : WINDOW (paperDesignP 12878) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12878 4 (55 / 100) /
      (12878 : ℝ) / ((12878 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12878

/-! The dimension-12878 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12878
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12878) (wl ws : ℝ) : SplitData 12878 :=
  BstLean.Part162.dPaper (paperDesignP 12878) c wl ws
    (√(2 / (12878 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12878 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12878 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12878) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12878) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12878 : ℝ)) * eR c * 12878 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12878) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12878 - 1)))
    (rowSplit c wl ws).good a ∂muI 12878 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12878) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12878 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12878) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12878 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12878) c (rowSplit c wl ws),
    hellG2 12878 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12878 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12878} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12878} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12878 t c BstLean.Part266.agent12878.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12878} (R : RootSource t c) :
    |√(QStand (paperDesignP 12878) t c) - √(qTilde (paperDesignP 12878) t c)| ≤
      BstLean.Part266.agent12878.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12878

/-! Rational enclosures for the HQ fluctuation price at dimension 12879. -/
namespace BstLean.Part266.Row12879
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1635578987 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22928179 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12879 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12879 * A / 2 + D + L * √(A * D)) ≤ (231174383 / 50000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12879 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1635578987 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12879 L e4 d4 ≤ (8377415897 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12879 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1635578987 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12879 L e6 d6 ≤ (12691573633 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12879 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1635578987 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12879 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12879 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12879 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12879 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22928179 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((231174383 / 50000000000)) ^ 2 / 2 + ((231174383 / 50000000000)) * ((8377415897 / 200000000000)) ^ 2 / 6 +
      ((8377415897 / 200000000000)) ^ 4 / 24 + ((8377415897 / 200000000000)) ^ 2 * ((12691573633 / 200000000000)) ^ 3 / 120 +
      2187 * ((12691573633 / 200000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12879 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12879 : ℝ) * ((1 + 3 * ((22928179 / 1000000000))) / (4 * (1 - (22928179 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22928179 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12879 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22928179 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12879 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12879 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12879

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12879
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113485681 / 1000000) : ℝ) ≤ √12879 ∧ √12879 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1461581 : ℝ) ≤ Jz 12879 ∧ 1000000 ≤ Jz 12879 := by
  have hr : ((113485681 / 1000000) : ℝ) ≤ √12879 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12879 : ℝ) * √12879 ≤ (⌈(12879 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12879
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12879 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12879 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12879 : ℝ) = (⌈(12879 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1461581 : ℝ) ≤ Jz 12879 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12879 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12879) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12879 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12879 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12879 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12879 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12879 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12879 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12879) :
    (12879 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12879 * √(qB 12879))) ≤
      (67928837 / 125000000000) := by
  have hden : ((113485681 / 1000000) : ℝ) * (63 / 100) ≤ √12879 * √(qB 12879) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12879 : ℝ) * √(qB 12879) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12879) :
    (12879 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12879 * √(qB 12879))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12879 : ℝ) * √(qB 12879) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12879 : ℝ) * (√12879 *
      (c1F (exp (1 / 2) / 12) (Jz 12879) * (186 / 10000) / Jz 12879)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12879)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12879 : ℝ) * (√12879 *
      (c1F (exp (1 / 2) / 12) (Jz 12879) * (186 / 10000) / Jz 12879)) =
      (12879 * (√12879 * c1F (exp (1 / 2) / 12) (Jz 12879)) * (186 / 10000)) /
        Jz 12879 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12879)]
  nlinarith

theorem row_energy_rule :
    (12879 : ℝ) * (12879 *
      (c2F (exp (1 / 2) / 12) (Jz 12879) * (186 / 10000) ^ 2 / Jz 12879)) ≤
      (11042307 / 3125000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12879)]
  nlinarith

end BstLean.Part266.Row12879

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12879
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12879) (hc : A1 c ∈ BstLean.Part153.Eop 12879) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12879 : ℝ)) ≤ (498464137 / 40000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12879 : ℝ) + 2 * √12879 ≤ (3276492841 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12879 : ℝ) ≤ (56742841 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12879)
    (hc : A1 c ∈ BstLean.Part153.Eop 12879) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12879 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12879 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12879))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12879) (K : Set (Ix 12879)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12879 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12879 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12879) (hw : WINDOW (paperDesignP 12879) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12879)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12879) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12879 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12879 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12879 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12879 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12879) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12879)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12879)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12879

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12879
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12879) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12879 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12879) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12879) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12879 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12879 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12879 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12879}
    (hw : WINDOW (paperDesignP 12879) c) (hc : c ∈ tableEvent) (K : Set (Ix 12879)) :
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

def proposedBaseEvent : Set (Ret 12879) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12879)) : Prop where
  charge : (retDist (paperCentres 12879)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12879)} (h : TablePayment H) :
    (retDist (paperCentres 12879)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12879)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12879

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12879
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12879) (i : Fin 4) (a : Ix 12879) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12879) (a : Ix 12879) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12879) : Prop where
  moment : ∀ i, MomentBound (muI 12879) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12879} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12879) 8 (actualFourError c i)
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

end BstLean.Part266.Row12879

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12879
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

structure LatitudeVarianceCertificate (c : Ret 12879) : Prop where
  location : LBound (muI 12879) 12
    (fun a => conditionalVariance (stdGauss (Fin (12879 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12879) 12
    (fun a => conditionalVariance (stdGauss (Fin (12879 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12879) (hw : WINDOW (paperDesignP 12879) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12879 4 (55 / 100) /
      (12879 : ℝ) / ((12879 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12879

/-! The dimension-12879 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12879
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12879) (wl ws : ℝ) : SplitData 12879 :=
  BstLean.Part162.dPaper (paperDesignP 12879) c wl ws
    (√(2 / (12879 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12879 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12879 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12879) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12879) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12879 : ℝ)) * eR c * 12879 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12879) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12879 - 1)))
    (rowSplit c wl ws).good a ∂muI 12879 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12879) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12879 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12879) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12879 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12879) c (rowSplit c wl ws),
    hellG2 12879 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12879 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12879} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12879} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12879 t c BstLean.Part266.agent12879.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12879} (R : RootSource t c) :
    |√(QStand (paperDesignP 12879) t c) - √(qTilde (paperDesignP 12879) t c)| ≤
      BstLean.Part266.agent12879.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12879

/-! Rational enclosures for the HQ fluctuation price at dimension 12880. -/
namespace BstLean.Part266.Row12880
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (204439401 / 125000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (4585277 / 200000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12880 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12880 * A / 2 + D + L * √(A * D)) ≤ (4623689011 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12880 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((204439401 / 125000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12880 L e4 d4 ≤ (1675556329 / 40000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12880 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((204439401 / 125000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12880 L e6 d6 ≤ (24789309 / 390625000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12880 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((204439401 / 125000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12880 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12880 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12880 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12880 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (4585277 / 200000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4623689011 / 1000000000000)) ^ 2 / 2 + ((4623689011 / 1000000000000)) * ((1675556329 / 40000000000)) ^ 2 / 6 +
      ((1675556329 / 40000000000)) ^ 4 / 24 + ((1675556329 / 40000000000)) ^ 2 * ((24789309 / 390625000)) ^ 3 / 120 +
      2187 * ((24789309 / 390625000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12880 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12880 : ℝ) * ((1 + 3 * ((4585277 / 200000000))) / (4 * (1 - (4585277 / 200000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (4585277 / 200000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12880 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (4585277 / 200000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12880 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12880 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12880

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12880
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113490087 / 1000000) : ℝ) ≤ √12880 ∧ √12880 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1461751 : ℝ) ≤ Jz 12880 ∧ 1000000 ≤ Jz 12880 := by
  have hr : ((113490087 / 1000000) : ℝ) ≤ √12880 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12880 : ℝ) * √12880 ≤ (⌈(12880 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12880
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12880 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12880 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12880 : ℝ) = (⌈(12880 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1461751 : ℝ) ≤ Jz 12880 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12880 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12880) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12880 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12880 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12880 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12880 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12880 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12880 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12880) :
    (12880 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12880 * √(qB 12880))) ≤
      (33965737 / 62500000000) := by
  have hden : ((113490087 / 1000000) : ℝ) * (63 / 100) ≤ √12880 * √(qB 12880) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12880 : ℝ) * √(qB 12880) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12880) :
    (12880 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12880 * √(qB 12880))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12880 : ℝ) * √(qB 12880) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12880 : ℝ) * (√12880 *
      (c1F (exp (1 / 2) / 12) (Jz 12880) * (186 / 10000) / Jz 12880)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12880)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12880 : ℝ) * (√12880 *
      (c1F (exp (1 / 2) / 12) (Jz 12880) * (186 / 10000) / Jz 12880)) =
      (12880 * (√12880 * c1F (exp (1 / 2) / 12) (Jz 12880)) * (186 / 10000)) /
        Jz 12880 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12880)]
  nlinarith

theorem row_energy_rule :
    (12880 : ℝ) * (12880 *
      (c2F (exp (1 / 2) / 12) (Jz 12880) * (186 / 10000) ^ 2 / Jz 12880)) ≤
      (176683799 / 50000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12880)]
  nlinarith

end BstLean.Part266.Row12880

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12880
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12880) (hc : A1 c ∈ BstLean.Part153.Eop 12880) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12880 : ℝ)) ≤ (12461119657 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12880 : ℝ) + 2 * √12880 ≤ (819186261 / 62500) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12880 : ℝ) ≤ (14186261 / 125000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12880)
    (hc : A1 c ∈ BstLean.Part153.Eop 12880) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12880 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12880 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12880))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12880) (K : Set (Ix 12880)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12880 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12880 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12880) (hw : WINDOW (paperDesignP 12880) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12880)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12880) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12880 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12880 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12880 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12880 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12880) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12880)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12880)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12880

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12880
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12880) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12880 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12880) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12880) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12880 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12880 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12880 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12880}
    (hw : WINDOW (paperDesignP 12880) c) (hc : c ∈ tableEvent) (K : Set (Ix 12880)) :
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

def proposedBaseEvent : Set (Ret 12880) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12880)) : Prop where
  charge : (retDist (paperCentres 12880)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12880)} (h : TablePayment H) :
    (retDist (paperCentres 12880)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12880)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12880

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12880
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12880) (i : Fin 4) (a : Ix 12880) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12880) (a : Ix 12880) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12880) : Prop where
  moment : ∀ i, MomentBound (muI 12880) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12880} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12880) 8 (actualFourError c i)
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

end BstLean.Part266.Row12880

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12880
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

structure LatitudeVarianceCertificate (c : Ret 12880) : Prop where
  location : LBound (muI 12880) 12
    (fun a => conditionalVariance (stdGauss (Fin (12880 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12880) 12
    (fun a => conditionalVariance (stdGauss (Fin (12880 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12880) (hw : WINDOW (paperDesignP 12880) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12880 4 (55 / 100) /
      (12880 : ℝ) / ((12880 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12880

/-! The dimension-12880 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12880
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12880) (wl ws : ℝ) : SplitData 12880 :=
  BstLean.Part162.dPaper (paperDesignP 12880) c wl ws
    (√(2 / (12880 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12880 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12880 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12880) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12880) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12880 : ℝ)) * eR c * 12880 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12880) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12880 - 1)))
    (rowSplit c wl ws).good a ∂muI 12880 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12880) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12880 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12880) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12880 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12880) c (rowSplit c wl ws),
    hellG2 12880 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12880 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12880} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12880} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12880 t c BstLean.Part266.agent12880.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12880} (R : RootSource t c) :
    |√(QStand (paperDesignP 12880) t c) - √(qTilde (paperDesignP 12880) t c)| ≤
      BstLean.Part266.agent12880.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12880

/-! Rational enclosures for the HQ fluctuation price at dimension 12881. -/
namespace BstLean.Part266.Row12881
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (408862931 / 250000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (4584919 / 200000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12881 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12881 * A / 2 + D + L * √(A * D)) ≤ (1155972593 / 250000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12881 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((408862931 / 250000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12881 L e4 d4 ≤ (41890737041 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12881 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((408862931 / 250000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12881 L e6 d6 ≤ (6346339403 / 100000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12881 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((408862931 / 250000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12881 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12881 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12881 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12881 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (4584919 / 200000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((1155972593 / 250000000000)) ^ 2 / 2 + ((1155972593 / 250000000000)) * ((41890737041 / 1000000000000)) ^ 2 / 6 +
      ((41890737041 / 1000000000000)) ^ 4 / 24 + ((41890737041 / 1000000000000)) ^ 2 * ((6346339403 / 100000000000)) ^ 3 / 120 +
      2187 * ((6346339403 / 100000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12881 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12881 : ℝ) * ((1 + 3 * ((4584919 / 200000000))) / (4 * (1 - (4584919 / 200000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (4584919 / 200000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12881 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (4584919 / 200000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12881 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12881 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12881

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12881
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113494493 / 1000000) : ℝ) ≤ √12881 ∧ √12881 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1461921 : ℝ) ≤ Jz 12881 ∧ 1000000 ≤ Jz 12881 := by
  have hr : ((113494493 / 1000000) : ℝ) ≤ √12881 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12881 : ℝ) * √12881 ≤ (⌈(12881 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12881
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12881 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12881 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12881 : ℝ) = (⌈(12881 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1461921 : ℝ) ≤ Jz 12881 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12881 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12881) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12881 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12881 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12881 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12881 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12881 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12881 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12881) :
    (12881 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12881 * √(qB 12881))) ≤
      (271736443 / 500000000000) := by
  have hden : ((113494493 / 1000000) : ℝ) * (63 / 100) ≤ √12881 * √(qB 12881) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12881 : ℝ) * √(qB 12881) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12881) :
    (12881 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12881 * √(qB 12881))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12881 : ℝ) * √(qB 12881) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12881 : ℝ) * (√12881 *
      (c1F (exp (1 / 2) / 12) (Jz 12881) * (186 / 10000) / Jz 12881)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12881)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12881 : ℝ) * (√12881 *
      (c1F (exp (1 / 2) / 12) (Jz 12881) * (186 / 10000) / Jz 12881)) =
      (12881 * (√12881 * c1F (exp (1 / 2) / 12) (Jz 12881)) * (186 / 10000)) /
        Jz 12881 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12881)]
  nlinarith

theorem row_energy_rule :
    (12881 : ℝ) * (12881 *
      (c2F (exp (1 / 2) / 12) (Jz 12881) * (186 / 10000) ^ 2 / Jz 12881)) ≤
      (353381373 / 100000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12881)]
  nlinarith

end BstLean.Part266.Row12881

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12881
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12881) (hc : A1 c ∈ BstLean.Part153.Eop 12881) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12881 : ℝ)) ≤ (12460635947 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12881 : ℝ) + 2 * √12881 ≤ (3276997247 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12881 : ℝ) ≤ (56747247 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12881)
    (hc : A1 c ∈ BstLean.Part153.Eop 12881) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12881 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12881 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12881))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12881) (K : Set (Ix 12881)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12881 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12881 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12881) (hw : WINDOW (paperDesignP 12881) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12881)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12881) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12881 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12881 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12881 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12881 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12881) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12881)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12881)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12881

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12881
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12881) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12881 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12881) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12881) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12881 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12881 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12881 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12881}
    (hw : WINDOW (paperDesignP 12881) c) (hc : c ∈ tableEvent) (K : Set (Ix 12881)) :
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

def proposedBaseEvent : Set (Ret 12881) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12881)) : Prop where
  charge : (retDist (paperCentres 12881)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12881)} (h : TablePayment H) :
    (retDist (paperCentres 12881)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12881)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12881

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12881
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12881) (i : Fin 4) (a : Ix 12881) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12881) (a : Ix 12881) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12881) : Prop where
  moment : ∀ i, MomentBound (muI 12881) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12881} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12881) 8 (actualFourError c i)
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

end BstLean.Part266.Row12881

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12881
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

structure LatitudeVarianceCertificate (c : Ret 12881) : Prop where
  location : LBound (muI 12881) 12
    (fun a => conditionalVariance (stdGauss (Fin (12881 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12881) 12
    (fun a => conditionalVariance (stdGauss (Fin (12881 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12881) (hw : WINDOW (paperDesignP 12881) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12881 4 (55 / 100) /
      (12881 : ℝ) / ((12881 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12881

/-! The dimension-12881 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12881
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12881) (wl ws : ℝ) : SplitData 12881 :=
  BstLean.Part162.dPaper (paperDesignP 12881) c wl ws
    (√(2 / (12881 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12881 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12881 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12881) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12881) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12881 : ℝ)) * eR c * 12881 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12881) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12881 - 1)))
    (rowSplit c wl ws).good a ∂muI 12881 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12881) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12881 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12881) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12881 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12881) c (rowSplit c wl ws),
    hellG2 12881 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12881 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12881} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12881} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12881 t c BstLean.Part266.agent12881.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12881} (R : RootSource t c) :
    |√(QStand (paperDesignP 12881) t c) - √(qTilde (paperDesignP 12881) t c)| ≤
      BstLean.Part266.agent12881.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12881

/-! Rational enclosures for the HQ fluctuation price at dimension 12882. -/
namespace BstLean.Part266.Row12882
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (65415519 / 40000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22922801 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12882 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12882 * A / 2 + D + L * √(A * D)) ≤ (1156022931 / 250000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12882 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((65415519 / 40000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12882 L e4 d4 ≤ (41892565789 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12882 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((65415519 / 40000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12882 L e6 d6 ≤ (63466156917 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12882 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((65415519 / 40000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12882 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12882 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12882 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12882 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22922801 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((1156022931 / 250000000000)) ^ 2 / 2 + ((1156022931 / 250000000000)) * ((41892565789 / 1000000000000)) ^ 2 / 6 +
      ((41892565789 / 1000000000000)) ^ 4 / 24 + ((41892565789 / 1000000000000)) ^ 2 * ((63466156917 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63466156917 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12882 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12882 : ℝ) * ((1 + 3 * ((22922801 / 1000000000))) / (4 * (1 - (22922801 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22922801 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12882 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22922801 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12882 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12882 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12882

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12882
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((56749449 / 500000) : ℝ) ≤ √12882 ∧ √12882 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1462091 : ℝ) ≤ Jz 12882 ∧ 1000000 ≤ Jz 12882 := by
  have hr : ((56749449 / 500000) : ℝ) ≤ √12882 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12882 : ℝ) * √12882 ≤ (⌈(12882 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12882
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12882 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12882 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12882 : ℝ) = (⌈(12882 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1462091 : ℝ) ≤ Jz 12882 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12882 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12882) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12882 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12882 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12882 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12882 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12882 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12882 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12882) :
    (12882 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12882 * √(qB 12882))) ≤
      (16984187 / 31250000000) := by
  have hden : ((56749449 / 500000) : ℝ) * (63 / 100) ≤ √12882 * √(qB 12882) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12882 : ℝ) * √(qB 12882) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12882) :
    (12882 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12882 * √(qB 12882))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12882 : ℝ) * √(qB 12882) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12882 : ℝ) * (√12882 *
      (c1F (exp (1 / 2) / 12) (Jz 12882) * (186 / 10000) / Jz 12882)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12882)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12882 : ℝ) * (√12882 *
      (c1F (exp (1 / 2) / 12) (Jz 12882) * (186 / 10000) / Jz 12882)) =
      (12882 * (√12882 * c1F (exp (1 / 2) / 12) (Jz 12882)) * (186 / 10000)) /
        Jz 12882 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12882)]
  nlinarith

theorem row_energy_rule :
    (12882 : ℝ) * (12882 *
      (c2F (exp (1 / 2) / 12) (Jz 12882) * (186 / 10000) ^ 2 / Jz 12882)) ≤
      (3533951491 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12882)]
  nlinarith

end BstLean.Part266.Row12882

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12882
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12882) (hc : A1 c ∈ BstLean.Part153.Eop 12882) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12882 : ℝ)) ≤ (3115038073 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12882 : ℝ) + 2 * √12882 ≤ (6554498899 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12882 : ℝ) ≤ (113498899 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12882)
    (hc : A1 c ∈ BstLean.Part153.Eop 12882) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12882 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12882 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12882))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12882) (K : Set (Ix 12882)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12882 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12882 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12882) (hw : WINDOW (paperDesignP 12882) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12882)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12882) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12882 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12882 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12882 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12882 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12882) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12882)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12882)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12882

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12882
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12882) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12882 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12882) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12882) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12882 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12882 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12882 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12882}
    (hw : WINDOW (paperDesignP 12882) c) (hc : c ∈ tableEvent) (K : Set (Ix 12882)) :
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

def proposedBaseEvent : Set (Ret 12882) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12882)) : Prop where
  charge : (retDist (paperCentres 12882)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12882)} (h : TablePayment H) :
    (retDist (paperCentres 12882)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12882)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12882

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12882
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12882) (i : Fin 4) (a : Ix 12882) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12882) (a : Ix 12882) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12882) : Prop where
  moment : ∀ i, MomentBound (muI 12882) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12882} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12882) 8 (actualFourError c i)
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

end BstLean.Part266.Row12882

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12882
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

structure LatitudeVarianceCertificate (c : Ret 12882) : Prop where
  location : LBound (muI 12882) 12
    (fun a => conditionalVariance (stdGauss (Fin (12882 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12882) 12
    (fun a => conditionalVariance (stdGauss (Fin (12882 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12882) (hw : WINDOW (paperDesignP 12882) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12882 4 (55 / 100) /
      (12882 : ℝ) / ((12882 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12882

/-! The dimension-12882 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12882
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12882) (wl ws : ℝ) : SplitData 12882 :=
  BstLean.Part162.dPaper (paperDesignP 12882) c wl ws
    (√(2 / (12882 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12882 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12882 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12882) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12882) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12882 : ℝ)) * eR c * 12882 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12882) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12882 - 1)))
    (rowSplit c wl ws).good a ∂muI 12882 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12882) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12882 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12882) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12882 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12882) c (rowSplit c wl ws),
    hellG2 12882 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12882 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12882} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12882} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12882 t c BstLean.Part266.agent12882.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12882} (R : RootSource t c) :
    |√(QStand (paperDesignP 12882) t c) - √(qTilde (paperDesignP 12882) t c)| ≤
      BstLean.Part266.agent12882.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12882

/-! Rational enclosures for the HQ fluctuation price at dimension 12883. -/
namespace BstLean.Part266.Row12883
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1635324521 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (5730253 / 250000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12883 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12883 * A / 2 + D + L * √(A * D)) ≤ (924858617 / 200000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12883 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1635324521 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12883 L e4 d4 ≤ (10473598653 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12883 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1635324521 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12883 L e6 d6 ≤ (31734459959 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12883 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1635324521 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12883 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12883 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12883 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12883 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (5730253 / 250000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((924858617 / 200000000000)) ^ 2 / 2 + ((924858617 / 200000000000)) * ((10473598653 / 250000000000)) ^ 2 / 6 +
      ((10473598653 / 250000000000)) ^ 4 / 24 + ((10473598653 / 250000000000)) ^ 2 * ((31734459959 / 500000000000)) ^ 3 / 120 +
      2187 * ((31734459959 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12883 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12883 : ℝ) * ((1 + 3 * ((5730253 / 250000000))) / (4 * (1 - (5730253 / 250000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (5730253 / 250000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12883 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (5730253 / 250000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12883 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12883 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12883

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12883
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113503303 / 1000000) : ℝ) ≤ √12883 ∧ √12883 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1462262 : ℝ) ≤ Jz 12883 ∧ 1000000 ≤ Jz 12883 := by
  have hr : ((113503303 / 1000000) : ℝ) ≤ √12883 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12883 : ℝ) * √12883 ≤ (⌈(12883 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12883
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12883 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12883 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12883 : ℝ) = (⌈(12883 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1462262 : ℝ) ≤ Jz 12883 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12883 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12883) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12883 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12883 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12883 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12883 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12883 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12883 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12883) :
    (12883 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12883 * √(qB 12883))) ≤
      (13587877 / 25000000000) := by
  have hden : ((113503303 / 1000000) : ℝ) * (63 / 100) ≤ √12883 * √(qB 12883) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12883 : ℝ) * √(qB 12883) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12883) :
    (12883 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12883 * √(qB 12883))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12883 : ℝ) * √(qB 12883) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12883 : ℝ) * (√12883 *
      (c1F (exp (1 / 2) / 12) (Jz 12883) * (186 / 10000) / Jz 12883)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12883)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12883 : ℝ) * (√12883 *
      (c1F (exp (1 / 2) / 12) (Jz 12883) * (186 / 10000) / Jz 12883)) =
      (12883 * (√12883 * c1F (exp (1 / 2) / 12) (Jz 12883)) * (186 / 10000)) /
        Jz 12883 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12883)]
  nlinarith

theorem row_energy_rule :
    (12883 : ℝ) * (12883 *
      (c2F (exp (1 / 2) / 12) (Jz 12883) * (186 / 10000) ^ 2 / Jz 12883)) ≤
      (706817369 / 200000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12883)]
  nlinarith

end BstLean.Part266.Row12883

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12883
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12883) (hc : A1 c ∈ BstLean.Part153.Eop 12883) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12883 : ℝ)) ≤ (6229834347 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12883 : ℝ) + 2 * √12883 ≤ (819375413 / 62500) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12883 : ℝ) ≤ (14187913 / 125000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12883)
    (hc : A1 c ∈ BstLean.Part153.Eop 12883) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12883 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12883 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12883))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12883) (K : Set (Ix 12883)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12883 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12883 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12883) (hw : WINDOW (paperDesignP 12883) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12883)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12883) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12883 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12883 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12883 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12883 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12883) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12883)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12883)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12883

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12883
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12883) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12883 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12883) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12883) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12883 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12883 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12883 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12883}
    (hw : WINDOW (paperDesignP 12883) c) (hc : c ∈ tableEvent) (K : Set (Ix 12883)) :
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

def proposedBaseEvent : Set (Ret 12883) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12883)) : Prop where
  charge : (retDist (paperCentres 12883)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12883)} (h : TablePayment H) :
    (retDist (paperCentres 12883)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12883)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12883

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12883
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12883) (i : Fin 4) (a : Ix 12883) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12883) (a : Ix 12883) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12883) : Prop where
  moment : ∀ i, MomentBound (muI 12883) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12883} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12883) 8 (actualFourError c i)
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

end BstLean.Part266.Row12883

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12883
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

structure LatitudeVarianceCertificate (c : Ret 12883) : Prop where
  location : LBound (muI 12883) 12
    (fun a => conditionalVariance (stdGauss (Fin (12883 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12883) 12
    (fun a => conditionalVariance (stdGauss (Fin (12883 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12883) (hw : WINDOW (paperDesignP 12883) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12883 4 (55 / 100) /
      (12883 : ℝ) / ((12883 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12883

/-! The dimension-12883 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12883
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12883) (wl ws : ℝ) : SplitData 12883 :=
  BstLean.Part162.dPaper (paperDesignP 12883) c wl ws
    (√(2 / (12883 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12883 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12883 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12883) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12883) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12883 : ℝ)) * eR c * 12883 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12883) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12883 - 1)))
    (rowSplit c wl ws).good a ∂muI 12883 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12883) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12883 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12883) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12883 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12883) c (rowSplit c wl ws),
    hellG2 12883 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12883 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12883} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12883} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12883 t c BstLean.Part266.agent12883.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12883} (R : RootSource t c) :
    |√(QStand (paperDesignP 12883) t c) - √(qTilde (paperDesignP 12883) t c)| ≤
      BstLean.Part266.agent12883.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12883

/-! Rational enclosures for the HQ fluctuation price at dimension 12884. -/
namespace BstLean.Part266.Row12884
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (817630401 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (1145961 / 50000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12884 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12884 * A / 2 + D + L * √(A * D)) ≤ (2312247219 / 500000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12884 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((817630401 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12884 L e4 d4 ≤ (5237027921 / 125000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12884 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((817630401 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12884 L e6 d6 ≤ (247936261 / 3906250000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12884 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((817630401 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12884 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12884 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12884 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12884 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (1145961 / 50000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((2312247219 / 500000000000)) ^ 2 / 2 + ((2312247219 / 500000000000)) * ((5237027921 / 125000000000)) ^ 2 / 6 +
      ((5237027921 / 125000000000)) ^ 4 / 24 + ((5237027921 / 125000000000)) ^ 2 * ((247936261 / 3906250000)) ^ 3 / 120 +
      2187 * ((247936261 / 3906250000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12884 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12884 : ℝ) * ((1 + 3 * ((1145961 / 50000000))) / (4 * (1 - (1145961 / 50000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (1145961 / 50000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12884 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (1145961 / 50000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12884 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12884 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12884

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12884
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((28376927 / 250000) : ℝ) ≤ √12884 ∧ √12884 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1462432 : ℝ) ≤ Jz 12884 ∧ 1000000 ≤ Jz 12884 := by
  have hr : ((28376927 / 250000) : ℝ) ≤ √12884 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12884 : ℝ) * √12884 ≤ (⌈(12884 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12884
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12884 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12884 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12884 : ℝ) = (⌈(12884 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1462432 : ℝ) ≤ Jz 12884 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12884 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12884) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12884 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12884 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12884 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12884 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12884 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12884 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12884) :
    (12884 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12884 * √(qB 12884))) ≤
      (271768087 / 500000000000) := by
  have hden : ((28376927 / 250000) : ℝ) * (63 / 100) ≤ √12884 * √(qB 12884) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12884 : ℝ) * √(qB 12884) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12884) :
    (12884 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12884 * √(qB 12884))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12884 : ℝ) * √(qB 12884) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12884 : ℝ) * (√12884 *
      (c1F (exp (1 / 2) / 12) (Jz 12884) * (186 / 10000) / Jz 12884)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12884)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12884 : ℝ) * (√12884 *
      (c1F (exp (1 / 2) / 12) (Jz 12884) * (186 / 10000) / Jz 12884)) =
      (12884 * (√12884 * c1F (exp (1 / 2) / 12) (Jz 12884)) * (186 / 10000)) /
        Jz 12884 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12884)]
  nlinarith

theorem row_energy_rule :
    (12884 : ℝ) * (12884 *
      (c2F (exp (1 / 2) / 12) (Jz 12884) * (186 / 10000) ^ 2 / Jz 12884)) ≤
      (3534224627 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12884)]
  nlinarith

end BstLean.Part266.Row12884

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12884
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12884) (hc : A1 c ∈ BstLean.Part153.Eop 12884) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12884 : ℝ)) ≤ (12167173 / 976562500) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12884 : ℝ) + 2 * √12884 ≤ (6555507709 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12884 : ℝ) ≤ (113507709 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12884)
    (hc : A1 c ∈ BstLean.Part153.Eop 12884) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12884 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12884 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12884))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12884) (K : Set (Ix 12884)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12884 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12884 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12884) (hw : WINDOW (paperDesignP 12884) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12884)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12884) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12884 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12884 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12884 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12884 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12884) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12884)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12884)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12884

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12884
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12884) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12884 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12884) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12884) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12884 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12884 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12884 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12884}
    (hw : WINDOW (paperDesignP 12884) c) (hc : c ∈ tableEvent) (K : Set (Ix 12884)) :
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

def proposedBaseEvent : Set (Ret 12884) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12884)) : Prop where
  charge : (retDist (paperCentres 12884)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12884)} (h : TablePayment H) :
    (retDist (paperCentres 12884)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12884)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12884

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12884
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12884) (i : Fin 4) (a : Ix 12884) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12884) (a : Ix 12884) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12884) : Prop where
  moment : ∀ i, MomentBound (muI 12884) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12884} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12884) 8 (actualFourError c i)
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

end BstLean.Part266.Row12884

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12884
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

structure LatitudeVarianceCertificate (c : Ret 12884) : Prop where
  location : LBound (muI 12884) 12
    (fun a => conditionalVariance (stdGauss (Fin (12884 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12884) 12
    (fun a => conditionalVariance (stdGauss (Fin (12884 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12884) (hw : WINDOW (paperDesignP 12884) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12884 4 (55 / 100) /
      (12884 : ℝ) / ((12884 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12884

/-! The dimension-12884 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12884
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12884) (wl ws : ℝ) : SplitData 12884 :=
  BstLean.Part162.dPaper (paperDesignP 12884) c wl ws
    (√(2 / (12884 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12884 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12884 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12884) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12884) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12884 : ℝ)) * eR c * 12884 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12884) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12884 - 1)))
    (rowSplit c wl ws).good a ∂muI 12884 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12884) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12884 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12884) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12884 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12884) c (rowSplit c wl ws),
    hellG2 12884 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12884 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12884} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12884} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12884 t c BstLean.Part266.agent12884.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12884} (R : RootSource t c) :
    |√(QStand (paperDesignP 12884) t c) - √(qTilde (paperDesignP 12884) t c)| ≤
      BstLean.Part266.agent12884.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12884

/-! Rational enclosures for the HQ fluctuation price at dimension 12885. -/
namespace BstLean.Part266.Row12885
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1635197377 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22917431 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12885 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12885 * A / 2 + D + L * √(A * D)) ≤ (23123479 / 5000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12885 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1635197377 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12885 L e4 d4 ≤ (41898052199 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12885 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1635197377 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12885 L e6 d6 ≤ (15868611457 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12885 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1635197377 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12885 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12885 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12885 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12885 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22917431 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((23123479 / 5000000000)) ^ 2 / 2 + ((23123479 / 5000000000)) * ((41898052199 / 1000000000000)) ^ 2 / 6 +
      ((41898052199 / 1000000000000)) ^ 4 / 24 + ((41898052199 / 1000000000000)) ^ 2 * ((15868611457 / 250000000000)) ^ 3 / 120 +
      2187 * ((15868611457 / 250000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12885 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12885 : ℝ) * ((1 + 3 * ((22917431 / 1000000000))) / (4 * (1 - (22917431 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22917431 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12885 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22917431 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12885 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12885 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12885

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12885
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113512113 / 1000000) : ℝ) ≤ √12885 ∧ √12885 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1462602 : ℝ) ≤ Jz 12885 ∧ 1000000 ≤ Jz 12885 := by
  have hr : ((113512113 / 1000000) : ℝ) ≤ √12885 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12885 : ℝ) * √12885 ≤ (⌈(12885 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12885
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12885 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12885 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12885 : ℝ) = (⌈(12885 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1462602 : ℝ) ≤ Jz 12885 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12885 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12885) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12885 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12885 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12885 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12885 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12885 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12885 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12885) :
    (12885 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12885 * √(qB 12885))) ≤
      (543557267 / 1000000000000) := by
  have hden : ((113512113 / 1000000) : ℝ) * (63 / 100) ≤ √12885 * √(qB 12885) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12885 : ℝ) * √(qB 12885) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12885) :
    (12885 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12885 * √(qB 12885))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12885 : ℝ) * √(qB 12885) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12885 : ℝ) * (√12885 *
      (c1F (exp (1 / 2) / 12) (Jz 12885) * (186 / 10000) / Jz 12885)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12885)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12885 : ℝ) * (√12885 *
      (c1F (exp (1 / 2) / 12) (Jz 12885) * (186 / 10000) / Jz 12885)) =
      (12885 * (√12885 * c1F (exp (1 / 2) / 12) (Jz 12885)) * (186 / 10000)) /
        Jz 12885 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12885)]
  nlinarith

theorem row_energy_rule :
    (12885 : ℝ) * (12885 *
      (c2F (exp (1 / 2) / 12) (Jz 12885) * (186 / 10000) ^ 2 / Jz 12885)) ≤
      (176718121 / 50000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12885)]
  nlinarith

end BstLean.Part266.Row12885

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12885
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12885) (hc : A1 c ∈ BstLean.Part153.Eop 12885) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12885 : ℝ)) ≤ (6229350833 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12885 : ℝ) + 2 * √12885 ≤ (3278006057 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12885 : ℝ) ≤ (56756057 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12885)
    (hc : A1 c ∈ BstLean.Part153.Eop 12885) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12885 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12885 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12885))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12885) (K : Set (Ix 12885)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12885 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12885 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12885) (hw : WINDOW (paperDesignP 12885) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12885)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12885) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12885 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12885 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12885 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12885 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12885) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12885)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12885)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12885

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12885
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12885) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12885 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12885) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12885) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12885 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12885 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12885 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12885}
    (hw : WINDOW (paperDesignP 12885) c) (hc : c ∈ tableEvent) (K : Set (Ix 12885)) :
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

def proposedBaseEvent : Set (Ret 12885) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12885)) : Prop where
  charge : (retDist (paperCentres 12885)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12885)} (h : TablePayment H) :
    (retDist (paperCentres 12885)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12885)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12885

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12885
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12885) (i : Fin 4) (a : Ix 12885) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12885) (a : Ix 12885) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12885) : Prop where
  moment : ∀ i, MomentBound (muI 12885) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12885} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12885) 8 (actualFourError c i)
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

end BstLean.Part266.Row12885

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12885
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

structure LatitudeVarianceCertificate (c : Ret 12885) : Prop where
  location : LBound (muI 12885) 12
    (fun a => conditionalVariance (stdGauss (Fin (12885 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12885) 12
    (fun a => conditionalVariance (stdGauss (Fin (12885 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12885) (hw : WINDOW (paperDesignP 12885) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12885 4 (55 / 100) /
      (12885 : ℝ) / ((12885 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12885

/-! The dimension-12885 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12885
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12885) (wl ws : ℝ) : SplitData 12885 :=
  BstLean.Part162.dPaper (paperDesignP 12885) c wl ws
    (√(2 / (12885 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12885 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12885 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12885) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12885) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12885 : ℝ)) * eR c * 12885 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12885) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12885 - 1)))
    (rowSplit c wl ws).good a ∂muI 12885 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12885) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12885 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12885) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12885 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12885) c (rowSplit c wl ws),
    hellG2 12885 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12885 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12885} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12885} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12885 t c BstLean.Part266.agent12885.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12885} (R : RootSource t c) :
    |√(QStand (paperDesignP 12885) t c) - √(qTilde (paperDesignP 12885) t c)| ≤
      BstLean.Part266.agent12885.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12885

/-! Rational enclosures for the HQ fluctuation price at dimension 12886. -/
namespace BstLean.Part266.Row12886
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1635133687 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22915639 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12886 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12886 * A / 2 + D + L * √(A * D)) ≤ (2312448577 / 500000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12886 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1635133687 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12886 L e4 d4 ≤ (20949940481 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12886 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1635133687 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12886 L e6 d6 ≤ (31738604369 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12886 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1635133687 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12886 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12886 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12886 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12886 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22915639 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((2312448577 / 500000000000)) ^ 2 / 2 + ((2312448577 / 500000000000)) * ((20949940481 / 500000000000)) ^ 2 / 6 +
      ((20949940481 / 500000000000)) ^ 4 / 24 + ((20949940481 / 500000000000)) ^ 2 * ((31738604369 / 500000000000)) ^ 3 / 120 +
      2187 * ((31738604369 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12886 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12886 : ℝ) * ((1 + 3 * ((22915639 / 1000000000))) / (4 * (1 - (22915639 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22915639 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12886 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22915639 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12886 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12886 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12886

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12886
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((56758259 / 500000) : ℝ) ≤ √12886 ∧ √12886 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1462772 : ℝ) ≤ Jz 12886 ∧ 1000000 ≤ Jz 12886 := by
  have hr : ((56758259 / 500000) : ℝ) ≤ √12886 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12886 : ℝ) * √12886 ≤ (⌈(12886 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12886
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12886 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12886 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12886 : ℝ) = (⌈(12886 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1462772 : ℝ) ≤ Jz 12886 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12886 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12886) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12886 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12886 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12886 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12886 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12886 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12886 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12886) :
    (12886 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12886 * √(qB 12886))) ≤
      (271789179 / 500000000000) := by
  have hden : ((56758259 / 500000) : ℝ) * (63 / 100) ≤ √12886 * √(qB 12886) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12886 : ℝ) * √(qB 12886) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12886) :
    (12886 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12886 * √(qB 12886))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12886 : ℝ) * √(qB 12886) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12886 : ℝ) * (√12886 *
      (c1F (exp (1 / 2) / 12) (Jz 12886) * (186 / 10000) / Jz 12886)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12886)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12886 : ℝ) * (√12886 *
      (c1F (exp (1 / 2) / 12) (Jz 12886) * (186 / 10000) / Jz 12886)) =
      (12886 * (√12886 * c1F (exp (1 / 2) / 12) (Jz 12886)) * (186 / 10000)) /
        Jz 12886 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12886)]
  nlinarith

theorem row_energy_rule :
    (12886 : ℝ) * (12886 *
      (c2F (exp (1 / 2) / 12) (Jz 12886) * (186 / 10000) ^ 2 / Jz 12886)) ≤
      (3534500223 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12886)]
  nlinarith

end BstLean.Part266.Row12886

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12886
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12886) (hc : A1 c ∈ BstLean.Part153.Eop 12886) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12886 : ℝ)) ≤ (3114554559 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12886 : ℝ) + 2 * √12886 ≤ (6556516519 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12886 : ℝ) ≤ (113516519 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12886)
    (hc : A1 c ∈ BstLean.Part153.Eop 12886) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12886 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12886 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12886))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12886) (K : Set (Ix 12886)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12886 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12886 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12886) (hw : WINDOW (paperDesignP 12886) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12886)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12886) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12886 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12886 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12886 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12886 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12886) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12886)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12886)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12886

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12886
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12886) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12886 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12886) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12886) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12886 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12886 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12886 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12886}
    (hw : WINDOW (paperDesignP 12886) c) (hc : c ∈ tableEvent) (K : Set (Ix 12886)) :
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

def proposedBaseEvent : Set (Ret 12886) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12886)) : Prop where
  charge : (retDist (paperCentres 12886)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12886)} (h : TablePayment H) :
    (retDist (paperCentres 12886)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12886)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12886

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12886
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12886) (i : Fin 4) (a : Ix 12886) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12886) (a : Ix 12886) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12886) : Prop where
  moment : ∀ i, MomentBound (muI 12886) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12886} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12886) 8 (actualFourError c i)
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

end BstLean.Part266.Row12886

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12886
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

structure LatitudeVarianceCertificate (c : Ret 12886) : Prop where
  location : LBound (muI 12886) 12
    (fun a => conditionalVariance (stdGauss (Fin (12886 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12886) 12
    (fun a => conditionalVariance (stdGauss (Fin (12886 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12886) (hw : WINDOW (paperDesignP 12886) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12886 4 (55 / 100) /
      (12886 : ℝ) / ((12886 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12886

/-! The dimension-12886 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12886
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12886) (wl ws : ℝ) : SplitData 12886 :=
  BstLean.Part162.dPaper (paperDesignP 12886) c wl ws
    (√(2 / (12886 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12886 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12886 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12886) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12886) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12886 : ℝ)) * eR c * 12886 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12886) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12886 - 1)))
    (rowSplit c wl ws).good a ∂muI 12886 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12886) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12886 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12886) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12886 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12886) c (rowSplit c wl ws),
    hellG2 12886 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12886 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12886} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12886} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12886 t c BstLean.Part266.agent12886.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12886} (R : RootSource t c) :
    |√(QStand (paperDesignP 12886) t c) - √(qTilde (paperDesignP 12886) t c)| ≤
      BstLean.Part266.agent12886.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12886

/-! Rational enclosures for the HQ fluctuation price at dimension 12887. -/
namespace BstLean.Part266.Row12887
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (408767503 / 250000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (2864231 / 125000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12887 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12887 * A / 2 + D + L * √(A * D)) ≤ (4625098509 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12887 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((408767503 / 250000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12887 L e4 d4 ≤ (41901709729 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12887 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((408767503 / 250000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12887 L e6 d6 ≤ (63479971653 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12887 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((408767503 / 250000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12887 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12887 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12887 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12887 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (2864231 / 125000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4625098509 / 1000000000000)) ^ 2 / 2 + ((4625098509 / 1000000000000)) * ((41901709729 / 1000000000000)) ^ 2 / 6 +
      ((41901709729 / 1000000000000)) ^ 4 / 24 + ((41901709729 / 1000000000000)) ^ 2 * ((63479971653 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63479971653 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12887 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12887 : ℝ) * ((1 + 3 * ((2864231 / 125000000))) / (4 * (1 - (2864231 / 125000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (2864231 / 125000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12887 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (2864231 / 125000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12887 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12887 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12887

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12887
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113520923 / 1000000) : ℝ) ≤ √12887 ∧ √12887 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1462943 : ℝ) ≤ Jz 12887 ∧ 1000000 ≤ Jz 12887 := by
  have hr : ((113520923 / 1000000) : ℝ) ≤ √12887 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12887 : ℝ) * √12887 ≤ (⌈(12887 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12887
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12887 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12887 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12887 : ℝ) = (⌈(12887 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1462943 : ℝ) ≤ Jz 12887 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12887 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12887) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12887 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12887 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12887 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12887 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12887 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12887 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12887) :
    (12887 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12887 * √(qB 12887))) ≤
      (543599447 / 1000000000000) := by
  have hden : ((113520923 / 1000000) : ℝ) * (63 / 100) ≤ √12887 * √(qB 12887) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12887 : ℝ) * √(qB 12887) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12887) :
    (12887 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12887 * √(qB 12887))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12887 : ℝ) * √(qB 12887) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12887 : ℝ) * (√12887 *
      (c1F (exp (1 / 2) / 12) (Jz 12887) * (186 / 10000) / Jz 12887)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12887)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12887 : ℝ) * (√12887 *
      (c1F (exp (1 / 2) / 12) (Jz 12887) * (186 / 10000) / Jz 12887)) =
      (12887 * (√12887 * c1F (exp (1 / 2) / 12) (Jz 12887)) * (186 / 10000)) /
        Jz 12887 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12887)]
  nlinarith

theorem row_energy_rule :
    (12887 : ℝ) * (12887 *
      (c2F (exp (1 / 2) / 12) (Jz 12887) * (186 / 10000) ^ 2 / Jz 12887)) ≤
      (176731781 / 50000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12887)]
  nlinarith

end BstLean.Part266.Row12887

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12887
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12887) (hc : A1 c ∈ BstLean.Part153.Eop 12887) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12887 : ℝ)) ≤ (12457734863 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12887 : ℝ) + 2 * √12887 ≤ (1639255231 / 125000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12887 : ℝ) ≤ (28380231 / 250000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12887)
    (hc : A1 c ∈ BstLean.Part153.Eop 12887) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12887 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12887 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12887))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12887) (K : Set (Ix 12887)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12887 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12887 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12887) (hw : WINDOW (paperDesignP 12887) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12887)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12887) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12887 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12887 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12887 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12887 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12887) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12887)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12887)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12887

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12887
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12887) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12887 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12887) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12887) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12887 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12887 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12887 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12887}
    (hw : WINDOW (paperDesignP 12887) c) (hc : c ∈ tableEvent) (K : Set (Ix 12887)) :
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

def proposedBaseEvent : Set (Ret 12887) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12887)) : Prop where
  charge : (retDist (paperCentres 12887)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12887)} (h : TablePayment H) :
    (retDist (paperCentres 12887)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12887)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12887

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12887
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12887) (i : Fin 4) (a : Ix 12887) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12887) (a : Ix 12887) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12887) : Prop where
  moment : ∀ i, MomentBound (muI 12887) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12887} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12887) 8 (actualFourError c i)
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

end BstLean.Part266.Row12887

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12887
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

structure LatitudeVarianceCertificate (c : Ret 12887) : Prop where
  location : LBound (muI 12887) 12
    (fun a => conditionalVariance (stdGauss (Fin (12887 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12887) 12
    (fun a => conditionalVariance (stdGauss (Fin (12887 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12887) (hw : WINDOW (paperDesignP 12887) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12887 4 (55 / 100) /
      (12887 : ℝ) / ((12887 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12887

/-! The dimension-12887 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12887
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12887) (wl ws : ℝ) : SplitData 12887 :=
  BstLean.Part162.dPaper (paperDesignP 12887) c wl ws
    (√(2 / (12887 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12887 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12887 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12887) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12887) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12887 : ℝ)) * eR c * 12887 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12887) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12887 - 1)))
    (rowSplit c wl ws).good a ∂muI 12887 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12887) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12887 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12887) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12887 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12887) c (rowSplit c wl ws),
    hellG2 12887 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12887 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12887} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12887} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12887 t c BstLean.Part266.agent12887.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12887} (R : RootSource t c) :
    |√(QStand (paperDesignP 12887) t c) - √(qTilde (paperDesignP 12887) t c)| ≤
      BstLean.Part266.agent12887.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12887

/-! Rational enclosures for the HQ fluctuation price at dimension 12888. -/
namespace BstLean.Part266.Row12888
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (204375829 / 125000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22912061 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12888 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12888 * A / 2 + D + L * √(A * D)) ≤ (144540621 / 31250000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12888 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((204375829 / 125000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12888 L e4 d4 ≤ (41903538571 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12888 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((204375829 / 125000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12888 L e6 d6 ≤ (63482734683 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12888 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((204375829 / 125000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12888 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12888 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12888 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12888 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22912061 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((144540621 / 31250000000)) ^ 2 / 2 + ((144540621 / 31250000000)) * ((41903538571 / 1000000000000)) ^ 2 / 6 +
      ((41903538571 / 1000000000000)) ^ 4 / 24 + ((41903538571 / 1000000000000)) ^ 2 * ((63482734683 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63482734683 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12888 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12888 : ℝ) * ((1 + 3 * ((22912061 / 1000000000))) / (4 * (1 - (22912061 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22912061 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12888 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22912061 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12888 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12888 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12888

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12888
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113525327 / 1000000) : ℝ) ≤ √12888 ∧ √12888 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1463113 : ℝ) ≤ Jz 12888 ∧ 1000000 ≤ Jz 12888 := by
  have hr : ((113525327 / 1000000) : ℝ) ≤ √12888 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12888 : ℝ) * √12888 ≤ (⌈(12888 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12888
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12888 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12888 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12888 : ℝ) = (⌈(12888 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1463113 : ℝ) ≤ Jz 12888 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12888 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12888) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12888 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12888 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12888 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12888 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12888 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12888 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12888) :
    (12888 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12888 * √(qB 12888))) ≤
      (543620539 / 1000000000000) := by
  have hden : ((113525327 / 1000000) : ℝ) * (63 / 100) ≤ √12888 * √(qB 12888) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12888 : ℝ) * √(qB 12888) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12888) :
    (12888 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12888 * √(qB 12888))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12888 : ℝ) * √(qB 12888) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12888 : ℝ) * (√12888 *
      (c1F (exp (1 / 2) / 12) (Jz 12888) * (186 / 10000) / Jz 12888)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12888)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12888 : ℝ) * (√12888 *
      (c1F (exp (1 / 2) / 12) (Jz 12888) * (186 / 10000) / Jz 12888)) =
      (12888 * (√12888 * c1F (exp (1 / 2) / 12) (Jz 12888)) * (186 / 10000)) /
        Jz 12888 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12888)]
  nlinarith

theorem row_energy_rule :
    (12888 : ℝ) * (12888 *
      (c2F (exp (1 / 2) / 12) (Jz 12888) * (186 / 10000) ^ 2 / Jz 12888)) ≤
      (706954689 / 200000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12888)]
  nlinarith

end BstLean.Part266.Row12888

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12888
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12888) (hc : A1 c ∈ BstLean.Part153.Eop 12888) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12888 : ℝ)) ≤ (6228625773 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12888 : ℝ) + 2 * √12888 ≤ (409845333 / 31250) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12888 : ℝ) ≤ (7095333 / 62500))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12888)
    (hc : A1 c ∈ BstLean.Part153.Eop 12888) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12888 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12888 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12888))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12888) (K : Set (Ix 12888)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12888 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12888 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12888) (hw : WINDOW (paperDesignP 12888) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12888)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12888) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12888 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12888 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12888 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12888 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12888) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12888)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12888)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12888

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12888
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12888) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12888 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12888) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12888) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12888 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12888 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12888 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12888}
    (hw : WINDOW (paperDesignP 12888) c) (hc : c ∈ tableEvent) (K : Set (Ix 12888)) :
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

def proposedBaseEvent : Set (Ret 12888) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12888)) : Prop where
  charge : (retDist (paperCentres 12888)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12888)} (h : TablePayment H) :
    (retDist (paperCentres 12888)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12888)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12888

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12888
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12888) (i : Fin 4) (a : Ix 12888) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12888) (a : Ix 12888) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12888) : Prop where
  moment : ∀ i, MomentBound (muI 12888) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12888} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12888) 8 (actualFourError c i)
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

end BstLean.Part266.Row12888

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12888
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

structure LatitudeVarianceCertificate (c : Ret 12888) : Prop where
  location : LBound (muI 12888) 12
    (fun a => conditionalVariance (stdGauss (Fin (12888 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12888) 12
    (fun a => conditionalVariance (stdGauss (Fin (12888 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12888) (hw : WINDOW (paperDesignP 12888) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12888 4 (55 / 100) /
      (12888 : ℝ) / ((12888 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12888

/-! The dimension-12888 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12888
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12888) (wl ws : ℝ) : SplitData 12888 :=
  BstLean.Part162.dPaper (paperDesignP 12888) c wl ws
    (√(2 / (12888 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12888 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12888 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12888) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12888) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12888 : ℝ)) * eR c * 12888 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12888) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12888 - 1)))
    (rowSplit c wl ws).good a ∂muI 12888 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12888) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12888 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12888) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12888 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12888) c (rowSplit c wl ws),
    hellG2 12888 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12888 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12888} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12888} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12888 t c BstLean.Part266.agent12888.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12888} (R : RootSource t c) :
    |√(QStand (paperDesignP 12888) t c) - √(qTilde (paperDesignP 12888) t c)| ≤
      BstLean.Part266.agent12888.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12888

/-! Rational enclosures for the HQ fluctuation price at dimension 12889. -/
namespace BstLean.Part266.Row12889
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1634942987 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (2291027 / 100000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12889 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12889 * A / 2 + D + L * √(A * D)) ≤ (4625501227 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12889 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1634942987 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12889 L e4 d4 ≤ (20952683673 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12889 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1634942987 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12889 L e6 d6 ≤ (6348549761 / 100000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12889 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1634942987 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12889 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12889 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12889 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12889 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (2291027 / 100000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4625501227 / 1000000000000)) ^ 2 / 2 + ((4625501227 / 1000000000000)) * ((20952683673 / 500000000000)) ^ 2 / 6 +
      ((20952683673 / 500000000000)) ^ 4 / 24 + ((20952683673 / 500000000000)) ^ 2 * ((6348549761 / 100000000000)) ^ 3 / 120 +
      2187 * ((6348549761 / 100000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12889 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12889 : ℝ) * ((1 + 3 * ((2291027 / 100000000))) / (4 * (1 - (2291027 / 100000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (2291027 / 100000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12889 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (2291027 / 100000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12889 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12889 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12889

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12889
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113529731 / 1000000) : ℝ) ≤ √12889 ∧ √12889 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1463283 : ℝ) ≤ Jz 12889 ∧ 1000000 ≤ Jz 12889 := by
  have hr : ((113529731 / 1000000) : ℝ) ≤ √12889 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12889 : ℝ) * √12889 ≤ (⌈(12889 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12889
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12889 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12889 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12889 : ℝ) = (⌈(12889 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1463283 : ℝ) ≤ Jz 12889 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12889 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12889) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12889 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12889 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12889 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12889 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12889 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12889 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12889) :
    (12889 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12889 * √(qB 12889))) ≤
      (54364163 / 100000000000) := by
  have hden : ((113529731 / 1000000) : ℝ) * (63 / 100) ≤ √12889 * √(qB 12889) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12889 : ℝ) * √(qB 12889) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12889) :
    (12889 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12889 * √(qB 12889))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12889 : ℝ) * √(qB 12889) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12889 : ℝ) * (√12889 *
      (c1F (exp (1 / 2) / 12) (Jz 12889) * (186 / 10000) / Jz 12889)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12889)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12889 : ℝ) * (√12889 *
      (c1F (exp (1 / 2) / 12) (Jz 12889) * (186 / 10000) / Jz 12889)) =
      (12889 * (√12889 * c1F (exp (1 / 2) / 12) (Jz 12889)) * (186 / 10000)) /
        Jz 12889 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12889)]
  nlinarith

theorem row_energy_rule :
    (12889 : ℝ) * (12889 *
      (c2F (exp (1 / 2) / 12) (Jz 12889) * (186 / 10000) ^ 2 / Jz 12889)) ≤
      (44186391 / 12500000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12889)]
  nlinarith

end BstLean.Part266.Row12889

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12889
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12889) (hc : A1 c ∈ BstLean.Part153.Eop 12889) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12889 : ℝ)) ≤ (6228384143 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12889 : ℝ) + 2 * √12889 ≤ (1639507433 / 125000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12889 : ℝ) ≤ (28382433 / 250000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12889)
    (hc : A1 c ∈ BstLean.Part153.Eop 12889) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12889 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12889 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12889))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12889) (K : Set (Ix 12889)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12889 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12889 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12889) (hw : WINDOW (paperDesignP 12889) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12889)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12889) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12889 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12889 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12889 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12889 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12889) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12889)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12889)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12889

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12889
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12889) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12889 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12889) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12889) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12889 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12889 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12889 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12889}
    (hw : WINDOW (paperDesignP 12889) c) (hc : c ∈ tableEvent) (K : Set (Ix 12889)) :
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

def proposedBaseEvent : Set (Ret 12889) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12889)) : Prop where
  charge : (retDist (paperCentres 12889)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12889)} (h : TablePayment H) :
    (retDist (paperCentres 12889)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12889)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12889

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12889
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12889) (i : Fin 4) (a : Ix 12889) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12889) (a : Ix 12889) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12889) : Prop where
  moment : ∀ i, MomentBound (muI 12889) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12889} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12889) 8 (actualFourError c i)
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

end BstLean.Part266.Row12889

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12889
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

structure LatitudeVarianceCertificate (c : Ret 12889) : Prop where
  location : LBound (muI 12889) 12
    (fun a => conditionalVariance (stdGauss (Fin (12889 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12889) 12
    (fun a => conditionalVariance (stdGauss (Fin (12889 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12889) (hw : WINDOW (paperDesignP 12889) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12889 4 (55 / 100) /
      (12889 : ℝ) / ((12889 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12889

/-! The dimension-12889 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12889
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12889) (wl ws : ℝ) : SplitData 12889 :=
  BstLean.Part162.dPaper (paperDesignP 12889) c wl ws
    (√(2 / (12889 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12889 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12889 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12889) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12889) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12889 : ℝ)) * eR c * 12889 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12889) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12889 - 1)))
    (rowSplit c wl ws).good a ∂muI 12889 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12889) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12889 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12889) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12889 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12889) c (rowSplit c wl ws),
    hellG2 12889 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12889 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12889} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12889} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12889 t c BstLean.Part266.agent12889.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12889} (R : RootSource t c) :
    |√(QStand (paperDesignP 12889) t c) - √(qTilde (paperDesignP 12889) t c)| ≤
      BstLean.Part266.agent12889.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12889

/-! Rational enclosures for the HQ fluctuation price at dimension 12890. -/
namespace BstLean.Part266.Row12890
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (408719909 / 250000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22908483 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12890 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12890 * A / 2 + D + L * √(A * D)) ≤ (4625702591 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12890 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((408719909 / 250000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12890 L e4 d4 ≤ (8381439239 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12890 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((408719909 / 250000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12890 L e6 d6 ≤ (63488260651 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12890 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((408719909 / 250000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12890 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12890 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12890 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12890 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22908483 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4625702591 / 1000000000000)) ^ 2 / 2 + ((4625702591 / 1000000000000)) * ((8381439239 / 200000000000)) ^ 2 / 6 +
      ((8381439239 / 200000000000)) ^ 4 / 24 + ((8381439239 / 200000000000)) ^ 2 * ((63488260651 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63488260651 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12890 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12890 : ℝ) * ((1 + 3 * ((22908483 / 1000000000))) / (4 * (1 - (22908483 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22908483 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12890 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22908483 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12890 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12890 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12890

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12890
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((22706827 / 200000) : ℝ) ≤ √12890 ∧ √12890 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1463454 : ℝ) ≤ Jz 12890 ∧ 1000000 ≤ Jz 12890 := by
  have hr : ((22706827 / 200000) : ℝ) ≤ √12890 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12890 : ℝ) * √12890 ≤ (⌈(12890 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12890
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12890 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12890 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12890 : ℝ) = (⌈(12890 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1463454 : ℝ) ≤ Jz 12890 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12890 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12890) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12890 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12890 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12890 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12890 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12890 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12890 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12890) :
    (12890 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12890 * √(qB 12890))) ≤
      (543662719 / 1000000000000) := by
  have hden : ((22706827 / 200000) : ℝ) * (63 / 100) ≤ √12890 * √(qB 12890) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12890 : ℝ) * √(qB 12890) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12890) :
    (12890 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12890 * √(qB 12890))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12890 : ℝ) * √(qB 12890) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12890 : ℝ) * (√12890 *
      (c1F (exp (1 / 2) / 12) (Jz 12890) * (186 / 10000) / Jz 12890)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12890)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12890 : ℝ) * (√12890 *
      (c1F (exp (1 / 2) / 12) (Jz 12890) * (186 / 10000) / Jz 12890)) =
      (12890 * (√12890 * c1F (exp (1 / 2) / 12) (Jz 12890)) * (186 / 10000)) /
        Jz 12890 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12890)]
  nlinarith

theorem row_energy_rule :
    (12890 : ℝ) * (12890 *
      (c2F (exp (1 / 2) / 12) (Jz 12890) * (186 / 10000) ^ 2 / Jz 12890)) ≤
      (3535046709 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12890)]
  nlinarith

end BstLean.Part266.Row12890

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12890
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12890) (hc : A1 c ∈ BstLean.Part153.Eop 12890) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12890 : ℝ)) ≤ (12456285081 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12890 : ℝ) + 2 * √12890 ≤ (819816767 / 62500) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12890 : ℝ) ≤ (14191767 / 125000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12890)
    (hc : A1 c ∈ BstLean.Part153.Eop 12890) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12890 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12890 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12890))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12890) (K : Set (Ix 12890)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12890 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12890 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12890) (hw : WINDOW (paperDesignP 12890) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12890)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12890) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12890 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12890 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12890 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12890 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12890) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12890)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12890)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12890

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12890
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12890) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12890 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12890) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12890) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12890 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12890 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12890 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12890}
    (hw : WINDOW (paperDesignP 12890) c) (hc : c ∈ tableEvent) (K : Set (Ix 12890)) :
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

def proposedBaseEvent : Set (Ret 12890) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12890)) : Prop where
  charge : (retDist (paperCentres 12890)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12890)} (h : TablePayment H) :
    (retDist (paperCentres 12890)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12890)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12890

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12890
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12890) (i : Fin 4) (a : Ix 12890) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12890) (a : Ix 12890) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12890) : Prop where
  moment : ∀ i, MomentBound (muI 12890) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12890} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12890) 8 (actualFourError c i)
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

end BstLean.Part266.Row12890

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12890
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

structure LatitudeVarianceCertificate (c : Ret 12890) : Prop where
  location : LBound (muI 12890) 12
    (fun a => conditionalVariance (stdGauss (Fin (12890 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12890) 12
    (fun a => conditionalVariance (stdGauss (Fin (12890 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12890) (hw : WINDOW (paperDesignP 12890) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12890 4 (55 / 100) /
      (12890 : ℝ) / ((12890 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12890

/-! The dimension-12890 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12890
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12890) (wl ws : ℝ) : SplitData 12890 :=
  BstLean.Part162.dPaper (paperDesignP 12890) c wl ws
    (√(2 / (12890 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12890 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12890 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12890) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12890) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12890 : ℝ)) * eR c * 12890 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12890) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12890 - 1)))
    (rowSplit c wl ws).good a ∂muI 12890 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12890) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12890 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12890) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12890 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12890) c (rowSplit c wl ws),
    hellG2 12890 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12890 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12890} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12890} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12890 t c BstLean.Part266.agent12890.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12890} (R : RootSource t c) :
    |√(QStand (paperDesignP 12890) t c) - √(qTilde (paperDesignP 12890) t c)| ≤
      BstLean.Part266.agent12890.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12890

/-! Rational enclosures for the HQ fluctuation price at dimension 12891. -/
namespace BstLean.Part266.Row12891
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (81740801 / 50000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22906693 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12891 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12891 * A / 2 + D + L * √(A * D)) ≤ (1156475987 / 250000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12891 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((81740801 / 50000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12891 L e4 d4 ≤ (41909024977 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12891 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((81740801 / 50000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12891 L e6 d6 ≤ (63491023589 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12891 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((81740801 / 50000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12891 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12891 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12891 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12891 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22906693 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((1156475987 / 250000000000)) ^ 2 / 2 + ((1156475987 / 250000000000)) * ((41909024977 / 1000000000000)) ^ 2 / 6 +
      ((41909024977 / 1000000000000)) ^ 4 / 24 + ((41909024977 / 1000000000000)) ^ 2 * ((63491023589 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63491023589 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12891 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12891 : ℝ) * ((1 + 3 * ((22906693 / 1000000000))) / (4 * (1 - (22906693 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22906693 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12891 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22906693 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12891 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12891 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12891

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12891
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113538539 / 1000000) : ℝ) ≤ √12891 ∧ √12891 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1463624 : ℝ) ≤ Jz 12891 ∧ 1000000 ≤ Jz 12891 := by
  have hr : ((113538539 / 1000000) : ℝ) ≤ √12891 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12891 : ℝ) * √12891 ≤ (⌈(12891 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12891
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12891 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12891 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12891 : ℝ) = (⌈(12891 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1463624 : ℝ) ≤ Jz 12891 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12891 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12891) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12891 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12891 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12891 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12891 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12891 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12891 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12891) :
    (12891 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12891 * √(qB 12891))) ≤
      (543683807 / 1000000000000) := by
  have hden : ((113538539 / 1000000) : ℝ) * (63 / 100) ≤ √12891 * √(qB 12891) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12891 : ℝ) * √(qB 12891) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12891) :
    (12891 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12891 * √(qB 12891))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12891 : ℝ) * √(qB 12891) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12891 : ℝ) * (√12891 *
      (c1F (exp (1 / 2) / 12) (Jz 12891) * (186 / 10000) / Jz 12891)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12891)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12891 : ℝ) * (√12891 *
      (c1F (exp (1 / 2) / 12) (Jz 12891) * (186 / 10000) / Jz 12891)) =
      (12891 * (√12891 * c1F (exp (1 / 2) / 12) (Jz 12891)) * (186 / 10000)) /
        Jz 12891 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12891)]
  nlinarith

theorem row_energy_rule :
    (12891 : ℝ) * (12891 *
      (c2F (exp (1 / 2) / 12) (Jz 12891) * (186 / 10000) ^ 2 / Jz 12891)) ≤
      (1767592283 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12891)]
  nlinarith

end BstLean.Part266.Row12891

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12891
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12891) (hc : A1 c ∈ BstLean.Part153.Eop 12891) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12891 : ℝ)) ≤ (12455801933 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12891 : ℝ) + 2 * √12891 ≤ (327951927 / 25000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12891 : ℝ) ≤ (5676927 / 50000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12891)
    (hc : A1 c ∈ BstLean.Part153.Eop 12891) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12891 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12891 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12891))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12891) (K : Set (Ix 12891)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12891 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12891 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12891) (hw : WINDOW (paperDesignP 12891) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12891)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12891) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12891 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12891 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12891 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12891 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12891) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12891)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12891)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12891

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12891
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12891) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12891 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12891) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12891) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12891 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12891 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12891 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12891}
    (hw : WINDOW (paperDesignP 12891) c) (hc : c ∈ tableEvent) (K : Set (Ix 12891)) :
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

def proposedBaseEvent : Set (Ret 12891) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12891)) : Prop where
  charge : (retDist (paperCentres 12891)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12891)} (h : TablePayment H) :
    (retDist (paperCentres 12891)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12891)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12891

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12891
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12891) (i : Fin 4) (a : Ix 12891) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12891) (a : Ix 12891) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12891) : Prop where
  moment : ∀ i, MomentBound (muI 12891) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12891} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12891) 8 (actualFourError c i)
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

end BstLean.Part266.Row12891

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12891
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

structure LatitudeVarianceCertificate (c : Ret 12891) : Prop where
  location : LBound (muI 12891) 12
    (fun a => conditionalVariance (stdGauss (Fin (12891 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12891) 12
    (fun a => conditionalVariance (stdGauss (Fin (12891 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12891) (hw : WINDOW (paperDesignP 12891) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12891 4 (55 / 100) /
      (12891 : ℝ) / ((12891 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12891

/-! The dimension-12891 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12891
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12891) (wl ws : ℝ) : SplitData 12891 :=
  BstLean.Part162.dPaper (paperDesignP 12891) c wl ws
    (√(2 / (12891 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12891 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12891 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12891) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12891) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12891 : ℝ)) * eR c * 12891 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12891) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12891 - 1)))
    (rowSplit c wl ws).good a ∂muI 12891 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12891) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12891 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12891) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12891 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12891) c (rowSplit c wl ws),
    hellG2 12891 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12891 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12891} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12891} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12891 t c BstLean.Part266.agent12891.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12891} (R : RootSource t c) :
    |√(QStand (paperDesignP 12891) t c) - √(qTilde (paperDesignP 12891) t c)| ≤
      BstLean.Part266.agent12891.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12891

/-! Rational enclosures for the HQ fluctuation price at dimension 12892. -/
namespace BstLean.Part266.Row12892
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1634752419 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (2863113 / 125000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12892 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12892 * A / 2 + D + L * √(A * D)) ≤ (578263163 / 125000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12892 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1634752419 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12892 L e4 d4 ≤ (41910853763 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12892 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1634752419 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12892 L e6 d6 ≤ (63493786533 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12892 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1634752419 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12892 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12892 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12892 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12892 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (2863113 / 125000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((578263163 / 125000000000)) ^ 2 / 2 + ((578263163 / 125000000000)) * ((41910853763 / 1000000000000)) ^ 2 / 6 +
      ((41910853763 / 1000000000000)) ^ 4 / 24 + ((41910853763 / 1000000000000)) ^ 2 * ((63493786533 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63493786533 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12892 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12892 : ℝ) * ((1 + 3 * ((2863113 / 125000000))) / (4 * (1 - (2863113 / 125000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (2863113 / 125000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12892 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (2863113 / 125000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12892 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12892 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12892

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12892
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113542943 / 1000000) : ℝ) ≤ √12892 ∧ √12892 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1463794 : ℝ) ≤ Jz 12892 ∧ 1000000 ≤ Jz 12892 := by
  have hr : ((113542943 / 1000000) : ℝ) ≤ √12892 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12892 : ℝ) * √12892 ≤ (⌈(12892 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12892
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12892 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12892 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12892 : ℝ) = (⌈(12892 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1463794 : ℝ) ≤ Jz 12892 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12892 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12892) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12892 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12892 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12892 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12892 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12892 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12892 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12892) :
    (12892 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12892 * √(qB 12892))) ≤
      (543704893 / 1000000000000) := by
  have hden : ((113542943 / 1000000) : ℝ) * (63 / 100) ≤ √12892 * √(qB 12892) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12892 : ℝ) * √(qB 12892) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12892) :
    (12892 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12892 * √(qB 12892))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12892 : ℝ) * √(qB 12892) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12892 : ℝ) * (√12892 *
      (c1F (exp (1 / 2) / 12) (Jz 12892) * (186 / 10000) / Jz 12892)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12892)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12892 : ℝ) * (√12892 *
      (c1F (exp (1 / 2) / 12) (Jz 12892) * (186 / 10000) / Jz 12892)) =
      (12892 * (√12892 * c1F (exp (1 / 2) / 12) (Jz 12892)) * (186 / 10000)) /
        Jz 12892 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12892)]
  nlinarith

theorem row_energy_rule :
    (12892 : ℝ) * (12892 *
      (c2F (exp (1 / 2) / 12) (Jz 12892) * (186 / 10000) ^ 2 / Jz 12892)) ≤
      (55239413 / 15625000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12892)]
  nlinarith

end BstLean.Part266.Row12892

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12892
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12892) (hc : A1 c ∈ BstLean.Part153.Eop 12892) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12892 : ℝ)) ≤ (12455318841 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12892 : ℝ) + 2 * √12892 ≤ (204985717 / 15625) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12892 : ℝ) ≤ (3548217 / 31250))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12892)
    (hc : A1 c ∈ BstLean.Part153.Eop 12892) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12892 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12892 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12892))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12892) (K : Set (Ix 12892)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12892 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12892 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12892) (hw : WINDOW (paperDesignP 12892) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12892)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12892) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12892 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12892 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12892 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12892 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12892) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12892)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12892)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12892

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12892
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12892) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12892 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12892) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12892) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12892 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12892 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12892 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12892}
    (hw : WINDOW (paperDesignP 12892) c) (hc : c ∈ tableEvent) (K : Set (Ix 12892)) :
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

def proposedBaseEvent : Set (Ret 12892) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12892)) : Prop where
  charge : (retDist (paperCentres 12892)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12892)} (h : TablePayment H) :
    (retDist (paperCentres 12892)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12892)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12892

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12892
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12892) (i : Fin 4) (a : Ix 12892) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12892) (a : Ix 12892) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12892) : Prop where
  moment : ∀ i, MomentBound (muI 12892) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12892} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12892) 8 (actualFourError c i)
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

end BstLean.Part266.Row12892

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12892
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

structure LatitudeVarianceCertificate (c : Ret 12892) : Prop where
  location : LBound (muI 12892) 12
    (fun a => conditionalVariance (stdGauss (Fin (12892 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12892) 12
    (fun a => conditionalVariance (stdGauss (Fin (12892 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12892) (hw : WINDOW (paperDesignP 12892) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12892 4 (55 / 100) /
      (12892 : ℝ) / ((12892 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12892

/-! The dimension-12892 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12892
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12892) (wl ws : ℝ) : SplitData 12892 :=
  BstLean.Part162.dPaper (paperDesignP 12892) c wl ws
    (√(2 / (12892 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12892 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12892 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12892) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12892) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12892 : ℝ)) * eR c * 12892 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12892) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12892 - 1)))
    (rowSplit c wl ws).good a ∂muI 12892 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12892) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12892 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12892) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12892 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12892) c (rowSplit c wl ws),
    hellG2 12892 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12892 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12892} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12892} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12892 t c BstLean.Part266.agent12892.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12892} (R : RootSource t c) :
    |√(QStand (paperDesignP 12892) t c) - √(qTilde (paperDesignP 12892) t c)| ≤
      BstLean.Part266.agent12892.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12892

/-! Rational enclosures for the HQ fluctuation price at dimension 12893. -/
namespace BstLean.Part266.Row12893
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1634688833 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11451557 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12893 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12893 * A / 2 + D + L * √(A * D)) ≤ (2313153331 / 500000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12893 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1634688833 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12893 L e4 d4 ≤ (41912682553 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12893 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1634688833 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12893 L e6 d6 ≤ (63496549483 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12893 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1634688833 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12893 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12893 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12893 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12893 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11451557 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((2313153331 / 500000000000)) ^ 2 / 2 + ((2313153331 / 500000000000)) * ((41912682553 / 1000000000000)) ^ 2 / 6 +
      ((41912682553 / 1000000000000)) ^ 4 / 24 + ((41912682553 / 1000000000000)) ^ 2 * ((63496549483 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63496549483 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12893 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12893 : ℝ) * ((1 + 3 * ((11451557 / 500000000))) / (4 * (1 - (11451557 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11451557 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12893 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11451557 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12893 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12893 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12893

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12893
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((56773673 / 500000) : ℝ) ≤ √12893 ∧ √12893 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1463964 : ℝ) ≤ Jz 12893 ∧ 1000000 ≤ Jz 12893 := by
  have hr : ((56773673 / 500000) : ℝ) ≤ √12893 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12893 : ℝ) * √12893 ≤ (⌈(12893 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12893
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12893 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12893 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12893 : ℝ) = (⌈(12893 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1463964 : ℝ) ≤ Jz 12893 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12893 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12893) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12893 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12893 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12893 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12893 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12893 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12893 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12893) :
    (12893 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12893 * √(qB 12893))) ≤
      (271862991 / 500000000000) := by
  have hden : ((56773673 / 500000) : ℝ) * (63 / 100) ≤ √12893 * √(qB 12893) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12893 : ℝ) * √(qB 12893) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12893) :
    (12893 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12893 * √(qB 12893))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12893 : ℝ) * √(qB 12893) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12893 : ℝ) * (√12893 *
      (c1F (exp (1 / 2) / 12) (Jz 12893) * (186 / 10000) / Jz 12893)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12893)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12893 : ℝ) * (√12893 *
      (c1F (exp (1 / 2) / 12) (Jz 12893) * (186 / 10000) / Jz 12893)) =
      (12893 * (√12893 * c1F (exp (1 / 2) / 12) (Jz 12893)) * (186 / 10000)) /
        Jz 12893 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12893)]
  nlinarith

theorem row_energy_rule :
    (12893 : ℝ) * (12893 *
      (c2F (exp (1 / 2) / 12) (Jz 12893) * (186 / 10000) ^ 2 / Jz 12893)) ≤
      (353546031 / 100000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12893)]
  nlinarith

end BstLean.Part266.Row12893

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12893
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12893) (hc : A1 c ∈ BstLean.Part153.Eop 12893) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12893 : ℝ)) ≤ (2490967161 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12893 : ℝ) + 2 * √12893 ≤ (6560047347 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12893 : ℝ) ≤ (113547347 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12893)
    (hc : A1 c ∈ BstLean.Part153.Eop 12893) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12893 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12893 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12893))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12893) (K : Set (Ix 12893)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12893 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12893 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12893) (hw : WINDOW (paperDesignP 12893) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12893)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12893) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12893 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12893 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12893 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12893 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12893) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12893)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12893)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12893

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12893
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12893) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12893 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12893) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12893) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12893 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12893 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12893 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12893}
    (hw : WINDOW (paperDesignP 12893) c) (hc : c ∈ tableEvent) (K : Set (Ix 12893)) :
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

def proposedBaseEvent : Set (Ret 12893) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12893)) : Prop where
  charge : (retDist (paperCentres 12893)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12893)} (h : TablePayment H) :
    (retDist (paperCentres 12893)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12893)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12893

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12893
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12893) (i : Fin 4) (a : Ix 12893) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12893) (a : Ix 12893) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12893) : Prop where
  moment : ∀ i, MomentBound (muI 12893) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12893} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12893) 8 (actualFourError c i)
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

end BstLean.Part266.Row12893

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12893
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

structure LatitudeVarianceCertificate (c : Ret 12893) : Prop where
  location : LBound (muI 12893) 12
    (fun a => conditionalVariance (stdGauss (Fin (12893 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12893) 12
    (fun a => conditionalVariance (stdGauss (Fin (12893 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12893) (hw : WINDOW (paperDesignP 12893) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12893 4 (55 / 100) /
      (12893 : ℝ) / ((12893 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12893

/-! The dimension-12893 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12893
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12893) (wl ws : ℝ) : SplitData 12893 :=
  BstLean.Part162.dPaper (paperDesignP 12893) c wl ws
    (√(2 / (12893 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12893 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12893 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12893) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12893) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12893 : ℝ)) * eR c * 12893 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12893) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12893 - 1)))
    (rowSplit c wl ws).good a ∂muI 12893 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12893) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12893 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12893) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12893 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12893) c (rowSplit c wl ws),
    hellG2 12893 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12893 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12893} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12893} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12893 t c BstLean.Part266.agent12893.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12893} (R : RootSource t c) :
    |√(QStand (paperDesignP 12893) t c) - √(qTilde (paperDesignP 12893) t c)| ≤
      BstLean.Part266.agent12893.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12893

/-! Rational enclosures for the HQ fluctuation price at dimension 12894. -/
namespace BstLean.Part266.Row12894
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (817312631 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11450663 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12894 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12894 * A / 2 + D + L * √(A * D)) ≤ (4626508019 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12894 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((817312631 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12894 L e4 d4 ≤ (20957255673 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12894 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((817312631 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12894 L e6 d6 ≤ (31749656219 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12894 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((817312631 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12894 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12894 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12894 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12894 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11450663 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4626508019 / 1000000000000)) ^ 2 / 2 + ((4626508019 / 1000000000000)) * ((20957255673 / 500000000000)) ^ 2 / 6 +
      ((20957255673 / 500000000000)) ^ 4 / 24 + ((20957255673 / 500000000000)) ^ 2 * ((31749656219 / 500000000000)) ^ 3 / 120 +
      2187 * ((31749656219 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12894 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12894 : ℝ) * ((1 + 3 * ((11450663 / 500000000))) / (4 * (1 - (11450663 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11450663 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12894 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11450663 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12894 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12894 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12894

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12894
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((454207 / 4000) : ℝ) ≤ √12894 ∧ √12894 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1464135 : ℝ) ≤ Jz 12894 ∧ 1000000 ≤ Jz 12894 := by
  have hr : ((454207 / 4000) : ℝ) ≤ √12894 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12894 : ℝ) * √12894 ≤ (⌈(12894 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12894
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12894 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12894 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12894 : ℝ) = (⌈(12894 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1464135 : ℝ) ≤ Jz 12894 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12894 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12894) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12894 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12894 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12894 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12894 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12894 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12894 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12894) :
    (12894 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12894 * √(qB 12894))) ≤
      (67968383 / 125000000000) := by
  have hden : ((454207 / 4000) : ℝ) * (63 / 100) ≤ √12894 * √(qB 12894) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12894 : ℝ) * √(qB 12894) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12894) :
    (12894 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12894 * √(qB 12894))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12894 : ℝ) * √(qB 12894) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12894 : ℝ) * (√12894 *
      (c1F (exp (1 / 2) / 12) (Jz 12894) * (186 / 10000) / Jz 12894)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12894)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12894 : ℝ) * (√12894 *
      (c1F (exp (1 / 2) / 12) (Jz 12894) * (186 / 10000) / Jz 12894)) =
      (12894 * (√12894 * c1F (exp (1 / 2) / 12) (Jz 12894)) * (186 / 10000)) /
        Jz 12894 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12894)]
  nlinarith

theorem row_energy_rule :
    (12894 : ℝ) * (12894 *
      (c2F (exp (1 / 2) / 12) (Jz 12894) * (186 / 10000) ^ 2 / Jz 12894)) ≤
      (1767797891 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12894)]
  nlinarith

end BstLean.Part266.Row12894

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12894
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12894) (hc : A1 c ∈ BstLean.Part153.Eop 12894) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12894 : ℝ)) ≤ (6227176413 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12894 : ℝ) + 2 * √12894 ≤ (6560551751 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12894 : ℝ) ≤ (113551751 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12894)
    (hc : A1 c ∈ BstLean.Part153.Eop 12894) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12894 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12894 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12894))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12894) (K : Set (Ix 12894)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12894 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12894 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12894) (hw : WINDOW (paperDesignP 12894) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12894)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12894) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12894 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12894 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12894 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12894 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12894) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12894)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12894)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12894

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12894
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12894) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12894 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12894) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12894) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12894 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12894 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12894 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12894}
    (hw : WINDOW (paperDesignP 12894) c) (hc : c ∈ tableEvent) (K : Set (Ix 12894)) :
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

def proposedBaseEvent : Set (Ret 12894) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12894)) : Prop where
  charge : (retDist (paperCentres 12894)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12894)} (h : TablePayment H) :
    (retDist (paperCentres 12894)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12894)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12894

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12894
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12894) (i : Fin 4) (a : Ix 12894) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12894) (a : Ix 12894) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12894) : Prop where
  moment : ∀ i, MomentBound (muI 12894) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12894} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12894) 8 (actualFourError c i)
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

end BstLean.Part266.Row12894

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12894
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

structure LatitudeVarianceCertificate (c : Ret 12894) : Prop where
  location : LBound (muI 12894) 12
    (fun a => conditionalVariance (stdGauss (Fin (12894 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12894) 12
    (fun a => conditionalVariance (stdGauss (Fin (12894 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12894) (hw : WINDOW (paperDesignP 12894) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12894 4 (55 / 100) /
      (12894 : ℝ) / ((12894 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12894

/-! The dimension-12894 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12894
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12894) (wl ws : ℝ) : SplitData 12894 :=
  BstLean.Part162.dPaper (paperDesignP 12894) c wl ws
    (√(2 / (12894 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12894 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12894 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12894) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12894) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12894 : ℝ)) * eR c * 12894 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12894) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12894 - 1)))
    (rowSplit c wl ws).good a ∂muI 12894 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12894) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12894 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12894) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12894 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12894) c (rowSplit c wl ws),
    hellG2 12894 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12894 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12894} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12894} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12894 t c BstLean.Part266.agent12894.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12894} (R : RootSource t c) :
    |√(QStand (paperDesignP 12894) t c) - √(qTilde (paperDesignP 12894) t c)| ≤
      BstLean.Part266.agent12894.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12894

/-! Rational enclosures for the HQ fluctuation price at dimension 12895. -/
namespace BstLean.Part266.Row12895
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (326912397 / 200000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22899541 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12895 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12895 * A / 2 + D + L * √(A * D)) ≤ (925341877 / 200000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12895 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((326912397 / 200000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12895 L e4 d4 ≤ (8383268043 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12895 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((326912397 / 200000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12895 L e6 d6 ≤ (15875518877 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12895 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((326912397 / 200000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12895 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12895 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12895 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12895 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22899541 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((925341877 / 200000000000)) ^ 2 / 2 + ((925341877 / 200000000000)) * ((8383268043 / 200000000000)) ^ 2 / 6 +
      ((8383268043 / 200000000000)) ^ 4 / 24 + ((8383268043 / 200000000000)) ^ 2 * ((15875518877 / 250000000000)) ^ 3 / 120 +
      2187 * ((15875518877 / 250000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12895 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12895 : ℝ) * ((1 + 3 * ((22899541 / 1000000000))) / (4 * (1 - (22899541 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22899541 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12895 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22899541 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12895 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12895 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12895

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12895
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113556153 / 1000000) : ℝ) ≤ √12895 ∧ √12895 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1464305 : ℝ) ≤ Jz 12895 ∧ 1000000 ≤ Jz 12895 := by
  have hr : ((113556153 / 1000000) : ℝ) ≤ √12895 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12895 : ℝ) * √12895 ≤ (⌈(12895 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12895
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12895 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12895 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12895 : ℝ) = (⌈(12895 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1464305 : ℝ) ≤ Jz 12895 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12895 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12895) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12895 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12895 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12895 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12895 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12895 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12895 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12895) :
    (12895 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12895 * √(qB 12895))) ≤
      (10875363 / 20000000000) := by
  have hden : ((113556153 / 1000000) : ℝ) * (63 / 100) ≤ √12895 * √(qB 12895) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12895 : ℝ) * √(qB 12895) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12895) :
    (12895 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12895 * √(qB 12895))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12895 : ℝ) * √(qB 12895) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12895 : ℝ) * (√12895 *
      (c1F (exp (1 / 2) / 12) (Jz 12895) * (186 / 10000) / Jz 12895)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12895)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12895 : ℝ) * (√12895 *
      (c1F (exp (1 / 2) / 12) (Jz 12895) * (186 / 10000) / Jz 12895)) =
      (12895 * (√12895 * c1F (exp (1 / 2) / 12) (Jz 12895)) * (186 / 10000)) /
        Jz 12895 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12895)]
  nlinarith

theorem row_energy_rule :
    (12895 : ℝ) * (12895 *
      (c2F (exp (1 / 2) / 12) (Jz 12895) * (186 / 10000) ^ 2 / Jz 12895)) ≤
      (3535733681 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12895)]
  nlinarith

end BstLean.Part266.Row12895

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12895
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12895) (hc : A1 c ∈ BstLean.Part153.Eop 12895) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12895 : ℝ)) ≤ (6226934951 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12895 : ℝ) + 2 * √12895 ≤ (3280528077 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12895 : ℝ) ≤ (56778077 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12895)
    (hc : A1 c ∈ BstLean.Part153.Eop 12895) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12895 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12895 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12895))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12895) (K : Set (Ix 12895)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12895 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12895 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12895) (hw : WINDOW (paperDesignP 12895) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12895)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12895) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12895 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12895 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12895 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12895 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12895) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12895)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12895)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12895

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12895
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12895) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12895 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12895) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12895) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12895 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12895 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12895 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12895}
    (hw : WINDOW (paperDesignP 12895) c) (hc : c ∈ tableEvent) (K : Set (Ix 12895)) :
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

def proposedBaseEvent : Set (Ret 12895) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12895)) : Prop where
  charge : (retDist (paperCentres 12895)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12895)} (h : TablePayment H) :
    (retDist (paperCentres 12895)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12895)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12895

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12895
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12895) (i : Fin 4) (a : Ix 12895) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12895) (a : Ix 12895) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12895) : Prop where
  moment : ∀ i, MomentBound (muI 12895) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12895} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12895) 8 (actualFourError c i)
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

end BstLean.Part266.Row12895

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12895
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

structure LatitudeVarianceCertificate (c : Ret 12895) : Prop where
  location : LBound (muI 12895) 12
    (fun a => conditionalVariance (stdGauss (Fin (12895 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12895) 12
    (fun a => conditionalVariance (stdGauss (Fin (12895 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12895) (hw : WINDOW (paperDesignP 12895) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12895 4 (55 / 100) /
      (12895 : ℝ) / ((12895 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12895

/-! The dimension-12895 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12895
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12895) (wl ws : ℝ) : SplitData 12895 :=
  BstLean.Part162.dPaper (paperDesignP 12895) c wl ws
    (√(2 / (12895 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12895 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12895 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12895) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12895) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12895 : ℝ)) * eR c * 12895 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12895) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12895 - 1)))
    (rowSplit c wl ws).good a ∂muI 12895 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12895) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12895 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12895) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12895 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12895) c (rowSplit c wl ws),
    hellG2 12895 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12895 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12895} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12895} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12895 t c BstLean.Part266.agent12895.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12895} (R : RootSource t c) :
    |√(QStand (paperDesignP 12895) t c) - √(qTilde (paperDesignP 12895) t c)| ≤
      BstLean.Part266.agent12895.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12895

/-! Rational enclosures for the HQ fluctuation price at dimension 12896. -/
namespace BstLean.Part266.Row12896
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (408624611 / 250000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22897753 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12896 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12896 * A / 2 + D + L * √(A * D)) ≤ (578363843 / 125000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12896 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((408624611 / 250000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12896 L e4 d4 ≤ (5239771127 / 125000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12896 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((408624611 / 250000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12896 L e6 d6 ≤ (2540193539 / 40000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12896 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((408624611 / 250000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12896 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12896 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12896 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12896 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22897753 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((578363843 / 125000000000)) ^ 2 / 2 + ((578363843 / 125000000000)) * ((5239771127 / 125000000000)) ^ 2 / 6 +
      ((5239771127 / 125000000000)) ^ 4 / 24 + ((5239771127 / 125000000000)) ^ 2 * ((2540193539 / 40000000000)) ^ 3 / 120 +
      2187 * ((2540193539 / 40000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12896 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12896 : ℝ) * ((1 + 3 * ((22897753 / 1000000000))) / (4 * (1 - (22897753 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22897753 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12896 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22897753 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12896 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12896 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12896

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12896
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((28390139 / 250000) : ℝ) ≤ √12896 ∧ √12896 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1464475 : ℝ) ≤ Jz 12896 ∧ 1000000 ≤ Jz 12896 := by
  have hr : ((28390139 / 250000) : ℝ) ≤ √12896 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12896 : ℝ) * √12896 ≤ (⌈(12896 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12896
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12896 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12896 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12896 : ℝ) = (⌈(12896 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1464475 : ℝ) ≤ Jz 12896 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12896 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12896) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12896 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12896 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12896 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12896 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12896 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12896 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12896) :
    (12896 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12896 * √(qB 12896))) ≤
      (271894617 / 500000000000) := by
  have hden : ((28390139 / 250000) : ℝ) * (63 / 100) ≤ √12896 * √(qB 12896) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12896 : ℝ) * √(qB 12896) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12896) :
    (12896 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12896 * √(qB 12896))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12896 : ℝ) * √(qB 12896) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12896 : ℝ) * (√12896 *
      (c1F (exp (1 / 2) / 12) (Jz 12896) * (186 / 10000) / Jz 12896)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12896)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12896 : ℝ) * (√12896 *
      (c1F (exp (1 / 2) / 12) (Jz 12896) * (186 / 10000) / Jz 12896)) =
      (12896 * (√12896 * c1F (exp (1 / 2) / 12) (Jz 12896)) * (186 / 10000)) /
        Jz 12896 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12896)]
  nlinarith

theorem row_energy_rule :
    (12896 : ℝ) * (12896 *
      (c2F (exp (1 / 2) / 12) (Jz 12896) * (186 / 10000) ^ 2 / Jz 12896)) ≤
      (353587159 / 100000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12896)]
  nlinarith

end BstLean.Part266.Row12896

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12896
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12896) (hc : A1 c ∈ BstLean.Part153.Eop 12896) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12896 : ℝ)) ≤ (2490677407 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12896 : ℝ) + 2 * √12896 ≤ (6561560557 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12896 : ℝ) ≤ (113560557 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12896)
    (hc : A1 c ∈ BstLean.Part153.Eop 12896) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12896 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12896 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12896))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12896) (K : Set (Ix 12896)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12896 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12896 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12896) (hw : WINDOW (paperDesignP 12896) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12896)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12896) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12896 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12896 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12896 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12896 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12896) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12896)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12896)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12896

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12896
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12896) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12896 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12896) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12896) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12896 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12896 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12896 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12896}
    (hw : WINDOW (paperDesignP 12896) c) (hc : c ∈ tableEvent) (K : Set (Ix 12896)) :
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

def proposedBaseEvent : Set (Ret 12896) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12896)) : Prop where
  charge : (retDist (paperCentres 12896)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12896)} (h : TablePayment H) :
    (retDist (paperCentres 12896)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12896)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12896

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12896
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12896) (i : Fin 4) (a : Ix 12896) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12896) (a : Ix 12896) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12896) : Prop where
  moment : ∀ i, MomentBound (muI 12896) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12896} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12896) 8 (actualFourError c i)
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

end BstLean.Part266.Row12896

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12896
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

structure LatitudeVarianceCertificate (c : Ret 12896) : Prop where
  location : LBound (muI 12896) 12
    (fun a => conditionalVariance (stdGauss (Fin (12896 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12896) 12
    (fun a => conditionalVariance (stdGauss (Fin (12896 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12896) (hw : WINDOW (paperDesignP 12896) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12896 4 (55 / 100) /
      (12896 : ℝ) / ((12896 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12896

/-! The dimension-12896 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12896
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12896) (wl ws : ℝ) : SplitData 12896 :=
  BstLean.Part162.dPaper (paperDesignP 12896) c wl ws
    (√(2 / (12896 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12896 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12896 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12896) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12896) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12896 : ℝ)) * eR c * 12896 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12896) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12896 - 1)))
    (rowSplit c wl ws).good a ∂muI 12896 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12896) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12896 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12896) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12896 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12896) c (rowSplit c wl ws),
    hellG2 12896 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12896 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12896} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12896} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12896 t c BstLean.Part266.agent12896.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12896} (R : RootSource t c) :
    |√(QStand (paperDesignP 12896) t c) - √(qTilde (paperDesignP 12896) t c)| ≤
      BstLean.Part266.agent12896.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12896

/-! Rational enclosures for the HQ fluctuation price at dimension 12897. -/
namespace BstLean.Part266.Row12897
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (408608729 / 250000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (4579193 / 200000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12897 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12897 * A / 2 + D + L * √(A * D)) ≤ (4627112103 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12897 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((408608729 / 250000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12897 L e4 d4 ≤ (2095999891 / 50000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12897 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((408608729 / 250000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12897 L e6 d6 ≤ (7938450181 / 125000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12897 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((408608729 / 250000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12897 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12897 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12897 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12897 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (4579193 / 200000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4627112103 / 1000000000000)) ^ 2 / 2 + ((4627112103 / 1000000000000)) * ((2095999891 / 50000000000)) ^ 2 / 6 +
      ((2095999891 / 50000000000)) ^ 4 / 24 + ((2095999891 / 50000000000)) ^ 2 * ((7938450181 / 125000000000)) ^ 3 / 120 +
      2187 * ((7938450181 / 125000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12897 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12897 : ℝ) * ((1 + 3 * ((4579193 / 200000000))) / (4 * (1 - (4579193 / 200000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (4579193 / 200000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12897 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (4579193 / 200000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12897 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12897 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12897

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12897
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113564959 / 1000000) : ℝ) ≤ √12897 ∧ √12897 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1464646 : ℝ) ≤ Jz 12897 ∧ 1000000 ≤ Jz 12897 := by
  have hr : ((113564959 / 1000000) : ℝ) ≤ √12897 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12897 : ℝ) * √12897 ≤ (⌈(12897 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12897
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12897 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12897 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12897 : ℝ) = (⌈(12897 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1464646 : ℝ) ≤ Jz 12897 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12897 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12897) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12897 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12897 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12897 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12897 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12897 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12897 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12897) :
    (12897 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12897 * √(qB 12897))) ≤
      (543810317 / 1000000000000) := by
  have hden : ((113564959 / 1000000) : ℝ) * (63 / 100) ≤ √12897 * √(qB 12897) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12897 : ℝ) * √(qB 12897) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12897) :
    (12897 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12897 * √(qB 12897))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12897 : ℝ) * √(qB 12897) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12897 : ℝ) * (√12897 *
      (c1F (exp (1 / 2) / 12) (Jz 12897) * (186 / 10000) / Jz 12897)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12897)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12897 : ℝ) * (√12897 *
      (c1F (exp (1 / 2) / 12) (Jz 12897) * (186 / 10000) / Jz 12897)) =
      (12897 * (√12897 * c1F (exp (1 / 2) / 12) (Jz 12897)) * (186 / 10000)) /
        Jz 12897 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12897)]
  nlinarith

theorem row_energy_rule :
    (12897 : ℝ) * (12897 *
      (c2F (exp (1 / 2) / 12) (Jz 12897) * (186 / 10000) ^ 2 / Jz 12897)) ≤
      (707201419 / 200000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12897)]
  nlinarith

end BstLean.Part266.Row12897

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12897
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12897) (hc : A1 c ∈ BstLean.Part153.Eop 12897) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12897 : ℝ)) ≤ (389153257 / 31250000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12897 : ℝ) + 2 * √12897 ≤ (41012906 / 3125) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12897 : ℝ) ≤ (709781 / 6250))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12897)
    (hc : A1 c ∈ BstLean.Part153.Eop 12897) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12897 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12897 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12897))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12897) (K : Set (Ix 12897)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12897 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12897 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12897) (hw : WINDOW (paperDesignP 12897) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12897)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12897) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12897 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12897 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12897 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12897 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12897) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12897)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12897)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12897

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12897
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12897) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12897 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12897) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12897) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12897 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12897 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12897 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12897}
    (hw : WINDOW (paperDesignP 12897) c) (hc : c ∈ tableEvent) (K : Set (Ix 12897)) :
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

def proposedBaseEvent : Set (Ret 12897) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12897)) : Prop where
  charge : (retDist (paperCentres 12897)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12897)} (h : TablePayment H) :
    (retDist (paperCentres 12897)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12897)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12897

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12897
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12897) (i : Fin 4) (a : Ix 12897) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12897) (a : Ix 12897) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12897) : Prop where
  moment : ∀ i, MomentBound (muI 12897) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12897} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12897) 8 (actualFourError c i)
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

end BstLean.Part266.Row12897

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12897
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

structure LatitudeVarianceCertificate (c : Ret 12897) : Prop where
  location : LBound (muI 12897) 12
    (fun a => conditionalVariance (stdGauss (Fin (12897 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12897) 12
    (fun a => conditionalVariance (stdGauss (Fin (12897 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12897) (hw : WINDOW (paperDesignP 12897) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12897 4 (55 / 100) /
      (12897 : ℝ) / ((12897 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12897

/-! The dimension-12897 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12897
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12897) (wl ws : ℝ) : SplitData 12897 :=
  BstLean.Part162.dPaper (paperDesignP 12897) c wl ws
    (√(2 / (12897 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12897 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12897 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12897) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12897) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12897 : ℝ)) * eR c * 12897 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12897) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12897 - 1)))
    (rowSplit c wl ws).good a ∂muI 12897 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12897) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12897 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12897) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12897 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12897) c (rowSplit c wl ws),
    hellG2 12897 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12897 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12897} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12897} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12897 t c BstLean.Part266.agent12897.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12897} (R : RootSource t c) :
    |√(QStand (paperDesignP 12897) t c) - √(qTilde (paperDesignP 12897) t c)| ≤
      BstLean.Part266.agent12897.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12897

/-! Rational enclosures for the HQ fluctuation price at dimension 12898. -/
namespace BstLean.Part266.Row12898
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1634371403 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11447089 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12898 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12898 * A / 2 + D + L * √(A * D)) ≤ (2313656731 / 500000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12898 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1634371403 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12898 L e4 d4 ≤ (41921826629 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12898 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1634371403 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12898 L e6 d6 ≤ (31755182213 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12898 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1634371403 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12898 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12898 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12898 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12898 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11447089 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((2313656731 / 500000000000)) ^ 2 / 2 + ((2313656731 / 500000000000)) * ((41921826629 / 1000000000000)) ^ 2 / 6 +
      ((41921826629 / 1000000000000)) ^ 4 / 24 + ((41921826629 / 1000000000000)) ^ 2 * ((31755182213 / 500000000000)) ^ 3 / 120 +
      2187 * ((31755182213 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12898 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12898 : ℝ) * ((1 + 3 * ((11447089 / 500000000))) / (4 * (1 - (11447089 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11447089 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12898 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11447089 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12898 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12898 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12898

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12898
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((56784681 / 500000) : ℝ) ≤ √12898 ∧ √12898 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1464816 : ℝ) ≤ Jz 12898 ∧ 1000000 ≤ Jz 12898 := by
  have hr : ((56784681 / 500000) : ℝ) ≤ √12898 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12898 : ℝ) * √12898 ≤ (⌈(12898 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12898
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12898 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12898 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12898 : ℝ) = (⌈(12898 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1464816 : ℝ) ≤ Jz 12898 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12898 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12898) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12898 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12898 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12898 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12898 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12898 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12898 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12898) :
    (12898 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12898 * √(qB 12898))) ≤
      (271915699 / 500000000000) := by
  have hden : ((56784681 / 500000) : ℝ) * (63 / 100) ≤ √12898 * √(qB 12898) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12898 : ℝ) * √(qB 12898) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12898) :
    (12898 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12898 * √(qB 12898))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12898 : ℝ) * √(qB 12898) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12898 : ℝ) * (√12898 *
      (c1F (exp (1 / 2) / 12) (Jz 12898) * (186 / 10000) / Jz 12898)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12898)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12898 : ℝ) * (√12898 *
      (c1F (exp (1 / 2) / 12) (Jz 12898) * (186 / 10000) / Jz 12898)) =
      (12898 * (√12898 * c1F (exp (1 / 2) / 12) (Jz 12898)) * (186 / 10000)) /
        Jz 12898 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12898)]
  nlinarith

theorem row_energy_rule :
    (12898 : ℝ) * (12898 *
      (c2F (exp (1 / 2) / 12) (Jz 12898) * (186 / 10000) ^ 2 / Jz 12898)) ≤
      (141445801 / 40000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12898)]
  nlinarith

end BstLean.Part266.Row12898

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12898
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12898) (hc : A1 c ∈ BstLean.Part153.Eop 12898) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12898 : ℝ)) ≤ (12452421469 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12898 : ℝ) + 2 * √12898 ≤ (6562569363 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12898 : ℝ) ≤ (113569363 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12898)
    (hc : A1 c ∈ BstLean.Part153.Eop 12898) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12898 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12898 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12898))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12898) (K : Set (Ix 12898)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12898 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12898 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12898) (hw : WINDOW (paperDesignP 12898) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12898)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12898) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12898 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12898 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12898 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12898 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12898) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12898)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12898)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12898

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12898
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12898) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12898 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12898) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12898) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12898 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12898 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12898 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12898}
    (hw : WINDOW (paperDesignP 12898) c) (hc : c ∈ tableEvent) (K : Set (Ix 12898)) :
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

def proposedBaseEvent : Set (Ret 12898) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12898)) : Prop where
  charge : (retDist (paperCentres 12898)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12898)} (h : TablePayment H) :
    (retDist (paperCentres 12898)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12898)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12898

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12898
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12898) (i : Fin 4) (a : Ix 12898) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12898) (a : Ix 12898) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12898) : Prop where
  moment : ∀ i, MomentBound (muI 12898) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12898} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12898) 8 (actualFourError c i)
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

end BstLean.Part266.Row12898

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12898
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

structure LatitudeVarianceCertificate (c : Ret 12898) : Prop where
  location : LBound (muI 12898) 12
    (fun a => conditionalVariance (stdGauss (Fin (12898 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12898) 12
    (fun a => conditionalVariance (stdGauss (Fin (12898 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12898) (hw : WINDOW (paperDesignP 12898) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12898 4 (55 / 100) /
      (12898 : ℝ) / ((12898 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12898

/-! The dimension-12898 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12898
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12898) (wl ws : ℝ) : SplitData 12898 :=
  BstLean.Part162.dPaper (paperDesignP 12898) c wl ws
    (√(2 / (12898 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12898 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12898 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12898) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12898) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12898 : ℝ)) * eR c * 12898 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12898) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12898 - 1)))
    (rowSplit c wl ws).good a ∂muI 12898 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12898) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12898 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12898) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12898 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12898) c (rowSplit c wl ws),
    hellG2 12898 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12898 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12898} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12898} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12898 t c BstLean.Part266.agent12898.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12898} (R : RootSource t c) :
    |√(QStand (paperDesignP 12898) t c) - √(qTilde (paperDesignP 12898) t c)| ≤
      BstLean.Part266.agent12898.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12898

/-! Rational enclosures for the HQ fluctuation price at dimension 12899. -/
namespace BstLean.Part266.Row12899
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (817153953 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22892391 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12899 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12899 * A / 2 + D + L * √(A * D)) ≤ (2313757411 / 500000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12899 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((817153953 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12899 L e4 d4 ≤ (41923655441 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12899 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((817153953 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12899 L e6 d6 ≤ (6351312741 / 100000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12899 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((817153953 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12899 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12899 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12899 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12899 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22892391 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((2313757411 / 500000000000)) ^ 2 / 2 + ((2313757411 / 500000000000)) * ((41923655441 / 1000000000000)) ^ 2 / 6 +
      ((41923655441 / 1000000000000)) ^ 4 / 24 + ((41923655441 / 1000000000000)) ^ 2 * ((6351312741 / 100000000000)) ^ 3 / 120 +
      2187 * ((6351312741 / 100000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12899 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12899 : ℝ) * ((1 + 3 * ((22892391 / 1000000000))) / (4 * (1 - (22892391 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22892391 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12899 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22892391 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12899 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12899 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12899

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12899
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((28393441 / 250000) : ℝ) ≤ √12899 ∧ √12899 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1464986 : ℝ) ≤ Jz 12899 ∧ 1000000 ≤ Jz 12899 := by
  have hr : ((28393441 / 250000) : ℝ) ≤ √12899 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12899 : ℝ) * √12899 ≤ (⌈(12899 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12899
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12899 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12899 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12899 : ℝ) = (⌈(12899 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1464986 : ℝ) ≤ Jz 12899 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12899 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12899) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12899 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12899 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12899 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12899 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12899 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12899 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12899) :
    (12899 : ℝ) * (283 / 100 * 164 * (d / 2) / (√12899 * √(qB 12899))) ≤
      (271926241 / 500000000000) := by
  have hden : ((28393441 / 250000) : ℝ) * (63 / 100) ≤ √12899 * √(qB 12899) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12899 : ℝ) * √(qB 12899) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12899) :
    (12899 : ℝ) * (2 * (283 / 100 * 164) ^ 2 * (d / 2) /
      (12899 * √(qB 12899))) ≤ (177796563 / 40000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12899 : ℝ) * √(qB 12899) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12899 : ℝ) * (√12899 *
      (c1F (exp (1 / 2) / 12) (Jz 12899) * (186 / 10000) / Jz 12899)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12899)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12899 : ℝ) * (√12899 *
      (c1F (exp (1 / 2) / 12) (Jz 12899) * (186 / 10000) / Jz 12899)) =
      (12899 * (√12899 * c1F (exp (1 / 2) / 12) (Jz 12899)) * (186 / 10000)) /
        Jz 12899 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12899)]
  nlinarith

theorem row_energy_rule :
    (12899 : ℝ) * (12899 *
      (c2F (exp (1 / 2) / 12) (Jz 12899) * (186 / 10000) ^ 2 / Jz 12899)) ≤
      (1768141483 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12899)]
  nlinarith

end BstLean.Part266.Row12899

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12899
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12899) (hc : A1 c ∈ BstLean.Part153.Eop 12899) :
    BstLean.Part152.opN (A1 c) ≤ 164 := by
  refine hc.trans ?_
  have hs : √(2 / (12899 : ℝ)) ≤ (1245193877 / 100000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12899 : ℝ) + 2 * √12899 ≤ (1312614753 / 100000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12899 : ℝ) ≤ (22714753 / 200000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12899)
    (hc : A1 c ∈ BstLean.Part153.Eop 12899) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12899 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12899 * 164 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12899))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12899) (K : Set (Ix 12899)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12899 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12899 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12899) (hw : WINDOW (paperDesignP 12899) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12899)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12899) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12899 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12899 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12899 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12899 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12899) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12899)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12899)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12899

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12899
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12899) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12899 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12899) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12899) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12899 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12899 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12899 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12899}
    (hw : WINDOW (paperDesignP 12899) c) (hc : c ∈ tableEvent) (K : Set (Ix 12899)) :
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

def proposedBaseEvent : Set (Ret 12899) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12899)) : Prop where
  charge : (retDist (paperCentres 12899)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12899)} (h : TablePayment H) :
    (retDist (paperCentres 12899)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12899)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12899

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12899
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12899) (i : Fin 4) (a : Ix 12899) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12899) (a : Ix 12899) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12899) : Prop where
  moment : ∀ i, MomentBound (muI 12899) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12899} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12899) 8 (actualFourError c i)
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

end BstLean.Part266.Row12899

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12899
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

structure LatitudeVarianceCertificate (c : Ret 12899) : Prop where
  location : LBound (muI 12899) 12
    (fun a => conditionalVariance (stdGauss (Fin (12899 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12899) 12
    (fun a => conditionalVariance (stdGauss (Fin (12899 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12899) (hw : WINDOW (paperDesignP 12899) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12899 4 (55 / 100) /
      (12899 : ℝ) / ((12899 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12899

/-! The dimension-12899 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12899
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12899) (wl ws : ℝ) : SplitData 12899 :=
  BstLean.Part162.dPaper (paperDesignP 12899) c wl ws
    (√(2 / (12899 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12899 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12899 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12899) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12899) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12899 : ℝ)) * eR c * 12899 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12899) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12899 - 1)))
    (rowSplit c wl ws).good a ∂muI 12899 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12899) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12899 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12899) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12899 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12899) c (rowSplit c wl ws),
    hellG2 12899 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12899 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12899} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12899} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12899 t c BstLean.Part266.agent12899.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12899} (R : RootSource t c) :
    |√(QStand (paperDesignP 12899) t c) - √(qTilde (paperDesignP 12899) t c)| ≤
      BstLean.Part266.agent12899.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12899
