import BstLean.Part266Shard29Step1


/-! Rational enclosures for the HQ fluctuation price at dimension 13075. -/
namespace BstLean.Part266.Row13075
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1623249831 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22582223 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13075 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13075 * A / 2 + D + L * √(A * D)) ≤ (932591509 / 200000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13075 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1623249831 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13075 L e4 d4 ≤ (4224555643 / 100000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13075 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1623249831 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13075 L e6 d6 ≤ (31999729069 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13075 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1623249831 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13075 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13075 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13075 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13075 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22582223 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((932591509 / 200000000000)) ^ 2 / 2 + ((932591509 / 200000000000)) * ((4224555643 / 100000000000)) ^ 2 / 6 +
      ((4224555643 / 100000000000)) ^ 4 / 24 + ((4224555643 / 100000000000)) ^ 2 * ((31999729069 / 500000000000)) ^ 3 / 120 +
      2187 * ((31999729069 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13075 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13075 : ℝ) * ((1 + 3 * ((22582223 / 1000000000))) / (4 * (1 - (22582223 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22582223 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13075 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22582223 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13075 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13075 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13075

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13075
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((57172983 / 500000) : ℝ) ≤ √13075 ∧ √13075 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1495072 : ℝ) ≤ Jz 13075 ∧ 1000000 ≤ Jz 13075 := by
  have hr : ((57172983 / 500000) : ℝ) ≤ √13075 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13075 : ℝ) * √13075 ≤ (⌈(13075 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13075
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13075 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13075 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13075 : ℝ) = (⌈(13075 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1495072 : ℝ) ≤ Jz 13075 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13075 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13075) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13075 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13075 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13075 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13075 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13075 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13075 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13075) :
    (13075 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13075 * √(qB 13075))) ≤
      (550888919 / 1000000000000) := by
  have hden : ((57172983 / 500000) : ℝ) * (63 / 100) ≤ √13075 * √(qB 13075) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13075 : ℝ) * √(qB 13075) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13075) :
    (13075 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13075 * √(qB 13075))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13075 : ℝ) * √(qB 13075) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13075 : ℝ) * (√13075 *
      (c1F (exp (1 / 2) / 12) (Jz 13075) * (186 / 10000) / Jz 13075)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13075)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13075 : ℝ) * (√13075 *
      (c1F (exp (1 / 2) / 12) (Jz 13075) * (186 / 10000) / Jz 13075)) =
      (13075 * (√13075 * c1F (exp (1 / 2) / 12) (Jz 13075)) * (186 / 10000)) /
        Jz 13075 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13075)]
  nlinarith

theorem row_energy_rule :
    (13075 : ℝ) * (13075 *
      (c2F (exp (1 / 2) / 12) (Jz 13075) * (186 / 10000) ^ 2 / Jz 13075)) ≤
      (1780162669 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13075)]
  nlinarith

end BstLean.Part266.Row13075

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13075
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13075) (hc : A1 c ∈ BstLean.Part153.Eop 13075) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13075 : ℝ)) ≤ (12367848283 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13075 : ℝ) + 2 * √13075 ≤ (6651845967 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13075 : ℝ) ≤ (114345967 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13075)
    (hc : A1 c ∈ BstLean.Part153.Eop 13075) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13075 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13075 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13075))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13075) (K : Set (Ix 13075)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13075 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13075 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13075) (hw : WINDOW (paperDesignP 13075) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13075)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13075) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13075 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13075 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13075 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13075 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13075) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13075)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13075)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13075

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13075
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13075) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13075 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13075) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13075) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13075 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13075 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13075 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13075}
    (hw : WINDOW (paperDesignP 13075) c) (hc : c ∈ tableEvent) (K : Set (Ix 13075)) :
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

def proposedBaseEvent : Set (Ret 13075) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13075)) : Prop where
  charge : (retDist (paperCentres 13075)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13075)} (h : TablePayment H) :
    (retDist (paperCentres 13075)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13075)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13075

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13075
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13075) (i : Fin 4) (a : Ix 13075) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13075) (a : Ix 13075) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13075) : Prop where
  moment : ∀ i, MomentBound (muI 13075) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13075} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13075) 8 (actualFourError c i)
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

end BstLean.Part266.Row13075

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13075
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

structure LatitudeVarianceCertificate (c : Ret 13075) : Prop where
  location : LBound (muI 13075) 12
    (fun a => conditionalVariance (stdGauss (Fin (13075 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13075) 12
    (fun a => conditionalVariance (stdGauss (Fin (13075 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13075) (hw : WINDOW (paperDesignP 13075) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13075 4 (55 / 100) /
      (13075 : ℝ) / ((13075 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13075

/-! The dimension-13075 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13075
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13075) (wl ws : ℝ) : SplitData 13075 :=
  BstLean.Part162.dPaper (paperDesignP 13075) c wl ws
    (√(2 / (13075 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13075 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13075 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13075) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13075) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13075 : ℝ)) * eR c * 13075 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13075) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13075 - 1)))
    (rowSplit c wl ws).good a ∂muI 13075 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13075) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13075 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13075) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13075 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13075) c (rowSplit c wl ws),
    hellG2 13075 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13075 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13075} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13075} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13075 t c BstLean.Part266.agent13075.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13075} (R : RootSource t c) :
    |√(QStand (paperDesignP 13075) t c) - √(qTilde (paperDesignP 13075) t c)| ≤
      BstLean.Part266.agent13075.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13075

/-! Rational enclosures for the HQ fluctuation price at dimension 13076. -/
namespace BstLean.Part266.Row13076
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (81159389 / 50000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22580487 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13076 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13076 * A / 2 + D + L * √(A * D)) ≤ (4663158947 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13076 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((81159389 / 50000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13076 L e4 d4 ≤ (10561846403 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13076 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((81159389 / 50000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13076 L e6 d6 ≤ (32001110841 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13076 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((81159389 / 50000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13076 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13076 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13076 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13076 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22580487 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4663158947 / 1000000000000)) ^ 2 / 2 + ((4663158947 / 1000000000000)) * ((10561846403 / 250000000000)) ^ 2 / 6 +
      ((10561846403 / 250000000000)) ^ 4 / 24 + ((10561846403 / 250000000000)) ^ 2 * ((32001110841 / 500000000000)) ^ 3 / 120 +
      2187 * ((32001110841 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13076 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13076 : ℝ) * ((1 + 3 * ((22580487 / 1000000000))) / (4 * (1 - (22580487 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22580487 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13076 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22580487 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13076 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13076 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13076

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13076
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((57175169 / 500000) : ℝ) ≤ √13076 ∧ √13076 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1495244 : ℝ) ≤ Jz 13076 ∧ 1000000 ≤ Jz 13076 := by
  have hr : ((57175169 / 500000) : ℝ) ≤ √13076 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13076 : ℝ) * √13076 ≤ (⌈(13076 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13076
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13076 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13076 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13076 : ℝ) = (⌈(13076 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1495244 : ℝ) ≤ Jz 13076 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13076 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13076) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13076 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13076 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13076 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13076 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13076 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13076 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13076) :
    (13076 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13076 * √(qB 13076))) ≤
      (137727497 / 250000000000) := by
  have hden : ((57175169 / 500000) : ℝ) * (63 / 100) ≤ √13076 * √(qB 13076) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13076 : ℝ) * √(qB 13076) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13076) :
    (13076 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13076 * √(qB 13076))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13076 : ℝ) * √(qB 13076) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13076 : ℝ) * (√13076 *
      (c1F (exp (1 / 2) / 12) (Jz 13076) * (186 / 10000) / Jz 13076)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13076)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13076 : ℝ) * (√13076 *
      (c1F (exp (1 / 2) / 12) (Jz 13076) * (186 / 10000) / Jz 13076)) =
      (13076 * (√13076 * c1F (exp (1 / 2) / 12) (Jz 13076)) * (186 / 10000)) /
        Jz 13076 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13076)]
  nlinarith

theorem row_energy_rule :
    (13076 : ℝ) * (13076 *
      (c2F (exp (1 / 2) / 12) (Jz 13076) * (186 / 10000) ^ 2 / Jz 13076)) ≤
      (3560460347 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13076)]
  nlinarith

end BstLean.Part266.Row13076

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13076
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13076) (hc : A1 c ∈ BstLean.Part153.Eop 13076) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13076 : ℝ)) ≤ (1545921919 / 125000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13076 : ℝ) + 2 * √13076 ≤ (6652350339 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13076 : ℝ) ≤ (114350339 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13076)
    (hc : A1 c ∈ BstLean.Part153.Eop 13076) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13076 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13076 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13076))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13076) (K : Set (Ix 13076)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13076 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13076 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13076) (hw : WINDOW (paperDesignP 13076) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13076)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13076) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13076 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13076 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13076 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13076 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13076) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13076)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13076)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13076

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13076
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13076) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13076 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13076) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13076) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13076 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13076 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13076 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13076}
    (hw : WINDOW (paperDesignP 13076) c) (hc : c ∈ tableEvent) (K : Set (Ix 13076)) :
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

def proposedBaseEvent : Set (Ret 13076) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13076)) : Prop where
  charge : (retDist (paperCentres 13076)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13076)} (h : TablePayment H) :
    (retDist (paperCentres 13076)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13076)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13076

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13076
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13076) (i : Fin 4) (a : Ix 13076) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13076) (a : Ix 13076) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13076) : Prop where
  moment : ∀ i, MomentBound (muI 13076) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13076} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13076) 8 (actualFourError c i)
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

end BstLean.Part266.Row13076

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13076
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

structure LatitudeVarianceCertificate (c : Ret 13076) : Prop where
  location : LBound (muI 13076) 12
    (fun a => conditionalVariance (stdGauss (Fin (13076 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13076) 12
    (fun a => conditionalVariance (stdGauss (Fin (13076 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13076) (hw : WINDOW (paperDesignP 13076) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13076 4 (55 / 100) /
      (13076 : ℝ) / ((13076 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13076

/-! The dimension-13076 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13076
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13076) (wl ws : ℝ) : SplitData 13076 :=
  BstLean.Part162.dPaper (paperDesignP 13076) c wl ws
    (√(2 / (13076 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13076 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13076 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13076) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13076) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13076 : ℝ)) * eR c * 13076 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13076) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13076 - 1)))
    (rowSplit c wl ws).good a ∂muI 13076 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13076) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13076 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13076) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13076 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13076) c (rowSplit c wl ws),
    hellG2 13076 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13076 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13076} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13076} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13076 t c BstLean.Part266.agent13076.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13076} (R : RootSource t c) :
    |√(QStand (paperDesignP 13076) t c) - √(qTilde (paperDesignP 13076) t c)| ≤
      BstLean.Part266.agent13076.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13076

/-! Rational enclosures for the HQ fluctuation price at dimension 13077. -/
namespace BstLean.Part266.Row13077
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (324625093 / 200000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22578747 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13077 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13077 * A / 2 + D + L * √(A * D)) ≤ (4663360341 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13077 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((324625093 / 200000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13077 L e4 d4 ≤ (42249214727 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13077 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((324625093 / 200000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13077 L e6 d6 ≤ (512039881 / 8000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13077 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((324625093 / 200000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13077 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13077 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13077 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13077 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22578747 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4663360341 / 1000000000000)) ^ 2 / 2 + ((4663360341 / 1000000000000)) * ((42249214727 / 1000000000000)) ^ 2 / 6 +
      ((42249214727 / 1000000000000)) ^ 4 / 24 + ((42249214727 / 1000000000000)) ^ 2 * ((512039881 / 8000000000)) ^ 3 / 120 +
      2187 * ((512039881 / 8000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13077 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13077 : ℝ) * ((1 + 3 * ((22578747 / 1000000000))) / (4 * (1 - (22578747 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22578747 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13077 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22578747 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13077 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13077 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13077

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13077
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((114354711 / 1000000) : ℝ) ≤ √13077 ∧ √13077 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1495415 : ℝ) ≤ Jz 13077 ∧ 1000000 ≤ Jz 13077 := by
  have hr : ((114354711 / 1000000) : ℝ) ≤ √13077 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13077 : ℝ) * √13077 ≤ (⌈(13077 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13077
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13077 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13077 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13077 : ℝ) = (⌈(13077 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1495415 : ℝ) ≤ Jz 13077 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13077 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13077) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13077 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13077 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13077 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13077 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13077 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13077 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13077) :
    (13077 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13077 * √(qB 13077))) ≤
      (550931051 / 1000000000000) := by
  have hden : ((114354711 / 1000000) : ℝ) * (63 / 100) ≤ √13077 * √(qB 13077) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13077 : ℝ) * √(qB 13077) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13077) :
    (13077 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13077 * √(qB 13077))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13077 : ℝ) * √(qB 13077) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13077 : ℝ) * (√13077 *
      (c1F (exp (1 / 2) / 12) (Jz 13077) * (186 / 10000) / Jz 13077)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13077)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13077 : ℝ) * (√13077 *
      (c1F (exp (1 / 2) / 12) (Jz 13077) * (186 / 10000) / Jz 13077)) =
      (13077 * (√13077 * c1F (exp (1 / 2) / 12) (Jz 13077)) * (186 / 10000)) /
        Jz 13077 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13077)]
  nlinarith

theorem row_energy_rule :
    (13077 : ℝ) * (13077 *
      (c2F (exp (1 / 2) / 12) (Jz 13077) * (186 / 10000) ^ 2 / Jz 13077)) ≤
      (890149437 / 250000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13077)]
  nlinarith

end BstLean.Part266.Row13077

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13077
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13077) (hc : A1 c ∈ BstLean.Part153.Eop 13077) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13077 : ℝ)) ≤ (494676099 / 40000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13077 : ℝ) + 2 * √13077 ≤ (831606839 / 62500) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13077 : ℝ) ≤ (14294339 / 125000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13077)
    (hc : A1 c ∈ BstLean.Part153.Eop 13077) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13077 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13077 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13077))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13077) (K : Set (Ix 13077)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13077 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13077 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13077) (hw : WINDOW (paperDesignP 13077) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13077)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13077) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13077 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13077 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13077 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13077 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13077) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13077)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13077)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13077

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13077
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13077) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13077 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13077) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13077) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13077 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13077 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13077 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13077}
    (hw : WINDOW (paperDesignP 13077) c) (hc : c ∈ tableEvent) (K : Set (Ix 13077)) :
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

def proposedBaseEvent : Set (Ret 13077) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13077)) : Prop where
  charge : (retDist (paperCentres 13077)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13077)} (h : TablePayment H) :
    (retDist (paperCentres 13077)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13077)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13077

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13077
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13077) (i : Fin 4) (a : Ix 13077) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13077) (a : Ix 13077) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13077) : Prop where
  moment : ∀ i, MomentBound (muI 13077) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13077} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13077) 8 (actualFourError c i)
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

end BstLean.Part266.Row13077

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13077
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

structure LatitudeVarianceCertificate (c : Ret 13077) : Prop where
  location : LBound (muI 13077) 12
    (fun a => conditionalVariance (stdGauss (Fin (13077 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13077) 12
    (fun a => conditionalVariance (stdGauss (Fin (13077 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13077) (hw : WINDOW (paperDesignP 13077) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13077 4 (55 / 100) /
      (13077 : ℝ) / ((13077 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13077

/-! The dimension-13077 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13077
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13077) (wl ws : ℝ) : SplitData 13077 :=
  BstLean.Part162.dPaper (paperDesignP 13077) c wl ws
    (√(2 / (13077 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13077 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13077 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13077) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13077) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13077 : ℝ)) * eR c * 13077 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13077) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13077 - 1)))
    (rowSplit c wl ws).good a ∂muI 13077 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13077) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13077 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13077) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13077 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13077) c (rowSplit c wl ws),
    hellG2 13077 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13077 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13077} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13077} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13077 t c BstLean.Part266.agent13077.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13077} (R : RootSource t c) :
    |√(QStand (paperDesignP 13077) t c) - √(qTilde (paperDesignP 13077) t c)| ≤
      BstLean.Part266.agent13077.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13077

/-! Rational enclosures for the HQ fluctuation price at dimension 13078. -/
namespace BstLean.Part266.Row13078
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1623063443 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (5644253 / 250000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13078 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13078 * A / 2 + D + L * √(A * D)) ≤ (4663561743 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13078 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1623063443 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13078 L e4 d4 ≤ (10562760979 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13078 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1623063443 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13078 L e6 d6 ≤ (1600193717 / 25000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13078 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1623063443 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13078 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13078 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13078 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13078 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (5644253 / 250000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4663561743 / 1000000000000)) ^ 2 / 2 + ((4663561743 / 1000000000000)) * ((10562760979 / 250000000000)) ^ 2 / 6 +
      ((10562760979 / 250000000000)) ^ 4 / 24 + ((10562760979 / 250000000000)) ^ 2 * ((1600193717 / 25000000000)) ^ 3 / 120 +
      2187 * ((1600193717 / 25000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13078 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13078 : ℝ) * ((1 + 3 * ((5644253 / 250000000))) / (4 * (1 - (5644253 / 250000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (5644253 / 250000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13078 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (5644253 / 250000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13078 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13078 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13078

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13078
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((114359083 / 1000000) : ℝ) ≤ √13078 ∧ √13078 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1495587 : ℝ) ≤ Jz 13078 ∧ 1000000 ≤ Jz 13078 := by
  have hr : ((114359083 / 1000000) : ℝ) ≤ √13078 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13078 : ℝ) * √13078 ≤ (⌈(13078 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13078
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13078 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13078 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13078 : ℝ) = (⌈(13078 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1495587 : ℝ) ≤ Jz 13078 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13078 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13078) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13078 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13078 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13078 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13078 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13078 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13078 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13078) :
    (13078 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13078 * √(qB 13078))) ≤
      (550952117 / 1000000000000) := by
  have hden : ((114359083 / 1000000) : ℝ) * (63 / 100) ≤ √13078 * √(qB 13078) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13078 : ℝ) * √(qB 13078) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13078) :
    (13078 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13078 * √(qB 13078))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13078 : ℝ) * √(qB 13078) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13078 : ℝ) * (√13078 *
      (c1F (exp (1 / 2) / 12) (Jz 13078) * (186 / 10000) / Jz 13078)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13078)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13078 : ℝ) * (√13078 *
      (c1F (exp (1 / 2) / 12) (Jz 13078) * (186 / 10000) / Jz 13078)) =
      (13078 * (√13078 * c1F (exp (1 / 2) / 12) (Jz 13078)) * (186 / 10000)) /
        Jz 13078 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13078)]
  nlinarith

theorem row_energy_rule :
    (13078 : ℝ) * (13078 *
      (c2F (exp (1 / 2) / 12) (Jz 13078) * (186 / 10000) ^ 2 / Jz 13078)) ≤
      (1780366389 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13078)]
  nlinarith

end BstLean.Part266.Row13078

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13078
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13078) (hc : A1 c ∈ BstLean.Part153.Eop 13078) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13078 : ℝ)) ≤ (12366429653 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13078 : ℝ) + 2 * √13078 ≤ (1663339771 / 125000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13078 : ℝ) ≤ (28589771 / 250000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13078)
    (hc : A1 c ∈ BstLean.Part153.Eop 13078) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13078 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13078 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13078))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13078) (K : Set (Ix 13078)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13078 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13078 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13078) (hw : WINDOW (paperDesignP 13078) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13078)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13078) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13078 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13078 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13078 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13078 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13078) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13078)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13078)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13078

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13078
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13078) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13078 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13078) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13078) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13078 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13078 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13078 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13078}
    (hw : WINDOW (paperDesignP 13078) c) (hc : c ∈ tableEvent) (K : Set (Ix 13078)) :
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

def proposedBaseEvent : Set (Ret 13078) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13078)) : Prop where
  charge : (retDist (paperCentres 13078)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13078)} (h : TablePayment H) :
    (retDist (paperCentres 13078)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13078)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13078

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13078
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13078) (i : Fin 4) (a : Ix 13078) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13078) (a : Ix 13078) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13078) : Prop where
  moment : ∀ i, MomentBound (muI 13078) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13078} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13078) 8 (actualFourError c i)
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

end BstLean.Part266.Row13078

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13078
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

structure LatitudeVarianceCertificate (c : Ret 13078) : Prop where
  location : LBound (muI 13078) 12
    (fun a => conditionalVariance (stdGauss (Fin (13078 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13078) 12
    (fun a => conditionalVariance (stdGauss (Fin (13078 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13078) (hw : WINDOW (paperDesignP 13078) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13078 4 (55 / 100) /
      (13078 : ℝ) / ((13078 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13078

/-! The dimension-13078 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13078
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13078) (wl ws : ℝ) : SplitData 13078 :=
  BstLean.Part162.dPaper (paperDesignP 13078) c wl ws
    (√(2 / (13078 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13078 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13078 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13078) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13078) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13078 : ℝ)) * eR c * 13078 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13078) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13078 - 1)))
    (rowSplit c wl ws).good a ∂muI 13078 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13078) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13078 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13078) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13078 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13078) c (rowSplit c wl ws),
    hellG2 13078 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13078 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13078} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13078} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13078 t c BstLean.Part266.agent13078.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13078} (R : RootSource t c) :
    |√(QStand (paperDesignP 13078) t c) - √(qTilde (paperDesignP 13078) t c)| ≤
      BstLean.Part266.agent13078.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13078

/-! Rational enclosures for the HQ fluctuation price at dimension 13079. -/
namespace BstLean.Part266.Row13079
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1623001157 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (2821909 / 125000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13079 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13079 * A / 2 + D + L * √(A * D)) ≤ (2331881569 / 500000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13079 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1623001157 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13079 L e4 d4 ≤ (21126436519 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13079 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1623001157 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13079 L e6 d6 ≤ (32005256067 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13079 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1623001157 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13079 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13079 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13079 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13079 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (2821909 / 125000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((2331881569 / 500000000000)) ^ 2 / 2 + ((2331881569 / 500000000000)) * ((21126436519 / 500000000000)) ^ 2 / 6 +
      ((21126436519 / 500000000000)) ^ 4 / 24 + ((21126436519 / 500000000000)) ^ 2 * ((32005256067 / 500000000000)) ^ 3 / 120 +
      2187 * ((32005256067 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13079 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13079 : ℝ) * ((1 + 3 * ((2821909 / 125000000))) / (4 * (1 - (2821909 / 125000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (2821909 / 125000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13079 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (2821909 / 125000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13079 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13079 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13079

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13079
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((22872691 / 200000) : ℝ) ≤ √13079 ∧ √13079 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1495758 : ℝ) ≤ Jz 13079 ∧ 1000000 ≤ Jz 13079 := by
  have hr : ((22872691 / 200000) : ℝ) ≤ √13079 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13079 : ℝ) * √13079 ≤ (⌈(13079 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13079
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13079 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13079 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13079 : ℝ) = (⌈(13079 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1495758 : ℝ) ≤ Jz 13079 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13079 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13079) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13079 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13079 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13079 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13079 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13079 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13079 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13079) :
    (13079 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13079 * √(qB 13079))) ≤
      (550973181 / 1000000000000) := by
  have hden : ((22872691 / 200000) : ℝ) * (63 / 100) ≤ √13079 * √(qB 13079) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13079 : ℝ) * √(qB 13079) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13079) :
    (13079 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13079 * √(qB 13079))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13079 : ℝ) * √(qB 13079) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13079 : ℝ) * (√13079 *
      (c1F (exp (1 / 2) / 12) (Jz 13079) * (186 / 10000) / Jz 13079)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13079)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13079 : ℝ) * (√13079 *
      (c1F (exp (1 / 2) / 12) (Jz 13079) * (186 / 10000) / Jz 13079)) =
      (13079 * (√13079 * c1F (exp (1 / 2) / 12) (Jz 13079)) * (186 / 10000)) /
        Jz 13079 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13079)]
  nlinarith

theorem row_energy_rule :
    (13079 : ℝ) * (13079 *
      (c2F (exp (1 / 2) / 12) (Jz 13079) * (186 / 10000) ^ 2 / Jz 13079)) ≤
      (17804351 / 5000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13079)]
  nlinarith

end BstLean.Part266.Row13079

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13079
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13079) (hc : A1 c ∈ BstLean.Part153.Eop 13079) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13079 : ℝ)) ≤ (2473191377 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13079 : ℝ) + 2 * √13079 ≤ (207933233 / 15625) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13079 : ℝ) ≤ (1786929 / 15625))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13079)
    (hc : A1 c ∈ BstLean.Part153.Eop 13079) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13079 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13079 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13079))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13079) (K : Set (Ix 13079)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13079 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13079 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13079) (hw : WINDOW (paperDesignP 13079) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13079)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13079) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13079 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13079 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13079 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13079 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13079) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13079)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13079)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13079

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13079
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13079) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13079 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13079) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13079) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13079 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13079 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13079 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13079}
    (hw : WINDOW (paperDesignP 13079) c) (hc : c ∈ tableEvent) (K : Set (Ix 13079)) :
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

def proposedBaseEvent : Set (Ret 13079) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13079)) : Prop where
  charge : (retDist (paperCentres 13079)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13079)} (h : TablePayment H) :
    (retDist (paperCentres 13079)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13079)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13079

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13079
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13079) (i : Fin 4) (a : Ix 13079) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13079) (a : Ix 13079) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13079) : Prop where
  moment : ∀ i, MomentBound (muI 13079) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13079} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13079) 8 (actualFourError c i)
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

end BstLean.Part266.Row13079

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13079
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

structure LatitudeVarianceCertificate (c : Ret 13079) : Prop where
  location : LBound (muI 13079) 12
    (fun a => conditionalVariance (stdGauss (Fin (13079 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13079) 12
    (fun a => conditionalVariance (stdGauss (Fin (13079 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13079) (hw : WINDOW (paperDesignP 13079) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13079 4 (55 / 100) /
      (13079 : ℝ) / ((13079 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13079

/-! The dimension-13079 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13079
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13079) (wl ws : ℝ) : SplitData 13079 :=
  BstLean.Part162.dPaper (paperDesignP 13079) c wl ws
    (√(2 / (13079 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13079 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13079 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13079) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13079) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13079 : ℝ)) * eR c * 13079 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13079) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13079 - 1)))
    (rowSplit c wl ws).good a ∂muI 13079 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13079) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13079 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13079) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13079 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13079) c (rowSplit c wl ws),
    hellG2 13079 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13079 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13079} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13079} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13079 t c BstLean.Part266.agent13079.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13079} (R : RootSource t c) :
    |√(QStand (paperDesignP 13079) t c) - √(qTilde (paperDesignP 13079) t c)| ≤
      BstLean.Part266.agent13079.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13079

/-! Rational enclosures for the HQ fluctuation price at dimension 13080. -/
namespace BstLean.Part266.Row13080
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (405734791 / 250000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11286769 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13080 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13080 * A / 2 + D + L * √(A * D)) ≤ (4663964541 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13080 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((405734791 / 250000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13080 L e4 d4 ≤ (8450940447 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13080 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((405734791 / 250000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13080 L e6 d6 ≤ (64013275701 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13080 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((405734791 / 250000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13080 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13080 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13080 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13080 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11286769 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4663964541 / 1000000000000)) ^ 2 / 2 + ((4663964541 / 1000000000000)) * ((8450940447 / 200000000000)) ^ 2 / 6 +
      ((8450940447 / 200000000000)) ^ 4 / 24 + ((8450940447 / 200000000000)) ^ 2 * ((64013275701 / 1000000000000)) ^ 3 / 120 +
      2187 * ((64013275701 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13080 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13080 : ℝ) * ((1 + 3 * ((11286769 / 500000000))) / (4 * (1 - (11286769 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11286769 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13080 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11286769 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13080 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13080 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13080

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13080
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((114367827 / 1000000) : ℝ) ≤ √13080 ∧ √13080 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1495930 : ℝ) ≤ Jz 13080 ∧ 1000000 ≤ Jz 13080 := by
  have hr : ((114367827 / 1000000) : ℝ) ≤ √13080 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13080 : ℝ) * √13080 ≤ (⌈(13080 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13080
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13080 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13080 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13080 : ℝ) = (⌈(13080 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1495930 : ℝ) ≤ Jz 13080 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13080 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13080) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13080 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13080 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13080 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13080 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13080 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13080 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13080) :
    (13080 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13080 * √(qB 13080))) ≤
      (137748561 / 250000000000) := by
  have hden : ((114367827 / 1000000) : ℝ) * (63 / 100) ≤ √13080 * √(qB 13080) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13080 : ℝ) * √(qB 13080) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13080) :
    (13080 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13080 * √(qB 13080))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13080 : ℝ) * √(qB 13080) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13080 : ℝ) * (√13080 *
      (c1F (exp (1 / 2) / 12) (Jz 13080) * (186 / 10000) / Jz 13080)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13080)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13080 : ℝ) * (√13080 *
      (c1F (exp (1 / 2) / 12) (Jz 13080) * (186 / 10000) / Jz 13080)) =
      (13080 * (√13080 * c1F (exp (1 / 2) / 12) (Jz 13080)) * (186 / 10000)) /
        Jz 13080 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13080)]
  nlinarith

theorem row_energy_rule :
    (13080 : ℝ) * (13080 *
      (c2F (exp (1 / 2) / 12) (Jz 13080) * (186 / 10000) ^ 2 / Jz 13080)) ≤
      (3561005251 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13080)]
  nlinarith

end BstLean.Part266.Row13080

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13080
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13080) (hc : A1 c ∈ BstLean.Part153.Eop 13080) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13080 : ℝ)) ≤ (12365484171 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13080 : ℝ) + 2 * √13080 ≤ (1663591957 / 125000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13080 : ℝ) ≤ (28591957 / 250000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13080)
    (hc : A1 c ∈ BstLean.Part153.Eop 13080) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13080 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13080 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13080))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13080) (K : Set (Ix 13080)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13080 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13080 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13080) (hw : WINDOW (paperDesignP 13080) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13080)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13080) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13080 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13080 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13080 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13080 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13080) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13080)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13080)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13080

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13080
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13080) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13080 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13080) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13080) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13080 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13080 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13080 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13080}
    (hw : WINDOW (paperDesignP 13080) c) (hc : c ∈ tableEvent) (K : Set (Ix 13080)) :
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

def proposedBaseEvent : Set (Ret 13080) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13080)) : Prop where
  charge : (retDist (paperCentres 13080)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13080)} (h : TablePayment H) :
    (retDist (paperCentres 13080)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13080)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13080

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13080
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13080) (i : Fin 4) (a : Ix 13080) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13080) (a : Ix 13080) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13080) : Prop where
  moment : ∀ i, MomentBound (muI 13080) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13080} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13080) 8 (actualFourError c i)
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

end BstLean.Part266.Row13080

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13080
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

structure LatitudeVarianceCertificate (c : Ret 13080) : Prop where
  location : LBound (muI 13080) 12
    (fun a => conditionalVariance (stdGauss (Fin (13080 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13080) 12
    (fun a => conditionalVariance (stdGauss (Fin (13080 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13080) (hw : WINDOW (paperDesignP 13080) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13080 4 (55 / 100) /
      (13080 : ℝ) / ((13080 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13080

/-! The dimension-13080 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13080
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13080) (wl ws : ℝ) : SplitData 13080 :=
  BstLean.Part162.dPaper (paperDesignP 13080) c wl ws
    (√(2 / (13080 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13080 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13080 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13080) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13080) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13080 : ℝ)) * eR c * 13080 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13080) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13080 - 1)))
    (rowSplit c wl ws).good a ∂muI 13080 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13080) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13080 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13080) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13080 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13080) c (rowSplit c wl ws),
    hellG2 13080 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13080 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13080} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13080} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13080 t c BstLean.Part266.agent13080.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13080} (R : RootSource t c) :
    |√(QStand (paperDesignP 13080) t c) - √(qTilde (paperDesignP 13080) t c)| ≤
      BstLean.Part266.agent13080.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13080

/-! Rational enclosures for the HQ fluctuation price at dimension 13081. -/
namespace BstLean.Part266.Row13081
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (324575381 / 200000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22571799 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13081 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13081 * A / 2 + D + L * √(A * D)) ≤ (4664165937 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13081 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((324575381 / 200000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13081 L e4 d4 ≤ (10564132841 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13081 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((324575381 / 200000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13081 L e6 d6 ≤ (12803207833 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13081 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((324575381 / 200000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13081 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13081 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13081 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13081 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22571799 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4664165937 / 1000000000000)) ^ 2 / 2 + ((4664165937 / 1000000000000)) * ((10564132841 / 250000000000)) ^ 2 / 6 +
      ((10564132841 / 250000000000)) ^ 4 / 24 + ((10564132841 / 250000000000)) ^ 2 * ((12803207833 / 200000000000)) ^ 3 / 120 +
      2187 * ((12803207833 / 200000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13081 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13081 : ℝ) * ((1 + 3 * ((22571799 / 1000000000))) / (4 * (1 - (22571799 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22571799 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13081 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22571799 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13081 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13081 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13081

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13081
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((114372199 / 1000000) : ℝ) ≤ √13081 ∧ √13081 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1496101 : ℝ) ≤ Jz 13081 ∧ 1000000 ≤ Jz 13081 := by
  have hr : ((114372199 / 1000000) : ℝ) ≤ √13081 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13081 : ℝ) * √13081 ≤ (⌈(13081 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13081
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13081 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13081 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13081 : ℝ) = (⌈(13081 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1496101 : ℝ) ≤ Jz 13081 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13081 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13081) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13081 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13081 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13081 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13081 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13081 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13081 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13081) :
    (13081 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13081 * √(qB 13081))) ≤
      (110203061 / 200000000000) := by
  have hden : ((114372199 / 1000000) : ℝ) * (63 / 100) ≤ √13081 * √(qB 13081) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13081 : ℝ) * √(qB 13081) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13081) :
    (13081 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13081 * √(qB 13081))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13081 : ℝ) * √(qB 13081) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13081 : ℝ) * (√13081 *
      (c1F (exp (1 / 2) / 12) (Jz 13081) * (186 / 10000) / Jz 13081)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13081)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13081 : ℝ) * (√13081 *
      (c1F (exp (1 / 2) / 12) (Jz 13081) * (186 / 10000) / Jz 13081)) =
      (13081 * (√13081 * c1F (exp (1 / 2) / 12) (Jz 13081)) * (186 / 10000)) /
        Jz 13081 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13081)]
  nlinarith

theorem row_energy_rule :
    (13081 : ℝ) * (13081 *
      (c2F (exp (1 / 2) / 12) (Jz 13081) * (186 / 10000) ^ 2 / Jz 13081)) ≤
      (1780571347 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13081)]
  nlinarith

end BstLean.Part266.Row13081

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13081
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13081) (hc : A1 c ∈ BstLean.Part153.Eop 13081) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13081 : ℝ)) ≤ (1545626439 / 125000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13081 : ℝ) + 2 * √13081 ≤ (33274361 / 2500) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13081 : ℝ) ≤ (571861 / 5000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13081)
    (hc : A1 c ∈ BstLean.Part153.Eop 13081) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13081 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13081 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13081))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13081) (K : Set (Ix 13081)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13081 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13081 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13081) (hw : WINDOW (paperDesignP 13081) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13081)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13081) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13081 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13081 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13081 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13081 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13081) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13081)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13081)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13081

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13081
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13081) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13081 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13081) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13081) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13081 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13081 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13081 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13081}
    (hw : WINDOW (paperDesignP 13081) c) (hc : c ∈ tableEvent) (K : Set (Ix 13081)) :
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

def proposedBaseEvent : Set (Ret 13081) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13081)) : Prop where
  charge : (retDist (paperCentres 13081)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13081)} (h : TablePayment H) :
    (retDist (paperCentres 13081)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13081)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13081

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13081
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13081) (i : Fin 4) (a : Ix 13081) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13081) (a : Ix 13081) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13081) : Prop where
  moment : ∀ i, MomentBound (muI 13081) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13081} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13081) 8 (actualFourError c i)
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

end BstLean.Part266.Row13081

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13081
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

structure LatitudeVarianceCertificate (c : Ret 13081) : Prop where
  location : LBound (muI 13081) 12
    (fun a => conditionalVariance (stdGauss (Fin (13081 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13081) 12
    (fun a => conditionalVariance (stdGauss (Fin (13081 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13081) (hw : WINDOW (paperDesignP 13081) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13081 4 (55 / 100) /
      (13081 : ℝ) / ((13081 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13081

/-! The dimension-13081 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13081
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13081) (wl ws : ℝ) : SplitData 13081 :=
  BstLean.Part162.dPaper (paperDesignP 13081) c wl ws
    (√(2 / (13081 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13081 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13081 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13081) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13081) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13081 : ℝ)) * eR c * 13081 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13081) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13081 - 1)))
    (rowSplit c wl ws).good a ∂muI 13081 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13081) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13081 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13081) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13081 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13081) c (rowSplit c wl ws),
    hellG2 13081 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13081 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13081} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13081} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13081 t c BstLean.Part266.agent13081.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13081} (R : RootSource t c) :
    |√(QStand (paperDesignP 13081) t c) - √(qTilde (paperDesignP 13081) t c)| ≤
      BstLean.Part266.agent13081.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13081

/-! Rational enclosures for the HQ fluctuation price at dimension 13082. -/
namespace BstLean.Part266.Row13082
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (811407331 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22570061 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13082 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13082 * A / 2 + D + L * √(A * D)) ≤ (4664367333 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13082 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((811407331 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13082 L e4 d4 ≤ (42258360497 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13082 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((811407331 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13082 L e6 d6 ≤ (12803760527 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13082 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((811407331 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13082 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13082 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13082 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13082 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22570061 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4664367333 / 1000000000000)) ^ 2 / 2 + ((4664367333 / 1000000000000)) * ((42258360497 / 1000000000000)) ^ 2 / 6 +
      ((42258360497 / 1000000000000)) ^ 4 / 24 + ((42258360497 / 1000000000000)) ^ 2 * ((12803760527 / 200000000000)) ^ 3 / 120 +
      2187 * ((12803760527 / 200000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13082 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13082 : ℝ) * ((1 + 3 * ((22570061 / 1000000000))) / (4 * (1 - (22570061 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22570061 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13082 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22570061 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13082 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13082 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13082

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13082
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((114376571 / 1000000) : ℝ) ≤ √13082 ∧ √13082 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1496273 : ℝ) ≤ Jz 13082 ∧ 1000000 ≤ Jz 13082 := by
  have hr : ((114376571 / 1000000) : ℝ) ≤ √13082 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13082 : ℝ) * √13082 ≤ (⌈(13082 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13082
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13082 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13082 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13082 : ℝ) = (⌈(13082 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1496273 : ℝ) ≤ Jz 13082 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13082 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13082) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13082 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13082 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13082 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13082 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13082 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13082 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13082) :
    (13082 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13082 * √(qB 13082))) ≤
      (137759091 / 250000000000) := by
  have hden : ((114376571 / 1000000) : ℝ) * (63 / 100) ≤ √13082 * √(qB 13082) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13082 : ℝ) * √(qB 13082) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13082) :
    (13082 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13082 * √(qB 13082))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13082 : ℝ) * √(qB 13082) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13082 : ℝ) * (√13082 *
      (c1F (exp (1 / 2) / 12) (Jz 13082) * (186 / 10000) / Jz 13082)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13082)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13082 : ℝ) * (√13082 *
      (c1F (exp (1 / 2) / 12) (Jz 13082) * (186 / 10000) / Jz 13082)) =
      (13082 * (√13082 * c1F (exp (1 / 2) / 12) (Jz 13082)) * (186 / 10000)) /
        Jz 13082 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13082)]
  nlinarith

theorem row_energy_rule :
    (13082 : ℝ) * (13082 *
      (c2F (exp (1 / 2) / 12) (Jz 13082) * (186 / 10000) ^ 2 / Jz 13082)) ≤
      (1780638883 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13082)]
  nlinarith

end BstLean.Part266.Row13082

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13082
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13082) (hc : A1 c ∈ BstLean.Part153.Eop 13082) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13082 : ℝ)) ≤ (6182269453 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13082 : ℝ) + 2 * √13082 ≤ (1663844143 / 125000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13082 : ℝ) ≤ (28594143 / 250000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13082)
    (hc : A1 c ∈ BstLean.Part153.Eop 13082) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13082 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13082 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13082))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13082) (K : Set (Ix 13082)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13082 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13082 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13082) (hw : WINDOW (paperDesignP 13082) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13082)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13082) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13082 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13082 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13082 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13082 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13082) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13082)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13082)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13082

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13082
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13082) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13082 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13082) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13082) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13082 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13082 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13082 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13082}
    (hw : WINDOW (paperDesignP 13082) c) (hc : c ∈ tableEvent) (K : Set (Ix 13082)) :
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

def proposedBaseEvent : Set (Ret 13082) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13082)) : Prop where
  charge : (retDist (paperCentres 13082)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13082)} (h : TablePayment H) :
    (retDist (paperCentres 13082)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13082)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13082

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13082
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13082) (i : Fin 4) (a : Ix 13082) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13082) (a : Ix 13082) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13082) : Prop where
  moment : ∀ i, MomentBound (muI 13082) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13082} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13082) 8 (actualFourError c i)
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

end BstLean.Part266.Row13082

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13082
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

structure LatitudeVarianceCertificate (c : Ret 13082) : Prop where
  location : LBound (muI 13082) 12
    (fun a => conditionalVariance (stdGauss (Fin (13082 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13082) 12
    (fun a => conditionalVariance (stdGauss (Fin (13082 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13082) (hw : WINDOW (paperDesignP 13082) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13082 4 (55 / 100) /
      (13082 : ℝ) / ((13082 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13082

/-! The dimension-13082 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13082
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13082) (wl ws : ℝ) : SplitData 13082 :=
  BstLean.Part162.dPaper (paperDesignP 13082) c wl ws
    (√(2 / (13082 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13082 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13082 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13082) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13082) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13082 : ℝ)) * eR c * 13082 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13082) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13082 - 1)))
    (rowSplit c wl ws).good a ∂muI 13082 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13082) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13082 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13082) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13082 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13082) c (rowSplit c wl ws),
    hellG2 13082 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13082 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13082} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13082} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13082 t c BstLean.Part266.agent13082.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13082} (R : RootSource t c) :
    |√(QStand (paperDesignP 13082) t c) - √(qTilde (paperDesignP 13082) t c)| ≤
      BstLean.Part266.agent13082.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13082

/-! Rational enclosures for the HQ fluctuation price at dimension 13083. -/
namespace BstLean.Part266.Row13083
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (202844089 / 125000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22568327 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13083 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13083 * A / 2 + D + L * √(A * D)) ≤ (2332284369 / 500000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13083 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((202844089 / 125000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13083 L e4 d4 ≤ (8452037941 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13083 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((202844089 / 125000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13083 L e6 d6 ≤ (64021566219 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13083 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((202844089 / 125000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13083 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13083 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13083 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13083 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22568327 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((2332284369 / 500000000000)) ^ 2 / 2 + ((2332284369 / 500000000000)) * ((8452037941 / 200000000000)) ^ 2 / 6 +
      ((8452037941 / 200000000000)) ^ 4 / 24 + ((8452037941 / 200000000000)) ^ 2 * ((64021566219 / 1000000000000)) ^ 3 / 120 +
      2187 * ((64021566219 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13083 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13083 : ℝ) * ((1 + 3 * ((22568327 / 1000000000))) / (4 * (1 - (22568327 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22568327 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13083 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22568327 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13083 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13083 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13083

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13083
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((57190471 / 500000) : ℝ) ≤ √13083 ∧ √13083 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1496444 : ℝ) ≤ Jz 13083 ∧ 1000000 ≤ Jz 13083 := by
  have hr : ((57190471 / 500000) : ℝ) ≤ √13083 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13083 : ℝ) * √13083 ≤ (⌈(13083 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13083
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13083 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13083 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13083 : ℝ) = (⌈(13083 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1496444 : ℝ) ≤ Jz 13083 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13083 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13083) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13083 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13083 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13083 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13083 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13083 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13083 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13083) :
    (13083 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13083 * √(qB 13083))) ≤
      (551057427 / 1000000000000) := by
  have hden : ((57190471 / 500000) : ℝ) * (63 / 100) ≤ √13083 * √(qB 13083) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13083 : ℝ) * √(qB 13083) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13083) :
    (13083 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13083 * √(qB 13083))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13083 : ℝ) * √(qB 13083) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13083 : ℝ) * (√13083 *
      (c1F (exp (1 / 2) / 12) (Jz 13083) * (186 / 10000) / Jz 13083)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13083)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13083 : ℝ) * (√13083 *
      (c1F (exp (1 / 2) / 12) (Jz 13083) * (186 / 10000) / Jz 13083)) =
      (13083 * (√13083 * c1F (exp (1 / 2) / 12) (Jz 13083)) * (186 / 10000)) /
        Jz 13083 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13083)]
  nlinarith

theorem row_energy_rule :
    (13083 : ℝ) * (13083 *
      (c2F (exp (1 / 2) / 12) (Jz 13083) * (186 / 10000) ^ 2 / Jz 13083)) ≤
      (3561415229 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13083)]
  nlinarith

end BstLean.Part266.Row13083

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13083
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13083) (hc : A1 c ∈ BstLean.Part153.Eop 13083) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13083 : ℝ)) ≤ (2472813271 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13083 : ℝ) + 2 * √13083 ≤ (6655880943 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13083 : ℝ) ≤ (114380943 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13083)
    (hc : A1 c ∈ BstLean.Part153.Eop 13083) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13083 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13083 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13083))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13083) (K : Set (Ix 13083)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13083 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13083 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13083) (hw : WINDOW (paperDesignP 13083) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13083)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13083) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13083 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13083 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13083 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13083 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13083) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13083)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13083)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13083

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13083
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13083) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13083 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13083) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13083) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13083 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13083 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13083 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13083}
    (hw : WINDOW (paperDesignP 13083) c) (hc : c ∈ tableEvent) (K : Set (Ix 13083)) :
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

def proposedBaseEvent : Set (Ret 13083) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13083)) : Prop where
  charge : (retDist (paperCentres 13083)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13083)} (h : TablePayment H) :
    (retDist (paperCentres 13083)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13083)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13083

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13083
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13083) (i : Fin 4) (a : Ix 13083) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13083) (a : Ix 13083) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13083) : Prop where
  moment : ∀ i, MomentBound (muI 13083) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13083} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13083) 8 (actualFourError c i)
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

end BstLean.Part266.Row13083

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13083
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

structure LatitudeVarianceCertificate (c : Ret 13083) : Prop where
  location : LBound (muI 13083) 12
    (fun a => conditionalVariance (stdGauss (Fin (13083 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13083) 12
    (fun a => conditionalVariance (stdGauss (Fin (13083 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13083) (hw : WINDOW (paperDesignP 13083) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13083 4 (55 / 100) /
      (13083 : ℝ) / ((13083 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13083

/-! The dimension-13083 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13083
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13083) (wl ws : ℝ) : SplitData 13083 :=
  BstLean.Part162.dPaper (paperDesignP 13083) c wl ws
    (√(2 / (13083 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13083 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13083 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13083) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13083) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13083 : ℝ)) * eR c * 13083 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13083) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13083 - 1)))
    (rowSplit c wl ws).good a ∂muI 13083 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13083) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13083 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13083) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13083 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13083) c (rowSplit c wl ws),
    hellG2 13083 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13083 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13083} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13083} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13083 t c BstLean.Part266.agent13083.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13083} (R : RootSource t c) :
    |√(QStand (paperDesignP 13083) t c) - √(qTilde (paperDesignP 13083) t c)| ≤
      BstLean.Part266.agent13083.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13083

/-! Rational enclosures for the HQ fluctuation price at dimension 13084. -/
namespace BstLean.Part266.Row13084
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (25354539 / 15625000)
  epsilon : 0 ≤ ε ∧ ε ≤ (2256659 / 100000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13084 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13084 * A / 2 + D + L * √(A * D)) ≤ (932954027 / 200000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13084 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((25354539 / 15625000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13084 L e4 d4 ≤ (8452403769 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13084 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((25354539 / 15625000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13084 L e6 d6 ≤ (64024329699 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13084 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((25354539 / 15625000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13084 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13084 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13084 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13084 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (2256659 / 100000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((932954027 / 200000000000)) ^ 2 / 2 + ((932954027 / 200000000000)) * ((8452403769 / 200000000000)) ^ 2 / 6 +
      ((8452403769 / 200000000000)) ^ 4 / 24 + ((8452403769 / 200000000000)) ^ 2 * ((64024329699 / 1000000000000)) ^ 3 / 120 +
      2187 * ((64024329699 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13084 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13084 : ℝ) * ((1 + 3 * ((2256659 / 100000000))) / (4 * (1 - (2256659 / 100000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (2256659 / 100000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13084 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (2256659 / 100000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13084 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13084 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13084

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13084
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((114385313 / 1000000) : ℝ) ≤ √13084 ∧ √13084 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1496616 : ℝ) ≤ Jz 13084 ∧ 1000000 ≤ Jz 13084 := by
  have hr : ((114385313 / 1000000) : ℝ) ≤ √13084 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13084 : ℝ) * √13084 ≤ (⌈(13084 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13084
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13084 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13084 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13084 : ℝ) = (⌈(13084 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1496616 : ℝ) ≤ Jz 13084 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13084 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13084) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13084 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13084 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13084 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13084 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13084 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13084 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13084) :
    (13084 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13084 * √(qB 13084))) ≤
      (68884811 / 125000000000) := by
  have hden : ((114385313 / 1000000) : ℝ) * (63 / 100) ≤ √13084 * √(qB 13084) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13084 : ℝ) * √(qB 13084) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13084) :
    (13084 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13084 * √(qB 13084))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13084 : ℝ) * √(qB 13084) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13084 : ℝ) * (√13084 *
      (c1F (exp (1 / 2) / 12) (Jz 13084) * (186 / 10000) / Jz 13084)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13084)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13084 : ℝ) * (√13084 *
      (c1F (exp (1 / 2) / 12) (Jz 13084) * (186 / 10000) / Jz 13084)) =
      (13084 * (√13084 * c1F (exp (1 / 2) / 12) (Jz 13084)) * (186 / 10000)) /
        Jz 13084 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13084)]
  nlinarith

theorem row_energy_rule :
    (13084 : ℝ) * (13084 *
      (c2F (exp (1 / 2) / 12) (Jz 13084) * (186 / 10000) ^ 2 / Jz 13084)) ≤
      (1780775161 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13084)]
  nlinarith

end BstLean.Part266.Row13084

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13084
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13084) (hc : A1 c ∈ BstLean.Part153.Eop 13084) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13084 : ℝ)) ≤ (6181796929 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13084 : ℝ) + 2 * √13084 ≤ (3328192657 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13084 : ℝ) ≤ (57192657 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13084)
    (hc : A1 c ∈ BstLean.Part153.Eop 13084) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13084 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13084 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13084))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13084) (K : Set (Ix 13084)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13084 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13084 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13084) (hw : WINDOW (paperDesignP 13084) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13084)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13084) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13084 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13084 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13084 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13084 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13084) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13084)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13084)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13084

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13084
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13084) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13084 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13084) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13084) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13084 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13084 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13084 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13084}
    (hw : WINDOW (paperDesignP 13084) c) (hc : c ∈ tableEvent) (K : Set (Ix 13084)) :
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

def proposedBaseEvent : Set (Ret 13084) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13084)) : Prop where
  charge : (retDist (paperCentres 13084)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13084)} (h : TablePayment H) :
    (retDist (paperCentres 13084)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13084)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13084

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13084
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13084) (i : Fin 4) (a : Ix 13084) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13084) (a : Ix 13084) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13084) : Prop where
  moment : ∀ i, MomentBound (muI 13084) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13084} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13084) 8 (actualFourError c i)
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

end BstLean.Part266.Row13084

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13084
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

structure LatitudeVarianceCertificate (c : Ret 13084) : Prop where
  location : LBound (muI 13084) 12
    (fun a => conditionalVariance (stdGauss (Fin (13084 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13084) 12
    (fun a => conditionalVariance (stdGauss (Fin (13084 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13084) (hw : WINDOW (paperDesignP 13084) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13084 4 (55 / 100) /
      (13084 : ℝ) / ((13084 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13084

/-! The dimension-13084 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13084
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13084) (wl ws : ℝ) : SplitData 13084 :=
  BstLean.Part162.dPaper (paperDesignP 13084) c wl ws
    (√(2 / (13084 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13084 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13084 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13084) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13084) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13084 : ℝ)) * eR c * 13084 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13084) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13084 - 1)))
    (rowSplit c wl ws).good a ∂muI 13084 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13084) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13084 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13084) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13084 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13084) c (rowSplit c wl ws),
    hellG2 13084 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13084 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13084} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13084} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13084 t c BstLean.Part266.agent13084.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13084} (R : RootSource t c) :
    |√(QStand (paperDesignP 13084) t c) - √(qTilde (paperDesignP 13084) t c)| ≤
      BstLean.Part266.agent13084.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13084

/-! Rational enclosures for the HQ fluctuation price at dimension 13085. -/
namespace BstLean.Part266.Row13085
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (324525659 / 200000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22564853 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13085 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13085 * A / 2 + D + L * √(A * D)) ≤ (1166242883 / 250000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13085 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((324525659 / 200000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13085 L e4 d4 ≤ (10565961997 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13085 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((324525659 / 200000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13085 L e6 d6 ≤ (32013546593 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13085 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((324525659 / 200000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13085 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13085 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13085 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13085 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22564853 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((1166242883 / 250000000000)) ^ 2 / 2 + ((1166242883 / 250000000000)) * ((10565961997 / 250000000000)) ^ 2 / 6 +
      ((10565961997 / 250000000000)) ^ 4 / 24 + ((10565961997 / 250000000000)) ^ 2 * ((32013546593 / 500000000000)) ^ 3 / 120 +
      2187 * ((32013546593 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13085 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13085 : ℝ) * ((1 + 3 * ((22564853 / 1000000000))) / (4 * (1 - (22564853 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22564853 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13085 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22564853 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13085 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13085 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13085

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13085
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((28597421 / 250000) : ℝ) ≤ √13085 ∧ √13085 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1496788 : ℝ) ≤ Jz 13085 ∧ 1000000 ≤ Jz 13085 := by
  have hr : ((28597421 / 250000) : ℝ) ≤ √13085 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13085 : ℝ) * √13085 ≤ (⌈(13085 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13085
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13085 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13085 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13085 : ℝ) = (⌈(13085 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1496788 : ℝ) ≤ Jz 13085 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13085 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13085) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13085 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13085 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13085 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13085 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13085 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13085 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13085) :
    (13085 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13085 * √(qB 13085))) ≤
      (551099547 / 1000000000000) := by
  have hden : ((28597421 / 250000) : ℝ) * (63 / 100) ≤ √13085 * √(qB 13085) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13085 : ℝ) * √(qB 13085) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13085) :
    (13085 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13085 * √(qB 13085))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13085 : ℝ) * √(qB 13085) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13085 : ℝ) * (√13085 *
      (c1F (exp (1 / 2) / 12) (Jz 13085) * (186 / 10000) / Jz 13085)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13085)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13085 : ℝ) * (√13085 *
      (c1F (exp (1 / 2) / 12) (Jz 13085) * (186 / 10000) / Jz 13085)) =
      (13085 * (√13085 * c1F (exp (1 / 2) / 12) (Jz 13085)) * (186 / 10000)) /
        Jz 13085 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13085)]
  nlinarith

theorem row_energy_rule :
    (13085 : ℝ) * (13085 *
      (c2F (exp (1 / 2) / 12) (Jz 13085) * (186 / 10000) ^ 2 / Jz 13085)) ≤
      (1780842713 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13085)]
  nlinarith

end BstLean.Part266.Row13085

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13085
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13085) (hc : A1 c ∈ BstLean.Part153.Eop 13085) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13085 : ℝ)) ≤ (2472624283 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13085 : ℝ) + 2 * √13085 ≤ (1331377937 / 100000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13085 : ℝ) ≤ (22877937 / 200000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13085)
    (hc : A1 c ∈ BstLean.Part153.Eop 13085) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13085 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13085 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13085))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13085) (K : Set (Ix 13085)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13085 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13085 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13085) (hw : WINDOW (paperDesignP 13085) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13085)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13085) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13085 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13085 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13085 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13085 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13085) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13085)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13085)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13085

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13085
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13085) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13085 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13085) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13085) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13085 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13085 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13085 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13085}
    (hw : WINDOW (paperDesignP 13085) c) (hc : c ∈ tableEvent) (K : Set (Ix 13085)) :
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

def proposedBaseEvent : Set (Ret 13085) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13085)) : Prop where
  charge : (retDist (paperCentres 13085)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13085)} (h : TablePayment H) :
    (retDist (paperCentres 13085)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13085)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13085

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13085
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13085) (i : Fin 4) (a : Ix 13085) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13085) (a : Ix 13085) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13085) : Prop where
  moment : ∀ i, MomentBound (muI 13085) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13085} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13085) 8 (actualFourError c i)
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

end BstLean.Part266.Row13085

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13085
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

structure LatitudeVarianceCertificate (c : Ret 13085) : Prop where
  location : LBound (muI 13085) 12
    (fun a => conditionalVariance (stdGauss (Fin (13085 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13085) 12
    (fun a => conditionalVariance (stdGauss (Fin (13085 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13085) (hw : WINDOW (paperDesignP 13085) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13085 4 (55 / 100) /
      (13085 : ℝ) / ((13085 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13085

/-! The dimension-13085 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13085
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13085) (wl ws : ℝ) : SplitData 13085 :=
  BstLean.Part162.dPaper (paperDesignP 13085) c wl ws
    (√(2 / (13085 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13085 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13085 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13085) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13085) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13085 : ℝ)) * eR c * 13085 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13085) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13085 - 1)))
    (rowSplit c wl ws).good a ∂muI 13085 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13085) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13085 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13085) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13085 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13085) c (rowSplit c wl ws),
    hellG2 13085 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13085 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13085} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13085} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13085 t c BstLean.Part266.agent13085.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13085} (R : RootSource t c) :
    |√(QStand (paperDesignP 13085) t c) - √(qTilde (paperDesignP 13085) t c)| ≤
      BstLean.Part266.agent13085.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13085

/-! Rational enclosures for the HQ fluctuation price at dimension 13086. -/
namespace BstLean.Part266.Row13086
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1622566107 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (5640779 / 250000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13086 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13086 * A / 2 + D + L * √(A * D)) ≤ (466517293 / 100000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13086 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1622566107 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13086 L e4 d4 ≤ (8453135427 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13086 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1622566107 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13086 L e6 d6 ≤ (64029856677 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13086 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1622566107 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13086 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13086 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13086 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13086 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (5640779 / 250000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((466517293 / 100000000000)) ^ 2 / 2 + ((466517293 / 100000000000)) * ((8453135427 / 200000000000)) ^ 2 / 6 +
      ((8453135427 / 200000000000)) ^ 4 / 24 + ((8453135427 / 200000000000)) ^ 2 * ((64029856677 / 1000000000000)) ^ 3 / 120 +
      2187 * ((64029856677 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13086 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13086 : ℝ) * ((1 + 3 * ((5640779 / 250000000))) / (4 * (1 - (5640779 / 250000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (5640779 / 250000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13086 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (5640779 / 250000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13086 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13086 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13086

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13086
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((22878811 / 200000) : ℝ) ≤ √13086 ∧ √13086 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1496959 : ℝ) ≤ Jz 13086 ∧ 1000000 ≤ Jz 13086 := by
  have hr : ((22878811 / 200000) : ℝ) ≤ √13086 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13086 : ℝ) * √13086 ≤ (⌈(13086 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13086
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13086 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13086 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13086 : ℝ) = (⌈(13086 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1496959 : ℝ) ≤ Jz 13086 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13086 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13086) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13086 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13086 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13086 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13086 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13086 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13086 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13086) :
    (13086 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13086 * √(qB 13086))) ≤
      (110224121 / 200000000000) := by
  have hden : ((22878811 / 200000) : ℝ) * (63 / 100) ≤ √13086 * √(qB 13086) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13086 : ℝ) * √(qB 13086) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13086) :
    (13086 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13086 * √(qB 13086))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13086 : ℝ) * √(qB 13086) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13086 : ℝ) * (√13086 *
      (c1F (exp (1 / 2) / 12) (Jz 13086) * (186 / 10000) / Jz 13086)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13086)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13086 : ℝ) * (√13086 *
      (c1F (exp (1 / 2) / 12) (Jz 13086) * (186 / 10000) / Jz 13086)) =
      (13086 * (√13086 * c1F (exp (1 / 2) / 12) (Jz 13086)) * (186 / 10000)) /
        Jz 13086 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13086)]
  nlinarith

theorem row_energy_rule :
    (13086 : ℝ) * (13086 *
      (c2F (exp (1 / 2) / 12) (Jz 13086) * (186 / 10000) ^ 2 / Jz 13086)) ≤
      (89045573 / 25000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13086)]
  nlinarith

end BstLean.Part266.Row13086

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13086
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13086) (hc : A1 c ∈ BstLean.Part153.Eop 13086) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13086 : ℝ)) ≤ (6181324513 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13086 : ℝ) + 2 * √13086 ≤ (832174257 / 62500) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13086 : ℝ) ≤ (14299257 / 125000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13086)
    (hc : A1 c ∈ BstLean.Part153.Eop 13086) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13086 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13086 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13086))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13086) (K : Set (Ix 13086)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13086 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13086 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13086) (hw : WINDOW (paperDesignP 13086) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13086)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13086) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13086 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13086 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13086 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13086 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13086) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13086)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13086)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13086

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13086
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13086) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13086 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13086) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13086) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13086 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13086 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13086 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13086}
    (hw : WINDOW (paperDesignP 13086) c) (hc : c ∈ tableEvent) (K : Set (Ix 13086)) :
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

def proposedBaseEvent : Set (Ret 13086) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13086)) : Prop where
  charge : (retDist (paperCentres 13086)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13086)} (h : TablePayment H) :
    (retDist (paperCentres 13086)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13086)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13086

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13086
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13086) (i : Fin 4) (a : Ix 13086) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13086) (a : Ix 13086) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13086) : Prop where
  moment : ∀ i, MomentBound (muI 13086) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13086} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13086) 8 (actualFourError c i)
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

end BstLean.Part266.Row13086

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13086
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

structure LatitudeVarianceCertificate (c : Ret 13086) : Prop where
  location : LBound (muI 13086) 12
    (fun a => conditionalVariance (stdGauss (Fin (13086 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13086) 12
    (fun a => conditionalVariance (stdGauss (Fin (13086 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13086) (hw : WINDOW (paperDesignP 13086) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13086 4 (55 / 100) /
      (13086 : ℝ) / ((13086 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13086

/-! The dimension-13086 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13086
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13086) (wl ws : ℝ) : SplitData 13086 :=
  BstLean.Part162.dPaper (paperDesignP 13086) c wl ws
    (√(2 / (13086 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13086 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13086 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13086) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13086) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13086 : ℝ)) * eR c * 13086 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13086) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13086 - 1)))
    (rowSplit c wl ws).good a ∂muI 13086 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13086) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13086 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13086) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13086 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13086) c (rowSplit c wl ws),
    hellG2 13086 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13086 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13086} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13086} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13086 t c BstLean.Part266.agent13086.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13086} (R : RootSource t c) :
    |√(QStand (paperDesignP 13086) t c) - √(qTilde (paperDesignP 13086) t c)| ≤
      BstLean.Part266.agent13086.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13086

/-! Rational enclosures for the HQ fluctuation price at dimension 13087. -/
namespace BstLean.Part266.Row13087
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (324500843 / 200000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (2820173 / 125000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13087 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13087 * A / 2 + D + L * √(A * D)) ≤ (36448237 / 7812500000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13087 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((324500843 / 200000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13087 L e4 d4 ≤ (21133753179 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13087 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((324500843 / 200000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13087 L e6 d6 ≤ (16008155071 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13087 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((324500843 / 200000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13087 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13087 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13087 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13087 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (2820173 / 125000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((36448237 / 7812500000)) ^ 2 / 2 + ((36448237 / 7812500000)) * ((21133753179 / 500000000000)) ^ 2 / 6 +
      ((21133753179 / 500000000000)) ^ 4 / 24 + ((21133753179 / 500000000000)) ^ 2 * ((16008155071 / 250000000000)) ^ 3 / 120 +
      2187 * ((16008155071 / 250000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13087 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13087 : ℝ) * ((1 + 3 * ((2820173 / 125000000))) / (4 * (1 - (2820173 / 125000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (2820173 / 125000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13087 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (2820173 / 125000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13087 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13087 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13087

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13087
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((57199213 / 500000) : ℝ) ≤ √13087 ∧ √13087 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1497131 : ℝ) ≤ Jz 13087 ∧ 1000000 ≤ Jz 13087 := by
  have hr : ((57199213 / 500000) : ℝ) ≤ √13087 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13087 : ℝ) * √13087 ≤ (⌈(13087 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13087
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13087 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13087 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13087 : ℝ) = (⌈(13087 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1497131 : ℝ) ≤ Jz 13087 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13087 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13087) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13087 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13087 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13087 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13087 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13087 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13087 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13087) :
    (13087 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13087 * √(qB 13087))) ≤
      (551141661 / 1000000000000) := by
  have hden : ((57199213 / 500000) : ℝ) * (63 / 100) ≤ √13087 * √(qB 13087) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13087 : ℝ) * √(qB 13087) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13087) :
    (13087 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13087 * √(qB 13087))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13087 : ℝ) * √(qB 13087) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13087 : ℝ) * (√13087 *
      (c1F (exp (1 / 2) / 12) (Jz 13087) * (186 / 10000) / Jz 13087)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13087)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13087 : ℝ) * (√13087 *
      (c1F (exp (1 / 2) / 12) (Jz 13087) * (186 / 10000) / Jz 13087)) =
      (13087 * (√13087 * c1F (exp (1 / 2) / 12) (Jz 13087)) * (186 / 10000)) /
        Jz 13087 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13087)]
  nlinarith

theorem row_energy_rule :
    (13087 : ℝ) * (13087 *
      (c2F (exp (1 / 2) / 12) (Jz 13087) * (186 / 10000) ^ 2 / Jz 13087)) ≤
      (890489511 / 250000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13087)]
  nlinarith

end BstLean.Part266.Row13087

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13087
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13087) (hc : A1 c ∈ BstLean.Part153.Eop 13087) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13087 : ℝ)) ≤ (3090544173 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13087 : ℝ) + 2 * √13087 ≤ (6657898427 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13087 : ℝ) ≤ (114398427 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13087)
    (hc : A1 c ∈ BstLean.Part153.Eop 13087) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13087 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13087 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13087))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13087) (K : Set (Ix 13087)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13087 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13087 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13087) (hw : WINDOW (paperDesignP 13087) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13087)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13087) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13087 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13087 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13087 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13087 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13087) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13087)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13087)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13087

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13087
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13087) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13087 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13087) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13087) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13087 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13087 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13087 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13087}
    (hw : WINDOW (paperDesignP 13087) c) (hc : c ∈ tableEvent) (K : Set (Ix 13087)) :
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

def proposedBaseEvent : Set (Ret 13087) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13087)) : Prop where
  charge : (retDist (paperCentres 13087)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13087)} (h : TablePayment H) :
    (retDist (paperCentres 13087)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13087)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13087

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13087
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13087) (i : Fin 4) (a : Ix 13087) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13087) (a : Ix 13087) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13087) : Prop where
  moment : ∀ i, MomentBound (muI 13087) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13087} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13087) 8 (actualFourError c i)
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

end BstLean.Part266.Row13087

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13087
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

structure LatitudeVarianceCertificate (c : Ret 13087) : Prop where
  location : LBound (muI 13087) 12
    (fun a => conditionalVariance (stdGauss (Fin (13087 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13087) 12
    (fun a => conditionalVariance (stdGauss (Fin (13087 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13087) (hw : WINDOW (paperDesignP 13087) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13087 4 (55 / 100) /
      (13087 : ℝ) / ((13087 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13087

/-! The dimension-13087 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13087
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13087) (wl ws : ℝ) : SplitData 13087 :=
  BstLean.Part162.dPaper (paperDesignP 13087) c wl ws
    (√(2 / (13087 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13087 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13087 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13087) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13087) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13087 : ℝ)) * eR c * 13087 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13087) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13087 - 1)))
    (rowSplit c wl ws).good a ∂muI 13087 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13087) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13087 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13087) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13087 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13087) c (rowSplit c wl ws),
    hellG2 13087 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13087 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13087} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13087} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13087 t c BstLean.Part266.agent13087.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13087} (R : RootSource t c) :
    |√(QStand (paperDesignP 13087) t c) - √(qTilde (paperDesignP 13087) t c)| ≤
      BstLean.Part266.agent13087.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13087

/-! Rational enclosures for the HQ fluctuation price at dimension 13088. -/
namespace BstLean.Part266.Row13088
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (324488411 / 200000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (704989 / 31250000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13088 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13088 * A / 2 + D + L * √(A * D)) ≤ (933115147 / 200000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13088 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((324488411 / 200000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13088 L e4 d4 ≤ (5283666939 / 125000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13088 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((324488411 / 200000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13088 L e6 d6 ≤ (32017691893 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13088 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((324488411 / 200000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13088 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13088 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13088 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13088 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (704989 / 31250000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((933115147 / 200000000000)) ^ 2 / 2 + ((933115147 / 200000000000)) * ((5283666939 / 125000000000)) ^ 2 / 6 +
      ((5283666939 / 125000000000)) ^ 4 / 24 + ((5283666939 / 125000000000)) ^ 2 * ((32017691893 / 500000000000)) ^ 3 / 120 +
      2187 * ((32017691893 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13088 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13088 : ℝ) * ((1 + 3 * ((704989 / 31250000))) / (4 * (1 - (704989 / 31250000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (704989 / 31250000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13088 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (704989 / 31250000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13088 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13088 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13088

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13088
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((114402797 / 1000000) : ℝ) ≤ √13088 ∧ √13088 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1497302 : ℝ) ≤ Jz 13088 ∧ 1000000 ≤ Jz 13088 := by
  have hr : ((114402797 / 1000000) : ℝ) ≤ √13088 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13088 : ℝ) * √13088 ≤ (⌈(13088 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13088
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13088 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13088 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13088 : ℝ) = (⌈(13088 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1497302 : ℝ) ≤ Jz 13088 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13088 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13088) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13088 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13088 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13088 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13088 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13088 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13088 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13088) :
    (13088 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13088 * √(qB 13088))) ≤
      (110232543 / 200000000000) := by
  have hden : ((114402797 / 1000000) : ℝ) * (63 / 100) ≤ √13088 * √(qB 13088) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13088 : ℝ) * √(qB 13088) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13088) :
    (13088 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13088 * √(qB 13088))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13088 : ℝ) * √(qB 13088) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13088 : ℝ) * (√13088 *
      (c1F (exp (1 / 2) / 12) (Jz 13088) * (186 / 10000) / Jz 13088)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13088)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13088 : ℝ) * (√13088 *
      (c1F (exp (1 / 2) / 12) (Jz 13088) * (186 / 10000) / Jz 13088)) =
      (13088 * (√13088 * c1F (exp (1 / 2) / 12) (Jz 13088)) * (186 / 10000)) /
        Jz 13088 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13088)]
  nlinarith

theorem row_energy_rule :
    (13088 : ℝ) * (13088 *
      (c2F (exp (1 / 2) / 12) (Jz 13088) * (186 / 10000) ^ 2 / Jz 13088)) ≤
      (3562095559 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13088)]
  nlinarith

end BstLean.Part266.Row13088

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13088
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13088) (hc : A1 c ∈ BstLean.Part153.Eop 13088) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13088 : ℝ)) ≤ (12361704411 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13088 : ℝ) + 2 * √13088 ≤ (3329201399 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13088 : ℝ) ≤ (57201399 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13088)
    (hc : A1 c ∈ BstLean.Part153.Eop 13088) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13088 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13088 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13088))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13088) (K : Set (Ix 13088)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13088 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13088 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13088) (hw : WINDOW (paperDesignP 13088) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13088)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13088) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13088 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13088 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13088 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13088 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13088) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13088)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13088)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13088

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13088
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13088) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13088 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13088) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13088) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13088 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13088 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13088 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13088}
    (hw : WINDOW (paperDesignP 13088) c) (hc : c ∈ tableEvent) (K : Set (Ix 13088)) :
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

def proposedBaseEvent : Set (Ret 13088) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13088)) : Prop where
  charge : (retDist (paperCentres 13088)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13088)} (h : TablePayment H) :
    (retDist (paperCentres 13088)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13088)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13088

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13088
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13088) (i : Fin 4) (a : Ix 13088) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13088) (a : Ix 13088) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13088) : Prop where
  moment : ∀ i, MomentBound (muI 13088) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13088} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13088) 8 (actualFourError c i)
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

end BstLean.Part266.Row13088

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13088
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

structure LatitudeVarianceCertificate (c : Ret 13088) : Prop where
  location : LBound (muI 13088) 12
    (fun a => conditionalVariance (stdGauss (Fin (13088 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13088) 12
    (fun a => conditionalVariance (stdGauss (Fin (13088 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13088) (hw : WINDOW (paperDesignP 13088) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13088 4 (55 / 100) /
      (13088 : ℝ) / ((13088 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13088

/-! The dimension-13088 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13088
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13088) (wl ws : ℝ) : SplitData 13088 :=
  BstLean.Part162.dPaper (paperDesignP 13088) c wl ws
    (√(2 / (13088 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13088 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13088 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13088) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13088) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13088 : ℝ)) * eR c * 13088 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13088) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13088 - 1)))
    (rowSplit c wl ws).good a ∂muI 13088 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13088) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13088 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13088) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13088 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13088) c (rowSplit c wl ws),
    hellG2 13088 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13088 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13088} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13088} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13088 t c BstLean.Part266.agent13088.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13088} (R : RootSource t c) :
    |√(QStand (paperDesignP 13088) t c) - √(qTilde (paperDesignP 13088) t c)| ≤
      BstLean.Part266.agent13088.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13088

/-! Rational enclosures for the HQ fluctuation price at dimension 13089. -/
namespace BstLean.Part266.Row13089
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1622379911 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22557913 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13089 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13089 * A / 2 + D + L * √(A * D)) ≤ (2332888567 / 500000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13089 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1622379911 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13089 L e4 d4 ≤ (4227116467 / 100000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13089 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1622379911 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13089 L e6 d6 ≤ (32019073647 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13089 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1622379911 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13089 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13089 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13089 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13089 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22557913 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((2332888567 / 500000000000)) ^ 2 / 2 + ((2332888567 / 500000000000)) * ((4227116467 / 100000000000)) ^ 2 / 6 +
      ((4227116467 / 100000000000)) ^ 4 / 24 + ((4227116467 / 100000000000)) ^ 2 * ((32019073647 / 500000000000)) ^ 3 / 120 +
      2187 * ((32019073647 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13089 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13089 : ℝ) * ((1 + 3 * ((22557913 / 1000000000))) / (4 * (1 - (22557913 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22557913 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13089 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22557913 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13089 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13089 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13089

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13089
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((114407167 / 1000000) : ℝ) ≤ √13089 ∧ √13089 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1497474 : ℝ) ≤ Jz 13089 ∧ 1000000 ≤ Jz 13089 := by
  have hr : ((114407167 / 1000000) : ℝ) ≤ √13089 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13089 : ℝ) * √13089 ≤ (⌈(13089 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13089
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13089 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13089 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13089 : ℝ) = (⌈(13089 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1497474 : ℝ) ≤ Jz 13089 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13089 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13089) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13089 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13089 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13089 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13089 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13089 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13089 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13089) :
    (13089 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13089 * √(qB 13089))) ≤
      (551183773 / 1000000000000) := by
  have hden : ((114407167 / 1000000) : ℝ) * (63 / 100) ≤ √13089 * √(qB 13089) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13089 : ℝ) * √(qB 13089) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13089) :
    (13089 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13089 * √(qB 13089))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13089 : ℝ) * √(qB 13089) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13089 : ℝ) * (√13089 *
      (c1F (exp (1 / 2) / 12) (Jz 13089) * (186 / 10000) / Jz 13089)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13089)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13089 : ℝ) * (√13089 *
      (c1F (exp (1 / 2) / 12) (Jz 13089) * (186 / 10000) / Jz 13089)) =
      (13089 * (√13089 * c1F (exp (1 / 2) / 12) (Jz 13089)) * (186 / 10000)) /
        Jz 13089 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13089)]
  nlinarith

theorem row_energy_rule :
    (13089 : ℝ) * (13089 *
      (c2F (exp (1 / 2) / 12) (Jz 13089) * (186 / 10000) ^ 2 / Jz 13089)) ≤
      (222639419 / 62500000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13089)]
  nlinarith

end BstLean.Part266.Row13089

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13089
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13089) (hc : A1 c ∈ BstLean.Part153.Eop 13089) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13089 : ℝ)) ≤ (2472246437 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13089 : ℝ) + 2 * √13089 ≤ (208090849 / 15625) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13089 : ℝ) ≤ (1787612 / 15625))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13089)
    (hc : A1 c ∈ BstLean.Part153.Eop 13089) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13089 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13089 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13089))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13089) (K : Set (Ix 13089)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13089 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13089 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13089) (hw : WINDOW (paperDesignP 13089) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13089)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13089) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13089 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13089 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13089 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13089 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13089) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13089)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13089)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13089

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13089
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13089) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13089 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13089) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13089) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13089 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13089 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13089 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13089}
    (hw : WINDOW (paperDesignP 13089) c) (hc : c ∈ tableEvent) (K : Set (Ix 13089)) :
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

def proposedBaseEvent : Set (Ret 13089) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13089)) : Prop where
  charge : (retDist (paperCentres 13089)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13089)} (h : TablePayment H) :
    (retDist (paperCentres 13089)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13089)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13089

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13089
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13089) (i : Fin 4) (a : Ix 13089) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13089) (a : Ix 13089) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13089) : Prop where
  moment : ∀ i, MomentBound (muI 13089) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13089} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13089) 8 (actualFourError c i)
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

end BstLean.Part266.Row13089

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13089
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

structure LatitudeVarianceCertificate (c : Ret 13089) : Prop where
  location : LBound (muI 13089) 12
    (fun a => conditionalVariance (stdGauss (Fin (13089 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13089) 12
    (fun a => conditionalVariance (stdGauss (Fin (13089 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13089) (hw : WINDOW (paperDesignP 13089) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13089 4 (55 / 100) /
      (13089 : ℝ) / ((13089 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13089

/-! The dimension-13089 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13089
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13089) (wl ws : ℝ) : SplitData 13089 :=
  BstLean.Part162.dPaper (paperDesignP 13089) c wl ws
    (√(2 / (13089 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13089 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13089 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13089) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13089) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13089 : ℝ)) * eR c * 13089 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13089) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13089 - 1)))
    (rowSplit c wl ws).good a ∂muI 13089 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13089) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13089 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13089) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13089 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13089) c (rowSplit c wl ws),
    hellG2 13089 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13089 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13089} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13089} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13089 t c BstLean.Part266.agent13089.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13089} (R : RootSource t c) :
    |√(QStand (paperDesignP 13089) t c) - √(qTilde (paperDesignP 13089) t c)| ≤
      BstLean.Part266.agent13089.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13089

/-! Rational enclosures for the HQ fluctuation price at dimension 13090. -/
namespace BstLean.Part266.Row13090
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1622317781 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11278089 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13090 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13090 * A / 2 + D + L * √(A * D)) ≤ (4665978533 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13090 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1622317781 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13090 L e4 d4 ≤ (5284124229 / 125000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13090 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1622317781 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13090 L e6 d6 ≤ (8005113851 / 125000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13090 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1622317781 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13090 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13090 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13090 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13090 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11278089 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4665978533 / 1000000000000)) ^ 2 / 2 + ((4665978533 / 1000000000000)) * ((5284124229 / 125000000000)) ^ 2 / 6 +
      ((5284124229 / 125000000000)) ^ 4 / 24 + ((5284124229 / 125000000000)) ^ 2 * ((8005113851 / 125000000000)) ^ 3 / 120 +
      2187 * ((8005113851 / 125000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13090 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13090 : ℝ) * ((1 + 3 * ((11278089 / 500000000))) / (4 * (1 - (11278089 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11278089 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13090 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11278089 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13090 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13090 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13090

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13090
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((114411537 / 1000000) : ℝ) ≤ √13090 ∧ √13090 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1497646 : ℝ) ≤ Jz 13090 ∧ 1000000 ≤ Jz 13090 := by
  have hr : ((114411537 / 1000000) : ℝ) ≤ √13090 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13090 : ℝ) * √13090 ≤ (⌈(13090 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13090
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13090 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13090 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13090 : ℝ) = (⌈(13090 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1497646 : ℝ) ≤ Jz 13090 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13090 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13090) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13090 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13090 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13090 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13090 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13090 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13090 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13090) :
    (13090 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13090 * √(qB 13090))) ≤
      (551204829 / 1000000000000) := by
  have hden : ((114411537 / 1000000) : ℝ) * (63 / 100) ≤ √13090 * √(qB 13090) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13090 : ℝ) * √(qB 13090) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13090) :
    (13090 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13090 * √(qB 13090))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13090 : ℝ) * √(qB 13090) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13090 : ℝ) * (√13090 *
      (c1F (exp (1 / 2) / 12) (Jz 13090) * (186 / 10000) / Jz 13090)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13090)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13090 : ℝ) * (√13090 *
      (c1F (exp (1 / 2) / 12) (Jz 13090) * (186 / 10000) / Jz 13090)) =
      (13090 * (√13090 * c1F (exp (1 / 2) / 12) (Jz 13090)) * (186 / 10000)) /
        Jz 13090 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13090)]
  nlinarith

theorem row_energy_rule :
    (13090 : ℝ) * (13090 *
      (c2F (exp (1 / 2) / 12) (Jz 13090) * (186 / 10000) ^ 2 / Jz 13090)) ≤
      (3562365861 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13090)]
  nlinarith

end BstLean.Part266.Row13090

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13090
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13090) (hc : A1 c ∈ BstLean.Part153.Eop 13090) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13090 : ℝ)) ≤ (12360760013 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13090 : ℝ) + 2 * √13090 ≤ (3329705769 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13090 : ℝ) ≤ (57205769 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13090)
    (hc : A1 c ∈ BstLean.Part153.Eop 13090) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13090 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13090 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13090))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13090) (K : Set (Ix 13090)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13090 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13090 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13090) (hw : WINDOW (paperDesignP 13090) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13090)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13090) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13090 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13090 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13090 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13090 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13090) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13090)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13090)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13090

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13090
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13090) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13090 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13090) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13090) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13090 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13090 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13090 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13090}
    (hw : WINDOW (paperDesignP 13090) c) (hc : c ∈ tableEvent) (K : Set (Ix 13090)) :
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

def proposedBaseEvent : Set (Ret 13090) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13090)) : Prop where
  charge : (retDist (paperCentres 13090)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13090)} (h : TablePayment H) :
    (retDist (paperCentres 13090)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13090)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13090

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13090
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13090) (i : Fin 4) (a : Ix 13090) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13090) (a : Ix 13090) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13090) : Prop where
  moment : ∀ i, MomentBound (muI 13090) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13090} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13090) 8 (actualFourError c i)
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

end BstLean.Part266.Row13090

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13090
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

structure LatitudeVarianceCertificate (c : Ret 13090) : Prop where
  location : LBound (muI 13090) 12
    (fun a => conditionalVariance (stdGauss (Fin (13090 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13090) 12
    (fun a => conditionalVariance (stdGauss (Fin (13090 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13090) (hw : WINDOW (paperDesignP 13090) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13090 4 (55 / 100) /
      (13090 : ℝ) / ((13090 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13090

/-! The dimension-13090 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13090
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13090) (wl ws : ℝ) : SplitData 13090 :=
  BstLean.Part162.dPaper (paperDesignP 13090) c wl ws
    (√(2 / (13090 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13090 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13090 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13090) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13090) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13090 : ℝ)) * eR c * 13090 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13090) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13090 - 1)))
    (rowSplit c wl ws).good a ∂muI 13090 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13090) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13090 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13090) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13090 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13090) c (rowSplit c wl ws),
    hellG2 13090 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13090 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13090} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13090} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13090 t c BstLean.Part266.agent13090.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13090} (R : RootSource t c) :
    |√(QStand (paperDesignP 13090) t c) - √(qTilde (paperDesignP 13090) t c)| ≤
      BstLean.Part266.agent13090.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13090

/-! Rational enclosures for the HQ fluctuation price at dimension 13091. -/
namespace BstLean.Part266.Row13091
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (101390979 / 62500000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22554443 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13091 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13091 * A / 2 + D + L * √(A * D)) ≤ (4666179933 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13091 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((101390979 / 62500000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13091 L e4 d4 ≤ (42274822997 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13091 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((101390979 / 62500000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13091 L e6 d6 ≤ (64043674327 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13091 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((101390979 / 62500000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13091 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13091 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13091 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13091 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22554443 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4666179933 / 1000000000000)) ^ 2 / 2 + ((4666179933 / 1000000000000)) * ((42274822997 / 1000000000000)) ^ 2 / 6 +
      ((42274822997 / 1000000000000)) ^ 4 / 24 + ((42274822997 / 1000000000000)) ^ 2 * ((64043674327 / 1000000000000)) ^ 3 / 120 +
      2187 * ((64043674327 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13091 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13091 : ℝ) * ((1 + 3 * ((22554443 / 1000000000))) / (4 * (1 - (22554443 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22554443 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13091 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22554443 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13091 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13091 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13091

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13091
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((114415907 / 1000000) : ℝ) ≤ √13091 ∧ √13091 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1497817 : ℝ) ≤ Jz 13091 ∧ 1000000 ≤ Jz 13091 := by
  have hr : ((114415907 / 1000000) : ℝ) ≤ √13091 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13091 : ℝ) * √13091 ≤ (⌈(13091 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13091
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13091 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13091 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13091 : ℝ) = (⌈(13091 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1497817 : ℝ) ≤ Jz 13091 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13091 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13091) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13091 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13091 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13091 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13091 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13091 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13091 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13091) :
    (13091 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13091 * √(qB 13091))) ≤
      (137806471 / 250000000000) := by
  have hden : ((114415907 / 1000000) : ℝ) * (63 / 100) ≤ √13091 * √(qB 13091) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13091 : ℝ) * √(qB 13091) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13091) :
    (13091 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13091 * √(qB 13091))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13091 : ℝ) * √(qB 13091) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13091 : ℝ) * (√13091 *
      (c1F (exp (1 / 2) / 12) (Jz 13091) * (186 / 10000) / Jz 13091)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13091)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13091 : ℝ) * (√13091 *
      (c1F (exp (1 / 2) / 12) (Jz 13091) * (186 / 10000) / Jz 13091)) =
      (13091 * (√13091 * c1F (exp (1 / 2) / 12) (Jz 13091)) * (186 / 10000)) /
        Jz 13091 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13091)]
  nlinarith

theorem row_energy_rule :
    (13091 : ℝ) * (13091 *
      (c2F (exp (1 / 2) / 12) (Jz 13091) * (186 / 10000) ^ 2 / Jz 13091)) ≤
      (1781251703 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13091)]
  nlinarith

end BstLean.Part266.Row13091

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13091
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13091) (hc : A1 c ∈ BstLean.Part153.Eop 13091) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13091 : ℝ)) ≤ (2472057579 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13091 : ℝ) + 2 * √13091 ≤ (1664978977 / 125000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13091 : ℝ) ≤ (28603977 / 250000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13091)
    (hc : A1 c ∈ BstLean.Part153.Eop 13091) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13091 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13091 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13091))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13091) (K : Set (Ix 13091)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13091 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13091 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13091) (hw : WINDOW (paperDesignP 13091) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13091)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13091) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13091 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13091 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13091 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13091 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13091) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13091)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13091)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13091

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13091
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13091) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13091 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13091) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13091) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13091 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13091 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13091 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13091}
    (hw : WINDOW (paperDesignP 13091) c) (hc : c ∈ tableEvent) (K : Set (Ix 13091)) :
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

def proposedBaseEvent : Set (Ret 13091) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13091)) : Prop where
  charge : (retDist (paperCentres 13091)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13091)} (h : TablePayment H) :
    (retDist (paperCentres 13091)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13091)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13091

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13091
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13091) (i : Fin 4) (a : Ix 13091) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13091) (a : Ix 13091) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13091) : Prop where
  moment : ∀ i, MomentBound (muI 13091) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13091} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13091) 8 (actualFourError c i)
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

end BstLean.Part266.Row13091

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13091
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

structure LatitudeVarianceCertificate (c : Ret 13091) : Prop where
  location : LBound (muI 13091) 12
    (fun a => conditionalVariance (stdGauss (Fin (13091 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13091) 12
    (fun a => conditionalVariance (stdGauss (Fin (13091 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13091) (hw : WINDOW (paperDesignP 13091) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13091 4 (55 / 100) /
      (13091 : ℝ) / ((13091 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13091

/-! The dimension-13091 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13091
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13091) (wl ws : ℝ) : SplitData 13091 :=
  BstLean.Part162.dPaper (paperDesignP 13091) c wl ws
    (√(2 / (13091 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13091 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13091 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13091) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13091) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13091 : ℝ)) * eR c * 13091 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13091) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13091 - 1)))
    (rowSplit c wl ws).good a ∂muI 13091 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13091) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13091 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13091) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13091 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13091) c (rowSplit c wl ws),
    hellG2 13091 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13091 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13091} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13091} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13091 t c BstLean.Part266.agent13091.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13091} (R : RootSource t c) :
    |√(QStand (paperDesignP 13091) t c) - √(qTilde (paperDesignP 13091) t c)| ≤
      BstLean.Part266.agent13091.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13091

/-! Rational enclosures for the HQ fluctuation price at dimension 13092. -/
namespace BstLean.Part266.Row13092
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1622193563 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (5638177 / 250000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13092 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13092 * A / 2 + D + L * √(A * D)) ≤ (4666381333 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13092 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1622193563 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13092 L e4 d4 ≤ (21138326083 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13092 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1622193563 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13092 L e6 d6 ≤ (64046437853 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13092 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1622193563 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13092 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13092 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13092 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13092 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (5638177 / 250000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4666381333 / 1000000000000)) ^ 2 / 2 + ((4666381333 / 1000000000000)) * ((21138326083 / 500000000000)) ^ 2 / 6 +
      ((21138326083 / 500000000000)) ^ 4 / 24 + ((21138326083 / 500000000000)) ^ 2 * ((64046437853 / 1000000000000)) ^ 3 / 120 +
      2187 * ((64046437853 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13092 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13092 : ℝ) * ((1 + 3 * ((5638177 / 250000000))) / (4 * (1 - (5638177 / 250000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (5638177 / 250000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13092 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (5638177 / 250000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13092 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13092 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13092

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13092
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((114420277 / 1000000) : ℝ) ≤ √13092 ∧ √13092 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1497989 : ℝ) ≤ Jz 13092 ∧ 1000000 ≤ Jz 13092 := by
  have hr : ((114420277 / 1000000) : ℝ) ≤ √13092 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13092 : ℝ) * √13092 ≤ (⌈(13092 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13092
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13092 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13092 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13092 : ℝ) = (⌈(13092 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1497989 : ℝ) ≤ Jz 13092 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13092 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13092) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13092 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13092 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13092 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13092 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13092 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13092 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13092) :
    (13092 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13092 * √(qB 13092))) ≤
      (551246937 / 1000000000000) := by
  have hden : ((114420277 / 1000000) : ℝ) * (63 / 100) ≤ √13092 * √(qB 13092) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13092 : ℝ) * √(qB 13092) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13092) :
    (13092 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13092 * √(qB 13092))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13092 : ℝ) * √(qB 13092) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13092 : ℝ) * (√13092 *
      (c1F (exp (1 / 2) / 12) (Jz 13092) * (186 / 10000) / Jz 13092)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13092)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13092 : ℝ) * (√13092 *
      (c1F (exp (1 / 2) / 12) (Jz 13092) * (186 / 10000) / Jz 13092)) =
      (13092 * (√13092 * c1F (exp (1 / 2) / 12) (Jz 13092)) * (186 / 10000)) /
        Jz 13092 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13092)]
  nlinarith

theorem row_energy_rule :
    (13092 : ℝ) * (13092 *
      (c2F (exp (1 / 2) / 12) (Jz 13092) * (186 / 10000) ^ 2 / Jz 13092)) ≤
      (3562638583 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13092)]
  nlinarith

end BstLean.Part266.Row13092

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13092
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13092) (hc : A1 c ∈ BstLean.Part153.Eop 13092) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13092 : ℝ)) ≤ (12359815831 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13092 : ℝ) + 2 * √13092 ≤ (3330210139 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13092 : ℝ) ≤ (57210139 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13092)
    (hc : A1 c ∈ BstLean.Part153.Eop 13092) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13092 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13092 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13092))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13092) (K : Set (Ix 13092)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13092 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13092 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13092) (hw : WINDOW (paperDesignP 13092) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13092)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13092) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13092 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13092 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13092 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13092 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13092) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13092)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13092)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13092

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13092
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13092) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13092 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13092) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13092) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13092 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13092 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13092 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13092}
    (hw : WINDOW (paperDesignP 13092) c) (hc : c ∈ tableEvent) (K : Set (Ix 13092)) :
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

def proposedBaseEvent : Set (Ret 13092) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13092)) : Prop where
  charge : (retDist (paperCentres 13092)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13092)} (h : TablePayment H) :
    (retDist (paperCentres 13092)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13092)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13092

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13092
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13092) (i : Fin 4) (a : Ix 13092) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13092) (a : Ix 13092) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13092) : Prop where
  moment : ∀ i, MomentBound (muI 13092) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13092} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13092) 8 (actualFourError c i)
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

end BstLean.Part266.Row13092

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13092
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

structure LatitudeVarianceCertificate (c : Ret 13092) : Prop where
  location : LBound (muI 13092) 12
    (fun a => conditionalVariance (stdGauss (Fin (13092 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13092) 12
    (fun a => conditionalVariance (stdGauss (Fin (13092 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13092) (hw : WINDOW (paperDesignP 13092) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13092 4 (55 / 100) /
      (13092 : ℝ) / ((13092 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13092

/-! The dimension-13092 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13092
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13092) (wl ws : ℝ) : SplitData 13092 :=
  BstLean.Part162.dPaper (paperDesignP 13092) c wl ws
    (√(2 / (13092 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13092 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13092 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13092) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13092) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13092 : ℝ)) * eR c * 13092 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13092) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13092 - 1)))
    (rowSplit c wl ws).good a ∂muI 13092 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13092) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13092 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13092) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13092 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13092) c (rowSplit c wl ws),
    hellG2 13092 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13092 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13092} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13092} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13092 t c BstLean.Part266.agent13092.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13092} (R : RootSource t c) :
    |√(QStand (paperDesignP 13092) t c) - √(qTilde (paperDesignP 13092) t c)| ≤
      BstLean.Part266.agent13092.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13092

/-! Rational enclosures for the HQ fluctuation price at dimension 13093. -/
namespace BstLean.Part266.Row13093
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (64885259 / 40000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11275487 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13093 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13093 * A / 2 + D + L * √(A * D)) ≤ (2333291367 / 500000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13093 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((64885259 / 40000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13093 L e4 d4 ≤ (42278481339 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13093 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((64885259 / 40000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13093 L e6 d6 ≤ (64049201383 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13093 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((64885259 / 40000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13093 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13093 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13093 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13093 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11275487 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((2333291367 / 500000000000)) ^ 2 / 2 + ((2333291367 / 500000000000)) * ((42278481339 / 1000000000000)) ^ 2 / 6 +
      ((42278481339 / 1000000000000)) ^ 4 / 24 + ((42278481339 / 1000000000000)) ^ 2 * ((64049201383 / 1000000000000)) ^ 3 / 120 +
      2187 * ((64049201383 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13093 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13093 : ℝ) * ((1 + 3 * ((11275487 / 500000000))) / (4 * (1 - (11275487 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11275487 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13093 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11275487 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13093 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13093 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13093

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13093
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((114424647 / 1000000) : ℝ) ≤ √13093 ∧ √13093 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1498160 : ℝ) ≤ Jz 13093 ∧ 1000000 ≤ Jz 13093 := by
  have hr : ((114424647 / 1000000) : ℝ) ≤ √13093 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13093 : ℝ) * √13093 ≤ (⌈(13093 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13093
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13093 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13093 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13093 : ℝ) = (⌈(13093 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1498160 : ℝ) ≤ Jz 13093 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13093 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13093) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13093 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13093 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13093 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13093 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13093 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13093 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13093) :
    (13093 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13093 * √(qB 13093))) ≤
      (137816997 / 250000000000) := by
  have hden : ((114424647 / 1000000) : ℝ) * (63 / 100) ≤ √13093 * √(qB 13093) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13093 : ℝ) * √(qB 13093) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13093) :
    (13093 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13093 * √(qB 13093))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13093 : ℝ) * √(qB 13093) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13093 : ℝ) * (√13093 *
      (c1F (exp (1 / 2) / 12) (Jz 13093) * (186 / 10000) / Jz 13093)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13093)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13093 : ℝ) * (√13093 *
      (c1F (exp (1 / 2) / 12) (Jz 13093) * (186 / 10000) / Jz 13093)) =
      (13093 * (√13093 * c1F (exp (1 / 2) / 12) (Jz 13093)) * (186 / 10000)) /
        Jz 13093 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13093)]
  nlinarith

theorem row_energy_rule :
    (13093 : ℝ) * (13093 *
      (c2F (exp (1 / 2) / 12) (Jz 13093) * (186 / 10000) ^ 2 / Jz 13093)) ≤
      (3562776149 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13093)]
  nlinarith

end BstLean.Part266.Row13093

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13093
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13093) (hc : A1 c ∈ BstLean.Part153.Eop 13093) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13093 : ℝ)) ≤ (12359343821 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13093 : ℝ) + 2 * √13093 ≤ (832615581 / 62500) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13093 : ℝ) ≤ (14303081 / 125000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13093)
    (hc : A1 c ∈ BstLean.Part153.Eop 13093) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13093 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13093 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13093))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13093) (K : Set (Ix 13093)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13093 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13093 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13093) (hw : WINDOW (paperDesignP 13093) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13093)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13093) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13093 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13093 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13093 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13093 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13093) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13093)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13093)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13093

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13093
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13093) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13093 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13093) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13093) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13093 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13093 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13093 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13093}
    (hw : WINDOW (paperDesignP 13093) c) (hc : c ∈ tableEvent) (K : Set (Ix 13093)) :
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

def proposedBaseEvent : Set (Ret 13093) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13093)) : Prop where
  charge : (retDist (paperCentres 13093)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13093)} (h : TablePayment H) :
    (retDist (paperCentres 13093)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13093)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13093

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13093
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13093) (i : Fin 4) (a : Ix 13093) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13093) (a : Ix 13093) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13093) : Prop where
  moment : ∀ i, MomentBound (muI 13093) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13093} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13093) 8 (actualFourError c i)
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

end BstLean.Part266.Row13093

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13093
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

structure LatitudeVarianceCertificate (c : Ret 13093) : Prop where
  location : LBound (muI 13093) 12
    (fun a => conditionalVariance (stdGauss (Fin (13093 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13093) 12
    (fun a => conditionalVariance (stdGauss (Fin (13093 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13093) (hw : WINDOW (paperDesignP 13093) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13093 4 (55 / 100) /
      (13093 : ℝ) / ((13093 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13093

/-! The dimension-13093 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13093
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13093) (wl ws : ℝ) : SplitData 13093 :=
  BstLean.Part162.dPaper (paperDesignP 13093) c wl ws
    (√(2 / (13093 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13093 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13093 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13093) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13093) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13093 : ℝ)) * eR c * 13093 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13093) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13093 - 1)))
    (rowSplit c wl ws).good a ∂muI 13093 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13093) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13093 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13093) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13093 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13093) c (rowSplit c wl ws),
    hellG2 13093 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13093 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13093} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13093} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13093 t c BstLean.Part266.agent13093.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13093} (R : RootSource t c) :
    |√(QStand (paperDesignP 13093) t c) - √(qTilde (paperDesignP 13093) t c)| ≤
      BstLean.Part266.agent13093.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13093

/-! Rational enclosures for the HQ fluctuation price at dimension 13094. -/
namespace BstLean.Part266.Row13094
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1622069401 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22549241 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13094 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13094 * A / 2 + D + L * √(A * D)) ≤ (933356827 / 200000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13094 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1622069401 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13094 L e4 d4 ≤ (8456062103 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13094 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1622069401 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13094 L e6 d6 ≤ (32025982459 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13094 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1622069401 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13094 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13094 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13094 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13094 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22549241 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((933356827 / 200000000000)) ^ 2 / 2 + ((933356827 / 200000000000)) * ((8456062103 / 200000000000)) ^ 2 / 6 +
      ((8456062103 / 200000000000)) ^ 4 / 24 + ((8456062103 / 200000000000)) ^ 2 * ((32025982459 / 500000000000)) ^ 3 / 120 +
      2187 * ((32025982459 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13094 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13094 : ℝ) * ((1 + 3 * ((22549241 / 1000000000))) / (4 * (1 - (22549241 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22549241 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13094 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22549241 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13094 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13094 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13094

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13094
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((114429017 / 1000000) : ℝ) ≤ √13094 ∧ √13094 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1498332 : ℝ) ≤ Jz 13094 ∧ 1000000 ≤ Jz 13094 := by
  have hr : ((114429017 / 1000000) : ℝ) ≤ √13094 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13094 : ℝ) * √13094 ≤ (⌈(13094 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13094
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13094 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13094 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13094 : ℝ) = (⌈(13094 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1498332 : ℝ) ≤ Jz 13094 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13094 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13094) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13094 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13094 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13094 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13094 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13094 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13094 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13094) :
    (13094 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13094 * √(qB 13094))) ≤
      (275644519 / 500000000000) := by
  have hden : ((114429017 / 1000000) : ℝ) * (63 / 100) ≤ √13094 * √(qB 13094) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13094 : ℝ) * √(qB 13094) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13094) :
    (13094 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13094 * √(qB 13094))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13094 : ℝ) * √(qB 13094) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13094 : ℝ) * (√13094 *
      (c1F (exp (1 / 2) / 12) (Jz 13094) * (186 / 10000) / Jz 13094)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13094)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13094 : ℝ) * (√13094 *
      (c1F (exp (1 / 2) / 12) (Jz 13094) * (186 / 10000) / Jz 13094)) =
      (13094 * (√13094 * c1F (exp (1 / 2) / 12) (Jz 13094)) * (186 / 10000)) /
        Jz 13094 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13094)]
  nlinarith

theorem row_energy_rule :
    (13094 : ℝ) * (13094 *
      (c2F (exp (1 / 2) / 12) (Jz 13094) * (186 / 10000) ^ 2 / Jz 13094)) ≤
      (1781455673 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13094)]
  nlinarith

end BstLean.Part266.Row13094

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13094
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13094) (hc : A1 c ∈ BstLean.Part153.Eop 13094) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13094 : ℝ)) ≤ (2471774373 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13094 : ℝ) + 2 * √13094 ≤ (3330714509 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13094 : ℝ) ≤ (57214509 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13094)
    (hc : A1 c ∈ BstLean.Part153.Eop 13094) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13094 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13094 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13094))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13094) (K : Set (Ix 13094)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13094 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13094 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13094) (hw : WINDOW (paperDesignP 13094) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13094)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13094) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13094 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13094 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13094 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13094 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13094) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13094)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13094)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13094

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13094
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13094) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13094 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13094) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13094) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13094 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13094 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13094 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13094}
    (hw : WINDOW (paperDesignP 13094) c) (hc : c ∈ tableEvent) (K : Set (Ix 13094)) :
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

def proposedBaseEvent : Set (Ret 13094) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13094)) : Prop where
  charge : (retDist (paperCentres 13094)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13094)} (h : TablePayment H) :
    (retDist (paperCentres 13094)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13094)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13094

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13094
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13094) (i : Fin 4) (a : Ix 13094) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13094) (a : Ix 13094) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13094) : Prop where
  moment : ∀ i, MomentBound (muI 13094) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13094} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13094) 8 (actualFourError c i)
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

end BstLean.Part266.Row13094

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13094
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

structure LatitudeVarianceCertificate (c : Ret 13094) : Prop where
  location : LBound (muI 13094) 12
    (fun a => conditionalVariance (stdGauss (Fin (13094 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13094) 12
    (fun a => conditionalVariance (stdGauss (Fin (13094 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13094) (hw : WINDOW (paperDesignP 13094) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13094 4 (55 / 100) /
      (13094 : ℝ) / ((13094 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13094

/-! The dimension-13094 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13094
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13094) (wl ws : ℝ) : SplitData 13094 :=
  BstLean.Part162.dPaper (paperDesignP 13094) c wl ws
    (√(2 / (13094 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13094 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13094 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13094) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13094) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13094 : ℝ)) * eR c * 13094 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13094) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13094 - 1)))
    (rowSplit c wl ws).good a ∂muI 13094 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13094) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13094 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13094) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13094 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13094) c (rowSplit c wl ws),
    hellG2 13094 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13094 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13094} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13094} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13094 t c BstLean.Part266.agent13094.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13094} (R : RootSource t c) :
    |√(QStand (paperDesignP 13094) t c) - √(qTilde (paperDesignP 13094) t c)| ≤
      BstLean.Part266.agent13094.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13094

/-! Rational enclosures for the HQ fluctuation price at dimension 13095. -/
namespace BstLean.Part266.Row13095
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1622007343 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (22547507 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13095 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13095 * A / 2 + D + L * √(A * D)) ≤ (4666985537 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13095 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1622007343 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13095 L e4 d4 ≤ (8456427939 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13095 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1622007343 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13095 L e6 d6 ≤ (3202736423 / 50000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13095 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1622007343 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13095 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13095 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13095 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13095 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (22547507 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4666985537 / 1000000000000)) ^ 2 / 2 + ((4666985537 / 1000000000000)) * ((8456427939 / 200000000000)) ^ 2 / 6 +
      ((8456427939 / 200000000000)) ^ 4 / 24 + ((8456427939 / 200000000000)) ^ 2 * ((3202736423 / 50000000000)) ^ 3 / 120 +
      2187 * ((3202736423 / 50000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13095 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13095 : ℝ) * ((1 + 3 * ((22547507 / 1000000000))) / (4 * (1 - (22547507 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (22547507 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13095 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (22547507 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13095 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13095 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13095

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13095
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((57216693 / 500000) : ℝ) ≤ √13095 ∧ √13095 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1498504 : ℝ) ≤ Jz 13095 ∧ 1000000 ≤ Jz 13095 := by
  have hr : ((57216693 / 500000) : ℝ) ≤ √13095 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13095 : ℝ) * √13095 ≤ (⌈(13095 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13095
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13095 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13095 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13095 : ℝ) = (⌈(13095 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1498504 : ℝ) ≤ Jz 13095 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13095 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13095) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13095 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13095 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13095 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13095 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13095 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13095 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13095) :
    (13095 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13095 * √(qB 13095))) ≤
      (551310091 / 1000000000000) := by
  have hden : ((57216693 / 500000) : ℝ) * (63 / 100) ≤ √13095 * √(qB 13095) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13095 : ℝ) * √(qB 13095) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13095) :
    (13095 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13095 * √(qB 13095))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13095 : ℝ) * √(qB 13095) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13095 : ℝ) * (√13095 *
      (c1F (exp (1 / 2) / 12) (Jz 13095) * (186 / 10000) / Jz 13095)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13095)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13095 : ℝ) * (√13095 *
      (c1F (exp (1 / 2) / 12) (Jz 13095) * (186 / 10000) / Jz 13095)) =
      (13095 * (√13095 * c1F (exp (1 / 2) / 12) (Jz 13095)) * (186 / 10000)) /
        Jz 13095 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13095)]
  nlinarith

theorem row_energy_rule :
    (13095 : ℝ) * (13095 *
      (c2F (exp (1 / 2) / 12) (Jz 13095) * (186 / 10000) ^ 2 / Jz 13095)) ≤
      (712609311 / 200000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13095)]
  nlinarith

end BstLean.Part266.Row13095

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13095
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13095) (hc : A1 c ∈ BstLean.Part153.Eop 13095) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13095 : ℝ)) ≤ (12358399963 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13095 : ℝ) + 2 * √13095 ≤ (6661933387 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13095 : ℝ) ≤ (114433387 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13095)
    (hc : A1 c ∈ BstLean.Part153.Eop 13095) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13095 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13095 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13095))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13095) (K : Set (Ix 13095)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13095 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13095 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13095) (hw : WINDOW (paperDesignP 13095) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13095)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13095) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13095 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13095 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13095 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13095 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13095) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13095)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13095)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13095

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13095
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13095) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13095 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13095) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13095) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13095 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13095 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13095 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13095}
    (hw : WINDOW (paperDesignP 13095) c) (hc : c ∈ tableEvent) (K : Set (Ix 13095)) :
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

def proposedBaseEvent : Set (Ret 13095) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13095)) : Prop where
  charge : (retDist (paperCentres 13095)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13095)} (h : TablePayment H) :
    (retDist (paperCentres 13095)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13095)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13095

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13095
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13095) (i : Fin 4) (a : Ix 13095) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13095) (a : Ix 13095) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13095) : Prop where
  moment : ∀ i, MomentBound (muI 13095) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13095} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13095) 8 (actualFourError c i)
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

end BstLean.Part266.Row13095

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13095
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

structure LatitudeVarianceCertificate (c : Ret 13095) : Prop where
  location : LBound (muI 13095) 12
    (fun a => conditionalVariance (stdGauss (Fin (13095 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13095) 12
    (fun a => conditionalVariance (stdGauss (Fin (13095 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13095) (hw : WINDOW (paperDesignP 13095) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13095 4 (55 / 100) /
      (13095 : ℝ) / ((13095 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13095

/-! The dimension-13095 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13095
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13095) (wl ws : ℝ) : SplitData 13095 :=
  BstLean.Part162.dPaper (paperDesignP 13095) c wl ws
    (√(2 / (13095 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13095 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13095 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13095) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13095) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13095 : ℝ)) * eR c * 13095 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13095) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13095 - 1)))
    (rowSplit c wl ws).good a ∂muI 13095 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13095) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13095 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13095) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13095 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13095) c (rowSplit c wl ws),
    hellG2 13095 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13095 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13095} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13095} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13095 t c BstLean.Part266.agent13095.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13095} (R : RootSource t c) :
    |√(QStand (paperDesignP 13095) t c) - √(qTilde (paperDesignP 13095) t c)| ≤
      BstLean.Part266.agent13095.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13095

/-! Rational enclosures for the HQ fluctuation price at dimension 13096. -/
namespace BstLean.Part266.Row13096
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (810972649 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (901831 / 40000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13096 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13096 * A / 2 + D + L * √(A * D)) ≤ (4667186939 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13096 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((810972649 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13096 L e4 d4 ≤ (42283968879 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13096 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((810972649 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13096 L e6 d6 ≤ (64057492007 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13096 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((810972649 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13096 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13096 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13096 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13096 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (901831 / 40000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4667186939 / 1000000000000)) ^ 2 / 2 + ((4667186939 / 1000000000000)) * ((42283968879 / 1000000000000)) ^ 2 / 6 +
      ((42283968879 / 1000000000000)) ^ 4 / 24 + ((42283968879 / 1000000000000)) ^ 2 * ((64057492007 / 1000000000000)) ^ 3 / 120 +
      2187 * ((64057492007 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13096 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13096 : ℝ) * ((1 + 3 * ((901831 / 40000000))) / (4 * (1 - (901831 / 40000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (901831 / 40000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13096 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (901831 / 40000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13096 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13096 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13096

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13096
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((28609439 / 250000) : ℝ) ≤ √13096 ∧ √13096 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1498675 : ℝ) ≤ Jz 13096 ∧ 1000000 ≤ Jz 13096 := by
  have hr : ((28609439 / 250000) : ℝ) ≤ √13096 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13096 : ℝ) * √13096 ≤ (⌈(13096 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13096
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13096 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13096 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13096 : ℝ) = (⌈(13096 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1498675 : ℝ) ≤ Jz 13096 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13096 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13096) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13096 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13096 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13096 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13096 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13096 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13096 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13096) :
    (13096 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13096 * √(qB 13096))) ≤
      (551331137 / 1000000000000) := by
  have hden : ((28609439 / 250000) : ℝ) * (63 / 100) ≤ √13096 * √(qB 13096) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13096 : ℝ) * √(qB 13096) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13096) :
    (13096 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13096 * √(qB 13096))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13096 : ℝ) * √(qB 13096) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13096 : ℝ) * (√13096 *
      (c1F (exp (1 / 2) / 12) (Jz 13096) * (186 / 10000) / Jz 13096)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13096)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13096 : ℝ) * (√13096 *
      (c1F (exp (1 / 2) / 12) (Jz 13096) * (186 / 10000) / Jz 13096)) =
      (13096 * (√13096 * c1F (exp (1 / 2) / 12) (Jz 13096)) * (186 / 10000)) /
        Jz 13096 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13096)]
  nlinarith

theorem row_energy_rule :
    (13096 : ℝ) * (13096 *
      (c2F (exp (1 / 2) / 12) (Jz 13096) * (186 / 10000) ^ 2 / Jz 13096)) ≤
      (3563184151 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13096)]
  nlinarith

end BstLean.Part266.Row13096

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13096
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13096) (hc : A1 c ∈ BstLean.Part153.Eop 13096) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13096 : ℝ)) ≤ (2471585623 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13096 : ℝ) + 2 * √13096 ≤ (6662437757 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13096 : ℝ) ≤ (114437757 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13096)
    (hc : A1 c ∈ BstLean.Part153.Eop 13096) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13096 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13096 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13096))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13096) (K : Set (Ix 13096)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13096 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13096 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13096) (hw : WINDOW (paperDesignP 13096) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13096)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13096) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13096 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13096 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13096 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13096 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13096) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13096)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13096)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13096

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13096
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13096) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13096 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13096) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13096) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13096 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13096 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13096 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13096}
    (hw : WINDOW (paperDesignP 13096) c) (hc : c ∈ tableEvent) (K : Set (Ix 13096)) :
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

def proposedBaseEvent : Set (Ret 13096) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13096)) : Prop where
  charge : (retDist (paperCentres 13096)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13096)} (h : TablePayment H) :
    (retDist (paperCentres 13096)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13096)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13096

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13096
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13096) (i : Fin 4) (a : Ix 13096) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13096) (a : Ix 13096) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13096) : Prop where
  moment : ∀ i, MomentBound (muI 13096) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13096} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13096) 8 (actualFourError c i)
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

end BstLean.Part266.Row13096

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13096
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

structure LatitudeVarianceCertificate (c : Ret 13096) : Prop where
  location : LBound (muI 13096) 12
    (fun a => conditionalVariance (stdGauss (Fin (13096 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13096) 12
    (fun a => conditionalVariance (stdGauss (Fin (13096 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13096) (hw : WINDOW (paperDesignP 13096) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13096 4 (55 / 100) /
      (13096 : ℝ) / ((13096 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13096

/-! The dimension-13096 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13096
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13096) (wl ws : ℝ) : SplitData 13096 :=
  BstLean.Part162.dPaper (paperDesignP 13096) c wl ws
    (√(2 / (13096 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13096 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13096 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13096) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13096) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13096 : ℝ)) * eR c * 13096 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13096) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13096 - 1)))
    (rowSplit c wl ws).good a ∂muI 13096 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13096) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13096 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13096) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13096 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13096) c (rowSplit c wl ws),
    hellG2 13096 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13096 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13096} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13096} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13096 t c BstLean.Part266.agent13096.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13096} (R : RootSource t c) :
    |√(QStand (paperDesignP 13096) t c) - √(qTilde (paperDesignP 13096) t c)| ≤
      BstLean.Part266.agent13096.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13096

/-! Rational enclosures for the HQ fluctuation price at dimension 13097. -/
namespace BstLean.Part266.Row13097
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1621883267 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11272021 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13097 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13097 * A / 2 + D + L * √(A * D)) ≤ (4667388341 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13097 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1621883267 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13097 L e4 d4 ≤ (21142899033 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13097 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1621883267 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13097 L e6 d6 ≤ (64060255559 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13097 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1621883267 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13097 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13097 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13097 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13097 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11272021 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4667388341 / 1000000000000)) ^ 2 / 2 + ((4667388341 / 1000000000000)) * ((21142899033 / 500000000000)) ^ 2 / 6 +
      ((21142899033 / 500000000000)) ^ 4 / 24 + ((21142899033 / 500000000000)) ^ 2 * ((64060255559 / 1000000000000)) ^ 3 / 120 +
      2187 * ((64060255559 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13097 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13097 : ℝ) * ((1 + 3 * ((11272021 / 500000000))) / (4 * (1 - (11272021 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11272021 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13097 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11272021 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13097 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13097 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13097

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13097
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((915537 / 8000) : ℝ) ≤ √13097 ∧ √13097 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1498847 : ℝ) ≤ Jz 13097 ∧ 1000000 ≤ Jz 13097 := by
  have hr : ((915537 / 8000) : ℝ) ≤ √13097 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13097 : ℝ) * √13097 ≤ (⌈(13097 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13097
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13097 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13097 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13097 : ℝ) = (⌈(13097 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1498847 : ℝ) ≤ Jz 13097 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13097 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13097) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13097 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13097 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13097 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13097 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13097 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13097 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13097) :
    (13097 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13097 * √(qB 13097))) ≤
      (551352187 / 1000000000000) := by
  have hden : ((915537 / 8000) : ℝ) * (63 / 100) ≤ √13097 * √(qB 13097) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13097 : ℝ) * √(qB 13097) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13097) :
    (13097 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13097 * √(qB 13097))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13097 : ℝ) * √(qB 13097) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13097 : ℝ) * (√13097 *
      (c1F (exp (1 / 2) / 12) (Jz 13097) * (186 / 10000) / Jz 13097)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13097)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13097 : ℝ) * (√13097 *
      (c1F (exp (1 / 2) / 12) (Jz 13097) * (186 / 10000) / Jz 13097)) =
      (13097 * (√13097 * c1F (exp (1 / 2) / 12) (Jz 13097)) * (186 / 10000)) /
        Jz 13097 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13097)]
  nlinarith

theorem row_energy_rule :
    (13097 : ℝ) * (13097 *
      (c2F (exp (1 / 2) / 12) (Jz 13097) * (186 / 10000) ^ 2 / Jz 13097)) ≤
      (3563319381 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13097)]
  nlinarith

end BstLean.Part266.Row13097

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13097
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13097) (hc : A1 c ∈ BstLean.Part153.Eop 13097) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13097 : ℝ)) ≤ (6178728161 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13097 : ℝ) + 2 * √13097 ≤ (3331471063 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13097 : ℝ) ≤ (57221063 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13097)
    (hc : A1 c ∈ BstLean.Part153.Eop 13097) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13097 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13097 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13097))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13097) (K : Set (Ix 13097)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13097 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13097 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13097) (hw : WINDOW (paperDesignP 13097) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13097)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13097) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13097 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13097 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13097 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13097 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13097) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13097)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13097)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13097

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13097
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13097) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13097 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13097) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13097) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13097 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13097 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13097 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13097}
    (hw : WINDOW (paperDesignP 13097) c) (hc : c ∈ tableEvent) (K : Set (Ix 13097)) :
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

def proposedBaseEvent : Set (Ret 13097) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13097)) : Prop where
  charge : (retDist (paperCentres 13097)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13097)} (h : TablePayment H) :
    (retDist (paperCentres 13097)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13097)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13097

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13097
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13097) (i : Fin 4) (a : Ix 13097) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13097) (a : Ix 13097) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13097) : Prop where
  moment : ∀ i, MomentBound (muI 13097) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13097} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13097) 8 (actualFourError c i)
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

end BstLean.Part266.Row13097

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13097
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

structure LatitudeVarianceCertificate (c : Ret 13097) : Prop where
  location : LBound (muI 13097) 12
    (fun a => conditionalVariance (stdGauss (Fin (13097 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13097) 12
    (fun a => conditionalVariance (stdGauss (Fin (13097 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13097) (hw : WINDOW (paperDesignP 13097) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13097 4 (55 / 100) /
      (13097 : ℝ) / ((13097 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13097

/-! The dimension-13097 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13097
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13097) (wl ws : ℝ) : SplitData 13097 :=
  BstLean.Part162.dPaper (paperDesignP 13097) c wl ws
    (√(2 / (13097 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13097 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13097 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13097) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13097) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13097 : ℝ)) * eR c * 13097 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13097) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13097 - 1)))
    (rowSplit c wl ws).good a ∂muI 13097 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13097) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13097 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13097) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13097 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13097) c (rowSplit c wl ws),
    hellG2 13097 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13097 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13097} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13097} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13097 t c BstLean.Part266.agent13097.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13097} (R : RootSource t c) :
    |√(QStand (paperDesignP 13097) t c) - √(qTilde (paperDesignP 13097) t c)| ≤
      BstLean.Part266.agent13097.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13097

/-! Rational enclosures for the HQ fluctuation price at dimension 13098. -/
namespace BstLean.Part266.Row13098
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1621821249 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (2254231 / 100000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13098 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13098 * A / 2 + D + L * √(A * D)) ≤ (291724359 / 62500000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13098 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1621821249 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13098 L e4 d4 ≤ (42287627257 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13098 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1621821249 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13098 L e6 d6 ≤ (64063019117 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13098 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1621821249 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13098 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13098 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13098 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13098 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (2254231 / 100000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((291724359 / 62500000000)) ^ 2 / 2 + ((291724359 / 62500000000)) * ((42287627257 / 1000000000000)) ^ 2 / 6 +
      ((42287627257 / 1000000000000)) ^ 4 / 24 + ((42287627257 / 1000000000000)) ^ 2 * ((64063019117 / 1000000000000)) ^ 3 / 120 +
      2187 * ((64063019117 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13098 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13098 : ℝ) * ((1 + 3 * ((2254231 / 100000000))) / (4 * (1 - (2254231 / 100000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (2254231 / 100000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13098 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (2254231 / 100000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13098 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13098 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13098

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13098
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((57223247 / 500000) : ℝ) ≤ √13098 ∧ √13098 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1499019 : ℝ) ≤ Jz 13098 ∧ 1000000 ≤ Jz 13098 := by
  have hr : ((57223247 / 500000) : ℝ) ≤ √13098 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13098 : ℝ) * √13098 ≤ (⌈(13098 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13098
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13098 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13098 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13098 : ℝ) = (⌈(13098 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1499019 : ℝ) ≤ Jz 13098 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13098 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13098) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13098 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13098 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13098 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13098 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13098 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13098 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13098) :
    (13098 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13098 * √(qB 13098))) ≤
      (110274647 / 200000000000) := by
  have hden : ((57223247 / 500000) : ℝ) * (63 / 100) ≤ √13098 * √(qB 13098) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13098 : ℝ) * √(qB 13098) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13098) :
    (13098 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13098 * √(qB 13098))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13098 : ℝ) * √(qB 13098) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13098 : ℝ) * (√13098 *
      (c1F (exp (1 / 2) / 12) (Jz 13098) * (186 / 10000) / Jz 13098)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13098)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13098 : ℝ) * (√13098 *
      (c1F (exp (1 / 2) / 12) (Jz 13098) * (186 / 10000) / Jz 13098)) =
      (13098 * (√13098 * c1F (exp (1 / 2) / 12) (Jz 13098)) * (186 / 10000)) /
        Jz 13098 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13098)]
  nlinarith

theorem row_energy_rule :
    (13098 : ℝ) * (13098 *
      (c2F (exp (1 / 2) / 12) (Jz 13098) * (186 / 10000) ^ 2 / Jz 13098)) ≤
      (3563454621 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13098)]
  nlinarith

end BstLean.Part266.Row13098

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13098
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13098) (hc : A1 c ∈ BstLean.Part153.Eop 13098) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13098 : ℝ)) ≤ (6178492291 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13098 : ℝ) + 2 * √13098 ≤ (1332689299 / 100000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13098 : ℝ) ≤ (22889299 / 200000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13098)
    (hc : A1 c ∈ BstLean.Part153.Eop 13098) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13098 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13098 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13098))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13098) (K : Set (Ix 13098)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13098 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13098 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13098) (hw : WINDOW (paperDesignP 13098) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13098)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13098) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13098 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13098 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13098 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13098 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13098) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13098)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13098)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13098

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13098
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13098) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13098 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13098) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13098) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13098 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13098 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13098 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13098}
    (hw : WINDOW (paperDesignP 13098) c) (hc : c ∈ tableEvent) (K : Set (Ix 13098)) :
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

def proposedBaseEvent : Set (Ret 13098) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13098)) : Prop where
  charge : (retDist (paperCentres 13098)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13098)} (h : TablePayment H) :
    (retDist (paperCentres 13098)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13098)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13098

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13098
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13098) (i : Fin 4) (a : Ix 13098) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13098) (a : Ix 13098) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13098) : Prop where
  moment : ∀ i, MomentBound (muI 13098) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13098} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13098) 8 (actualFourError c i)
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

end BstLean.Part266.Row13098

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13098
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

structure LatitudeVarianceCertificate (c : Ret 13098) : Prop where
  location : LBound (muI 13098) 12
    (fun a => conditionalVariance (stdGauss (Fin (13098 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13098) 12
    (fun a => conditionalVariance (stdGauss (Fin (13098 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13098) (hw : WINDOW (paperDesignP 13098) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13098 4 (55 / 100) /
      (13098 : ℝ) / ((13098 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13098

/-! The dimension-13098 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13098
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13098) (wl ws : ℝ) : SplitData 13098 :=
  BstLean.Part162.dPaper (paperDesignP 13098) c wl ws
    (√(2 / (13098 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13098 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13098 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13098) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13098) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13098 : ℝ)) * eR c * 13098 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13098) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13098 - 1)))
    (rowSplit c wl ws).good a ∂muI 13098 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13098) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13098 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13098) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13098 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13098) c (rowSplit c wl ws),
    hellG2 13098 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13098 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13098} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13098} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13098 t c BstLean.Part266.agent13098.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13098} (R : RootSource t c) :
    |√(QStand (paperDesignP 13098) t c) - √(qTilde (paperDesignP 13098) t c)| ≤
      BstLean.Part266.agent13098.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13098

/-! Rational enclosures for the HQ fluctuation price at dimension 13099. -/
namespace BstLean.Part266.Row13099
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1621759247 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11270289 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 13099 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (13099 * A / 2 + D + L * √(A * D)) ≤ (4667791147 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13099 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1621759247 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 13099 L e4 d4 ≤ (42289456451 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13099 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1621759247 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 13099 L e6 d6 ≤ (1601644567 / 25000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (13099 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1621759247 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (13099 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 13099 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 13099 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (13099 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11270289 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4667791147 / 1000000000000)) ^ 2 / 2 + ((4667791147 / 1000000000000)) * ((42289456451 / 1000000000000)) ^ 2 / 6 +
      ((42289456451 / 1000000000000)) ^ 4 / 24 + ((42289456451 / 1000000000000)) ^ 2 * ((1601644567 / 25000000000)) ^ 3 / 120 +
      2187 * ((1601644567 / 25000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 13099 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((13099 : ℝ) * ((1 + 3 * ((11270289 / 500000000))) / (4 * (1 - (11270289 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11270289 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (13099 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11270289 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 13099 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 13099 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row13099

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row13099
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((57225431 / 500000) : ℝ) ≤ √13099 ∧ √13099 ≤ 115 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1499190 : ℝ) ≤ Jz 13099 ∧ 1000000 ≤ Jz 13099 := by
  have hr : ((57225431 / 500000) : ℝ) ≤ √13099 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (13099 : ℝ) * √13099 ≤ (⌈(13099 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 13099
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(13099 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(13099 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 13099 : ℝ) = (⌈(13099 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1499190 : ℝ) ≤ Jz 13099 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 13099 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 13099) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (13099 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13099 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (13099 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 13099 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 13099 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (13099 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 13099) :
    (13099 : ℝ) * (283 / 100 * 165 * (d / 2) / (√13099 * √(qB 13099))) ≤
      (275697143 / 500000000000) := by
  have hden : ((57225431 / 500000) : ℝ) * (63 / 100) ≤ √13099 * √(qB 13099) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(13099 : ℝ) * √(qB 13099) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 13099) :
    (13099 : ℝ) * (2 * (283 / 100 * 165) ^ 2 * (d / 2) /
      (13099 * √(qB 13099))) ≤ (562410701 / 125000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (13099 : ℝ) * √(qB 13099) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (13099 : ℝ) * (√13099 *
      (c1F (exp (1 / 2) / 12) (Jz 13099) * (186 / 10000) / Jz 13099)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 13099)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 115)
  have he : (13099 : ℝ) * (√13099 *
      (c1F (exp (1 / 2) / 12) (Jz 13099) * (186 / 10000) / Jz 13099)) =
      (13099 * (√13099 * c1F (exp (1 / 2) / 12) (Jz 13099)) * (186 / 10000)) /
        Jz 13099 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13099)]
  nlinarith

theorem row_energy_rule :
    (13099 : ℝ) * (13099 *
      (c2F (exp (1 / 2) / 12) (Jz 13099) * (186 / 10000) ^ 2 / Jz 13099)) ≤
      (445449031 / 125000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 13099)]
  nlinarith

end BstLean.Part266.Row13099

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row13099
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 13099) (hc : A1 c ∈ BstLean.Part153.Eop 13099) :
    BstLean.Part152.opN (A1 c) ≤ 165 := by
  refine hc.trans ?_
  have hs : √(2 / (13099 : ℝ)) ≤ (96535257 / 7812500000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (13099 : ℝ) + 2 * √13099 ≤ (6663950863 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(13099 : ℝ) ≤ (114450863 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 13099)
    (hc : A1 c ∈ BstLean.Part153.Eop 13099) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((13099 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      13099 * 165 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 13099))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 13099) (K : Set (Ix 13099)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 13099 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 13099 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 13099) (hw : WINDOW (paperDesignP 13099) c)
    (hc : c ∈ passEvent) {K : Set (Ix 13099)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 13099) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((13099 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 13099 ≤ energyError ^ 8) ∧
    (∫ a in K, ((13099 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 13099 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 13099) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 13099)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 13099)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row13099

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row13099
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 13099) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 13099 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 13099) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 13099) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 13099 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 13099 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 13099 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 13099}
    (hw : WINDOW (paperDesignP 13099) c) (hc : c ∈ tableEvent) (K : Set (Ix 13099)) :
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

def proposedBaseEvent : Set (Ret 13099) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 13099)) : Prop where
  charge : (retDist (paperCentres 13099)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 13099)} (h : TablePayment H) :
    (retDist (paperCentres 13099)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 13099)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row13099

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row13099
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 13099) (i : Fin 4) (a : Ix 13099) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 13099) (a : Ix 13099) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 13099) : Prop where
  moment : ∀ i, MomentBound (muI 13099) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 13099} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 13099) 8 (actualFourError c i)
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

end BstLean.Part266.Row13099

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row13099
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

structure LatitudeVarianceCertificate (c : Ret 13099) : Prop where
  location : LBound (muI 13099) 12
    (fun a => conditionalVariance (stdGauss (Fin (13099 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 13099) 12
    (fun a => conditionalVariance (stdGauss (Fin (13099 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 13099) (hw : WINDOW (paperDesignP 13099) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 13099 4 (55 / 100) /
      (13099 : ℝ) / ((13099 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row13099

/-! The dimension-13099 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row13099
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 13099) (wl ws : ℝ) : SplitData 13099 :=
  BstLean.Part162.dPaper (paperDesignP 13099) c wl ws
    (√(2 / (13099 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (13099 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (13099 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 13099) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 13099) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (13099 : ℝ)) * eR c * 13099 * chi
  moments : PaperMoments c (keptIx (paperDesignP 13099) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (13099 - 1)))
    (rowSplit c wl ws).good a ∂muI 13099 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 13099) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (13099 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 13099) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 13099 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 13099) c (rowSplit c wl ws),
    hellG2 13099 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 13099 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 13099} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 13099} (R : RootSource t c) :
    BstLean.Part243.RootInputs 13099 t c BstLean.Part266.agent13099.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 13099} (R : RootSource t c) :
    |√(QStand (paperDesignP 13099) t c) - √(qTilde (paperDesignP 13099) t c)| ≤
      BstLean.Part266.agent13099.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row13099
