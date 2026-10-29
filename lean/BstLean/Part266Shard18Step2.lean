import BstLean.Part266Shard18Step1


/-! Rational enclosures for the HQ fluctuation price at dimension 12800. -/
namespace BstLean.Part266.Row12800
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (820314071 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (2883829 / 125000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12800 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12800 * A / 2 + D + L * √(A * D)) ≤ (921516239 / 200000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12800 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((820314071 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12800 L e4 d4 ≤ (20871305857 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12800 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((820314071 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12800 L e6 d6 ≤ (12647921029 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12800 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((820314071 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12800 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12800 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12800 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12800 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (2883829 / 125000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((921516239 / 200000000000)) ^ 2 / 2 + ((921516239 / 200000000000)) * ((20871305857 / 500000000000)) ^ 2 / 6 +
      ((20871305857 / 500000000000)) ^ 4 / 24 + ((20871305857 / 500000000000)) ^ 2 * ((12647921029 / 200000000000)) ^ 3 / 120 +
      2187 * ((12647921029 / 200000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12800 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12800 : ℝ) * ((1 + 3 * ((2883829 / 125000000))) / (4 * (1 - (2883829 / 125000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (2883829 / 125000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12800 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (2883829 / 125000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12800 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12800 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12800

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12800
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((28284271 / 250000) : ℝ) ≤ √12800 ∧ √12800 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1448153 : ℝ) ≤ Jz 12800 ∧ 1000000 ≤ Jz 12800 := by
  have hr : ((28284271 / 250000) : ℝ) ≤ √12800 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12800 : ℝ) * √12800 ≤ (⌈(12800 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12800
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12800 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12800 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12800 : ℝ) = (⌈(12800 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1448153 : ℝ) ≤ Jz 12800 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12800 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12800) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12800 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12800 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12800 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12800 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12800 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12800 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12800) :
    (12800 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12800 * √(qB 12800))) ≤
      (538458003 / 1000000000000) := by
  have hden : ((28284271 / 250000) : ℝ) * (63 / 100) ≤ √12800 * √(qB 12800) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12800 : ℝ) * √(qB 12800) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12800) :
    (12800 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12800 * √(qB 12800))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12800 : ℝ) * √(qB 12800) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12800 : ℝ) * (√12800 *
      (c1F (exp (1 / 2) / 12) (Jz 12800) * (186 / 10000) / Jz 12800)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12800)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12800 : ℝ) * (√12800 *
      (c1F (exp (1 / 2) / 12) (Jz 12800) * (186 / 10000) / Jz 12800)) =
      (12800 * (√12800 * c1F (exp (1 / 2) / 12) (Jz 12800)) * (186 / 10000)) /
        Jz 12800 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12800)]
  nlinarith

theorem row_energy_rule :
    (12800 : ℝ) * (12800 *
      (c2F (exp (1 / 2) / 12) (Jz 12800) * (186 / 10000) ^ 2 / Jz 12800)) ≤
      (3522685639 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12800)]
  nlinarith

end BstLean.Part266.Row12800

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12800
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12800) (hc : A1 c ∈ BstLean.Part153.Eop 12800) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12800 : ℝ)) ≤ (12500000001 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12800 : ℝ) + 2 * √12800 ≤ (1302627417 / 100000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12800 : ℝ) ≤ (22627417 / 200000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12800)
    (hc : A1 c ∈ BstLean.Part153.Eop 12800) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12800 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12800 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12800))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12800) (K : Set (Ix 12800)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12800 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12800 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12800) (hw : WINDOW (paperDesignP 12800) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12800)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12800) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12800 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12800 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12800 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12800 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12800) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12800)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12800)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12800

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12800
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12800) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12800 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12800) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12800) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12800 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12800 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12800 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12800}
    (hw : WINDOW (paperDesignP 12800) c) (hc : c ∈ tableEvent) (K : Set (Ix 12800)) :
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

def proposedBaseEvent : Set (Ret 12800) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12800)) : Prop where
  charge : (retDist (paperCentres 12800)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12800)} (h : TablePayment H) :
    (retDist (paperCentres 12800)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12800)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12800

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12800
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12800) (i : Fin 4) (a : Ix 12800) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12800) (a : Ix 12800) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12800) : Prop where
  moment : ∀ i, MomentBound (muI 12800) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12800} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12800) 8 (actualFourError c i)
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

end BstLean.Part266.Row12800

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12800
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

structure LatitudeVarianceCertificate (c : Ret 12800) : Prop where
  location : LBound (muI 12800) 12
    (fun a => conditionalVariance (stdGauss (Fin (12800 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12800) 12
    (fun a => conditionalVariance (stdGauss (Fin (12800 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12800) (hw : WINDOW (paperDesignP 12800) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12800 4 (55 / 100) /
      (12800 : ℝ) / ((12800 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12800

/-! The dimension-12800 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12800
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12800) (wl ws : ℝ) : SplitData 12800 :=
  BstLean.Part162.dPaper (paperDesignP 12800) c wl ws
    (√(2 / (12800 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12800 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12800 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12800) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12800) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12800 : ℝ)) * eR c * 12800 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12800) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12800 - 1)))
    (rowSplit c wl ws).good a ∂muI 12800 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12800) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12800 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12800) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12800 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12800) c (rowSplit c wl ws),
    hellG2 12800 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12800 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12800} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12800} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12800 t c BstLean.Part266.agent12800.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12800} (R : RootSource t c) :
    |√(QStand (paperDesignP 12800) t c) - √(qTilde (paperDesignP 12800) t c)| ≤
      BstLean.Part266.agent12800.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12800

/-! Rational enclosures for the HQ fluctuation price at dimension 12801. -/
namespace BstLean.Part266.Row12801
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (65622561 / 40000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23068819 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12801 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12801 * A / 2 + D + L * √(A * D)) ≤ (4607782537 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12801 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((65622561 / 40000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12801 L e4 d4 ≤ (2609027523 / 62500000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12801 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((65622561 / 40000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12801 L e6 d6 ≤ (63242367889 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12801 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((65622561 / 40000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12801 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12801 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12801 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12801 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23068819 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4607782537 / 1000000000000)) ^ 2 / 2 + ((4607782537 / 1000000000000)) * ((2609027523 / 62500000000)) ^ 2 / 6 +
      ((2609027523 / 62500000000)) ^ 4 / 24 + ((2609027523 / 62500000000)) ^ 2 * ((63242367889 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63242367889 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12801 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12801 : ℝ) * ((1 + 3 * ((23068819 / 1000000000))) / (4 * (1 - (23068819 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23068819 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12801 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23068819 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12801 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12801 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12801

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12801
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((1767836 / 15625) : ℝ) ≤ √12801 ∧ √12801 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1448323 : ℝ) ≤ Jz 12801 ∧ 1000000 ≤ Jz 12801 := by
  have hr : ((1767836 / 15625) : ℝ) ≤ √12801 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12801 : ℝ) * √12801 ≤ (⌈(12801 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12801
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12801 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12801 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12801 : ℝ) = (⌈(12801 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1448323 : ℝ) ≤ Jz 12801 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12801 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12801) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12801 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12801 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12801 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12801 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12801 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12801 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12801) :
    (12801 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12801 * √(qB 12801))) ≤
      (538479033 / 1000000000000) := by
  have hden : ((1767836 / 15625) : ℝ) * (63 / 100) ≤ √12801 * √(qB 12801) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12801 : ℝ) * √(qB 12801) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12801) :
    (12801 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12801 * √(qB 12801))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12801 : ℝ) * √(qB 12801) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12801 : ℝ) * (√12801 *
      (c1F (exp (1 / 2) / 12) (Jz 12801) * (186 / 10000) / Jz 12801)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12801)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12801 : ℝ) * (√12801 *
      (c1F (exp (1 / 2) / 12) (Jz 12801) * (186 / 10000) / Jz 12801)) =
      (12801 * (√12801 * c1F (exp (1 / 2) / 12) (Jz 12801)) * (186 / 10000)) /
        Jz 12801 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12801)]
  nlinarith

theorem row_energy_rule :
    (12801 : ℝ) * (12801 *
      (c2F (exp (1 / 2) / 12) (Jz 12801) * (186 / 10000) ^ 2 / Jz 12801)) ≤
      (3522822533 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12801)]
  nlinarith

end BstLean.Part266.Row12801

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12801
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12801) (hc : A1 c ∈ BstLean.Part153.Eop 12801) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12801 : ℝ)) ≤ (3124877937 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12801 : ℝ) + 2 * √12801 ≤ (1302728301 / 100000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12801 : ℝ) ≤ (22628301 / 200000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12801)
    (hc : A1 c ∈ BstLean.Part153.Eop 12801) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12801 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12801 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12801))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12801) (K : Set (Ix 12801)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12801 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12801 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12801) (hw : WINDOW (paperDesignP 12801) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12801)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12801) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12801 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12801 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12801 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12801 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12801) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12801)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12801)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12801

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12801
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12801) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12801 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12801) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12801) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12801 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12801 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12801 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12801}
    (hw : WINDOW (paperDesignP 12801) c) (hc : c ∈ tableEvent) (K : Set (Ix 12801)) :
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

def proposedBaseEvent : Set (Ret 12801) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12801)) : Prop where
  charge : (retDist (paperCentres 12801)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12801)} (h : TablePayment H) :
    (retDist (paperCentres 12801)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12801)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12801

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12801
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12801) (i : Fin 4) (a : Ix 12801) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12801) (a : Ix 12801) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12801) : Prop where
  moment : ∀ i, MomentBound (muI 12801) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12801} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12801) 8 (actualFourError c i)
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

end BstLean.Part266.Row12801

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12801
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

structure LatitudeVarianceCertificate (c : Ret 12801) : Prop where
  location : LBound (muI 12801) 12
    (fun a => conditionalVariance (stdGauss (Fin (12801 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12801) 12
    (fun a => conditionalVariance (stdGauss (Fin (12801 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12801) (hw : WINDOW (paperDesignP 12801) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12801 4 (55 / 100) /
      (12801 : ℝ) / ((12801 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12801

/-! The dimension-12801 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12801
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12801) (wl ws : ℝ) : SplitData 12801 :=
  BstLean.Part162.dPaper (paperDesignP 12801) c wl ws
    (√(2 / (12801 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12801 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12801 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12801) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12801) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12801 : ℝ)) * eR c * 12801 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12801) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12801 - 1)))
    (rowSplit c wl ws).good a ∂muI 12801 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12801) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12801 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12801) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12801 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12801) c (rowSplit c wl ws),
    hellG2 12801 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12801 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12801} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12801} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12801 t c BstLean.Part266.agent12801.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12801} (R : RootSource t c) :
    |√(QStand (paperDesignP 12801) t c) - √(qTilde (paperDesignP 12801) t c)| ≤
      BstLean.Part266.agent12801.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12801

/-! Rational enclosures for the HQ fluctuation price at dimension 12802. -/
namespace BstLean.Part266.Row12802
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (820249961 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11533503 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12802 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12802 * A / 2 + D + L * √(A * D)) ≤ (4607983879 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12802 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((820249961 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12802 L e4 d4 ≤ (1669850761 / 40000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12802 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((820249961 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12802 L e6 d6 ≤ (63245130639 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12802 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((820249961 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12802 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12802 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12802 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12802 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11533503 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4607983879 / 1000000000000)) ^ 2 / 2 + ((4607983879 / 1000000000000)) * ((1669850761 / 40000000000)) ^ 2 / 6 +
      ((1669850761 / 40000000000)) ^ 4 / 24 + ((1669850761 / 40000000000)) ^ 2 * ((63245130639 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63245130639 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12802 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12802 : ℝ) * ((1 + 3 * ((11533503 / 500000000))) / (4 * (1 - (11533503 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11533503 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12802 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11533503 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12802 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12802 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12802

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12802
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113145923 / 1000000) : ℝ) ≤ √12802 ∧ √12802 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1448493 : ℝ) ≤ Jz 12802 ∧ 1000000 ≤ Jz 12802 := by
  have hr : ((113145923 / 1000000) : ℝ) ≤ √12802 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12802 : ℝ) * √12802 ≤ (⌈(12802 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12802
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12802 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12802 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12802 : ℝ) = (⌈(12802 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1448493 : ℝ) ≤ Jz 12802 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12802 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12802) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12802 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12802 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12802 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12802 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12802 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12802 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12802) :
    (12802 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12802 * √(qB 12802))) ≤
      (269250033 / 500000000000) := by
  have hden : ((113145923 / 1000000) : ℝ) * (63 / 100) ≤ √12802 * √(qB 12802) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12802 : ℝ) * √(qB 12802) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12802) :
    (12802 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12802 * √(qB 12802))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12802 : ℝ) * √(qB 12802) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12802 : ℝ) * (√12802 *
      (c1F (exp (1 / 2) / 12) (Jz 12802) * (186 / 10000) / Jz 12802)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12802)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12802 : ℝ) * (√12802 *
      (c1F (exp (1 / 2) / 12) (Jz 12802) * (186 / 10000) / Jz 12802)) =
      (12802 * (√12802 * c1F (exp (1 / 2) / 12) (Jz 12802)) * (186 / 10000)) /
        Jz 12802 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12802)]
  nlinarith

theorem row_energy_rule :
    (12802 : ℝ) * (12802 *
      (c2F (exp (1 / 2) / 12) (Jz 12802) * (186 / 10000) ^ 2 / Jz 12802)) ≤
      (1761479719 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12802)]
  nlinarith

end BstLean.Part266.Row12802

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12802
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12802) (hc : A1 c ∈ BstLean.Part153.Eop 12802) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12802 : ℝ)) ≤ (195297243 / 15625000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12802 : ℝ) + 2 * √12802 ≤ (1628536481 / 125000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12802 : ℝ) ≤ (28286481 / 250000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12802)
    (hc : A1 c ∈ BstLean.Part153.Eop 12802) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12802 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12802 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12802))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12802) (K : Set (Ix 12802)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12802 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12802 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12802) (hw : WINDOW (paperDesignP 12802) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12802)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12802) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12802 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12802 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12802 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12802 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12802) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12802)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12802)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12802

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12802
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12802) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12802 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12802) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12802) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12802 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12802 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12802 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12802}
    (hw : WINDOW (paperDesignP 12802) c) (hc : c ∈ tableEvent) (K : Set (Ix 12802)) :
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

def proposedBaseEvent : Set (Ret 12802) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12802)) : Prop where
  charge : (retDist (paperCentres 12802)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12802)} (h : TablePayment H) :
    (retDist (paperCentres 12802)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12802)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12802

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12802
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12802) (i : Fin 4) (a : Ix 12802) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12802) (a : Ix 12802) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12802) : Prop where
  moment : ∀ i, MomentBound (muI 12802) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12802} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12802) 8 (actualFourError c i)
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

end BstLean.Part266.Row12802

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12802
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

structure LatitudeVarianceCertificate (c : Ret 12802) : Prop where
  location : LBound (muI 12802) 12
    (fun a => conditionalVariance (stdGauss (Fin (12802 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12802) 12
    (fun a => conditionalVariance (stdGauss (Fin (12802 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12802) (hw : WINDOW (paperDesignP 12802) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12802 4 (55 / 100) /
      (12802 : ℝ) / ((12802 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12802

/-! The dimension-12802 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12802
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12802) (wl ws : ℝ) : SplitData 12802 :=
  BstLean.Part162.dPaper (paperDesignP 12802) c wl ws
    (√(2 / (12802 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12802 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12802 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12802) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12802) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12802 : ℝ)) * eR c * 12802 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12802) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12802 - 1)))
    (rowSplit c wl ws).good a ∂muI 12802 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12802) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12802 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12802) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12802 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12802) c (rowSplit c wl ws),
    hellG2 12802 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12802 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12802} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12802} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12802 t c BstLean.Part266.agent12802.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12802} (R : RootSource t c) :
    |√(QStand (paperDesignP 12802) t c) - √(qTilde (paperDesignP 12802) t c)| ≤
      BstLean.Part266.agent12802.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12802

/-! Rational enclosures for the HQ fluctuation price at dimension 12803. -/
namespace BstLean.Part266.Row12803
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (328087111 / 200000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (2306519 / 100000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12803 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12803 * A / 2 + D + L * √(A * D)) ≤ (4608185213 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12803 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((328087111 / 200000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12803 L e4 d4 ≤ (8349619523 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12803 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((328087111 / 200000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12803 L e6 d6 ≤ (31623946643 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12803 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((328087111 / 200000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12803 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12803 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12803 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12803 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (2306519 / 100000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4608185213 / 1000000000000)) ^ 2 / 2 + ((4608185213 / 1000000000000)) * ((8349619523 / 200000000000)) ^ 2 / 6 +
      ((8349619523 / 200000000000)) ^ 4 / 24 + ((8349619523 / 200000000000)) ^ 2 * ((31623946643 / 500000000000)) ^ 3 / 120 +
      2187 * ((31623946643 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12803 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12803 : ℝ) * ((1 + 3 * ((2306519 / 100000000))) / (4 * (1 - (2306519 / 100000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (2306519 / 100000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12803 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (2306519 / 100000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12803 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12803 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12803

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12803
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((56575171 / 500000) : ℝ) ≤ √12803 ∧ √12803 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1448662 : ℝ) ≤ Jz 12803 ∧ 1000000 ≤ Jz 12803 := by
  have hr : ((56575171 / 500000) : ℝ) ≤ √12803 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12803 : ℝ) * √12803 ≤ (⌈(12803 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12803
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12803 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12803 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12803 : ℝ) = (⌈(12803 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1448662 : ℝ) ≤ Jz 12803 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12803 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12803) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12803 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12803 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12803 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12803 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12803 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12803 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12803) :
    (12803 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12803 * √(qB 12803))) ≤
      (538521097 / 1000000000000) := by
  have hden : ((56575171 / 500000) : ℝ) * (63 / 100) ≤ √12803 * √(qB 12803) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12803 : ℝ) * √(qB 12803) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12803) :
    (12803 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12803 * √(qB 12803))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12803 : ℝ) * √(qB 12803) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12803 : ℝ) * (√12803 *
      (c1F (exp (1 / 2) / 12) (Jz 12803) * (186 / 10000) / Jz 12803)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12803)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12803 : ℝ) * (√12803 *
      (c1F (exp (1 / 2) / 12) (Jz 12803) * (186 / 10000) / Jz 12803)) =
      (12803 * (√12803 * c1F (exp (1 / 2) / 12) (Jz 12803)) * (186 / 10000)) /
        Jz 12803 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12803)]
  nlinarith

theorem row_energy_rule :
    (12803 : ℝ) * (12803 *
      (c2F (exp (1 / 2) / 12) (Jz 12803) * (186 / 10000) ^ 2 / Jz 12803)) ≤
      (704619757 / 200000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12803)]
  nlinarith

end BstLean.Part266.Row12803

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12803
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12803) (hc : A1 c ∈ BstLean.Part153.Eop 12803) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12803 : ℝ)) ≤ (6249267707 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12803 : ℝ) + 2 * √12803 ≤ (6514650343 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12803 : ℝ) ≤ (113150343 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12803)
    (hc : A1 c ∈ BstLean.Part153.Eop 12803) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12803 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12803 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12803))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12803) (K : Set (Ix 12803)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12803 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12803 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12803) (hw : WINDOW (paperDesignP 12803) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12803)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12803) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12803 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12803 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12803 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12803 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12803) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12803)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12803)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12803

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12803
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12803) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12803 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12803) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12803) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12803 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12803 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12803 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12803}
    (hw : WINDOW (paperDesignP 12803) c) (hc : c ∈ tableEvent) (K : Set (Ix 12803)) :
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

def proposedBaseEvent : Set (Ret 12803) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12803)) : Prop where
  charge : (retDist (paperCentres 12803)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12803)} (h : TablePayment H) :
    (retDist (paperCentres 12803)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12803)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12803

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12803
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12803) (i : Fin 4) (a : Ix 12803) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12803) (a : Ix 12803) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12803) : Prop where
  moment : ∀ i, MomentBound (muI 12803) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12803} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12803) 8 (actualFourError c i)
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

end BstLean.Part266.Row12803

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12803
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

structure LatitudeVarianceCertificate (c : Ret 12803) : Prop where
  location : LBound (muI 12803) 12
    (fun a => conditionalVariance (stdGauss (Fin (12803 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12803) 12
    (fun a => conditionalVariance (stdGauss (Fin (12803 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12803) (hw : WINDOW (paperDesignP 12803) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12803 4 (55 / 100) /
      (12803 : ℝ) / ((12803 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12803

/-! The dimension-12803 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12803
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12803) (wl ws : ℝ) : SplitData 12803 :=
  BstLean.Part162.dPaper (paperDesignP 12803) c wl ws
    (√(2 / (12803 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12803 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12803 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12803) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12803) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12803 : ℝ)) * eR c * 12803 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12803) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12803 - 1)))
    (rowSplit c wl ws).good a ∂muI 12803 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12803) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12803 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12803) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12803 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12803) c (rowSplit c wl ws),
    hellG2 12803 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12803 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12803} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12803} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12803 t c BstLean.Part266.agent12803.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12803} (R : RootSource t c) :
    |√(QStand (paperDesignP 12803) t c) - √(qTilde (paperDesignP 12803) t c)| ≤
      BstLean.Part266.agent12803.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12803

/-! Rational enclosures for the HQ fluctuation price at dimension 12804. -/
namespace BstLean.Part266.Row12804
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1640371481 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11531689 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12804 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12804 * A / 2 + D + L * √(A * D)) ≤ (1152096639 / 250000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12804 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1640371481 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12804 L e4 d4 ≤ (1043748157 / 25000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12804 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1640371481 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12804 L e6 d6 ≤ (63250656047 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12804 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1640371481 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12804 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12804 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12804 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12804 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11531689 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((1152096639 / 250000000000)) ^ 2 / 2 + ((1152096639 / 250000000000)) * ((1043748157 / 25000000000)) ^ 2 / 6 +
      ((1043748157 / 25000000000)) ^ 4 / 24 + ((1043748157 / 25000000000)) ^ 2 * ((63250656047 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63250656047 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12804 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12804 : ℝ) * ((1 + 3 * ((11531689 / 500000000))) / (4 * (1 - (11531689 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11531689 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12804 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11531689 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12804 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12804 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12804

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12804
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113154761 / 1000000) : ℝ) ≤ √12804 ∧ √12804 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1448832 : ℝ) ≤ Jz 12804 ∧ 1000000 ≤ Jz 12804 := by
  have hr : ((113154761 / 1000000) : ℝ) ≤ √12804 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12804 : ℝ) * √12804 ≤ (⌈(12804 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12804
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12804 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12804 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12804 : ℝ) = (⌈(12804 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1448832 : ℝ) ≤ Jz 12804 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12804 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12804) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12804 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12804 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12804 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12804 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12804 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12804 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12804) :
    (12804 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12804 * √(qB 12804))) ≤
      (538542127 / 1000000000000) := by
  have hden : ((113154761 / 1000000) : ℝ) * (63 / 100) ≤ √12804 * √(qB 12804) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12804 : ℝ) * √(qB 12804) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12804) :
    (12804 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12804 * √(qB 12804))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12804 : ℝ) * √(qB 12804) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12804 : ℝ) * (√12804 *
      (c1F (exp (1 / 2) / 12) (Jz 12804) * (186 / 10000) / Jz 12804)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12804)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12804 : ℝ) * (√12804 *
      (c1F (exp (1 / 2) / 12) (Jz 12804) * (186 / 10000) / Jz 12804)) =
      (12804 * (√12804 * c1F (exp (1 / 2) / 12) (Jz 12804)) * (186 / 10000)) /
        Jz 12804 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12804)]
  nlinarith

theorem row_energy_rule :
    (12804 : ℝ) * (12804 *
      (c2F (exp (1 / 2) / 12) (Jz 12804) * (186 / 10000) ^ 2 / Jz 12804)) ≤
      (3523235711 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12804)]
  nlinarith

end BstLean.Part266.Row12804

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12804
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12804) (hc : A1 c ∈ BstLean.Part153.Eop 12804) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12804 : ℝ)) ≤ (12498047333 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12804 : ℝ) + 2 * √12804 ≤ (3257577381 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12804 : ℝ) ≤ (56577381 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12804)
    (hc : A1 c ∈ BstLean.Part153.Eop 12804) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12804 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12804 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12804))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12804) (K : Set (Ix 12804)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12804 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12804 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12804) (hw : WINDOW (paperDesignP 12804) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12804)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12804) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12804 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12804 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12804 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12804 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12804) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12804)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12804)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12804

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12804
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12804) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12804 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12804) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12804) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12804 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12804 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12804 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12804}
    (hw : WINDOW (paperDesignP 12804) c) (hc : c ∈ tableEvent) (K : Set (Ix 12804)) :
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

def proposedBaseEvent : Set (Ret 12804) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12804)) : Prop where
  charge : (retDist (paperCentres 12804)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12804)} (h : TablePayment H) :
    (retDist (paperCentres 12804)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12804)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12804

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12804
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12804) (i : Fin 4) (a : Ix 12804) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12804) (a : Ix 12804) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12804) : Prop where
  moment : ∀ i, MomentBound (muI 12804) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12804} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12804) 8 (actualFourError c i)
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

end BstLean.Part266.Row12804

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12804
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

structure LatitudeVarianceCertificate (c : Ret 12804) : Prop where
  location : LBound (muI 12804) 12
    (fun a => conditionalVariance (stdGauss (Fin (12804 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12804) 12
    (fun a => conditionalVariance (stdGauss (Fin (12804 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12804) (hw : WINDOW (paperDesignP 12804) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12804 4 (55 / 100) /
      (12804 : ℝ) / ((12804 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12804

/-! The dimension-12804 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12804
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12804) (wl ws : ℝ) : SplitData 12804 :=
  BstLean.Part162.dPaper (paperDesignP 12804) c wl ws
    (√(2 / (12804 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12804 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12804 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12804) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12804) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12804 : ℝ)) * eR c * 12804 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12804) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12804 - 1)))
    (rowSplit c wl ws).good a ∂muI 12804 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12804) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12804 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12804) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12804 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12804) c (rowSplit c wl ws),
    hellG2 12804 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12804 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12804} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12804} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12804 t c BstLean.Part266.agent12804.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12804} (R : RootSource t c) :
    |√(QStand (paperDesignP 12804) t c) - √(qTilde (paperDesignP 12804) t c)| ≤
      BstLean.Part266.agent12804.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12804

/-! Rational enclosures for the HQ fluctuation price at dimension 12805. -/
namespace BstLean.Part266.Row12805
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (51259607 / 31250000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23061567 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12805 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12805 * A / 2 + D + L * √(A * D)) ≤ (46085879 / 10000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12805 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((51259607 / 31250000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12805 L e4 d4 ≤ (41751754949 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12805 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((51259607 / 31250000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12805 L e6 d6 ≤ (31626709407 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12805 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((51259607 / 31250000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12805 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12805 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12805 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12805 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23061567 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((46085879 / 10000000000)) ^ 2 / 2 + ((46085879 / 10000000000)) * ((41751754949 / 1000000000000)) ^ 2 / 6 +
      ((41751754949 / 1000000000000)) ^ 4 / 24 + ((41751754949 / 1000000000000)) ^ 2 * ((31626709407 / 500000000000)) ^ 3 / 120 +
      2187 * ((31626709407 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12805 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12805 : ℝ) * ((1 + 3 * ((23061567 / 1000000000))) / (4 * (1 - (23061567 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23061567 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12805 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23061567 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12805 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12805 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12805

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12805
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113159179 / 1000000) : ℝ) ≤ √12805 ∧ √12805 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1449002 : ℝ) ≤ Jz 12805 ∧ 1000000 ≤ Jz 12805 := by
  have hr : ((113159179 / 1000000) : ℝ) ≤ √12805 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12805 : ℝ) * √12805 ≤ (⌈(12805 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12805
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12805 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12805 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12805 : ℝ) = (⌈(12805 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1449002 : ℝ) ≤ Jz 12805 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12805 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12805) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12805 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12805 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12805 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12805 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12805 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12805 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12805) :
    (12805 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12805 * √(qB 12805))) ≤
      (13464079 / 25000000000) := by
  have hden : ((113159179 / 1000000) : ℝ) * (63 / 100) ≤ √12805 * √(qB 12805) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12805 : ℝ) * √(qB 12805) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12805) :
    (12805 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12805 * √(qB 12805))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12805 : ℝ) * √(qB 12805) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12805 : ℝ) * (√12805 *
      (c1F (exp (1 / 2) / 12) (Jz 12805) * (186 / 10000) / Jz 12805)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12805)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12805 : ℝ) * (√12805 *
      (c1F (exp (1 / 2) / 12) (Jz 12805) * (186 / 10000) / Jz 12805)) =
      (12805 * (√12805 * c1F (exp (1 / 2) / 12) (Jz 12805)) * (186 / 10000)) /
        Jz 12805 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12805)]
  nlinarith

theorem row_energy_rule :
    (12805 : ℝ) * (12805 *
      (c2F (exp (1 / 2) / 12) (Jz 12805) * (186 / 10000) ^ 2 / Jz 12805)) ≤
      (440421581 / 125000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12805)]
  nlinarith

end BstLean.Part266.Row12805

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12805
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12805) (hc : A1 c ∈ BstLean.Part153.Eop 12805) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12805 : ℝ)) ≤ (12497559309 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12805 : ℝ) + 2 * √12805 ≤ (325782959 / 25000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12805 : ℝ) ≤ (5657959 / 50000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12805)
    (hc : A1 c ∈ BstLean.Part153.Eop 12805) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12805 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12805 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12805))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12805) (K : Set (Ix 12805)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12805 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12805 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12805) (hw : WINDOW (paperDesignP 12805) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12805)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12805) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12805 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12805 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12805 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12805 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12805) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12805)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12805)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12805

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12805
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12805) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12805 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12805) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12805) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12805 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12805 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12805 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12805}
    (hw : WINDOW (paperDesignP 12805) c) (hc : c ∈ tableEvent) (K : Set (Ix 12805)) :
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

def proposedBaseEvent : Set (Ret 12805) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12805)) : Prop where
  charge : (retDist (paperCentres 12805)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12805)} (h : TablePayment H) :
    (retDist (paperCentres 12805)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12805)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12805

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12805
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12805) (i : Fin 4) (a : Ix 12805) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12805) (a : Ix 12805) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12805) : Prop where
  moment : ∀ i, MomentBound (muI 12805) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12805} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12805) 8 (actualFourError c i)
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

end BstLean.Part266.Row12805

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12805
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

structure LatitudeVarianceCertificate (c : Ret 12805) : Prop where
  location : LBound (muI 12805) 12
    (fun a => conditionalVariance (stdGauss (Fin (12805 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12805) 12
    (fun a => conditionalVariance (stdGauss (Fin (12805 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12805) (hw : WINDOW (paperDesignP 12805) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12805 4 (55 / 100) /
      (12805 : ℝ) / ((12805 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12805

/-! The dimension-12805 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12805
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12805) (wl ws : ℝ) : SplitData 12805 :=
  BstLean.Part162.dPaper (paperDesignP 12805) c wl ws
    (√(2 / (12805 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12805 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12805 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12805) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12805) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12805 : ℝ)) * eR c * 12805 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12805) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12805 - 1)))
    (rowSplit c wl ws).good a ∂muI 12805 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12805) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12805 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12805) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12805 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12805) c (rowSplit c wl ws),
    hellG2 12805 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12805 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12805} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12805} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12805 t c BstLean.Part266.agent12805.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12805} (R : RootSource t c) :
    |√(QStand (paperDesignP 12805) t c) - √(qTilde (paperDesignP 12805) t c)| ≤
      BstLean.Part266.agent12805.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12805

/-! Rational enclosures for the HQ fluctuation price at dimension 12806. -/
namespace BstLean.Part266.Row12806
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (820121551 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (2882469 / 125000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12806 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12806 * A / 2 + D + L * √(A * D)) ≤ (1152197309 / 250000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12806 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((820121551 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12806 L e4 d4 ≤ (41753583551 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12806 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((820121551 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12806 L e6 d6 ≤ (63256181479 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12806 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((820121551 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12806 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12806 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12806 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12806 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (2882469 / 125000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((1152197309 / 250000000000)) ^ 2 / 2 + ((1152197309 / 250000000000)) * ((41753583551 / 1000000000000)) ^ 2 / 6 +
      ((41753583551 / 1000000000000)) ^ 4 / 24 + ((41753583551 / 1000000000000)) ^ 2 * ((63256181479 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63256181479 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12806 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12806 : ℝ) * ((1 + 3 * ((2882469 / 125000000))) / (4 * (1 - (2882469 / 125000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (2882469 / 125000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12806 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (2882469 / 125000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12806 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12806 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12806

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12806
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((56581799 / 500000) : ℝ) ≤ √12806 ∧ √12806 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1449172 : ℝ) ≤ Jz 12806 ∧ 1000000 ≤ Jz 12806 := by
  have hr : ((56581799 / 500000) : ℝ) ≤ √12806 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12806 : ℝ) * √12806 ≤ (⌈(12806 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12806
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12806 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12806 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12806 : ℝ) = (⌈(12806 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1449172 : ℝ) ≤ Jz 12806 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12806 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12806) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12806 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12806 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12806 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12806 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12806 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12806 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12806) :
    (12806 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12806 * √(qB 12806))) ≤
      (269292093 / 500000000000) := by
  have hden : ((56581799 / 500000) : ℝ) * (63 / 100) ≤ √12806 * √(qB 12806) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12806 : ℝ) * √(qB 12806) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12806) :
    (12806 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12806 * √(qB 12806))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12806 : ℝ) * √(qB 12806) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12806 : ℝ) * (√12806 *
      (c1F (exp (1 / 2) / 12) (Jz 12806) * (186 / 10000) / Jz 12806)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12806)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12806 : ℝ) * (√12806 *
      (c1F (exp (1 / 2) / 12) (Jz 12806) * (186 / 10000) / Jz 12806)) =
      (12806 * (√12806 * c1F (exp (1 / 2) / 12) (Jz 12806)) * (186 / 10000)) /
        Jz 12806 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12806)]
  nlinarith

theorem row_energy_rule :
    (12806 : ℝ) * (12806 *
      (c2F (exp (1 / 2) / 12) (Jz 12806) * (186 / 10000) ^ 2 / Jz 12806)) ≤
      (880877399 / 250000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12806)]
  nlinarith

end BstLean.Part266.Row12806

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12806
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12806) (hc : A1 c ∈ BstLean.Part153.Eop 12806) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12806 : ℝ)) ≤ (12497071343 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12806 : ℝ) + 2 * √12806 ≤ (6516163599 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12806 : ℝ) ≤ (113163599 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12806)
    (hc : A1 c ∈ BstLean.Part153.Eop 12806) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12806 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12806 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12806))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12806) (K : Set (Ix 12806)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12806 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12806 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12806) (hw : WINDOW (paperDesignP 12806) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12806)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12806) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12806 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12806 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12806 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12806 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12806) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12806)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12806)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12806

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12806
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12806) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12806 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12806) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12806) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12806 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12806 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12806 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12806}
    (hw : WINDOW (paperDesignP 12806) c) (hc : c ∈ tableEvent) (K : Set (Ix 12806)) :
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

def proposedBaseEvent : Set (Ret 12806) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12806)) : Prop where
  charge : (retDist (paperCentres 12806)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12806)} (h : TablePayment H) :
    (retDist (paperCentres 12806)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12806)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12806

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12806
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12806) (i : Fin 4) (a : Ix 12806) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12806) (a : Ix 12806) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12806) : Prop where
  moment : ∀ i, MomentBound (muI 12806) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12806} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12806) 8 (actualFourError c i)
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

end BstLean.Part266.Row12806

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12806
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

structure LatitudeVarianceCertificate (c : Ret 12806) : Prop where
  location : LBound (muI 12806) 12
    (fun a => conditionalVariance (stdGauss (Fin (12806 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12806) 12
    (fun a => conditionalVariance (stdGauss (Fin (12806 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12806) (hw : WINDOW (paperDesignP 12806) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12806 4 (55 / 100) /
      (12806 : ℝ) / ((12806 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12806

/-! The dimension-12806 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12806
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12806) (wl ws : ℝ) : SplitData 12806 :=
  BstLean.Part162.dPaper (paperDesignP 12806) c wl ws
    (√(2 / (12806 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12806 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12806 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12806) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12806) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12806 : ℝ)) * eR c * 12806 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12806) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12806 - 1)))
    (rowSplit c wl ws).good a ∂muI 12806 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12806) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12806 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12806) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12806 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12806) c (rowSplit c wl ws),
    hellG2 12806 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12806 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12806} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12806} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12806 t c BstLean.Part266.agent12806.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12806} (R : RootSource t c) :
    |√(QStand (paperDesignP 12806) t c) - √(qTilde (paperDesignP 12806) t c)| ≤
      BstLean.Part266.agent12806.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12806

/-! Rational enclosures for the HQ fluctuation price at dimension 12807. -/
namespace BstLean.Part266.Row12807
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (820089537 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23057941 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12807 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12807 * A / 2 + D + L * √(A * D)) ≤ (230449529 / 50000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12807 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((820089537 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12807 L e4 d4 ≤ (41755412227 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12807 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((820089537 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12807 L e6 d6 ≤ (31629472129 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12807 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((820089537 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12807 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12807 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12807 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12807 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23057941 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((230449529 / 50000000000)) ^ 2 / 2 + ((230449529 / 50000000000)) * ((41755412227 / 1000000000000)) ^ 2 / 6 +
      ((41755412227 / 1000000000000)) ^ 4 / 24 + ((41755412227 / 1000000000000)) ^ 2 * ((31629472129 / 500000000000)) ^ 3 / 120 +
      2187 * ((31629472129 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12807 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12807 : ℝ) * ((1 + 3 * ((23057941 / 1000000000))) / (4 * (1 - (23057941 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23057941 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12807 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23057941 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12807 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12807 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12807

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12807
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((7073001 / 62500) : ℝ) ≤ √12807 ∧ √12807 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1449341 : ℝ) ≤ Jz 12807 ∧ 1000000 ≤ Jz 12807 := by
  have hr : ((7073001 / 62500) : ℝ) ≤ √12807 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12807 : ℝ) * √12807 ≤ (⌈(12807 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12807
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12807 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12807 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12807 : ℝ) = (⌈(12807 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1449341 : ℝ) ≤ Jz 12807 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12807 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12807) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12807 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12807 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12807 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12807 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12807 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12807 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12807) :
    (12807 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12807 * √(qB 12807))) ≤
      (16831413 / 31250000000) := by
  have hden : ((7073001 / 62500) : ℝ) * (63 / 100) ≤ √12807 * √(qB 12807) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12807 : ℝ) * √(qB 12807) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12807) :
    (12807 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12807 * √(qB 12807))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12807 : ℝ) * √(qB 12807) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12807 : ℝ) * (√12807 *
      (c1F (exp (1 / 2) / 12) (Jz 12807) * (186 / 10000) / Jz 12807)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12807)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12807 : ℝ) * (√12807 *
      (c1F (exp (1 / 2) / 12) (Jz 12807) * (186 / 10000) / Jz 12807)) =
      (12807 * (√12807 * c1F (exp (1 / 2) / 12) (Jz 12807)) * (186 / 10000)) /
        Jz 12807 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12807)]
  nlinarith

theorem row_energy_rule :
    (12807 : ℝ) * (12807 *
      (c2F (exp (1 / 2) / 12) (Jz 12807) * (186 / 10000) ^ 2 / Jz 12807)) ≤
      (1761824493 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12807)]
  nlinarith

end BstLean.Part266.Row12807

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12807
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12807) (hc : A1 c ∈ BstLean.Part153.Eop 12807) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12807 : ℝ)) ≤ (12496583433 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12807 : ℝ) + 2 * √12807 ≤ (6516668017 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12807 : ℝ) ≤ (113168017 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12807)
    (hc : A1 c ∈ BstLean.Part153.Eop 12807) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12807 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12807 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12807))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12807) (K : Set (Ix 12807)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12807 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12807 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12807) (hw : WINDOW (paperDesignP 12807) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12807)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12807) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12807 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12807 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12807 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12807 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12807) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12807)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12807)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12807

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12807
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12807) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12807 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12807) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12807) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12807 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12807 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12807 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12807}
    (hw : WINDOW (paperDesignP 12807) c) (hc : c ∈ tableEvent) (K : Set (Ix 12807)) :
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

def proposedBaseEvent : Set (Ret 12807) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12807)) : Prop where
  charge : (retDist (paperCentres 12807)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12807)} (h : TablePayment H) :
    (retDist (paperCentres 12807)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12807)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12807

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12807
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12807) (i : Fin 4) (a : Ix 12807) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12807) (a : Ix 12807) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12807) : Prop where
  moment : ∀ i, MomentBound (muI 12807) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12807} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12807) 8 (actualFourError c i)
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

end BstLean.Part266.Row12807

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12807
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

structure LatitudeVarianceCertificate (c : Ret 12807) : Prop where
  location : LBound (muI 12807) 12
    (fun a => conditionalVariance (stdGauss (Fin (12807 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12807) 12
    (fun a => conditionalVariance (stdGauss (Fin (12807 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12807) (hw : WINDOW (paperDesignP 12807) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12807 4 (55 / 100) /
      (12807 : ℝ) / ((12807 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12807

/-! The dimension-12807 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12807
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12807) (wl ws : ℝ) : SplitData 12807 :=
  BstLean.Part162.dPaper (paperDesignP 12807) c wl ws
    (√(2 / (12807 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12807 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12807 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12807) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12807) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12807 : ℝ)) * eR c * 12807 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12807) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12807 - 1)))
    (rowSplit c wl ws).good a ∂muI 12807 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12807) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12807 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12807) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12807 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12807) c (rowSplit c wl ws),
    hellG2 12807 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12807 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12807} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12807} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12807 t c BstLean.Part266.agent12807.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12807} (R : RootSource t c) :
    |√(QStand (paperDesignP 12807) t c) - √(qTilde (paperDesignP 12807) t c)| ≤
      BstLean.Part266.agent12807.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12807

/-! Rational enclosures for the HQ fluctuation price at dimension 12808. -/
namespace BstLean.Part266.Row12808
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (820057391 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23056127 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12808 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12808 * A / 2 + D + L * √(A * D)) ≤ (4609191917 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12808 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((820057391 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12808 L e4 d4 ≤ (41757240837 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12808 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((820057391 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12808 L e6 d6 ≤ (31630853467 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12808 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((820057391 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12808 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12808 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12808 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12808 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23056127 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4609191917 / 1000000000000)) ^ 2 / 2 + ((4609191917 / 1000000000000)) * ((41757240837 / 1000000000000)) ^ 2 / 6 +
      ((41757240837 / 1000000000000)) ^ 4 / 24 + ((41757240837 / 1000000000000)) ^ 2 * ((31630853467 / 500000000000)) ^ 3 / 120 +
      2187 * ((31630853467 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12808 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12808 : ℝ) * ((1 + 3 * ((23056127 / 1000000000))) / (4 * (1 - (23056127 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23056127 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12808 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23056127 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12808 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12808 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12808

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12808
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((56586217 / 500000) : ℝ) ≤ √12808 ∧ √12808 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1449511 : ℝ) ≤ Jz 12808 ∧ 1000000 ≤ Jz 12808 := by
  have hr : ((56586217 / 500000) : ℝ) ≤ √12808 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12808 : ℝ) * √12808 ≤ (⌈(12808 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12808
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12808 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12808 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12808 : ℝ) = (⌈(12808 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1449511 : ℝ) ≤ Jz 12808 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12808 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12808) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12808 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12808 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12808 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12808 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12808 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12808 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12808) :
    (12808 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12808 * √(qB 12808))) ≤
      (134656561 / 250000000000) := by
  have hden : ((56586217 / 500000) : ℝ) * (63 / 100) ≤ √12808 * √(qB 12808) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12808 : ℝ) * √(qB 12808) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12808) :
    (12808 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12808 * √(qB 12808))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12808 : ℝ) * √(qB 12808) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12808 : ℝ) * (√12808 *
      (c1F (exp (1 / 2) / 12) (Jz 12808) * (186 / 10000) / Jz 12808)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12808)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12808 : ℝ) * (√12808 *
      (c1F (exp (1 / 2) / 12) (Jz 12808) * (186 / 10000) / Jz 12808)) =
      (12808 * (√12808 * c1F (exp (1 / 2) / 12) (Jz 12808)) * (186 / 10000)) /
        Jz 12808 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12808)]
  nlinarith

theorem row_energy_rule :
    (12808 : ℝ) * (12808 *
      (c2F (exp (1 / 2) / 12) (Jz 12808) * (186 / 10000) ^ 2 / Jz 12808)) ≤
      (880946489 / 250000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12808)]
  nlinarith

end BstLean.Part266.Row12808

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12808
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12808) (hc : A1 c ∈ BstLean.Part153.Eop 12808) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12808 : ℝ)) ≤ (12496095581 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12808 : ℝ) + 2 * √12808 ≤ (1303434487 / 100000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12808 : ℝ) ≤ (22634487 / 200000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12808)
    (hc : A1 c ∈ BstLean.Part153.Eop 12808) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12808 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12808 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12808))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12808) (K : Set (Ix 12808)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12808 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12808 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12808) (hw : WINDOW (paperDesignP 12808) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12808)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12808) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12808 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12808 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12808 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12808 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12808) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12808)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12808)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12808

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12808
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12808) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12808 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12808) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12808) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12808 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12808 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12808 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12808}
    (hw : WINDOW (paperDesignP 12808) c) (hc : c ∈ tableEvent) (K : Set (Ix 12808)) :
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

def proposedBaseEvent : Set (Ret 12808) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12808)) : Prop where
  charge : (retDist (paperCentres 12808)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12808)} (h : TablePayment H) :
    (retDist (paperCentres 12808)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12808)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12808

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12808
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12808) (i : Fin 4) (a : Ix 12808) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12808) (a : Ix 12808) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12808) : Prop where
  moment : ∀ i, MomentBound (muI 12808) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12808} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12808) 8 (actualFourError c i)
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

end BstLean.Part266.Row12808

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12808
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

structure LatitudeVarianceCertificate (c : Ret 12808) : Prop where
  location : LBound (muI 12808) 12
    (fun a => conditionalVariance (stdGauss (Fin (12808 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12808) 12
    (fun a => conditionalVariance (stdGauss (Fin (12808 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12808) (hw : WINDOW (paperDesignP 12808) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12808 4 (55 / 100) /
      (12808 : ℝ) / ((12808 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12808

/-! The dimension-12808 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12808
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12808) (wl ws : ℝ) : SplitData 12808 :=
  BstLean.Part162.dPaper (paperDesignP 12808) c wl ws
    (√(2 / (12808 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12808 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12808 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12808) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12808) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12808 : ℝ)) * eR c * 12808 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12808) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12808 - 1)))
    (rowSplit c wl ws).good a ∂muI 12808 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12808) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12808 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12808) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12808 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12808) c (rowSplit c wl ws),
    hellG2 12808 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12808 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12808} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12808} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12808 t c BstLean.Part266.agent12808.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12808} (R : RootSource t c) :
    |√(QStand (paperDesignP 12808) t c) - √(qTilde (paperDesignP 12808) t c)| ≤
      BstLean.Part266.agent12808.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12808

/-! Rational enclosures for the HQ fluctuation price at dimension 12809. -/
namespace BstLean.Part266.Row12809
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1640050783 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23054317 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12809 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12809 * A / 2 + D + L * √(A * D)) ≤ (2304696631 / 500000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12809 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1640050783 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12809 L e4 d4 ≤ (41759069521 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12809 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1640050783 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12809 L e6 d6 ≤ (15816117431 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12809 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1640050783 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12809 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12809 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12809 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12809 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23054317 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((2304696631 / 500000000000)) ^ 2 / 2 + ((2304696631 / 500000000000)) * ((41759069521 / 1000000000000)) ^ 2 / 6 +
      ((41759069521 / 1000000000000)) ^ 4 / 24 + ((41759069521 / 1000000000000)) ^ 2 * ((15816117431 / 250000000000)) ^ 3 / 120 +
      2187 * ((15816117431 / 250000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12809 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12809 : ℝ) * ((1 + 3 * ((23054317 / 1000000000))) / (4 * (1 - (23054317 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23054317 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12809 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23054317 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12809 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12809 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12809

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12809
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((28294213 / 250000) : ℝ) ≤ √12809 ∧ √12809 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1449681 : ℝ) ≤ Jz 12809 ∧ 1000000 ≤ Jz 12809 := by
  have hr : ((28294213 / 250000) : ℝ) ≤ √12809 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12809 : ℝ) * √12809 ≤ (⌈(12809 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12809
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12809 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12809 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12809 : ℝ) = (⌈(12809 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1449681 : ℝ) ≤ Jz 12809 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12809 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12809) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12809 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12809 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12809 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12809 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12809 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12809 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12809) :
    (12809 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12809 * √(qB 12809))) ≤
      (53864727 / 100000000000) := by
  have hden : ((28294213 / 250000) : ℝ) * (63 / 100) ≤ √12809 * √(qB 12809) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12809 : ℝ) * √(qB 12809) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12809) :
    (12809 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12809 * √(qB 12809))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12809 : ℝ) * √(qB 12809) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12809 : ℝ) * (√12809 *
      (c1F (exp (1 / 2) / 12) (Jz 12809) * (186 / 10000) / Jz 12809)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12809)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12809 : ℝ) * (√12809 *
      (c1F (exp (1 / 2) / 12) (Jz 12809) * (186 / 10000) / Jz 12809)) =
      (12809 * (√12809 * c1F (exp (1 / 2) / 12) (Jz 12809)) * (186 / 10000)) /
        Jz 12809 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12809)]
  nlinarith

theorem row_energy_rule :
    (12809 : ℝ) * (12809 *
      (c2F (exp (1 / 2) / 12) (Jz 12809) * (186 / 10000) ^ 2 / Jz 12809)) ≤
      (440490367 / 125000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12809)]
  nlinarith

end BstLean.Part266.Row12809

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12809
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12809) (hc : A1 c ∈ BstLean.Part153.Eop 12809) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12809 : ℝ)) ≤ (2499121557 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12809 : ℝ) + 2 * √12809 ≤ (6517676853 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12809 : ℝ) ≤ (113176853 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12809)
    (hc : A1 c ∈ BstLean.Part153.Eop 12809) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12809 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12809 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12809))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12809) (K : Set (Ix 12809)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12809 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12809 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12809) (hw : WINDOW (paperDesignP 12809) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12809)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12809) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12809 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12809 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12809 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12809 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12809) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12809)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12809)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12809

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12809
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12809) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12809 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12809) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12809) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12809 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12809 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12809 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12809}
    (hw : WINDOW (paperDesignP 12809) c) (hc : c ∈ tableEvent) (K : Set (Ix 12809)) :
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

def proposedBaseEvent : Set (Ret 12809) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12809)) : Prop where
  charge : (retDist (paperCentres 12809)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12809)} (h : TablePayment H) :
    (retDist (paperCentres 12809)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12809)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12809

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12809
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12809) (i : Fin 4) (a : Ix 12809) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12809) (a : Ix 12809) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12809) : Prop where
  moment : ∀ i, MomentBound (muI 12809) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12809} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12809) 8 (actualFourError c i)
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

end BstLean.Part266.Row12809

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12809
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

structure LatitudeVarianceCertificate (c : Ret 12809) : Prop where
  location : LBound (muI 12809) 12
    (fun a => conditionalVariance (stdGauss (Fin (12809 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12809) 12
    (fun a => conditionalVariance (stdGauss (Fin (12809 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12809) (hw : WINDOW (paperDesignP 12809) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12809 4 (55 / 100) /
      (12809 : ℝ) / ((12809 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12809

/-! The dimension-12809 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12809
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12809) (wl ws : ℝ) : SplitData 12809 :=
  BstLean.Part162.dPaper (paperDesignP 12809) c wl ws
    (√(2 / (12809 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12809 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12809 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12809) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12809) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12809 : ℝ)) * eR c * 12809 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12809) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12809 - 1)))
    (rowSplit c wl ws).good a ∂muI 12809 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12809) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12809 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12809) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12809 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12809) c (rowSplit c wl ws),
    hellG2 12809 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12809 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12809} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12809} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12809 t c BstLean.Part266.agent12809.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12809} (R : RootSource t c) :
    |√(QStand (paperDesignP 12809) t c) - √(qTilde (paperDesignP 12809) t c)| ≤
      BstLean.Part266.agent12809.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12809

/-! Rational enclosures for the HQ fluctuation price at dimension 12810. -/
namespace BstLean.Part266.Row12810
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1639986521 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (2881563 / 125000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12810 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12810 * A / 2 + D + L * √(A * D)) ≤ (4609594599 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12810 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1639986521 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12810 L e4 d4 ≤ (41760898137 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12810 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1639986521 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12810 L e6 d6 ≤ (15816808103 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12810 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1639986521 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12810 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12810 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12810 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12810 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (2881563 / 125000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4609594599 / 1000000000000)) ^ 2 / 2 + ((4609594599 / 1000000000000)) * ((41760898137 / 1000000000000)) ^ 2 / 6 +
      ((41760898137 / 1000000000000)) ^ 4 / 24 + ((41760898137 / 1000000000000)) ^ 2 * ((15816808103 / 250000000000)) ^ 3 / 120 +
      2187 * ((15816808103 / 250000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12810 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12810 : ℝ) * ((1 + 3 * ((2881563 / 125000000))) / (4 * (1 - (2881563 / 125000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (2881563 / 125000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12810 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (2881563 / 125000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12810 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12810 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12810

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12810
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((11318127 / 100000) : ℝ) ≤ √12810 ∧ √12810 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1449851 : ℝ) ≤ Jz 12810 ∧ 1000000 ≤ Jz 12810 := by
  have hr : ((11318127 / 100000) : ℝ) ≤ √12810 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12810 : ℝ) * √12810 ≤ (⌈(12810 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12810
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12810 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12810 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12810 : ℝ) = (⌈(12810 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1449851 : ℝ) ≤ Jz 12810 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12810 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12810) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12810 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12810 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12810 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12810 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12810 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12810 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12810) :
    (12810 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12810 * √(qB 12810))) ≤
      (107733659 / 200000000000) := by
  have hden : ((11318127 / 100000) : ℝ) * (63 / 100) ≤ √12810 * √(qB 12810) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12810 : ℝ) * √(qB 12810) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12810) :
    (12810 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12810 * √(qB 12810))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12810 : ℝ) * √(qB 12810) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12810 : ℝ) * (√12810 *
      (c1F (exp (1 / 2) / 12) (Jz 12810) * (186 / 10000) / Jz 12810)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12810)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12810 : ℝ) * (√12810 *
      (c1F (exp (1 / 2) / 12) (Jz 12810) * (186 / 10000) / Jz 12810)) =
      (12810 * (√12810 * c1F (exp (1 / 2) / 12) (Jz 12810)) * (186 / 10000)) /
        Jz 12810 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12810)]
  nlinarith

theorem row_energy_rule :
    (12810 : ℝ) * (12810 *
      (c2F (exp (1 / 2) / 12) (Jz 12810) * (186 / 10000) ^ 2 / Jz 12810)) ≤
      (3524059927 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12810)]
  nlinarith

end BstLean.Part266.Row12810

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12810
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12810) (hc : A1 c ∈ BstLean.Part153.Eop 12810) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12810 : ℝ)) ≤ (12495120047 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12810 : ℝ) + 2 * √12810 ≤ (6518181271 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12810 : ℝ) ≤ (113181271 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12810)
    (hc : A1 c ∈ BstLean.Part153.Eop 12810) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12810 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12810 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12810))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12810) (K : Set (Ix 12810)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12810 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12810 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12810) (hw : WINDOW (paperDesignP 12810) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12810)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12810) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12810 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12810 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12810 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12810 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12810) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12810)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12810)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12810

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12810
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12810) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12810 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12810) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12810) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12810 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12810 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12810 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12810}
    (hw : WINDOW (paperDesignP 12810) c) (hc : c ∈ tableEvent) (K : Set (Ix 12810)) :
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

def proposedBaseEvent : Set (Ret 12810) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12810)) : Prop where
  charge : (retDist (paperCentres 12810)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12810)} (h : TablePayment H) :
    (retDist (paperCentres 12810)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12810)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12810

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12810
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12810) (i : Fin 4) (a : Ix 12810) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12810) (a : Ix 12810) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12810) : Prop where
  moment : ∀ i, MomentBound (muI 12810) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12810} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12810) 8 (actualFourError c i)
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

end BstLean.Part266.Row12810

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12810
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

structure LatitudeVarianceCertificate (c : Ret 12810) : Prop where
  location : LBound (muI 12810) 12
    (fun a => conditionalVariance (stdGauss (Fin (12810 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12810) 12
    (fun a => conditionalVariance (stdGauss (Fin (12810 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12810) (hw : WINDOW (paperDesignP 12810) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12810 4 (55 / 100) /
      (12810 : ℝ) / ((12810 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12810

/-! The dimension-12810 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12810
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12810) (wl ws : ℝ) : SplitData 12810 :=
  BstLean.Part162.dPaper (paperDesignP 12810) c wl ws
    (√(2 / (12810 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12810 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12810 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12810) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12810) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12810 : ℝ)) * eR c * 12810 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12810) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12810 - 1)))
    (rowSplit c wl ws).good a ∂muI 12810 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12810) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12810 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12810) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12810 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12810) c (rowSplit c wl ws),
    hellG2 12810 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12810 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12810} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12810} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12810 t c BstLean.Part266.agent12810.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12810} (R : RootSource t c) :
    |√(QStand (paperDesignP 12810) t c) - √(qTilde (paperDesignP 12810) t c)| ≤
      BstLean.Part266.agent12810.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12810

/-! Rational enclosures for the HQ fluctuation price at dimension 12811. -/
namespace BstLean.Part266.Row12811
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (819961137 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23050691 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12811 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12811 * A / 2 + D + L * √(A * D)) ≤ (4609795937 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12811 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((819961137 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12811 L e4 d4 ≤ (20881363379 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12811 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((819961137 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12811 L e6 d6 ≤ (31634997553 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12811 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((819961137 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12811 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12811 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12811 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12811 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23050691 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4609795937 / 1000000000000)) ^ 2 / 2 + ((4609795937 / 1000000000000)) * ((20881363379 / 500000000000)) ^ 2 / 6 +
      ((20881363379 / 500000000000)) ^ 4 / 24 + ((20881363379 / 500000000000)) ^ 2 * ((31634997553 / 500000000000)) ^ 3 / 120 +
      2187 * ((31634997553 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12811 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12811 : ℝ) * ((1 + 3 * ((23050691 / 1000000000))) / (4 * (1 - (23050691 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23050691 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12811 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23050691 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12811 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12811 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12811

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12811
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((14148211 / 125000) : ℝ) ≤ √12811 ∧ √12811 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1450020 : ℝ) ≤ Jz 12811 ∧ 1000000 ≤ Jz 12811 := by
  have hr : ((14148211 / 125000) : ℝ) ≤ √12811 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12811 : ℝ) * √12811 ≤ (⌈(12811 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12811
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12811 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12811 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12811 : ℝ) = (⌈(12811 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1450020 : ℝ) ≤ Jz 12811 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12811 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12811) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12811 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12811 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12811 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12811 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12811 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12811 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12811) :
    (12811 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12811 * √(qB 12811))) ≤
      (269344659 / 500000000000) := by
  have hden : ((14148211 / 125000) : ℝ) * (63 / 100) ≤ √12811 * √(qB 12811) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12811 : ℝ) * √(qB 12811) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12811) :
    (12811 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12811 * √(qB 12811))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12811 : ℝ) * √(qB 12811) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12811 : ℝ) * (√12811 *
      (c1F (exp (1 / 2) / 12) (Jz 12811) * (186 / 10000) / Jz 12811)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12811)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12811 : ℝ) * (√12811 *
      (c1F (exp (1 / 2) / 12) (Jz 12811) * (186 / 10000) / Jz 12811)) =
      (12811 * (√12811 * c1F (exp (1 / 2) / 12) (Jz 12811)) * (186 / 10000)) /
        Jz 12811 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12811)]
  nlinarith

theorem row_energy_rule :
    (12811 : ℝ) * (12811 *
      (c2F (exp (1 / 2) / 12) (Jz 12811) * (186 / 10000) ^ 2 / Jz 12811)) ≤
      (3524199359 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12811)]
  nlinarith

end BstLean.Part266.Row12811

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12811
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12811) (hc : A1 c ∈ BstLean.Part153.Eop 12811) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12811 : ℝ)) ≤ (6247316183 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12811 : ℝ) + 2 * √12811 ≤ (6518685689 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12811 : ℝ) ≤ (113185689 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12811)
    (hc : A1 c ∈ BstLean.Part153.Eop 12811) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12811 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12811 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12811))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12811) (K : Set (Ix 12811)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12811 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12811 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12811) (hw : WINDOW (paperDesignP 12811) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12811)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12811) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12811 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12811 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12811 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12811 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12811) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12811)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12811)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12811

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12811
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12811) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12811 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12811) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12811) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12811 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12811 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12811 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12811}
    (hw : WINDOW (paperDesignP 12811) c) (hc : c ∈ tableEvent) (K : Set (Ix 12811)) :
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

def proposedBaseEvent : Set (Ret 12811) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12811)) : Prop where
  charge : (retDist (paperCentres 12811)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12811)} (h : TablePayment H) :
    (retDist (paperCentres 12811)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12811)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12811

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12811
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12811) (i : Fin 4) (a : Ix 12811) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12811) (a : Ix 12811) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12811) : Prop where
  moment : ∀ i, MomentBound (muI 12811) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12811} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12811) 8 (actualFourError c i)
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

end BstLean.Part266.Row12811

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12811
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

structure LatitudeVarianceCertificate (c : Ret 12811) : Prop where
  location : LBound (muI 12811) 12
    (fun a => conditionalVariance (stdGauss (Fin (12811 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12811) 12
    (fun a => conditionalVariance (stdGauss (Fin (12811 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12811) (hw : WINDOW (paperDesignP 12811) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12811 4 (55 / 100) /
      (12811 : ℝ) / ((12811 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12811

/-! The dimension-12811 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12811
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12811) (wl ws : ℝ) : SplitData 12811 :=
  BstLean.Part162.dPaper (paperDesignP 12811) c wl ws
    (√(2 / (12811 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12811 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12811 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12811) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12811) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12811 : ℝ)) * eR c * 12811 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12811) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12811 - 1)))
    (rowSplit c wl ws).good a ∂muI 12811 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12811) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12811 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12811) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12811 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12811) c (rowSplit c wl ws),
    hellG2 12811 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12811 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12811} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12811} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12811 t c BstLean.Part266.agent12811.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12811} (R : RootSource t c) :
    |√(QStand (paperDesignP 12811) t c) - √(qTilde (paperDesignP 12811) t c)| ≤
      BstLean.Part266.agent12811.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12811

/-! Rational enclosures for the HQ fluctuation price at dimension 12812. -/
namespace BstLean.Part266.Row12812
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (819929161 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11524441 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12812 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12812 * A / 2 + D + L * √(A * D)) ≤ (1152499321 / 250000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12812 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((819929161 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12812 L e4 d4 ≤ (20882277727 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12812 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((819929161 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12812 L e6 d6 ≤ (31636378957 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12812 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((819929161 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12812 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12812 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12812 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12812 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11524441 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((1152499321 / 250000000000)) ^ 2 / 2 + ((1152499321 / 250000000000)) * ((20882277727 / 500000000000)) ^ 2 / 6 +
      ((20882277727 / 500000000000)) ^ 4 / 24 + ((20882277727 / 500000000000)) ^ 2 * ((31636378957 / 500000000000)) ^ 3 / 120 +
      2187 * ((31636378957 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12812 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12812 : ℝ) * ((1 + 3 * ((11524441 / 500000000))) / (4 * (1 - (11524441 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11524441 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12812 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11524441 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12812 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12812 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12812

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12812
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((22638021 / 200000) : ℝ) ≤ √12812 ∧ √12812 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1450190 : ℝ) ≤ Jz 12812 ∧ 1000000 ≤ Jz 12812 := by
  have hr : ((22638021 / 200000) : ℝ) ≤ √12812 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12812 : ℝ) * √12812 ≤ (⌈(12812 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12812
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12812 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12812 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12812 : ℝ) = (⌈(12812 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1450190 : ℝ) ≤ Jz 12812 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12812 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12812) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12812 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12812 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12812 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12812 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12812 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12812 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12812) :
    (12812 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12812 * √(qB 12812))) ≤
      (67338793 / 125000000000) := by
  have hden : ((22638021 / 200000) : ℝ) * (63 / 100) ≤ √12812 * √(qB 12812) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12812 : ℝ) * √(qB 12812) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12812) :
    (12812 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12812 * √(qB 12812))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12812 : ℝ) * √(qB 12812) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12812 : ℝ) * (√12812 *
      (c1F (exp (1 / 2) / 12) (Jz 12812) * (186 / 10000) / Jz 12812)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12812)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12812 : ℝ) * (√12812 *
      (c1F (exp (1 / 2) / 12) (Jz 12812) * (186 / 10000) / Jz 12812)) =
      (12812 * (√12812 * c1F (exp (1 / 2) / 12) (Jz 12812)) * (186 / 10000)) /
        Jz 12812 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12812)]
  nlinarith

theorem row_energy_rule :
    (12812 : ℝ) * (12812 *
      (c2F (exp (1 / 2) / 12) (Jz 12812) * (186 / 10000) ^ 2 / Jz 12812)) ≤
      (3524336371 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12812)]
  nlinarith

end BstLean.Part266.Row12812

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12812
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12812) (hc : A1 c ∈ BstLean.Part153.Eop 12812) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12812 : ℝ)) ≤ (6247072371 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12812 : ℝ) + 2 * √12812 ≤ (3259595053 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12812 : ℝ) ≤ (56595053 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12812)
    (hc : A1 c ∈ BstLean.Part153.Eop 12812) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12812 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12812 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12812))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12812) (K : Set (Ix 12812)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12812 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12812 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12812) (hw : WINDOW (paperDesignP 12812) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12812)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12812) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12812 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12812 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12812 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12812 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12812) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12812)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12812)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12812

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12812
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12812) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12812 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12812) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12812) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12812 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12812 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12812 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12812}
    (hw : WINDOW (paperDesignP 12812) c) (hc : c ∈ tableEvent) (K : Set (Ix 12812)) :
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

def proposedBaseEvent : Set (Ret 12812) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12812)) : Prop where
  charge : (retDist (paperCentres 12812)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12812)} (h : TablePayment H) :
    (retDist (paperCentres 12812)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12812)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12812

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12812
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12812) (i : Fin 4) (a : Ix 12812) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12812) (a : Ix 12812) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12812) : Prop where
  moment : ∀ i, MomentBound (muI 12812) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12812} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12812) 8 (actualFourError c i)
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

end BstLean.Part266.Row12812

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12812
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

structure LatitudeVarianceCertificate (c : Ret 12812) : Prop where
  location : LBound (muI 12812) 12
    (fun a => conditionalVariance (stdGauss (Fin (12812 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12812) 12
    (fun a => conditionalVariance (stdGauss (Fin (12812 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12812) (hw : WINDOW (paperDesignP 12812) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12812 4 (55 / 100) /
      (12812 : ℝ) / ((12812 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12812

/-! The dimension-12812 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12812
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12812) (wl ws : ℝ) : SplitData 12812 :=
  BstLean.Part162.dPaper (paperDesignP 12812) c wl ws
    (√(2 / (12812 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12812 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12812 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12812) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12812) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12812 : ℝ)) * eR c * 12812 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12812) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12812 - 1)))
    (rowSplit c wl ws).good a ∂muI 12812 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12812) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12812 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12812) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12812 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12812) c (rowSplit c wl ws),
    hellG2 12812 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12812 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12812} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12812} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12812 t c BstLean.Part266.agent12812.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12812} (R : RootSource t c) :
    |√(QStand (paperDesignP 12812) t c) - √(qTilde (paperDesignP 12812) t c)| ≤
      BstLean.Part266.agent12812.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12812

/-! Rational enclosures for the HQ fluctuation price at dimension 12813. -/
namespace BstLean.Part266.Row12813
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1639794103 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (2304707 / 100000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12813 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12813 * A / 2 + D + L * √(A * D)) ≤ (4610198623 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12813 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1639794103 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12813 L e4 d4 ≤ (20883192041 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12813 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1639794103 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12813 L e6 d6 ≤ (31637760309 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12813 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1639794103 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12813 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12813 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12813 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12813 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (2304707 / 100000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4610198623 / 1000000000000)) ^ 2 / 2 + ((4610198623 / 1000000000000)) * ((20883192041 / 500000000000)) ^ 2 / 6 +
      ((20883192041 / 500000000000)) ^ 4 / 24 + ((20883192041 / 500000000000)) ^ 2 * ((31637760309 / 500000000000)) ^ 3 / 120 +
      2187 * ((31637760309 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12813 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12813 : ℝ) * ((1 + 3 * ((2304707 / 100000000))) / (4 * (1 - (2304707 / 100000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (2304707 / 100000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12813 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (2304707 / 100000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12813 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12813 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12813

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12813
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((56597261 / 500000) : ℝ) ≤ √12813 ∧ √12813 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1450360 : ℝ) ≤ Jz 12813 ∧ 1000000 ≤ Jz 12813 := by
  have hr : ((56597261 / 500000) : ℝ) ≤ √12813 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12813 : ℝ) * √12813 ≤ (⌈(12813 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12813
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12813 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12813 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12813 : ℝ) = (⌈(12813 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1450360 : ℝ) ≤ Jz 12813 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12813 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12813) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12813 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12813 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12813 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12813 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12813 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12813 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12813) :
    (12813 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12813 * √(qB 12813))) ≤
      (538731369 / 1000000000000) := by
  have hden : ((56597261 / 500000) : ℝ) * (63 / 100) ≤ √12813 * √(qB 12813) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12813 : ℝ) * √(qB 12813) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12813) :
    (12813 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12813 * √(qB 12813))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12813 : ℝ) * √(qB 12813) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12813 : ℝ) * (√12813 *
      (c1F (exp (1 / 2) / 12) (Jz 12813) * (186 / 10000) / Jz 12813)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12813)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12813 : ℝ) * (√12813 *
      (c1F (exp (1 / 2) / 12) (Jz 12813) * (186 / 10000) / Jz 12813)) =
      (12813 * (√12813 * c1F (exp (1 / 2) / 12) (Jz 12813)) * (186 / 10000)) /
        Jz 12813 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12813)]
  nlinarith

theorem row_energy_rule :
    (12813 : ℝ) * (12813 *
      (c2F (exp (1 / 2) / 12) (Jz 12813) * (186 / 10000) ^ 2 / Jz 12813)) ≤
      (704894679 / 200000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12813)]
  nlinarith

end BstLean.Part266.Row12813

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12813
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12813) (hc : A1 c ∈ BstLean.Part153.Eop 12813) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12813 : ℝ)) ≤ (499746287 / 40000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12813 : ℝ) + 2 * √12813 ≤ (6519694523 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12813 : ℝ) ≤ (113194523 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12813)
    (hc : A1 c ∈ BstLean.Part153.Eop 12813) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12813 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12813 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12813))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12813) (K : Set (Ix 12813)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12813 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12813 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12813) (hw : WINDOW (paperDesignP 12813) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12813)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12813) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12813 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12813 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12813 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12813 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12813) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12813)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12813)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12813

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12813
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12813) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12813 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12813) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12813) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12813 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12813 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12813 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12813}
    (hw : WINDOW (paperDesignP 12813) c) (hc : c ∈ tableEvent) (K : Set (Ix 12813)) :
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

def proposedBaseEvent : Set (Ret 12813) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12813)) : Prop where
  charge : (retDist (paperCentres 12813)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12813)} (h : TablePayment H) :
    (retDist (paperCentres 12813)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12813)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12813

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12813
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12813) (i : Fin 4) (a : Ix 12813) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12813) (a : Ix 12813) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12813) : Prop where
  moment : ∀ i, MomentBound (muI 12813) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12813} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12813) 8 (actualFourError c i)
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

end BstLean.Part266.Row12813

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12813
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

structure LatitudeVarianceCertificate (c : Ret 12813) : Prop where
  location : LBound (muI 12813) 12
    (fun a => conditionalVariance (stdGauss (Fin (12813 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12813) 12
    (fun a => conditionalVariance (stdGauss (Fin (12813 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12813) (hw : WINDOW (paperDesignP 12813) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12813 4 (55 / 100) /
      (12813 : ℝ) / ((12813 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12813

/-! The dimension-12813 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12813
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12813) (wl ws : ℝ) : SplitData 12813 :=
  BstLean.Part162.dPaper (paperDesignP 12813) c wl ws
    (√(2 / (12813 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12813 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12813 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12813) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12813) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12813 : ℝ)) * eR c * 12813 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12813) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12813 - 1)))
    (rowSplit c wl ws).good a ∂muI 12813 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12813) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12813 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12813) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12813 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12813) c (rowSplit c wl ws),
    hellG2 12813 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12813 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12813} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12813} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12813 t c BstLean.Part266.agent12813.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12813} (R : RootSource t c) :
    |√(QStand (paperDesignP 12813) t c) - √(qTilde (paperDesignP 12813) t c)| ≤
      BstLean.Part266.agent12813.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12813

/-! Rational enclosures for the HQ fluctuation price at dimension 12814. -/
namespace BstLean.Part266.Row12814
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (819864951 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11522629 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12814 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12814 * A / 2 + D + L * √(A * D)) ≤ (2305199981 / 500000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12814 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((819864951 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12814 L e4 d4 ≤ (8353642543 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12814 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((819864951 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12814 L e6 d6 ≤ (6327828333 / 100000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12814 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((819864951 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12814 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12814 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12814 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12814 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11522629 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((2305199981 / 500000000000)) ^ 2 / 2 + ((2305199981 / 500000000000)) * ((8353642543 / 200000000000)) ^ 2 / 6 +
      ((8353642543 / 200000000000)) ^ 4 / 24 + ((8353642543 / 200000000000)) ^ 2 * ((6327828333 / 100000000000)) ^ 3 / 120 +
      2187 * ((6327828333 / 100000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12814 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12814 : ℝ) * ((1 + 3 * ((11522629 / 500000000))) / (4 * (1 - (11522629 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11522629 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12814 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11522629 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12814 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12814 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12814

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12814
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113198939 / 1000000) : ℝ) ≤ √12814 ∧ √12814 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1450530 : ℝ) ≤ Jz 12814 ∧ 1000000 ≤ Jz 12814 := by
  have hr : ((113198939 / 1000000) : ℝ) ≤ √12814 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12814 : ℝ) * √12814 ≤ (⌈(12814 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12814
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12814 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12814 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12814 : ℝ) = (⌈(12814 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1450530 : ℝ) ≤ Jz 12814 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12814 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12814) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12814 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12814 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12814 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12814 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12814 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12814 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12814) :
    (12814 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12814 * √(qB 12814))) ≤
      (538752391 / 1000000000000) := by
  have hden : ((113198939 / 1000000) : ℝ) * (63 / 100) ≤ √12814 * √(qB 12814) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12814 : ℝ) * √(qB 12814) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12814) :
    (12814 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12814 * √(qB 12814))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12814 : ℝ) * √(qB 12814) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12814 : ℝ) * (√12814 *
      (c1F (exp (1 / 2) / 12) (Jz 12814) * (186 / 10000) / Jz 12814)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12814)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12814 : ℝ) * (√12814 *
      (c1F (exp (1 / 2) / 12) (Jz 12814) * (186 / 10000) / Jz 12814)) =
      (12814 * (√12814 * c1F (exp (1 / 2) / 12) (Jz 12814)) * (186 / 10000)) /
        Jz 12814 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12814)]
  nlinarith

theorem row_energy_rule :
    (12814 : ℝ) * (12814 *
      (c2F (exp (1 / 2) / 12) (Jz 12814) * (186 / 10000) ^ 2 / Jz 12814)) ≤
      (3524610429 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12814)]
  nlinarith

end BstLean.Part266.Row12814

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12814
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12814) (hc : A1 c ∈ BstLean.Part153.Eop 12814) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12814 : ℝ)) ≤ (2498633933 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12814 : ℝ) + 2 * √12814 ≤ (326009947 / 25000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12814 : ℝ) ≤ (5659947 / 50000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12814)
    (hc : A1 c ∈ BstLean.Part153.Eop 12814) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12814 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12814 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12814))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12814) (K : Set (Ix 12814)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12814 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12814 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12814) (hw : WINDOW (paperDesignP 12814) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12814)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12814) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12814 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12814 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12814 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12814 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12814) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12814)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12814)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12814

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12814
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12814) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12814 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12814) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12814) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12814 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12814 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12814 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12814}
    (hw : WINDOW (paperDesignP 12814) c) (hc : c ∈ tableEvent) (K : Set (Ix 12814)) :
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

def proposedBaseEvent : Set (Ret 12814) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12814)) : Prop where
  charge : (retDist (paperCentres 12814)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12814)} (h : TablePayment H) :
    (retDist (paperCentres 12814)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12814)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12814

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12814
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12814) (i : Fin 4) (a : Ix 12814) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12814) (a : Ix 12814) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12814) : Prop where
  moment : ∀ i, MomentBound (muI 12814) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12814} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12814) 8 (actualFourError c i)
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

end BstLean.Part266.Row12814

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12814
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

structure LatitudeVarianceCertificate (c : Ret 12814) : Prop where
  location : LBound (muI 12814) 12
    (fun a => conditionalVariance (stdGauss (Fin (12814 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12814) 12
    (fun a => conditionalVariance (stdGauss (Fin (12814 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12814) (hw : WINDOW (paperDesignP 12814) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12814 4 (55 / 100) /
      (12814 : ℝ) / ((12814 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12814

/-! The dimension-12814 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12814
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12814) (wl ws : ℝ) : SplitData 12814 :=
  BstLean.Part162.dPaper (paperDesignP 12814) c wl ws
    (√(2 / (12814 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12814 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12814 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12814) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12814) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12814 : ℝ)) * eR c * 12814 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12814) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12814 - 1)))
    (rowSplit c wl ws).good a ∂muI 12814 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12814) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12814 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12814) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12814 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12814) c (rowSplit c wl ws),
    hellG2 12814 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12814 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12814} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12814} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12814 t c BstLean.Part266.agent12814.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12814} (R : RootSource t c) :
    |√(QStand (paperDesignP 12814) t c) - √(qTilde (paperDesignP 12814) t c)| ≤
      BstLean.Part266.agent12814.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12814

/-! Rational enclosures for the HQ fluctuation price at dimension 12815. -/
namespace BstLean.Part266.Row12815
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1639665993 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (460869 / 20000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12815 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12815 * A / 2 + D + L * √(A * D)) ≤ (461060131 / 100000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12815 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1639665993 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12815 L e4 d4 ≤ (20885020711 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12815 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1639665993 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12815 L e6 d6 ≤ (12656209231 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12815 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1639665993 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12815 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12815 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12815 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12815 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (460869 / 20000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((461060131 / 100000000000)) ^ 2 / 2 + ((461060131 / 100000000000)) * ((20885020711 / 500000000000)) ^ 2 / 6 +
      ((20885020711 / 500000000000)) ^ 4 / 24 + ((20885020711 / 500000000000)) ^ 2 * ((12656209231 / 200000000000)) ^ 3 / 120 +
      2187 * ((12656209231 / 200000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12815 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12815 : ℝ) * ((1 + 3 * ((460869 / 20000000))) / (4 * (1 - (460869 / 20000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (460869 / 20000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12815 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (460869 / 20000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12815 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12815 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12815

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12815
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((28300839 / 250000) : ℝ) ≤ √12815 ∧ √12815 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1450700 : ℝ) ≤ Jz 12815 ∧ 1000000 ≤ Jz 12815 := by
  have hr : ((28300839 / 250000) : ℝ) ≤ √12815 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12815 : ℝ) * √12815 ≤ (⌈(12815 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12815
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12815 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12815 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12815 : ℝ) = (⌈(12815 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1450700 : ℝ) ≤ Jz 12815 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12815 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12815) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12815 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12815 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12815 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12815 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12815 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12815 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12815) :
    (12815 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12815 * √(qB 12815))) ≤
      (538773413 / 1000000000000) := by
  have hden : ((28300839 / 250000) : ℝ) * (63 / 100) ≤ √12815 * √(qB 12815) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12815 : ℝ) * √(qB 12815) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12815) :
    (12815 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12815 * √(qB 12815))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12815 : ℝ) * √(qB 12815) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12815 : ℝ) * (√12815 *
      (c1F (exp (1 / 2) / 12) (Jz 12815) * (186 / 10000) / Jz 12815)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12815)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12815 : ℝ) * (√12815 *
      (c1F (exp (1 / 2) / 12) (Jz 12815) * (186 / 10000) / Jz 12815)) =
      (12815 * (√12815 * c1F (exp (1 / 2) / 12) (Jz 12815)) * (186 / 10000)) /
        Jz 12815 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12815)]
  nlinarith

theorem row_energy_rule :
    (12815 : ℝ) * (12815 *
      (c2F (exp (1 / 2) / 12) (Jz 12815) * (186 / 10000) ^ 2 / Jz 12815)) ≤
      (1762373737 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12815)]
  nlinarith

end BstLean.Part266.Row12815

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12815
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12815) (hc : A1 c ∈ BstLean.Part153.Eop 12815) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12815 : ℝ)) ≤ (12492682213 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12815 : ℝ) + 2 * √12815 ≤ (6520703357 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12815 : ℝ) ≤ (113203357 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12815)
    (hc : A1 c ∈ BstLean.Part153.Eop 12815) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12815 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12815 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12815))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12815) (K : Set (Ix 12815)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12815 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12815 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12815) (hw : WINDOW (paperDesignP 12815) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12815)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12815) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12815 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12815 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12815 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12815 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12815) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12815)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12815)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12815

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12815
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12815) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12815 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12815) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12815) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12815 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12815 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12815 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12815}
    (hw : WINDOW (paperDesignP 12815) c) (hc : c ∈ tableEvent) (K : Set (Ix 12815)) :
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

def proposedBaseEvent : Set (Ret 12815) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12815)) : Prop where
  charge : (retDist (paperCentres 12815)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12815)} (h : TablePayment H) :
    (retDist (paperCentres 12815)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12815)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12815

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12815
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12815) (i : Fin 4) (a : Ix 12815) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12815) (a : Ix 12815) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12815) : Prop where
  moment : ∀ i, MomentBound (muI 12815) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12815} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12815) 8 (actualFourError c i)
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

end BstLean.Part266.Row12815

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12815
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

structure LatitudeVarianceCertificate (c : Ret 12815) : Prop where
  location : LBound (muI 12815) 12
    (fun a => conditionalVariance (stdGauss (Fin (12815 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12815) 12
    (fun a => conditionalVariance (stdGauss (Fin (12815 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12815) (hw : WINDOW (paperDesignP 12815) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12815 4 (55 / 100) /
      (12815 : ℝ) / ((12815 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12815

/-! The dimension-12815 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12815
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12815) (wl ws : ℝ) : SplitData 12815 :=
  BstLean.Part162.dPaper (paperDesignP 12815) c wl ws
    (√(2 / (12815 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12815 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12815 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12815) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12815) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12815 : ℝ)) * eR c * 12815 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12815) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12815 - 1)))
    (rowSplit c wl ws).good a ∂muI 12815 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12815) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12815 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12815) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12815 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12815) c (rowSplit c wl ws),
    hellG2 12815 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12815 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12815} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12815} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12815 t c BstLean.Part266.agent12815.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12815} (R : RootSource t c) :
    |√(QStand (paperDesignP 12815) t c) - √(qTilde (paperDesignP 12815) t c)| ≤
      BstLean.Part266.agent12815.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12815

/-! Rational enclosures for the HQ fluctuation price at dimension 12816. -/
namespace BstLean.Part266.Row12816
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (819800911 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23041639 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12816 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12816 * A / 2 + D + L * √(A * D)) ≤ (92216053 / 20000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12816 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((819800911 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12816 L e4 d4 ≤ (20885935031 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12816 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((819800911 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12816 L e6 d6 ≤ (31641904439 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12816 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((819800911 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12816 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12816 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12816 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12816 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23041639 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((92216053 / 20000000000)) ^ 2 / 2 + ((92216053 / 20000000000)) * ((20885935031 / 500000000000)) ^ 2 / 6 +
      ((20885935031 / 500000000000)) ^ 4 / 24 + ((20885935031 / 500000000000)) ^ 2 * ((31641904439 / 500000000000)) ^ 3 / 120 +
      2187 * ((31641904439 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12816 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12816 : ℝ) * ((1 + 3 * ((23041639 / 1000000000))) / (4 * (1 - (23041639 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23041639 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12816 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23041639 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12816 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12816 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12816

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12816
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113207773 / 1000000) : ℝ) ≤ √12816 ∧ √12816 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1450869 : ℝ) ≤ Jz 12816 ∧ 1000000 ≤ Jz 12816 := by
  have hr : ((113207773 / 1000000) : ℝ) ≤ √12816 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12816 : ℝ) * √12816 ≤ (⌈(12816 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12816
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12816 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12816 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12816 : ℝ) = (⌈(12816 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1450869 : ℝ) ≤ Jz 12816 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12816 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12816) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12816 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12816 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12816 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12816 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12816 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12816 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12816) :
    (12816 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12816 * √(qB 12816))) ≤
      (8418663 / 15625000000) := by
  have hden : ((113207773 / 1000000) : ℝ) * (63 / 100) ≤ √12816 * √(qB 12816) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12816 : ℝ) * √(qB 12816) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12816) :
    (12816 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12816 * √(qB 12816))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12816 : ℝ) * √(qB 12816) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12816 : ℝ) * (√12816 *
      (c1F (exp (1 / 2) / 12) (Jz 12816) * (186 / 10000) / Jz 12816)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12816)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12816 : ℝ) * (√12816 *
      (c1F (exp (1 / 2) / 12) (Jz 12816) * (186 / 10000) / Jz 12816)) =
      (12816 * (√12816 * c1F (exp (1 / 2) / 12) (Jz 12816)) * (186 / 10000)) /
        Jz 12816 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12816)]
  nlinarith

theorem row_energy_rule :
    (12816 : ℝ) * (12816 *
      (c2F (exp (1 / 2) / 12) (Jz 12816) * (186 / 10000) ^ 2 / Jz 12816)) ≤
      (3524886959 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12816)]
  nlinarith

end BstLean.Part266.Row12816

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12816
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12816) (hc : A1 c ∈ BstLean.Part153.Eop 12816) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12816 : ℝ)) ≤ (12492194817 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12816 : ℝ) + 2 * √12816 ≤ (3260603887 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12816 : ℝ) ≤ (56603887 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12816)
    (hc : A1 c ∈ BstLean.Part153.Eop 12816) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12816 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12816 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12816))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12816) (K : Set (Ix 12816)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12816 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12816 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12816) (hw : WINDOW (paperDesignP 12816) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12816)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12816) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12816 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12816 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12816 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12816 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12816) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12816)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12816)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12816

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12816
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12816) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12816 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12816) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12816) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12816 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12816 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12816 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12816}
    (hw : WINDOW (paperDesignP 12816) c) (hc : c ∈ tableEvent) (K : Set (Ix 12816)) :
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

def proposedBaseEvent : Set (Ret 12816) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12816)) : Prop where
  charge : (retDist (paperCentres 12816)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12816)} (h : TablePayment H) :
    (retDist (paperCentres 12816)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12816)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12816

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12816
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12816) (i : Fin 4) (a : Ix 12816) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12816) (a : Ix 12816) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12816) : Prop where
  moment : ∀ i, MomentBound (muI 12816) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12816} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12816) 8 (actualFourError c i)
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

end BstLean.Part266.Row12816

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12816
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

structure LatitudeVarianceCertificate (c : Ret 12816) : Prop where
  location : LBound (muI 12816) 12
    (fun a => conditionalVariance (stdGauss (Fin (12816 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12816) 12
    (fun a => conditionalVariance (stdGauss (Fin (12816 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12816) (hw : WINDOW (paperDesignP 12816) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12816 4 (55 / 100) /
      (12816 : ℝ) / ((12816 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12816

/-! The dimension-12816 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12816
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12816) (wl ws : ℝ) : SplitData 12816 :=
  BstLean.Part162.dPaper (paperDesignP 12816) c wl ws
    (√(2 / (12816 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12816 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12816 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12816) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12816) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12816 : ℝ)) * eR c * 12816 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12816) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12816 - 1)))
    (rowSplit c wl ws).good a ∂muI 12816 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12816) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12816 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12816) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12816 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12816) c (rowSplit c wl ws),
    hellG2 12816 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12816 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12816} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12816} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12816 t c BstLean.Part266.agent12816.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12816} (R : RootSource t c) :
    |√(QStand (paperDesignP 12816) t c) - √(qTilde (paperDesignP 12816) t c)| ≤
      BstLean.Part266.agent12816.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12816

/-! Rational enclosures for the HQ fluctuation price at dimension 12817. -/
namespace BstLean.Part266.Row12817
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (3202222 / 1953125)
  epsilon : 0 ≤ ε ∧ ε ≤ (5759957 / 250000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12817 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12817 * A / 2 + D + L * √(A * D)) ≤ (461100399 / 100000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12817 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((3202222 / 1953125)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12817 L e4 d4 ≤ (8354739741 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12817 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((3202222 / 1953125)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12817 L e6 d6 ≤ (31643285803 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12817 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((3202222 / 1953125)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12817 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12817 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12817 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12817 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (5759957 / 250000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((461100399 / 100000000000)) ^ 2 / 2 + ((461100399 / 100000000000)) * ((8354739741 / 200000000000)) ^ 2 / 6 +
      ((8354739741 / 200000000000)) ^ 4 / 24 + ((8354739741 / 200000000000)) ^ 2 * ((31643285803 / 500000000000)) ^ 3 / 120 +
      2187 * ((31643285803 / 500000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12817 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12817 : ℝ) * ((1 + 3 * ((5759957 / 250000000))) / (4 * (1 - (5759957 / 250000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (5759957 / 250000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12817 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (5759957 / 250000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12817 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12817 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12817

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12817
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((11321219 / 100000) : ℝ) ≤ √12817 ∧ √12817 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1451039 : ℝ) ≤ Jz 12817 ∧ 1000000 ≤ Jz 12817 := by
  have hr : ((11321219 / 100000) : ℝ) ≤ √12817 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12817 : ℝ) * √12817 ≤ (⌈(12817 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12817
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12817 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12817 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12817 : ℝ) = (⌈(12817 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1451039 : ℝ) ≤ Jz 12817 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12817 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12817) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12817 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12817 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12817 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12817 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12817 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12817 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12817) :
    (12817 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12817 * √(qB 12817))) ≤
      (10776309 / 20000000000) := by
  have hden : ((11321219 / 100000) : ℝ) * (63 / 100) ≤ √12817 * √(qB 12817) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12817 : ℝ) * √(qB 12817) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12817) :
    (12817 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12817 * √(qB 12817))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12817 : ℝ) * √(qB 12817) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12817 : ℝ) * (√12817 *
      (c1F (exp (1 / 2) / 12) (Jz 12817) * (186 / 10000) / Jz 12817)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12817)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12817 : ℝ) * (√12817 *
      (c1F (exp (1 / 2) / 12) (Jz 12817) * (186 / 10000) / Jz 12817)) =
      (12817 * (√12817 * c1F (exp (1 / 2) / 12) (Jz 12817)) * (186 / 10000)) /
        Jz 12817 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12817)]
  nlinarith

theorem row_energy_rule :
    (12817 : ℝ) * (12817 *
      (c2F (exp (1 / 2) / 12) (Jz 12817) * (186 / 10000) ^ 2 / Jz 12817)) ≤
      (141000961 / 40000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12817)]
  nlinarith

end BstLean.Part266.Row12817

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12817
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12817) (hc : A1 c ∈ BstLean.Part153.Eop 12817) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12817 : ℝ)) ≤ (6245853739 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12817 : ℝ) + 2 * √12817 ≤ (6521712191 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12817 : ℝ) ≤ (113212191 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12817)
    (hc : A1 c ∈ BstLean.Part153.Eop 12817) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12817 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12817 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12817))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12817) (K : Set (Ix 12817)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12817 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12817 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12817) (hw : WINDOW (paperDesignP 12817) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12817)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12817) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12817 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12817 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12817 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12817 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12817) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12817)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12817)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12817

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12817
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12817) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12817 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12817) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12817) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12817 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12817 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12817 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12817}
    (hw : WINDOW (paperDesignP 12817) c) (hc : c ∈ tableEvent) (K : Set (Ix 12817)) :
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

def proposedBaseEvent : Set (Ret 12817) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12817)) : Prop where
  charge : (retDist (paperCentres 12817)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12817)} (h : TablePayment H) :
    (retDist (paperCentres 12817)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12817)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12817

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12817
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12817) (i : Fin 4) (a : Ix 12817) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12817) (a : Ix 12817) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12817) : Prop where
  moment : ∀ i, MomentBound (muI 12817) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12817} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12817) 8 (actualFourError c i)
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

end BstLean.Part266.Row12817

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12817
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

structure LatitudeVarianceCertificate (c : Ret 12817) : Prop where
  location : LBound (muI 12817) 12
    (fun a => conditionalVariance (stdGauss (Fin (12817 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12817) 12
    (fun a => conditionalVariance (stdGauss (Fin (12817 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12817) (hw : WINDOW (paperDesignP 12817) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12817 4 (55 / 100) /
      (12817 : ℝ) / ((12817 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12817

/-! The dimension-12817 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12817
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12817) (wl ws : ℝ) : SplitData 12817 :=
  BstLean.Part162.dPaper (paperDesignP 12817) c wl ws
    (√(2 / (12817 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12817 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12817 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12817) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12817) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12817 : ℝ)) * eR c * 12817 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12817) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12817 - 1)))
    (rowSplit c wl ws).good a ∂muI 12817 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12817) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12817 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12817) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12817 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12817) c (rowSplit c wl ws),
    hellG2 12817 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12817 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12817} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12817} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12817 t c BstLean.Part266.agent12817.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12817} (R : RootSource t c) :
    |√(QStand (paperDesignP 12817) t c) - √(qTilde (paperDesignP 12817) t c)| ≤
      BstLean.Part266.agent12817.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12817

/-! Rational enclosures for the HQ fluctuation price at dimension 12818. -/
namespace BstLean.Part266.Row12818
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1639473521 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11519009 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12818 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12818 * A / 2 + D + L * √(A * D)) ≤ (4611205331 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12818 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1639473521 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12818 L e4 d4 ≤ (5221940919 / 125000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12818 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1639473521 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12818 L e6 d6 ≤ (3164466717 / 50000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12818 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1639473521 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12818 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12818 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12818 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12818 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11519009 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4611205331 / 1000000000000)) ^ 2 / 2 + ((4611205331 / 1000000000000)) * ((5221940919 / 125000000000)) ^ 2 / 6 +
      ((5221940919 / 125000000000)) ^ 4 / 24 + ((5221940919 / 125000000000)) ^ 2 * ((3164466717 / 50000000000)) ^ 3 / 120 +
      2187 * ((3164466717 / 50000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12818 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12818 : ℝ) * ((1 + 3 * ((11519009 / 500000000))) / (4 * (1 - (11519009 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11519009 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12818 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11519009 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12818 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12818 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12818

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12818
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((56608303 / 500000) : ℝ) ≤ √12818 ∧ √12818 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1451209 : ℝ) ≤ Jz 12818 ∧ 1000000 ≤ Jz 12818 := by
  have hr : ((56608303 / 500000) : ℝ) ≤ √12818 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12818 : ℝ) * √12818 ≤ (⌈(12818 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12818
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12818 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12818 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12818 : ℝ) = (⌈(12818 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1451209 : ℝ) ≤ Jz 12818 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12818 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12818) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12818 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12818 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12818 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12818 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12818 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12818 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12818) :
    (12818 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12818 * √(qB 12818))) ≤
      (538836471 / 1000000000000) := by
  have hden : ((56608303 / 500000) : ℝ) * (63 / 100) ≤ √12818 * √(qB 12818) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12818 : ℝ) * √(qB 12818) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12818) :
    (12818 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12818 * √(qB 12818))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12818 : ℝ) * √(qB 12818) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12818 : ℝ) * (√12818 *
      (c1F (exp (1 / 2) / 12) (Jz 12818) * (186 / 10000) / Jz 12818)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12818)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12818 : ℝ) * (√12818 *
      (c1F (exp (1 / 2) / 12) (Jz 12818) * (186 / 10000) / Jz 12818)) =
      (12818 * (√12818 * c1F (exp (1 / 2) / 12) (Jz 12818)) * (186 / 10000)) /
        Jz 12818 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12818)]
  nlinarith

theorem row_energy_rule :
    (12818 : ℝ) * (12818 *
      (c2F (exp (1 / 2) / 12) (Jz 12818) * (186 / 10000) ^ 2 / Jz 12818)) ≤
      (1762580551 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12818)]
  nlinarith

end BstLean.Part266.Row12818

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12818
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12818) (hc : A1 c ∈ BstLean.Part153.Eop 12818) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12818 : ℝ)) ≤ (12491220197 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12818 : ℝ) + 2 * √12818 ≤ (6522216607 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12818 : ℝ) ≤ (113216607 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12818)
    (hc : A1 c ∈ BstLean.Part153.Eop 12818) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12818 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12818 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12818))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12818) (K : Set (Ix 12818)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12818 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12818 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12818) (hw : WINDOW (paperDesignP 12818) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12818)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12818) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12818 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12818 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12818 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12818 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12818) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12818)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12818)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12818

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12818
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12818) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12818 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12818) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12818) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12818 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12818 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12818 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12818}
    (hw : WINDOW (paperDesignP 12818) c) (hc : c ∈ tableEvent) (K : Set (Ix 12818)) :
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

def proposedBaseEvent : Set (Ret 12818) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12818)) : Prop where
  charge : (retDist (paperCentres 12818)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12818)} (h : TablePayment H) :
    (retDist (paperCentres 12818)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12818)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12818

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12818
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12818) (i : Fin 4) (a : Ix 12818) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12818) (a : Ix 12818) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12818) : Prop where
  moment : ∀ i, MomentBound (muI 12818) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12818} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12818) 8 (actualFourError c i)
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

end BstLean.Part266.Row12818

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12818
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

structure LatitudeVarianceCertificate (c : Ret 12818) : Prop where
  location : LBound (muI 12818) 12
    (fun a => conditionalVariance (stdGauss (Fin (12818 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12818) 12
    (fun a => conditionalVariance (stdGauss (Fin (12818 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12818) (hw : WINDOW (paperDesignP 12818) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12818 4 (55 / 100) /
      (12818 : ℝ) / ((12818 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12818

/-! The dimension-12818 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12818
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12818) (wl ws : ℝ) : SplitData 12818 :=
  BstLean.Part162.dPaper (paperDesignP 12818) c wl ws
    (√(2 / (12818 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12818 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12818 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12818) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12818) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12818 : ℝ)) * eR c * 12818 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12818) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12818 - 1)))
    (rowSplit c wl ws).good a ∂muI 12818 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12818) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12818 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12818) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12818 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12818) c (rowSplit c wl ws),
    hellG2 12818 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12818 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12818} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12818} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12818 t c BstLean.Part266.agent12818.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12818} (R : RootSource t c) :
    |√(QStand (paperDesignP 12818) t c) - √(qTilde (paperDesignP 12818) t c)| ≤
      BstLean.Part266.agent12818.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12818

/-! Rational enclosures for the HQ fluctuation price at dimension 12819. -/
namespace BstLean.Part266.Row12819
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1639409673 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (5759053 / 250000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12819 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12819 * A / 2 + D + L * √(A * D)) ≤ (4611406681 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12819 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1639409673 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12819 L e4 d4 ≤ (1671094243 / 40000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12819 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1639409673 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12819 L e6 d6 ≤ (63292097189 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12819 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1639409673 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12819 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12819 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12819 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12819 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (5759053 / 250000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4611406681 / 1000000000000)) ^ 2 / 2 + ((4611406681 / 1000000000000)) * ((1671094243 / 40000000000)) ^ 2 / 6 +
      ((1671094243 / 40000000000)) ^ 4 / 24 + ((1671094243 / 40000000000)) ^ 2 * ((63292097189 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63292097189 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12819 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12819 : ℝ) * ((1 + 3 * ((5759053 / 250000000))) / (4 * (1 - (5759053 / 250000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (5759053 / 250000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12819 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (5759053 / 250000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12819 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12819 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12819

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12819
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((56610511 / 500000) : ℝ) ≤ √12819 ∧ √12819 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1451379 : ℝ) ≤ Jz 12819 ∧ 1000000 ≤ Jz 12819 := by
  have hr : ((56610511 / 500000) : ℝ) ≤ √12819 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12819 : ℝ) * √12819 ≤ (⌈(12819 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12819
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12819 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12819 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12819 : ℝ) = (⌈(12819 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1451379 : ℝ) ≤ Jz 12819 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12819 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12819) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12819 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12819 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12819 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12819 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12819 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12819 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12819) :
    (12819 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12819 * √(qB 12819))) ≤
      (538857491 / 1000000000000) := by
  have hden : ((56610511 / 500000) : ℝ) * (63 / 100) ≤ √12819 * √(qB 12819) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12819 : ℝ) * √(qB 12819) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12819) :
    (12819 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12819 * √(qB 12819))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12819 : ℝ) * √(qB 12819) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12819 : ℝ) * (√12819 *
      (c1F (exp (1 / 2) / 12) (Jz 12819) * (186 / 10000) / Jz 12819)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12819)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12819 : ℝ) * (√12819 *
      (c1F (exp (1 / 2) / 12) (Jz 12819) * (186 / 10000) / Jz 12819)) =
      (12819 * (√12819 * c1F (exp (1 / 2) / 12) (Jz 12819)) * (186 / 10000)) /
        Jz 12819 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12819)]
  nlinarith

theorem row_energy_rule :
    (12819 : ℝ) * (12819 *
      (c2F (exp (1 / 2) / 12) (Jz 12819) * (186 / 10000) ^ 2 / Jz 12819)) ≤
      (352529819 / 100000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12819)]
  nlinarith

end BstLean.Part266.Row12819

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12819
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12819) (hc : A1 c ∈ BstLean.Part153.Eop 12819) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12819 : ℝ)) ≤ (3122683243 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12819 : ℝ) + 2 * √12819 ≤ (6522721023 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12819 : ℝ) ≤ (113221023 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12819)
    (hc : A1 c ∈ BstLean.Part153.Eop 12819) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12819 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12819 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12819))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12819) (K : Set (Ix 12819)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12819 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12819 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12819) (hw : WINDOW (paperDesignP 12819) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12819)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12819) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12819 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12819 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12819 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12819 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12819) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12819)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12819)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12819

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12819
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12819) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12819 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12819) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12819) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12819 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12819 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12819 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12819}
    (hw : WINDOW (paperDesignP 12819) c) (hc : c ∈ tableEvent) (K : Set (Ix 12819)) :
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

def proposedBaseEvent : Set (Ret 12819) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12819)) : Prop where
  charge : (retDist (paperCentres 12819)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12819)} (h : TablePayment H) :
    (retDist (paperCentres 12819)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12819)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12819

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12819
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12819) (i : Fin 4) (a : Ix 12819) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12819) (a : Ix 12819) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12819) : Prop where
  moment : ∀ i, MomentBound (muI 12819) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12819} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12819) 8 (actualFourError c i)
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

end BstLean.Part266.Row12819

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12819
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

structure LatitudeVarianceCertificate (c : Ret 12819) : Prop where
  location : LBound (muI 12819) 12
    (fun a => conditionalVariance (stdGauss (Fin (12819 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12819) 12
    (fun a => conditionalVariance (stdGauss (Fin (12819 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12819) (hw : WINDOW (paperDesignP 12819) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12819 4 (55 / 100) /
      (12819 : ℝ) / ((12819 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12819

/-! The dimension-12819 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12819
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12819) (wl ws : ℝ) : SplitData 12819 :=
  BstLean.Part162.dPaper (paperDesignP 12819) c wl ws
    (√(2 / (12819 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12819 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12819 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12819) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12819) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12819 : ℝ)) * eR c * 12819 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12819) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12819 - 1)))
    (rowSplit c wl ws).good a ∂muI 12819 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12819) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12819 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12819) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12819 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12819) c (rowSplit c wl ws),
    hellG2 12819 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12819 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12819} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12819} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12819 t c BstLean.Part266.agent12819.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12819} (R : RootSource t c) :
    |√(QStand (paperDesignP 12819) t c) - √(qTilde (paperDesignP 12819) t c)| ≤
      BstLean.Part266.agent12819.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12819

/-! Rational enclosures for the HQ fluctuation price at dimension 12820. -/
namespace BstLean.Part266.Row12820
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1639345561 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (11517201 / 500000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12820 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12820 * A / 2 + D + L * √(A * D)) ≤ (4611608023 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12820 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1639345561 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12820 L e4 d4 ≤ (4177918473 / 100000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12820 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1639345561 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12820 L e6 d6 ≤ (12658971987 / 200000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12820 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1639345561 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12820 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12820 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12820 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12820 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (11517201 / 500000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4611608023 / 1000000000000)) ^ 2 / 2 + ((4611608023 / 1000000000000)) * ((4177918473 / 100000000000)) ^ 2 / 6 +
      ((4177918473 / 100000000000)) ^ 4 / 24 + ((4177918473 / 100000000000)) ^ 2 * ((12658971987 / 200000000000)) ^ 3 / 120 +
      2187 * ((12658971987 / 200000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12820 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12820 : ℝ) * ((1 + 3 * ((11517201 / 500000000))) / (4 * (1 - (11517201 / 500000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (11517201 / 500000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12820 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (11517201 / 500000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12820 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12820 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12820

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12820
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((56612719 / 500000) : ℝ) ≤ √12820 ∧ √12820 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1451549 : ℝ) ≤ Jz 12820 ∧ 1000000 ≤ Jz 12820 := by
  have hr : ((56612719 / 500000) : ℝ) ≤ √12820 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12820 : ℝ) * √12820 ≤ (⌈(12820 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12820
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12820 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12820 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12820 : ℝ) = (⌈(12820 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1451549 : ℝ) ≤ Jz 12820 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12820 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12820) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12820 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12820 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12820 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12820 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12820 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12820 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12820) :
    (12820 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12820 * √(qB 12820))) ≤
      (134719627 / 250000000000) := by
  have hden : ((56612719 / 500000) : ℝ) * (63 / 100) ≤ √12820 * √(qB 12820) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12820 : ℝ) * √(qB 12820) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12820) :
    (12820 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12820 * √(qB 12820))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12820 : ℝ) * √(qB 12820) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12820 : ℝ) * (√12820 *
      (c1F (exp (1 / 2) / 12) (Jz 12820) * (186 / 10000) / Jz 12820)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12820)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12820 : ℝ) * (√12820 *
      (c1F (exp (1 / 2) / 12) (Jz 12820) * (186 / 10000) / Jz 12820)) =
      (12820 * (√12820 * c1F (exp (1 / 2) / 12) (Jz 12820)) * (186 / 10000)) /
        Jz 12820 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12820)]
  nlinarith

theorem row_energy_rule :
    (12820 : ℝ) * (12820 *
      (c2F (exp (1 / 2) / 12) (Jz 12820) * (186 / 10000) ^ 2 / Jz 12820)) ≤
      (3525435289 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12820)]
  nlinarith

end BstLean.Part266.Row12820

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12820
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12820) (hc : A1 c ∈ BstLean.Part153.Eop 12820) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12820 : ℝ)) ≤ (2498049161 / 200000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12820 : ℝ) + 2 * √12820 ≤ (6523225439 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12820 : ℝ) ≤ (113225439 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12820)
    (hc : A1 c ∈ BstLean.Part153.Eop 12820) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12820 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12820 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12820))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12820) (K : Set (Ix 12820)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12820 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12820 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12820) (hw : WINDOW (paperDesignP 12820) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12820)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12820) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12820 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12820 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12820 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12820 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12820) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12820)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12820)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12820

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12820
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12820) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12820 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12820) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12820) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12820 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12820 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12820 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12820}
    (hw : WINDOW (paperDesignP 12820) c) (hc : c ∈ tableEvent) (K : Set (Ix 12820)) :
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

def proposedBaseEvent : Set (Ret 12820) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12820)) : Prop where
  charge : (retDist (paperCentres 12820)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12820)} (h : TablePayment H) :
    (retDist (paperCentres 12820)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12820)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12820

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12820
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12820) (i : Fin 4) (a : Ix 12820) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12820) (a : Ix 12820) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12820) : Prop where
  moment : ∀ i, MomentBound (muI 12820) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12820} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12820) 8 (actualFourError c i)
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

end BstLean.Part266.Row12820

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12820
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

structure LatitudeVarianceCertificate (c : Ret 12820) : Prop where
  location : LBound (muI 12820) 12
    (fun a => conditionalVariance (stdGauss (Fin (12820 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12820) 12
    (fun a => conditionalVariance (stdGauss (Fin (12820 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12820) (hw : WINDOW (paperDesignP 12820) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12820 4 (55 / 100) /
      (12820 : ℝ) / ((12820 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12820

/-! The dimension-12820 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12820
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12820) (wl ws : ℝ) : SplitData 12820 :=
  BstLean.Part162.dPaper (paperDesignP 12820) c wl ws
    (√(2 / (12820 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12820 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12820 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12820) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12820) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12820 : ℝ)) * eR c * 12820 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12820) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12820 - 1)))
    (rowSplit c wl ws).good a ∂muI 12820 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12820) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12820 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12820) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12820 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12820) c (rowSplit c wl ws),
    hellG2 12820 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12820 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12820} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12820} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12820 t c BstLean.Part266.agent12820.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12820} (R : RootSource t c) :
    |√(QStand (paperDesignP 12820) t c) - √(qTilde (paperDesignP 12820) t c)| ≤
      BstLean.Part266.agent12820.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12820

/-! Rational enclosures for the HQ fluctuation price at dimension 12821. -/
namespace BstLean.Part266.Row12821
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (204910183 / 125000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (23032593 / 1000000000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12821 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12821 * A / 2 + D + L * √(A * D)) ≤ (922361873 / 200000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12821 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((204910183 / 125000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12821 L e4 d4 ≤ (41781013389 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12821 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((204910183 / 125000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12821 L e6 d6 ≤ (63297622687 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12821 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((204910183 / 125000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12821 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12821 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12821 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12821 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (23032593 / 1000000000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((922361873 / 200000000000)) ^ 2 / 2 + ((922361873 / 200000000000)) * ((41781013389 / 1000000000000)) ^ 2 / 6 +
      ((41781013389 / 1000000000000)) ^ 4 / 24 + ((41781013389 / 1000000000000)) ^ 2 * ((63297622687 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63297622687 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12821 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12821 : ℝ) * ((1 + 3 * ((23032593 / 1000000000))) / (4 * (1 - (23032593 / 1000000000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (23032593 / 1000000000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12821 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (23032593 / 1000000000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12821 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12821 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12821

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12821
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((56614927 / 500000) : ℝ) ≤ √12821 ∧ √12821 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1451718 : ℝ) ≤ Jz 12821 ∧ 1000000 ≤ Jz 12821 := by
  have hr : ((56614927 / 500000) : ℝ) ≤ √12821 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12821 : ℝ) * √12821 ≤ (⌈(12821 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12821
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12821 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12821 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12821 : ℝ) = (⌈(12821 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1451718 : ℝ) ≤ Jz 12821 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12821 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12821) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12821 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12821 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12821 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12821 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12821 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12821 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12821) :
    (12821 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12821 * √(qB 12821))) ≤
      (134724881 / 250000000000) := by
  have hden : ((56614927 / 500000) : ℝ) * (63 / 100) ≤ √12821 * √(qB 12821) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12821 : ℝ) * √(qB 12821) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12821) :
    (12821 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12821 * √(qB 12821))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12821 : ℝ) * √(qB 12821) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12821 : ℝ) * (√12821 *
      (c1F (exp (1 / 2) / 12) (Jz 12821) * (186 / 10000) / Jz 12821)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12821)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12821 : ℝ) * (√12821 *
      (c1F (exp (1 / 2) / 12) (Jz 12821) * (186 / 10000) / Jz 12821)) =
      (12821 * (√12821 * c1F (exp (1 / 2) / 12) (Jz 12821)) * (186 / 10000)) /
        Jz 12821 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12821)]
  nlinarith

theorem row_energy_rule :
    (12821 : ℝ) * (12821 *
      (c2F (exp (1 / 2) / 12) (Jz 12821) * (186 / 10000) ^ 2 / Jz 12821)) ≤
      (3525574827 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12821)]
  nlinarith

end BstLean.Part266.Row12821

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12821
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12821) (hc : A1 c ∈ BstLean.Part153.Eop 12821) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12821 : ℝ)) ≤ (6244879347 / 500000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12821 : ℝ) + 2 * √12821 ≤ (1304745971 / 100000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12821 : ℝ) ≤ (22645971 / 200000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12821)
    (hc : A1 c ∈ BstLean.Part153.Eop 12821) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12821 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12821 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12821))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12821) (K : Set (Ix 12821)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12821 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12821 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12821) (hw : WINDOW (paperDesignP 12821) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12821)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12821) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12821 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12821 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12821 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12821 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12821) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12821)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12821)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12821

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12821
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12821) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12821 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12821) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12821) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12821 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12821 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12821 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12821}
    (hw : WINDOW (paperDesignP 12821) c) (hc : c ∈ tableEvent) (K : Set (Ix 12821)) :
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

def proposedBaseEvent : Set (Ret 12821) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12821)) : Prop where
  charge : (retDist (paperCentres 12821)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12821)} (h : TablePayment H) :
    (retDist (paperCentres 12821)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12821)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12821

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12821
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12821) (i : Fin 4) (a : Ix 12821) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12821) (a : Ix 12821) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12821) : Prop where
  moment : ∀ i, MomentBound (muI 12821) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12821} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12821) 8 (actualFourError c i)
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

end BstLean.Part266.Row12821

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12821
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

structure LatitudeVarianceCertificate (c : Ret 12821) : Prop where
  location : LBound (muI 12821) 12
    (fun a => conditionalVariance (stdGauss (Fin (12821 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12821) 12
    (fun a => conditionalVariance (stdGauss (Fin (12821 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12821) (hw : WINDOW (paperDesignP 12821) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12821 4 (55 / 100) /
      (12821 : ℝ) / ((12821 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12821

/-! The dimension-12821 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12821
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12821) (wl ws : ℝ) : SplitData 12821 :=
  BstLean.Part162.dPaper (paperDesignP 12821) c wl ws
    (√(2 / (12821 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12821 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12821 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12821) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12821) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12821 : ℝ)) * eR c * 12821 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12821) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12821 - 1)))
    (rowSplit c wl ws).good a ∂muI 12821 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12821) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12821 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12821) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12821 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12821) c (rowSplit c wl ws),
    hellG2 12821 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12821 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12821} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12821} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12821 t c BstLean.Part266.agent12821.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12821} (R : RootSource t c) :
    |√(QStand (paperDesignP 12821) t c) - √(qTilde (paperDesignP 12821) t c)| ≤
      BstLean.Part266.agent12821.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12821

/-! Rational enclosures for the HQ fluctuation price at dimension 12822. -/
namespace BstLean.Part266.Row12822
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (819608691 / 500000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (44982 / 1953125)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12822 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12822 * A / 2 + D + L * √(A * D)) ≤ (1153002677 / 250000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12822 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((819608691 / 500000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12822 L e4 d4 ≤ (10445710513 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12822 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((819608691 / 500000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12822 L e6 d6 ≤ (15825096361 / 250000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12822 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((819608691 / 500000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12822 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12822 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12822 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12822 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (44982 / 1953125)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((1153002677 / 250000000000)) ^ 2 / 2 + ((1153002677 / 250000000000)) * ((10445710513 / 250000000000)) ^ 2 / 6 +
      ((10445710513 / 250000000000)) ^ 4 / 24 + ((10445710513 / 250000000000)) ^ 2 * ((15825096361 / 250000000000)) ^ 3 / 120 +
      2187 * ((15825096361 / 250000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12822 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12822 : ℝ) * ((1 + 3 * ((44982 / 1953125))) / (4 * (1 - (44982 / 1953125))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (44982 / 1953125)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12822 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (44982 / 1953125)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12822 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12822 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12822

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12822
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((11323427 / 100000) : ℝ) ≤ √12822 ∧ √12822 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1451888 : ℝ) ≤ Jz 12822 ∧ 1000000 ≤ Jz 12822 := by
  have hr : ((11323427 / 100000) : ℝ) ≤ √12822 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12822 : ℝ) * √12822 ≤ (⌈(12822 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12822
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12822 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12822 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12822 : ℝ) = (⌈(12822 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1451888 : ℝ) ≤ Jz 12822 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12822 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12822) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12822 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12822 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12822 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12822 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12822 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12822 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12822) :
    (12822 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12822 * √(qB 12822))) ≤
      (538920539 / 1000000000000) := by
  have hden : ((11323427 / 100000) : ℝ) * (63 / 100) ≤ √12822 * √(qB 12822) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12822 : ℝ) * √(qB 12822) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12822) :
    (12822 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12822 * √(qB 12822))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12822 : ℝ) * √(qB 12822) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12822 : ℝ) * (√12822 *
      (c1F (exp (1 / 2) / 12) (Jz 12822) * (186 / 10000) / Jz 12822)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12822)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12822 : ℝ) * (√12822 *
      (c1F (exp (1 / 2) / 12) (Jz 12822) * (186 / 10000) / Jz 12822)) =
      (12822 * (√12822 * c1F (exp (1 / 2) / 12) (Jz 12822)) * (186 / 10000)) /
        Jz 12822 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12822)]
  nlinarith

theorem row_energy_rule :
    (12822 : ℝ) * (12822 *
      (c2F (exp (1 / 2) / 12) (Jz 12822) * (186 / 10000) ^ 2 / Jz 12822)) ≤
      (3525711947 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12822)]
  nlinarith

end BstLean.Part266.Row12822

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12822
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12822) (hc : A1 c ∈ BstLean.Part153.Eop 12822) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12822 : ℝ)) ≤ (12489271641 / 1000000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12822 : ℝ) + 2 * √12822 ≤ (6524234271 / 500000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12822 : ℝ) ≤ (113234271 / 1000000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12822)
    (hc : A1 c ∈ BstLean.Part153.Eop 12822) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12822 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12822 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12822))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12822) (K : Set (Ix 12822)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12822 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12822 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12822) (hw : WINDOW (paperDesignP 12822) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12822)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12822) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12822 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12822 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12822 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12822 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12822) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12822)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12822)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12822

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12822
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12822) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12822 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12822) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12822) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12822 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12822 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12822 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12822}
    (hw : WINDOW (paperDesignP 12822) c) (hc : c ∈ tableEvent) (K : Set (Ix 12822)) :
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

def proposedBaseEvent : Set (Ret 12822) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12822)) : Prop where
  charge : (retDist (paperCentres 12822)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12822)} (h : TablePayment H) :
    (retDist (paperCentres 12822)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12822)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12822

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12822
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12822) (i : Fin 4) (a : Ix 12822) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12822) (a : Ix 12822) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12822) : Prop where
  moment : ∀ i, MomentBound (muI 12822) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12822} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12822) 8 (actualFourError c i)
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

end BstLean.Part266.Row12822

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12822
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

structure LatitudeVarianceCertificate (c : Ret 12822) : Prop where
  location : LBound (muI 12822) 12
    (fun a => conditionalVariance (stdGauss (Fin (12822 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12822) 12
    (fun a => conditionalVariance (stdGauss (Fin (12822 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12822) (hw : WINDOW (paperDesignP 12822) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12822 4 (55 / 100) /
      (12822 : ℝ) / ((12822 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12822

/-! The dimension-12822 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12822
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12822) (wl ws : ℝ) : SplitData 12822 :=
  BstLean.Part162.dPaper (paperDesignP 12822) c wl ws
    (√(2 / (12822 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12822 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12822 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12822) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12822) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12822 : ℝ)) * eR c * 12822 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12822) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12822 - 1)))
    (rowSplit c wl ws).good a ∂muI 12822 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12822) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12822 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12822) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12822 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12822) c (rowSplit c wl ws),
    hellG2 12822 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12822 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12822} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12822} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12822 t c BstLean.Part266.agent12822.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12822} (R : RootSource t c) :
    |√(QStand (paperDesignP 12822) t c) - √(qTilde (paperDesignP 12822) t c)| ≤
      BstLean.Part266.agent12822.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12822

/-! Rational enclosures for the HQ fluctuation price at dimension 12823. -/
namespace BstLean.Part266.Row12823
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1639153313 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (1439311 / 62500000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12823 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12823 * A / 2 + D + L * √(A * D)) ≤ (4612212051 / 1000000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12823 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1639153313 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12823 L e4 d4 ≤ (20892335359 / 500000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12823 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1639153313 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12823 L e6 d6 ≤ (63303148207 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12823 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1639153313 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12823 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12823 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12823 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12823 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (1439311 / 62500000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((4612212051 / 1000000000000)) ^ 2 / 2 + ((4612212051 / 1000000000000)) * ((20892335359 / 500000000000)) ^ 2 / 6 +
      ((20892335359 / 500000000000)) ^ 4 / 24 + ((20892335359 / 500000000000)) ^ 2 * ((63303148207 / 1000000000000)) ^ 3 / 120 +
      2187 * ((63303148207 / 1000000000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12823 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12823 : ℝ) * ((1 + 3 * ((1439311 / 62500000))) / (4 * (1 - (1439311 / 62500000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (1439311 / 62500000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12823 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (1439311 / 62500000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12823 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12823 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12823

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12823
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((22647737 / 200000) : ℝ) ≤ √12823 ∧ √12823 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1452058 : ℝ) ≤ Jz 12823 ∧ 1000000 ≤ Jz 12823 := by
  have hr : ((22647737 / 200000) : ℝ) ≤ √12823 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12823 : ℝ) * √12823 ≤ (⌈(12823 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12823
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12823 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12823 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12823 : ℝ) = (⌈(12823 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1452058 : ℝ) ≤ Jz 12823 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12823 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12823) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12823 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12823 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12823 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12823 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12823 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12823 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12823) :
    (12823 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12823 * √(qB 12823))) ≤
      (538941557 / 1000000000000) := by
  have hden : ((22647737 / 200000) : ℝ) * (63 / 100) ≤ √12823 * √(qB 12823) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12823 : ℝ) * √(qB 12823) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12823) :
    (12823 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12823 * √(qB 12823))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12823 : ℝ) * √(qB 12823) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12823 : ℝ) * (√12823 *
      (c1F (exp (1 / 2) / 12) (Jz 12823) * (186 / 10000) / Jz 12823)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12823)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12823 : ℝ) * (√12823 *
      (c1F (exp (1 / 2) / 12) (Jz 12823) * (186 / 10000) / Jz 12823)) =
      (12823 * (√12823 * c1F (exp (1 / 2) / 12) (Jz 12823)) * (186 / 10000)) /
        Jz 12823 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12823)]
  nlinarith

theorem row_energy_rule :
    (12823 : ℝ) * (12823 *
      (c2F (exp (1 / 2) / 12) (Jz 12823) * (186 / 10000) ^ 2 / Jz 12823)) ≤
      (1762924539 / 500000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12823)]
  nlinarith

end BstLean.Part266.Row12823

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12823
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12823) (hc : A1 c ∈ BstLean.Part153.Eop 12823) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12823 : ℝ)) ≤ (3122196161 / 250000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12823 : ℝ) + 2 * √12823 ≤ (3262369343 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12823 : ℝ) ≤ (56619343 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12823)
    (hc : A1 c ∈ BstLean.Part153.Eop 12823) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12823 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12823 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12823))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12823) (K : Set (Ix 12823)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12823 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12823 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12823) (hw : WINDOW (paperDesignP 12823) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12823)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12823) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12823 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12823 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12823 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12823 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12823) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12823)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12823)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12823

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12823
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12823) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12823 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12823) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12823) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12823 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12823 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12823 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12823}
    (hw : WINDOW (paperDesignP 12823) c) (hc : c ∈ tableEvent) (K : Set (Ix 12823)) :
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

def proposedBaseEvent : Set (Ret 12823) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12823)) : Prop where
  charge : (retDist (paperCentres 12823)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12823)} (h : TablePayment H) :
    (retDist (paperCentres 12823)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12823)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12823

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12823
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12823) (i : Fin 4) (a : Ix 12823) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12823) (a : Ix 12823) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12823) : Prop where
  moment : ∀ i, MomentBound (muI 12823) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12823} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12823) 8 (actualFourError c i)
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

end BstLean.Part266.Row12823

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12823
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

structure LatitudeVarianceCertificate (c : Ret 12823) : Prop where
  location : LBound (muI 12823) 12
    (fun a => conditionalVariance (stdGauss (Fin (12823 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12823) 12
    (fun a => conditionalVariance (stdGauss (Fin (12823 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12823) (hw : WINDOW (paperDesignP 12823) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12823 4 (55 / 100) /
      (12823 : ℝ) / ((12823 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12823

/-! The dimension-12823 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12823
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12823) (wl ws : ℝ) : SplitData 12823 :=
  BstLean.Part162.dPaper (paperDesignP 12823) c wl ws
    (√(2 / (12823 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12823 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12823 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12823) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12823) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12823 : ℝ)) * eR c * 12823 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12823) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12823 - 1)))
    (rowSplit c wl ws).good a ∂muI 12823 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12823) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12823 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12823) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12823 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12823) c (rowSplit c wl ws),
    hellG2 12823 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12823 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12823} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12823} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12823 t c BstLean.Part266.agent12823.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12823} (R : RootSource t c) :
    |√(QStand (paperDesignP 12823) t c) - √(qTilde (paperDesignP 12823) t c)| ≤
      BstLean.Part266.agent12823.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12823

/-! Rational enclosures for the HQ fluctuation price at dimension 12824. -/
namespace BstLean.Part266.Row12824
open BstLean.Part252
open Real
open BstLean.Part162 BstLean.Part180

structure FluctPriceBounds (κ L ε Exp A D e4 d4 e6 d6 : ℝ) : Prop where
  kappa : 0 ≤ κ ∧ κ ≤ 1001 / 1000
  location : 0 ≤ L ∧ L ≤ (1639089261 / 1000000000)
  epsilon : 0 ≤ ε ∧ ε ≤ (719599 / 31250000)
  exponential : 0 ≤ Exp ∧ Exp ≤ 2187
  energy : 0 ≤ A ∧ A ≤ 406 / 10 ^ 9
  displacement : 0 ≤ D ∧ D ≤ 1957 / 10 ^ 6
  energy_four : 0 ≤ e4 ∧ e4 ≤ 192 / 10 ^ 5
  location_four : 0 ≤ d4 ∧ d4 ≤ 133 / 1000
  energy_six : 0 ≤ e6 ∧ e6 ≤ 236 / 10 ^ 5
  location_six : 0 ≤ d6 ∧ d6 ≤ 164 / 1000

theorem fluct_chi_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    priceC κ 12824 L ε Exp A D e4 d4 e6 d6 ≤ 13 / 10 ^ 6 := by
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
  have hT2 : κ * (12824 * A / 2 + D + L * √(A * D)) ≤ (922482679 / 200000000000) := by
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12824 * (406 / 10 ^ 9) / 2 +
          1957 / 10 ^ 6 + ((1639089261 / 1000000000)) * (29 / 10 ^ 6)) := by gcongr
      _ ≤ _ := by norm_num
  have hT4 : tK κ 12824 L e4 d4 ≤ (41786499389 / 1000000000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12824 / 2 * (192 / 10 ^ 5) ^ 2 +
          (133 / 1000) ^ 2 + ((1639089261 / 1000000000)) * (133 / 1000) * (192 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT6 : tK κ 12824 L e6 d6 ≤ (989154859 / 15625000000) := by
    unfold tK
    calc
      _ ≤ (1001 / 1000 : ℝ) * (12824 / 2 * (236 / 10 ^ 5) ^ 2 +
          (164 / 1000) ^ 2 + ((1639089261 / 1000000000)) * (164 / 1000) * (236 / 10 ^ 5)) := by gcongr
      _ ≤ _ := by norm_num
  have hT20 : 0 ≤ κ * (12824 * A / 2 + D + L * √(A * D)) := by positivity
  have hT40 : 0 ≤ tK κ 12824 L e4 d4 := by unfold tK; positivity
  have hT60 : 0 ≤ tK κ 12824 L e6 d6 := by unfold tK; positivity
  unfold priceC
  calc
    _ ≤ (1001 / 1000 : ℝ) * (12824 * (406 / 10 ^ 9) ^ 2 / 4 +
        (1 + (719599 / 31250000)) * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) +
      ((922482679 / 200000000000)) ^ 2 / 2 + ((922482679 / 200000000000)) * ((41786499389 / 1000000000000)) ^ 2 / 6 +
      ((41786499389 / 1000000000000)) ^ 4 / 24 + ((41786499389 / 1000000000000)) ^ 2 * ((989154859 / 15625000000)) ^ 3 / 120 +
      2187 * ((989154859 / 15625000000)) ^ 6 / 720 := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_cubic_price {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    cubP 12824 ε (85 / 100) (64 / 100) A D e6 d6 ≤ 13 / 10 ^ 7 := by
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
    _ ≤ (((12824 : ℝ) * ((1 + 3 * ((719599 / 31250000))) / (4 * (1 - (719599 / 31250000))))) ^ 3 *
        ((406 / 10 ^ 9) * (638 / 10 ^ 6) * (236 / 10 ^ 5) ^ 3) / (64 / 100) ^ 2 +
        (1 / (2 * (1 - (719599 / 31250000)))) ^ 3 *
          ((1957 / 10 ^ 6) * (45 / 1000) * (164 / 1000) ^ 3) / (1 - 64 / 100) ^ 2) /
          (85 / 100) ^ 2 +
      (12824 * (406 / 10 ^ 9) ^ 2 + 2 * (406 / 10 ^ 9) * (1957 / 10 ^ 6)) /
        ((1 - (719599 / 31250000)) ^ 2 * (1 - 85 / 100) ^ 2) := by gcongr
    _ ≤ _ := by norm_num

theorem fluct_mixture_root {κ L ε Exp A D e4 d4 e6 d6 : ℝ}
    (h : FluctPriceBounds κ L ε Exp A D e4 d4 e6 d6) :
    √(priceC κ 12824 L ε Exp A D e4 d4 e6 d6 / 4 +
      3 / 4 * cubP 12824 ε (85 / 100) (64 / 100) A D e6 d6) ≤ 2060 / 10 ^ 6 := by
  apply sqrt_le_iff.mpr
  refine ⟨by norm_num, ?_⟩
  have hc := fluct_chi_price h
  have hq := fluct_cubic_price h
  linarith

end BstLean.Part266.Row12824

/-! The fixed grid and Gaussian rule leave explicit room for the exact-rule errors. -/
namespace BstLean.Part266.Row12824
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)

theorem row_sqrt_bounds : ((113243101 / 1000000) : ℝ) ≤ √12824 ∧ √12824 ≤ 114 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1452228 : ℝ) ≤ Jz 12824 ∧ 1000000 ≤ Jz 12824 := by
  have hr : ((113243101 / 1000000) : ℝ) ≤ √12824 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12824 : ℝ) * √12824 ≤ (⌈(12824 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12824
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12824 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12824 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12824 : ℝ) = (⌈(12824 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1452228 : ℝ) ≤ Jz 12824 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12824 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12824) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12824 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12824 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12824 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12824 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12824 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12824 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12824) :
    (12824 : ℝ) * (283 / 100 * 163 * (d / 2) / (√12824 * √(qB 12824))) ≤
      (67370321 / 125000000000) := by
  have hden : ((113243101 / 1000000) : ℝ) * (63 / 100) ≤ √12824 * √(qB 12824) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12824 : ℝ) * √(qB 12824) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12824) :
    (12824 : ℝ) * (2 * (283 / 100 * 163) ^ 2 * (d / 2) /
      (12824 * √(qB 12824))) ≤ (4390873069 / 1000000000000) := by
  have hden := row_bulk_radius
  have hpos : 0 < (12824 : ℝ) * √(qB 12824) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12824 : ℝ) * (√12824 *
      (c1F (exp (1 / 2) / 12) (Jz 12824) * (186 / 10000) / Jz 12824)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12824)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 114)
  have he : (12824 : ℝ) * (√12824 *
      (c1F (exp (1 / 2) / 12) (Jz 12824) * (186 / 10000) / Jz 12824)) =
      (12824 * (√12824 * c1F (exp (1 / 2) / 12) (Jz 12824)) * (186 / 10000)) /
        Jz 12824 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12824)]
  nlinarith

theorem row_energy_rule :
    (12824 : ℝ) * (12824 *
      (c2F (exp (1 / 2) / 12) (Jz 12824) * (186 / 10000) ^ 2 / Jz 12824)) ≤
      (3525986219 / 1000000000000) := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12824)]
  nlinarith

end BstLean.Part266.Row12824

/-! The stored-table moments reduce to the two errors of the exact Gaussian rule. -/
namespace BstLean.Part266.Row12824
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

theorem first_matrix_op_row (c : Ret 12824) (hc : A1 c ∈ BstLean.Part153.Eop 12824) :
    BstLean.Part152.opN (A1 c) ≤ 163 := by
  refine hc.trans ?_
  have hs : √(2 / (12824 : ℝ)) ≤ (1561037213 / 125000000000) :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12824 : ℝ) + 2 * √12824 ≤ (3262621551 / 250000) := by
    linarith [(sqrt_le_iff.mpr (by norm_num) : √(12824 : ℝ) ≤ (56621551 / 500000))]
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12824)
    (hc : A1 c ∈ BstLean.Part153.Eop 12824) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12824 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12824 * 163 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12824))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12824) (K : Set (Ix 12824)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12824 ≤ (649 / 10000 : ℝ) ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12824 ≤ (2173 / 10000 : ℝ) ^ 8

theorem stored_table_moments (c : Ret 12824) (hw : WINDOW (paperDesignP 12824) c)
    (hc : c ∈ passEvent) {K : Set (Ix 12824)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12824) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12824 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12824 ≤ energyError ^ 8) ∧
    (∫ a in K, ((12824 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12824 ≤ locationError ^ 8) := by
  have hfirst := hc.1.1.2 hw.2.1
  have h1 := first_matrix_row c hfirst
  have h2 := second_matrix_row c hc.1.2
  have hθ := window_winC (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1 hθ.2.1 hθ.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12824) c a))
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
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12824)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12824)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold energyError
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold locationError
    linarith

end BstLean.Part266.Row12824

/-! The table event is defined by the actual exact-rule moments, before choosing a split. -/
namespace BstLean.Part266.Row12824
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169

def tableEvent : Set (Ret 12824) := {c | BstLean.Part170.windowW c.1 →
  BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8 ∧
  BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}

theorem tableEvent_measurable : MeasurableSet tableEvent := by
  have hw : MeasurableSet {c : Ret 12824 | BstLean.Part170.windowW c.1} :=
    BstLean.Part170.measurableSet_windowW.preimage measurable_fst
  have hf := measurableSet_le (BstLean.Part170.measurable_intF_comp (n := 12824) measurable_id)
    (measurable_const (a := (649 / 10000 : ℝ) ^ 8))
  have he := measurableSet_le (BstLean.Part170.measurable_intW_comp (n := 12824) measurable_id)
    (measurable_const (a := (2173 / 10000 : ℝ) ^ 8))
  have heq : tableEvent = {c : Ret 12824 | BstLean.Part170.windowW c.1}ᶜ ∪
      ({c : Ret 12824 | BstLean.Part170.intF c ≤ (649 / 10000 : ℝ) ^ 8} ∩
        {c : Ret 12824 | BstLean.Part170.intW c ≤ (2173 / 10000 : ℝ) ^ 8}) := by
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

theorem exactTableMoments_of_event {c : Ret 12824}
    (hw : WINDOW (paperDesignP 12824) c) (hc : c ∈ tableEvent) (K : Set (Ix 12824)) :
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

def proposedBaseEvent : Set (Ret 12824) := baseEvent tableEvent

theorem proposedBaseEvent_measurable : MeasurableSet proposedBaseEvent :=
  baseEvent_measurable tableEvent_measurable

/-- The remaining payment concerns this particular table event and the given hidden event. -/
structure TablePayment (H : Set (Ret 12824)) : Prop where
  charge : (retDist (paperCentres 12824)).real (H ∩ tableEventᶜ) ≤ tableChargeAllowance

theorem proposedBaseEvent_charge {H : Set (Ret 12824)} (h : TablePayment H) :
    (retDist (paperCentres 12824)).real (H ∩ proposedBaseEventᶜ) ≤
      BstLean.Part249.baseChargeAllowance := baseEvent_charge h.charge

theorem proposedBaseEvent_certificate {H : Set (Ret 12824)} (h : TablePayment H) :
    BaseEventCertificate H tableEvent := baseEventCertificate tableEvent_measurable h.charge

end BstLean.Part266.Row12824

/-! Four original-matrix error moments supply the actual stored-table event. -/
namespace BstLean.Part266.Row12824
open BstLean.Part252
open MeasureTheory Real Set
open scoped ENNReal
open BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170
open BstLean.Part220 BstLean.Part223 BstLean.Part242

noncomputable def fourAllowances : Fin 4 → ℝ :=
  ![327299256 / 10 ^ 10, 318401156 / 10 ^ 10,
    1806348476 / 10 ^ 10, 341964241 / 10 ^ 10]

noncomputable def actualFourError (c : Ret 12824) (i : Fin 4) (a : Ix 12824) : ℝ :=
  originalFourErrors c i (gW c.1 a) (A2 c)

theorem actualFour_decomposition (c : Ret 12824) (a : Ix 12824) :
    actualFourError c 0 a + actualFourError c 1 a = exF c a ∧
    actualFourError c 2 a + actualFourError c 3 a = exW c a := by
  exact originalFour_decomposition c (gW c.1 a) (A2 c)

structure FourTableMoments (c : Ret 12824) : Prop where
  moment : ∀ i, MomentBound (muI 12824) (biasOrder i) (actualFourError c i)
    (fourAllowances i)

theorem fourTableMoments_to_event {c : Ret 12824} (h : FourTableMoments c) :
    c ∈ tableEvent := by
  have hb (i : Fin 4) : MomentBound (muI 12824) 8 (actualFourError c i)
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

end BstLean.Part266.Row12824

/-! The realized latitude event supplies the two normalized variance fields of SY2. -/
namespace BstLean.Part266.Row12824
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

structure LatitudeVarianceCertificate (c : Ret 12824) : Prop where
  location : LBound (muI 12824) 12
    (fun a => conditionalVariance (stdGauss (Fin (12824 - 1))) (fun v => fLatitude c (a, v)))
    varianceTwelve
  residual : LBound (muI 12824) 12
    (fun a => conditionalVariance (stdGauss (Fin (12824 - 1))) (fun v => zLatitude c (a, v)))
    varianceTwelve

theorem latitudeVarianceCertificate (c : Ret 12824) (hw : WINDOW (paperDesignP 12824) c)
    (he : 0 < eR c) (hc : c ∈ passEvent) : LatitudeVarianceCertificate c := by
  have hL := BstLean.Part212.freshRetainedEvent160_fields (hc.1.1.1.2 hw.2.1)
    (window_winC (by norm_num) c hw)
  have hC := fresh_latitude_constant_pos_row.le
  have hnum : BstLean.Part212.freshLatitudeConstant160 12824 4 (55 / 100) /
      (12824 : ℝ) / ((12824 : ℝ) - 2) ≤ varianceTwelve := by
    have h := latitude_constant_sharp_row
    norm_num [varianceTwelve] at *
    linarith
  have hf := fLatitude_variance_norm12 (by norm_num) c hC he hL
  have hz := zLatitude_variance_norm12 (by norm_num) c hC hL
  refine ⟨⟨hf.measurable, by norm_num [varianceTwelve], ?_⟩,
    ⟨hz.measurable, by norm_num [varianceTwelve], ?_⟩⟩
  · exact hf.bound.trans (ENNReal.ofReal_le_ofReal hnum)
  · exact hz.bound.trans (ENNReal.ofReal_le_ofReal hnum)

end BstLean.Part266.Row12824

/-! The dimension-12824 root constructor uses the original conditional passes.
The network moment and fluctuation supplies remain explicit. -/
namespace BstLean.Part266.Row12824
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part29 (stdGauss)

noncomputable def rowSplit (c : Ret 12824) (wl ws : ℝ) : SplitData 12824 :=
  BstLean.Part162.dPaper (paperDesignP 12824) c wl ws
    (√(2 / (12824 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12824 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12824 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are bounds on the actual network integrals, not the replacement conclusion. -/
structure RootSource (t : ℝ) (c : Ret 12824) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12824) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤
    (2 / (12824 : ℝ)) * eR c * 12824 * chi
  moments : PaperMoments c (keptIx (paperDesignP 12824) c (rowSplit c wl ws))
    varianceMax energyError locationError locationNorm varianceNorm
  removal : ∫ a, removed (stdGauss (Fin (12824 - 1)))
    (rowSplit c wl ws).good a ∂muI 12824 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12824) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12824 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12824) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12824 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12824) c (rowSplit c wl ws),
    hellG2 12824 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12824 ≤ displacementBudget

/-- All pass guards and integrability proofs are supplied, including the variable bias floor. -/
theorem row_pass_inputs {t : ℝ} {c : Ret 12824} (R : RootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax energyError locationError locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [energyError]) (by norm_num [locationError])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre R.moments

/-- The constructor supplies the requested Lean structure after the source integrals are bounded. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12824} (R : RootSource t c) :
    BstLean.Part243.RootInputs 12824 t c BstLean.Part266.agent12824.root where
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

theorem replacement_of_source {t : ℝ} {c : Ret 12824} (R : RootSource t c) :
    |√(QStand (paperDesignP 12824) t c) - √(qTilde (paperDesignP 12824) t c)| ≤
      BstLean.Part266.agent12824.root := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part266.Row12824
