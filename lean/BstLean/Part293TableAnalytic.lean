import BstLean.Part293Stored
import BstLean.Part293TableGeometry
import BstLean.Part293TableNumbers
import BstLean.Part293OperatorVariance
import BstLean.Part252Variance

/-! Deterministic table adapters, independent of the unfinished table event charge. -/
namespace BstLean.Part293
open Real Set MeasureTheory
open BstLean.Part130 BstLean.Part157 BstLean.Part161 BstLean.Part169 BstLean.Part170

theorem table_variance_of_operators {n : ℕ} (hn : 8000 ≤ n) (c : Ret n)
    {O1 O2 : ℝ} (h1 : OpB (A1 c) O1) (h2 : OpB (A2 c) O2)
    (h10 : 0 ≤ O1) (h20 : 0 ≤ O2)
    (hprod : (O2 * O1) ^ 2 ≤ 16.411 * (n : ℝ))
    (hb : normSq (bR c) ≠ 0) (a : Ix n) : |VR c a| ≤ 0.00411 := by
  have hv := BstLean.Part252.variance_pointwise (by omega) c hb h1 h2 h10 h20 a
  rw [abs_of_nonneg hv.1]
  apply hv.2.trans
  have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  rw [div_pow, sq_sqrt hn0.le,
    div_le_iff₀ (show (0 : ℝ) < (n : ℝ) - 2 by linarith)]
  have hp : (O2 * O1) ^ 2 / n ≤ 16.411 := (div_le_iff₀ hn0).mpr hprod
  nlinarith

noncomputable def storedInputs_of_operator_bounds {n : ℕ} (hn : 8000 ≤ n) (c : Ret n)
    (hw : TableWorldGuard c.1) {O1 O2 : ℝ}
    (hO1 : 0 < O1) (hO2 : 0 < O2)
    (hA : OpB (A1 c) O1) (hB : OpB (A2 c) O2)
    (hfirst : O1 ^ 2 ≤ (2049 / 1000 : ℝ) * n)
    (hprod : (O2 * O1) ^ 2 ≤ 16.411 * (n : ℝ))
    (hF : intF c ≤ (0.0472657646 : ℝ) ^ 8)
    (hW : intW c ≤ (0.1726196304 : ℝ) ^ 8)
    {K : Set (Ix n)} (hK : MeasurableSet K) (hsub : K ⊆ bulkIx (paperDesignP n) c) :
    StoredInputs c K 0.1802 0.05125 := by
  have hLH := (bulk_of_window (by omega) c hw.1.1 hw.1.2.1 hw.1.2.2).1
  have hd0 : 0 ≤ nodeD c / 2 := by
    unfold nodeD
    exact div_nonneg (div_nonneg (sub_nonneg.mpr hLH.le) (Nat.cast_nonneg _)) (by norm_num)
  have hg := table_grid_prices hn (mul_nonneg hO2.le hO1.le) hd0 hprod
    (normalized_node_width hn c hw)
  have hr := table_rule_prices hn
  refine {
    O1 := O1
    O2 := O2
    q := 391 / 1000
    sigma := tableSigma n
    tableF := 0.0472657646
    tableW := 0.1726196304
    gridF := 0.000625
    gridW := 0.00507
    ruleF := 0.003346
    ruleW := 0.002497
    O1_pos := hO1
    O2_pos := hO2
    q_pos := by norm_num
    sigma_pos := (tableSigma_bounds hn).1
    tableF_pos := by norm_num
    tableW_pos := by norm_num
    first_operator := hA
    second_operator := hB
    kept_measurable := hK
    kept_bulk := hsub
    node_separation := hLH
    node_bulk := ?_
    node_variance := ?_
    exact_location := hF
    exact_energy := hW
    grid_location := hg.1
    grid_energy := hg.2
    rule_location := hr.1
    rule_energy := hr.2
    location_total := by norm_num
    energy_total := by norm_num }
  · intro s hsL hsH
    have hh := (table_bulk_geometry hn c hw ⟨hsL, hsH⟩).2.1
    linarith
  · intro a ha
    have hl := hsub ha
    have hg' := (gIdx_near (by omega) c hLH hl.1 hl.2).2
    have hnode := BstLean.Part169.nodeS_mem c hLH hg'
    have hgeo := table_bulk_geometry hn c hw hnode
    have hsq : sgR c a ^ 2 ≤ 1 := by change nodeS c _ ^ 2 ≤ 1; linarith [hgeo.2.1]
    have hc := BstLean.Part172.sg_wr_ne (by omega : 1 ≤ n) hw.1
    have hv := variance_le_operator (by omega) c hc hA hsq
    have hnR : (8000 : ℝ) ≤ n := by exact_mod_cast hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hd : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    apply hv.trans
    rw [tableSigma, sq_sqrt (div_nonneg (by norm_num) hd.le)]
    calc
      _ ≤ 2 * ((2049 / 1000 : ℝ) * n) / (n * ((n : ℝ) - 1)) * (605 / 1000) := by
        exact mul_le_mul
          (div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hfirst (by norm_num)) (by positivity))
          hgeo.2.2 (by linarith [hsq]) (by positivity)
      _ ≤ 2.48 / ((n : ℝ) - 1) := by
        field_simp
        nlinarith

end BstLean.Part293
