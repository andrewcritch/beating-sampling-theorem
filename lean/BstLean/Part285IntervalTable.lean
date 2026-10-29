import BstLean.Part280World

/-! A symbolic sharp-table payment at each dimension. No per-row data. -/
namespace BstLean.Part285.Interval
open MeasureTheory Real Set Matrix
open scoped ENNReal
open BstLean.Part29 (stdGauss)
open BstLean.Part130 BstLean.Part153 BstLean.Part157 BstLean.Part161 BstLean.Part169
open BstLean.Part170 BstLean.Part220 BstLean.Part223
open BstLean.Part252 (product_charge_ae)
open BstLean.Part276 (fourA)
open BstLean.Part280 (tightG sharpTableN sharpTableN_measurable sharpTableN_bad_subset
  nodeMeasureN nodeMeasureN_mass nodeMeasureN_moment12 node_geometryN sharpVarianceEventN
  sharpFirstEventN sharpFirstEventN_measurable sharpVarianceEventN_charge sharpBadPairN
  sharpBadPairN_measurable sharpPairEventN sharpPairEventN_measurable first_charge_priceN)

variable {n : ℕ}

noncomputable def exactFourPrice (n : ℕ) (O : ℝ) : ℝ :=
  let p := completeMomentPrices n (58 / 100) O (17 / (100 * n)) (26 / (10 * n))
    (statisticsConstant (paperBound256 n)) √((42 / 10 : ℝ) / n) (5275 / 10000)
  p 0 / fourA 0 ^ 24 + p 1 / fourA 1 ^ 16 + p 2 / fourA 2 ^ 18 + p 3 / fourA 3 ^ 16

theorem exactFourPrice_nonneg (n : ℕ) (O : ℝ) : 0 ≤ exactFourPrice n O := by
  unfold exactFourPrice
  exact add_nonneg (add_nonneg (add_nonneg
    (div_nonneg (completeMomentPrices_nonneg ..) (by positivity))
    (div_nonneg (completeMomentPrices_nonneg ..) (by positivity)))
    (div_nonneg (completeMomentPrices_nonneg ..) (by positivity)))
    (div_nonneg (completeMomentPrices_nonneg ..) (by positivity))

theorem first_matrix_exact {O : ℝ} (c : Ret n)
    (hO : √(2 / (n : ℝ)) * ((n : ℝ) + 2 * √(n : ℝ)) ≤ O)
    (hc : A1 c ∈ Eop n) : OpB (A1 c) O :=
  opB_of_opN (A1 c) (hc.trans hO)

theorem sharpFirstEventK_charge (hn : 11883 ≤ n) (hn2 : n ≤ 16199) {wr : WRet n}
    (hw : tightG wr) :
    (gaussMat (mA n) n (2 / (n : ℝ))).real (sharpFirstEventN (by omega) wr)ᶜ ≤
      (126145 / 10 ^ 9 : ℝ) := by
  have hn' : 11883 ≤ n := by omega
  have hc := BstLean.Part172.sg_wr_ne (by omega) hw.1
  have hs (g : Fin (Js n)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := node_geometryN hn' hw (0, 0) g.isLt
    linarith [h.2.1]
  have hstat := paperCoefficient_statistics_oneTenThousand (by omega) (by omega)
    wr hc (nodeMeasureN (by omega) wr) (nodeMeasureN_mass (by omega) wr).le Fin.val hs
  unfold sharpFirstEventN
  repeat rw [compl_inter]
  exact ((measureReal_union_le _ _).trans (add_le_add
    ((measureReal_union_le _ _).trans (add_le_add (Eop_prob (by omega))
      (sharpVarianceEventN_charge hn' hw))) hstat)).trans (first_charge_priceN hn')

theorem sharp_conditional_charge_exact (hn : 11883 ≤ n) (hn2 : n ≤ 16199) {O : ℝ}
    (hO0 : 0 ≤ O)
    (hO : ∀ c : Ret n, A1 c ∈ Eop n → OpB (A1 c) O)
    (hgap : 0 < envelopeGap n (58 / 100) O (17 / (100 * n))) {wr : WRet n}
    (hwt : tightG wr) :
    ∀ᵐ X ∂gaussMat (mA n) n (2 / (n : ℝ)), X ∈ sharpFirstEventN (by omega) wr →
      (gaussMat (mA n) (mA n) (tA n))
        {M | (X, M) ∈ sharpBadPairN n wr} ≤ ENNReal.ofReal (exactFourPrice n O) := by
  have hn' : 11883 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hx0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hw : windowW wr := hwt.1
  have hc := BstLean.Part172.sg_wr_ne hn1 hw
  have hs (g : Fin (Js n)) : nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ 1 := by
    have h := node_geometryN hn' hwt (0, 0) g.isLt
    linarith [h.2.1]
  have hq (g : Fin (Js n)) : 0 ≤ 1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ∧
      1 - nodeS (mkR wr (0, 0)) g.val ^ 2 ≤ (58 / 100 : ℝ) :=
    ⟨sub_nonneg.mpr (hs g), (node_geometryN hn' hwt (0, 0) g.isLt).2.2⟩
  have h12 := nodeMeasureN_moment12 hn' hwt
  filter_upwards [paperNodes_kink_ae (by omega) wr Fin.val hs] with X hk
  intro hX
  have hvar := hX.1.2
  have hmin (g : Fin (Js n)) := (hvar g).1
  have hmax (g : Fin (Js n)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤ (26 / (10 * n) : ℝ) := by
    refine (hvar g).2.trans ?_
    have h1 : 42 / (10 * (n : ℝ)) * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) ≤
        42 / (10 * (n : ℝ)) * (58 / 100) :=
      mul_le_mul_of_nonneg_left (hq g).2 (by positivity)
    have h2 : 42 / (10 * (n : ℝ)) * (58 / 100) ≤ 26 / (10 * n) := by
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
      norm_num
    exact h1.trans h2
  have htrace (g : Fin (Js n)) :
      vsig2 (mkR wr (X, 0)) (nodeS (mkR wr (X, 0)) g.val) ≤
        √((42 / 10 : ℝ) / n) ^ 2 * (1 - nodeS (mkR wr (0, 0)) g.val ^ 2) := by
    rw [sq_sqrt (by positivity)]
    have e : (42 / 10 : ℝ) / n = 42 / (10 * n) := by
      rw [div_div]
    rw [e]
    exact (hvar g).2
  have hA (i : Fin 4) : 0 < fourA i := BstLean.Part276.fourA_pos i
  have hmark := paperOriginalFour_markov (by omega) wr hc (nodeMeasureN hn1 wr)
    (nodeMeasureN_mass hn1 wr).le Fin.val hs X (by norm_num : (0 : ℝ) ≤ 58 / 100)
    hO0 (by positivity : (0 : ℝ) < 17 / (100 * n))
    (by positivity : (0 : ℝ) ≤ 26 / (10 * n)) (statisticsConstant_pos ((paperStatisticsBound_pos (by omega : 4 ≤ n)
      (by norm_num : 1 ≤ (2 : ℕ))).trans_le
      (paperStatisticsBound_le_paperBound (by omega : 8000 ≤ n) (by omega : n ≤ 16384)))).le
    (sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 5275 / 10000)
    (hO (mkR wr (X, 0)) hX.1.1) hX.2 (fun g => (hq g).2)
    hmin hmax htrace hgap h12 hk fourA hA
  have hreal : (gaussMat (mA n) (mA n) (tA n)).real
      {M | (X, M) ∈ sharpBadPairN n wr} ≤ (exactFourPrice n O) :=
    ((measureReal_mono (sharpTableN_bad_subset hn1 (mkR wr (X, 0)))
      (measure_ne_top _ _)).trans hmark)
  rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
  exact ENNReal.ofReal_le_ofReal hreal

theorem sharp_world_charge_exact (hn : 11883 ≤ n) (hn2 : n ≤ 16199) {O : ℝ}
    (hO0 : 0 ≤ O)
    (hO : ∀ c : Ret n, A1 c ∈ Eop n → OpB (A1 c) O)
    (hgap : 0 < envelopeGap n (58 / 100) O (17 / (100 * n))) (wr : WRet n) :
    (nuA n).real (sharpBadPairN n wr) ≤ 126145 / 10 ^ 9 + exactFourPrice n O := by
  by_cases hw : tightG wr
  · exact product_charge_ae _ _ (sharpFirstEventN_measurable (by omega) wr)
      (sharpBadPairN_measurable wr) (by norm_num) (exactFourPrice_nonneg n O)
      (sharpFirstEventK_charge hn hn2 hw)
      (sharp_conditional_charge_exact hn hn2 hO0 hO hgap hw)
  · have he : sharpBadPairN n wr = ∅ := by
      ext θ
      simp only [sharpBadPairN, mem_setOf_eq, mem_empty_iff_false, iff_false, not_not]
      intro h
      exact False.elim (hw h)
    rw [he, measureReal_empty]
    linarith [exactFourPrice_nonneg n O]

/-- The smaller, dimension-dependent table price. -/
theorem sharpTable_per_n_charge (hn : 11883 ≤ n) (hn2 : n ≤ 16199) {O : ℝ}
    (hO0 : 0 ≤ O)
    (hO : ∀ c : Ret n, A1 c ∈ Eop n → OpB (A1 c) O)
    (hgap : 0 < envelopeGap n (58 / 100) O (17 / (100 * n))) :
    (retDist (paperCentres n)).real (sharpTableN n)ᶜ ≤
      126145 / 10 ^ 9 + exactFourPrice n O := by
  have h := retDist_pair_charge (paperCentres n) sharpPairEventN_measurable
    (by linarith [exactFourPrice_nonneg n O] : (0 : ℝ) ≤ 126145 / 10 ^ 9 + exactFourPrice n O)
    (sharp_world_charge_exact hn hn2 hO0 hO hgap)
  convert h using 1
  congr 1

/-- The exact first-layer operator envelope at dimension `n`. -/
noncomputable def firstOp (n : ℕ) : ℝ :=
  √(2 / (n : ℝ)) * ((n : ℝ) + 2 * √(n : ℝ))

theorem firstOp_nonneg (n : ℕ) : 0 ≤ firstOp n := by unfold firstOp; positivity

theorem firstOp_le (hn : 12000 ≤ n) (hn2 : n ≤ 16199) : firstOp n ≤ 183 := by
  have hl : (12000 : ℝ) ≤ n := by exact_mod_cast hn
  have hu : (n : ℝ) ≤ 16199 := by exact_mod_cast hn2
  have hp : (0 : ℝ) < n := by linarith
  have hs : √(2 / (n : ℝ)) * √n = √2 := by
    rw [← sqrt_mul (by positivity), div_mul_cancel₀ _ hp.ne']
  have hm : √(2 / (n : ℝ)) * n = √2 * √n := by
    calc
      _ = (√(2 / (n : ℝ)) * √n) * √n := by
        rw [mul_assoc, ← pow_two, sq_sqrt hp.le]
      _ = _ := by rw [hs]
  have h2 : √(2 : ℝ) ≤ 14143 / 10000 := sqrt_le_iff.mpr (by norm_num)
  have hN : √(n : ℝ) ≤ 12728 / 100 := sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  have he : firstOp n = √2 * (√n + 2) := by
    unfold firstOp
    calc
      _ = √(2 / (n : ℝ)) * n + 2 * (√(2 / (n : ℝ)) * √n) := by ring
      _ = _ := by rw [hm, hs]; ring
  rw [he]
  exact (mul_le_mul h2 (by linarith : √(n : ℝ) + 2 ≤ 12928 / 100)
    (by positivity) (by norm_num)).trans (by norm_num)

theorem firstOp_gap (hn : 12000 ≤ n) (hn2 : n ≤ 16199) :
    0 < envelopeGap n (58 / 100) (firstOp n) (17 / (100 * n)) := by
  have hl : (12000 : ℝ) ≤ n := by exact_mod_cast hn
  have hu : (n : ℝ) ≤ 16199 := by exact_mod_cast hn2
  have hp : (0 : ℝ) < n := by linarith
  have ho := pow_le_pow_left₀ (firstOp_nonneg n) (firstOp_le hn hn2) 2
  have hden : 0 < (n : ℝ) - 2 := by linarith
  have ht : 0 ≤ 2 * (2 / (n : ℝ) ^ 2) * ((58 / 100) / (n - 2)) := by positivity
  have hm := mul_le_mul_of_nonneg_left ho ht
  have hd : 0 < (17 / (100 * (n : ℝ))) / 2 -
      2 * (2 / (n : ℝ) ^ 2) * ((58 / 100) * 183 ^ 2 / (n - 2)) := by
    have h1 : (17 / (100 * 16199) / 2 : ℝ) ≤ 17 / (100 * (n : ℝ)) / 2 := by
      gcongr
    have h2 : 2 * (2 / (n : ℝ) ^ 2) * ((58 / 100) * 183 ^ 2 / (n - 2)) ≤
        (2 * (2 / 12000 ^ 2) * ((58 / 100) * 183 ^ 2 / (12000 - 2)) : ℝ) := by
      gcongr
      all_goals first | linarith | exact div_nonneg (by positivity) hden.le
    exact lt_of_lt_of_le (by norm_num) (sub_le_sub h1 h2)
  unfold envelopeGap
  rw [BstLean.Part280.tA_eq]
  ring_nf at hm hd ⊢
  linarith only [hm, hd]

/-- A table price that varies with `n`, with all operator and gap premises discharged. -/
noncomputable def tablePrice (n : ℕ) : ℝ :=
  126145 / 10 ^ 9 + exactFourPrice n (firstOp n)

theorem sharpTable_dimension_charge (hn : 12000 ≤ n) (hn2 : n ≤ 16199) :
    (retDist (paperCentres n)).real (sharpTableN n)ᶜ ≤ tablePrice n :=
  sharpTable_per_n_charge (by omega) hn2 (firstOp_nonneg n)
    (fun c hc => first_matrix_exact c (le_refl _) hc) (firstOp_gap hn hn2)

end BstLean.Part285.Interval
