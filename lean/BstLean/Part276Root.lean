import BstLean.Part276Table

/-! The sharp bias supply at dimension 12224: the stored-table event with the paper's
allowances gives the energy and location errors, and the paper's `aw`, `af` give
the replacement root `0.0074488`. -/
namespace BstLean.Part276.Row12224
open BstLean.Part252
open MeasureTheory Real Set
open BstLean.Part130 BstLean.Part157 BstLean.Part160 BstLean.Part161 BstLean.Part169
open BstLean.Part150 (c1F c2F)
open BstLean.Part29 (stdGauss)
open BstLean.Part276 (sharpTable tableF tableW tightW_of_window)

noncomputable def eta : ℝ := 2147 / 10 ^ 6
noncomputable def mixtureFloor : ℝ := 215240 / 10 ^ 6
noncomputable def biasFloor : ℝ := (1 - eta) * mixtureFloor
noncomputable def chi : ℝ := 1065 / 1000
noncomputable def epsilon : ℝ := 1 / 50
noncomputable def varianceMax : ℝ := 3 / 1000
/-- The paper's energy and location allowances at 12224: the four allowances plus the
Lean rule and grid errors. -/
noncomputable def sharpAw : ℝ := 15923 / 10 ^ 5
noncomputable def sharpAf : ℝ := 5415 / 10 ^ 5
noncomputable def locationNorm : ℝ := 1002 / 1000
noncomputable def varianceNorm : ℝ := 1 / 2000
/-- The removal, mixture and displacement values of the stored row, rounded up. -/
noncomputable def removalBudget : ℝ := (5044 / 10 ^ 8) ^ 2 / (2 * (1 + eta⁻¹))
noncomputable def mixtureRoot : ℝ := 299269 / 10 ^ 8
noncomputable def displacementBudget : ℝ := (28185 / 10 ^ 8) ^ 2
noncomputable def biasRootCap : ℝ := 4072 / 10 ^ 6
/-- The stored row root `hi(ha) = 0.0074488` (rounded up). -/
noncomputable def rootTarget : ℝ := 74488 / 10 ^ 7

theorem eta_pos : 0 < eta := by norm_num [eta]
theorem eta_lt_one : eta < 1 := by norm_num [eta]
theorem bias_floor_ge : (1 / 5 : ℝ) ≤ biasFloor := by
  norm_num [biasFloor, eta, mixtureFloor]
theorem bias_threshold_pos : 0 < epsilon - varianceMax / biasFloor := by
  norm_num [epsilon, varianceMax, biasFloor, eta, mixtureFloor]

theorem stored_squared_price :
    BstLean.Part241.squaredPrice 12224 chi biasFloor epsilon varianceMax
      sharpAw sharpAf locationNorm varianceNorm ≤ biasRootCap ^ 2 := by
  norm_num [BstLean.Part241.squaredPrice, BstLean.Part241.regularPrice,
    BstLean.Part241.scaleBound, BstLean.Part241.exceptionalMass, chi, biasFloor,
    epsilon, varianceMax, sharpAw, sharpAf, locationNorm, varianceNorm,
    biasRootCap, eta, mixtureFloor]

theorem stored_bias_root :
    BstLean.Part241.biasRoot 12224 chi biasFloor epsilon varianceMax
      sharpAw sharpAf locationNorm varianceNorm ≤ biasRootCap := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num [biasRootCap], stored_squared_price⟩)

theorem removal_root : √(2 * (1 + eta⁻¹) * removalBudget) = 5044 / 10 ^ 8 := by
  have h : 2 * (1 + eta⁻¹) * removalBudget = (5044 / 10 ^ 8 : ℝ) ^ 2 := by
    norm_num [eta, removalBudget]
  rw [h, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 5044 / 10 ^ 8)]

theorem displacement_root : √displacementBudget = 28185 / 10 ^ 8 := by
  exact Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 28185 / 10 ^ 8)

theorem second_matrix_row_12224 (c : Ret 12224) (hc : c ∈ BstLean.Part164.Eop2 12224) :
    OpB (A2 c) (283 / 100) := by
  apply opB_of_opN
  refine hc.trans ?_
  have hs : √(2 / (mA 12224 : ℝ)) ≤ 1157 / 10 ^ 7 := by
    apply (sqrt_le_iff).mpr
    norm_num [mA]
  exact (mul_le_mul_of_nonneg_right hs (by norm_num : (0 : ℝ) ≤ 2 * 12224 + 5)).trans
    (by norm_num)

theorem root_reserve :
    √(2 * (1 + eta⁻¹) * removalBudget) + mixtureRoot + √displacementBudget +
      BstLean.Part241.biasRoot 12224 chi biasFloor epsilon varianceMax
        sharpAw sharpAf locationNorm varianceNorm +
      1 / 10 ^ 8 + 1 / 10 ^ 20 ≤ rootTarget := by
  rw [removal_root, displacement_root]
  have h := stored_bias_root
  norm_num [mixtureRoot, biasRootCap, rootTarget] at *
  linarith



theorem row_sqrt_bounds : (110 : ℝ) ≤ √12224 ∧ √12224 ≤ 112 := by
  constructor
  · exact Real.le_sqrt_of_sq_le (by norm_num)
  · exact (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩

theorem row_rule_size : (1350000 : ℝ) ≤ Jz 12224 ∧ 1000000 ≤ Jz 12224 := by
  have hr : (1105 / 10 : ℝ) ≤ √12224 := Real.le_sqrt_of_sq_le (by norm_num)
  have hx : (12224 : ℝ) * √12224 ≤ (⌈(12224 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by
    have he := rpow_three_halves 12224
    norm_num only [Nat.cast_ofNat] at he
    rw [← he]
    exact Nat.le_ceil _
  have hc : 1 ≤ ⌈(12224 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ := by
    have hh : (1 : ℝ) ≤ (⌈(12224 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) := by linarith
    exact_mod_cast hh
  have he : (Jz 12224 : ℝ) = (⌈(12224 : ℝ) ^ ((3 : ℝ) / 2)⌉₊ : ℝ) - 1 := by
    unfold Jz
    norm_num only [Nat.cast_ofNat]
    rw [Nat.cast_sub hc]
    simp
  have hh : (1350000 : ℝ) ≤ Jz 12224 := by rw [he]; linarith
  exact ⟨hh, by exact_mod_cast (show (1000000 : ℝ) ≤ Jz 12224 by linarith)⟩

theorem row_bulk_radius : (63 / 100 : ℝ) ≤ √(qB 12224) := by
  have h1 : √(54 / 100 : ℝ) ≤ 735 / 1000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h2 : √(55 / 100 / (12224 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have h0 : 0 ≤ √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12224 : ℝ)) := by positivity
  have hh : √(54 / 100 : ℝ) + 6 * √(55 / 100 / (12224 : ℝ)) ≤ 776 / 1000 := by
    linarith
  apply Real.le_sqrt_of_sq_le
  unfold qB
  nlinarith

theorem row_bulk_positive : 0 < qB 12224 := by
  have h := row_bulk_radius
  exact Real.sqrt_pos.mp (by linarith)

theorem row_grid_width : DeltaP 12224 ≤ (13 / 10 ^ 9 : ℝ) := by
  have h : √(55 / 100 / (12224 : ℝ)) ≤ 671 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  unfold DeltaP
  norm_num only [Nat.cast_ofNat]
  linarith

theorem row_location_grid {d : ℝ} (hd : d ≤ DeltaP 12224) :
    (12224 : ℝ) * (283 / 100 * 160 * (d / 2) / (√12224 * √(qB 12224))) ≤
      54 / 100000 := by
  have hden : (110 : ℝ) * (63 / 100) ≤ √12224 * √(qB 12224) :=
    mul_le_mul row_sqrt_bounds.1 row_bulk_radius (by norm_num) (sqrt_nonneg _)
  have hpos : 0 < √(12224 : ℝ) * √(qB 12224) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_energy_grid {d : ℝ} (hd : d ≤ DeltaP 12224) :
    (12224 : ℝ) * (2 * (283 / 100 * 160) ^ 2 * (d / 2) /
      (12224 * √(qB 12224))) ≤ 424 / 100000 := by
  have hden := row_bulk_radius
  have hpos : 0 < (12224 : ℝ) * √(qB 12224) := by linarith
  have hd' := hd.trans row_grid_width
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem row_location_rule :
    (12224 : ℝ) * (√12224 *
      (c1F (exp (1 / 2) / 12) (Jz 12224) * (186 / 10000) / Jz 12224)) ≤
      370 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c1F_le row_rule_size.2
  have hC0 := BstLean.Part169.c1F_nonneg (Jz 12224)
  have hm := mul_le_mul row_sqrt_bounds.2 hC hC0 (by norm_num : (0 : ℝ) ≤ 112)
  have he : (12224 : ℝ) * (√12224 *
      (c1F (exp (1 / 2) / 12) (Jz 12224) * (186 / 10000) / Jz 12224)) =
      (12224 * (√12224 * c1F (exp (1 / 2) / 12) (Jz 12224)) * (186 / 10000)) /
        Jz 12224 := by ring
  rw [he, div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12224)]
  nlinarith

theorem row_energy_rule :
    (12224 : ℝ) * (12224 *
      (c2F (exp (1 / 2) / 12) (Jz 12224) * (186 / 10000) ^ 2 / Jz 12224)) ≤
      355 / 100000 := by
  have hJ := row_rule_size.1
  have hC := BstLean.Part169.c2F_le row_rule_size.2
  rw [mul_div_assoc', mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < Jz 12224)]
  nlinarith





theorem first_matrix_op_row (c : Ret 12224) (hc : A1 c ∈ BstLean.Part153.Eop 12224) :
    BstLean.Part152.opN (A1 c) ≤ 160 := by
  refine hc.trans ?_
  have hs : √(2 / (12224 : ℝ)) ≤ 1285 / 100000 :=
    (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hn : √(12224 : ℝ) ≤ 111 := (sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hsum : (12224 : ℝ) + 2 * √12224 ≤ 12446 := by linarith
  exact (mul_le_mul hs hsum (by positivity) (by norm_num)).trans (by norm_num)

theorem row_node_variance (c : Ret 12224)
    (hc : A1 c ∈ BstLean.Part153.Eop 12224) {s : ℝ} (hs : s ^ 2 ≤ 1) :
    vsig2 c s ≤ (186 / 10000 : ℝ) ^ 2 := by
  have hop := first_matrix_op_row c hc
  have hop0 := BstLean.Part152.opN_nonneg (A1 c)
  have hop2 := pow_le_pow_left₀ hop0 hop 2
  have hm : (1 - s ^ 2) * ((12224 : ℝ) * BstLean.Part152.opN (A1 c) ^ 2) ≤
      12224 * 160 ^ 2 := by
    have hh := mul_le_mul (show 1 - s ^ 2 ≤ 1 by nlinarith)
      (mul_le_mul_of_nonneg_left hop2 (by norm_num : (0 : ℝ) ≤ 12224))
      (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hh := vsig2_le (by norm_num) c hs
  norm_num [mA] at hh
  nlinarith

structure ExactTableMoments (c : Ret 12224) (K : Set (Ix 12224)) : Prop where
  location : ∫ a in K, exF c a ^ 8 ∂muI 12224 ≤ tableF ^ 8
  energy : ∫ a in K, exW c a ^ 8 ∂muI 12224 ≤ tableW ^ 8

theorem stored_table_moments (c : Ret 12224) (hw : WINDOW (paperDesignP 12224) c)
    (hfirst : A1 c ∈ BstLean.Part153.Eop 12224) (hsecond : c ∈ BstLean.Part164.Eop2 12224)
    {K : Set (Ix 12224)} (hK : MeasurableSet K)
    (hsub : K ⊆ bulkIx (paperDesignP 12224) c) (hX : ExactTableMoments c K) :
    (∫ a in K, ((12224 : ℝ) * (wbR c a - wtR c a)) ^ 8 ∂muI 12224 ≤ sharpAw ^ 8) ∧
    (∫ a in K, ((12224 : ℝ) * (fbR c a - ftR c a)) ^ 8 ∂muI 12224 ≤ sharpAf ^ 8) := by
  have h1 := opB_of_opN (A1 c) (first_matrix_op_row c hfirst)
  have h2 := second_matrix_row_12224 c hsecond
  have hθ := BstLean.Part276.tightW_of_window (by norm_num) c hw
  obtain ⟨hLH, hbulk, hwidth⟩ := bulk_of_window (by norm_num) c hθ.1.1 hθ.1.2.1 hθ.1.2.2
  have hvs : ∀ a ∈ K, vsig2 c (sgR c a) ≤ (186 / 10000 : ℝ) ^ 2 := by
    intro a _
    obtain ⟨hs1, hs2⟩ := nodeS_mem c hLH
      (gIdx_lt c (by norm_num) (latC (paperDesignP 12224) c a))
    have hs := hbulk _ hs1 hs2
    exact row_node_variance c hfirst (by change _ ≤ 1; unfold sgR; linarith [row_bulk_positive])
  obtain ⟨MF, bF⟩ := bdd_exF (by norm_num) c
  obtain ⟨MW, bW⟩ := bdd_exW (by norm_num) c
  have iF := intOn_of_bdd ((measurable_exF c).pow_const 8)
    (bdd_pow bF 8) K
  have iW := intOn_of_bdd ((measurable_exW c).pow_const 8)
    (bdd_pow bW 8) K
  have htF : (0 : ℝ) < tableF := by norm_num [BstLean.Part276.tableF]
  have htW : (0 : ℝ) < tableW := by norm_num [BstLean.Part276.tableW]
  have hf := location_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    htF iF hX.location
  have he := energy_error_of_exact (by norm_num) c hK hsub h1 h2
    (by norm_num) (by norm_num) row_bulk_positive (by norm_num) hLH hbulk hvs
    htW iW hX.energy
  have hfg := row_location_grid hwidth
  have heg := row_energy_grid hwidth
  have hD : 0 < nodeD c := by
    unfold nodeD Js
    exact div_pos (by linarith) (by norm_num)
  have hc1 := BstLean.Part169.c1F_nonneg (Jz 12224)
  have hc2 := BstLean.Part169.c2F_nonneg (Jz 12224)
  constructor
  · refine he.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_energy_rule
    unfold sharpAw
    norm_num only [BstLean.Part276.tableW] at *
    linarith
  · refine hf.2.trans (pow_le_pow_left₀ (by positivity) ?_ 8)
    have hr := row_location_rule
    unfold sharpAf
    norm_num only [BstLean.Part276.tableF] at *
    linarith



theorem exactTableMoments_of_sharp {c : Ret 12224}
    (hw : WINDOW (paperDesignP 12224) c) (hc : c ∈ sharpTable) (K : Set (Ix 12224)) :
    ExactTableMoments c K := by
  have h := hc (tightW_of_window (by norm_num) c hw)
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

noncomputable def rowSplit (c : Ret 12224) (wl ws : ℝ) : SplitData 12224 :=
  BstLean.Part162.dPaper (paperDesignP 12224) c wl ws
    (√(2 / (12224 : ℝ) * mixtureFloor)) eta eta_pos eta_lt_one

theorem row_split_floor :
    (2 / (12224 : ℝ)) * biasFloor =
      (1 - eta) * (√(2 / (12224 : ℝ) * mixtureFloor)) ^ 2 := by
  rw [Real.sq_sqrt (by norm_num [mixtureFloor])]
  unfold biasFloor
  ring

/-- The fields are actual-network bounds. The table field is the sharp table event,
paid by `sharpTable_ret_charge`; the other moment fields and the three integrals
are the caller's supplies on the retained event. -/
structure SharpRootSource (t : ℝ) (c : Ret 12224) where
  wl : ℝ
  ws : ℝ
  window : WINDOW (paperDesignP 12224) c
  energy_pos : 0 < eR c
  centre : normSq c.2.1.2 ≤ (2 / (12224 : ℝ)) * eR c * 12224 * chi
  first : A1 c ∈ BstLean.Part153.Eop 12224
  second : c ∈ BstLean.Part164.Eop2 12224
  table : c ∈ sharpTable
  variance : ∀ a ∈ keptIx (paperDesignP 12224) c (rowSplit c wl ws), |VR c a| ≤ varianceMax
  location4 : ∫ a in keptIx (paperDesignP 12224) c (rowSplit c wl ws),
    fbR c a ^ 4 ∂muI 12224 ≤ locationNorm ^ 4
  location24 : ∫ a in keptIx (paperDesignP 12224) c (rowSplit c wl ws),
    fbR c a ^ 24 ∂muI 12224 ≤ locationNorm ^ 24
  variance2 : ∫ a in keptIx (paperDesignP 12224) c (rowSplit c wl ws),
    ((12224 : ℝ) * VR c a) ^ 2 ∂muI 12224 ≤ varianceNorm ^ 2
  removal : ∫ a, removed (stdGauss (Fin (12224 - 1)))
    (rowSplit c wl ws).good a ∂muI 12224 ≤ removalBudget
  mixture : ∫ a in keptIx (paperDesignP 12224) c (rowSplit c wl ws),
    (√(goodMean (stdGauss (Fin (12224 - 1))) (rowSplit c wl ws).good
      (pLat (paperDesignP 12224) t c) a) - √(q0Lat t c (rowSplit c wl ws) a)) ^ 2
      ∂muI 12224 ≤ mixtureRoot ^ 2
  displacement : ∫ a in keptIx (paperDesignP 12224) c (rowSplit c wl ws),
    hellG2 12224 (((rowSplit c wl ws).lam0 a - (rowSplit c wl ws).lamb a) ^ 2 *
      normSq c.2.1.2) ((rowSplit c wl ws).S0 a) ((rowSplit c wl ws).Sb a)
      ∂muI 12224 ≤ displacementBudget

/-- The statistics-to-moment transfer: the sharp table event gives the paper's
energy and location errors on the kept set. -/
theorem sharp_paper_moments {t : ℝ} {c : Ret 12224} (R : SharpRootSource t c) :
    PaperMoments c (keptIx (paperDesignP 12224) c (rowSplit c R.wl R.ws))
      varianceMax sharpAw sharpAf locationNorm varianceNorm := by
  have hK : MeasurableSet (keptIx (paperDesignP 12224) c (rowSplit c R.wl R.ws)) :=
    measurableSet_keptSet _ (rowSplit c R.wl R.ws).mgood (measurableSet_bulkIx _ _) _
  have hsub : keptIx (paperDesignP 12224) c (rowSplit c R.wl R.ws) ⊆
      bulkIx (paperDesignP 12224) c := fun _ h => h.1
  have htab := stored_table_moments c R.window R.first R.second hK hsub
    (exactTableMoments_of_sharp R.window R.table _)
  exact ⟨R.variance, htab.1, htab.2, R.location4, R.location24, R.variance2⟩

theorem row_pass_inputs {t : ℝ} {c : Ret 12224} (R : SharpRootSource t c) :
    BstLean.Part241.PassInputs c (rowSplit c R.wl R.ws) chi biasFloor epsilon
      varianceMax sharpAw sharpAf locationNorm varianceNorm := by
  exact passInputs_of_paperMoments (by norm_num) c eta_pos eta_lt_one
    (Real.sqrt_nonneg _) R.energy_pos bias_floor_ge (by norm_num [epsilon])
    bias_threshold_pos (by norm_num [sharpAw]) (by norm_num [sharpAf])
    (by norm_num [locationNorm]) (by norm_num [varianceNorm]) row_split_floor.le
    R.centre (sharp_paper_moments R)

/-- Acceptance object: `RootInputs` at 12224 with root `0.0074488`. -/
noncomputable def rootInputs {t : ℝ} {c : Ret 12224} (R : SharpRootSource t c) :
    BstLean.Part243.RootInputs 12224 t c rootTarget where
  split := rowSplit c R.wl R.ws
  chi := chi
  biasFloor := biasFloor
  epsilon := epsilon
  vmax := varianceMax
  aw := sharpAw
  af := sharpAf
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

theorem replacement_of_sharp_source {t : ℝ} {c : Ret 12224} (R : SharpRootSource t c) :
    |√(QStand (paperDesignP 12224) t c) - √(qTilde (paperDesignP 12224) t c)| ≤
      rootTarget := by
  let S := rootInputs R
  exact (BstLean.Part241.root_new_8000 (by norm_num) t c S.split S.window
    S.passes S.fluctuation).trans S.scalar

end BstLean.Part276.Row12224
